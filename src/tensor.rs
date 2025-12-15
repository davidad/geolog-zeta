//! Lazy tensor expressions for axiom checking
//!
//! A tensor indexed by finite sets A₀, A₁, ..., Aₙ₋₁ is a function
//! [∏ᵢ Aᵢ] → Bool. We represent this sparsely as the set of tuples
//! mapping to true.
//!
//! Key insight: tensor product followed by contraction should NEVER
//! materialize the intermediate product. Instead, we build expression
//! trees and fuse operations during evaluation.
//!
//! Two primitives suffice for einsum-style operations:
//! - **tensor_product**: ⊗ₖ Sₖ — indexed by all indices, value = ∧ of contributions
//! - **contract**: along a:[N]→[M], output O⊆[M] — identifies indices, sums over non-output
//!
//! Over the Boolean semiring: product = AND, sum = OR.

use std::collections::{BTreeSet, HashMap};
use std::rc::Rc;

// ============================================================================
// SPARSE TENSOR (materialized)
// ============================================================================

/// A sparse Boolean tensor (materialized).
///
/// Indexed by a product of finite sets with given cardinalities.
/// Stores the set of index tuples that map to `true`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SparseTensor {
    /// Cardinality of each index dimension
    pub dims: Vec<usize>,
    /// Set of tuples (as Vec<usize>) where the tensor is true
    /// Each tuple has length == dims.len()
    pub extent: BTreeSet<Vec<usize>>,
}

impl SparseTensor {
    /// Create an empty tensor (all false) with given dimensions
    pub fn empty(dims: Vec<usize>) -> Self {
        Self {
            dims,
            extent: BTreeSet::new(),
        }
    }

    /// Create a scalar tensor (0-dimensional) with given value
    pub fn scalar(value: bool) -> Self {
        let mut extent = BTreeSet::new();
        if value {
            extent.insert(vec![]);
        }
        Self {
            dims: vec![],
            extent,
        }
    }

    /// Number of dimensions (arity)
    pub fn arity(&self) -> usize {
        self.dims.len()
    }

    /// Number of true entries
    pub fn len(&self) -> usize {
        self.extent.len()
    }

    /// Check if empty (all false)
    pub fn is_empty(&self) -> bool {
        self.extent.is_empty()
    }

    /// Check if a specific tuple is true
    pub fn contains(&self, tuple: &[usize]) -> bool {
        self.extent.contains(tuple)
    }

    /// Insert a tuple (set to true)
    pub fn insert(&mut self, tuple: Vec<usize>) -> bool {
        debug_assert_eq!(tuple.len(), self.dims.len());
        debug_assert!(tuple.iter().zip(&self.dims).all(|(v, d)| *v < *d));
        self.extent.insert(tuple)
    }

    /// Remove a tuple (set to false)
    pub fn remove(&mut self, tuple: &[usize]) -> bool {
        self.extent.remove(tuple)
    }

    /// Iterate over all true tuples
    pub fn iter(&self) -> impl Iterator<Item = &Vec<usize>> {
        self.extent.iter()
    }
}

// ============================================================================
// TENSOR EXPRESSION (lazy)
// ============================================================================

/// A lazy tensor expression.
///
/// Operations build up an expression tree rather than immediately computing.
/// Evaluation fuses operations to avoid materializing large intermediates.
#[derive(Clone, Debug)]
pub enum TensorExpr {
    /// Materialized sparse tensor (leaf)
    Leaf(Rc<SparseTensor>),

    /// Lazy tensor product (cross join)
    /// Result dimensions = concatenation of input dimensions
    Product(Vec<TensorExpr>),

    /// Lazy contraction
    /// Maps input indices to output indices; indices mapping to same target
    /// are identified; targets not in output are summed (OR'd) over.
    Contract {
        inner: Box<TensorExpr>,
        /// For each input index, which target index (in 0..M)
        index_map: Vec<usize>,
        /// Which target indices appear in output
        output: BTreeSet<usize>,
    },
}

/// Metadata about a tensor expression (computable without materializing)
#[derive(Clone, Debug)]
pub struct TensorMeta {
    pub dims: Vec<usize>,
}

impl TensorExpr {
    /// Create a leaf from a sparse tensor
    pub fn leaf(t: SparseTensor) -> Self {
        TensorExpr::Leaf(Rc::new(t))
    }

    /// Create a scalar (0-dimensional) tensor expression
    pub fn scalar(value: bool) -> Self {
        TensorExpr::leaf(SparseTensor::scalar(value))
    }

    /// Get dimensions without materializing
    pub fn dims(&self) -> Vec<usize> {
        match self {
            TensorExpr::Leaf(t) => t.dims.clone(),
            TensorExpr::Product(exprs) => {
                exprs.iter().flat_map(|e| e.dims()).collect()
            }
            TensorExpr::Contract { inner, index_map, output } => {
                let inner_dims = inner.dims();
                // Build target -> dim mapping
                let mut target_dims: HashMap<usize, usize> = HashMap::new();
                for (i, &target) in index_map.iter().enumerate() {
                    target_dims.entry(target).or_insert(inner_dims[i]);
                }
                // Output dims in order
                let max_target = index_map.iter().copied().max().unwrap_or(0);
                (0..=max_target)
                    .filter(|t| output.contains(t))
                    .map(|t| *target_dims.get(&t).unwrap_or(&1))
                    .collect()
            }
        }
    }

    /// Arity (number of dimensions)
    pub fn arity(&self) -> usize {
        self.dims().len()
    }

    /// Materialize the tensor expression into a sparse tensor.
    ///
    /// This is where fusion happens: Contract(Product(...)) is evaluated
    /// without materializing the intermediate product.
    pub fn materialize(&self) -> SparseTensor {
        match self {
            TensorExpr::Leaf(t) => (**t).clone(),

            TensorExpr::Product(exprs) => {
                if exprs.is_empty() {
                    return SparseTensor::scalar(true);
                }
                // Materialize children and compute Cartesian product
                let materialized: Vec<SparseTensor> = exprs.iter().map(|e| e.materialize()).collect();
                let dims: Vec<usize> = materialized.iter().flat_map(|t| t.dims.iter().copied()).collect();
                let extent = cartesian_product_of_extents(&materialized);
                SparseTensor { dims, extent }
            }

            TensorExpr::Contract { inner, index_map, output } => {
                // Check for fusion opportunity: Contract(Product(...))
                if let TensorExpr::Product(children) = inner.as_ref() {
                    return self.fused_join(children, index_map, output);
                }

                // Otherwise, materialize inner and contract
                let inner_tensor = inner.materialize();
                contract_sparse(&inner_tensor, index_map, output)
            }
        }
    }

    /// Fused evaluation of Contract(Product([...])).
    /// Avoids materializing the full Cartesian product.
    fn fused_join(
        &self,
        children: &[TensorExpr],
        index_map: &[usize],
        output: &BTreeSet<usize>,
    ) -> SparseTensor {
        if children.is_empty() {
            let inner_result = SparseTensor::scalar(true);
            return contract_sparse(&inner_result, index_map, output);
        }

        // Materialize children
        let materialized: Vec<SparseTensor> = children.iter().map(|e| e.materialize()).collect();

        // Compute dimension offsets for each child
        let mut offsets = vec![0usize];
        for t in &materialized {
            offsets.push(offsets.last().unwrap() + t.arity());
        }

        // Figure out which target indices come from which children
        // and which input indices map to each target
        let max_target = index_map.iter().copied().max().unwrap_or(0);
        let mut target_to_inputs: HashMap<usize, Vec<usize>> = HashMap::new();
        for (i, &target) in index_map.iter().enumerate() {
            target_to_inputs.entry(target).or_default().push(i);
        }

        // Build output dimensions
        let inner_dims: Vec<usize> = materialized.iter().flat_map(|t| t.dims.iter().copied()).collect();
        let mut target_dims: HashMap<usize, usize> = HashMap::new();
        for (i, &target) in index_map.iter().enumerate() {
            target_dims.entry(target).or_insert(inner_dims[i]);
        }
        let output_targets: Vec<usize> = (0..=max_target)
            .filter(|t| output.contains(t))
            .collect();
        let output_dims: Vec<usize> = output_targets
            .iter()
            .map(|t| *target_dims.get(t).unwrap_or(&1))
            .collect();

        // Use hash join for 2-way, nested loops otherwise
        // (Future: Leapfrog Triejoin for multi-way)
        let mut result_extent: BTreeSet<Vec<usize>> = BTreeSet::new();

        if materialized.len() == 2 {
            // Hash join
            let (t1, t2) = (&materialized[0], &materialized[1]);
            let offset2 = offsets[1];

            // Find join keys: target indices that have inputs from both t1 and t2
            let t1_range = 0..t1.arity();
            let t2_range = offset2..(offset2 + t2.arity());

            let mut join_targets: Vec<usize> = Vec::new();
            let mut t1_key_indices: Vec<usize> = Vec::new();
            let mut t2_key_indices: Vec<usize> = Vec::new();

            for (&target, inputs) in &target_to_inputs {
                let from_t1: Vec<_> = inputs.iter().filter(|&&i| t1_range.contains(&i)).collect();
                let from_t2: Vec<_> = inputs.iter().filter(|&&i| t2_range.contains(&i)).collect();
                if !from_t1.is_empty() && !from_t2.is_empty() {
                    join_targets.push(target);
                    t1_key_indices.push(*from_t1[0]); // First input from t1
                    t2_key_indices.push(*from_t2[0] - offset2); // First input from t2 (local index)
                }
            }

            // Build hash table on t1
            let mut hash_table: HashMap<Vec<usize>, Vec<&Vec<usize>>> = HashMap::new();
            for tuple in t1.iter() {
                let key: Vec<usize> = t1_key_indices.iter().map(|&i| tuple[i]).collect();
                hash_table.entry(key).or_default().push(tuple);
            }

            // Probe with t2
            for tuple2 in t2.iter() {
                let key: Vec<usize> = t2_key_indices.iter().map(|&i| tuple2[i]).collect();
                if let Some(matches) = hash_table.get(&key) {
                    for tuple1 in matches {
                        // Combine and check full consistency
                        let combined: Vec<usize> = tuple1.iter().chain(tuple2.iter()).copied().collect();
                        if let Some(out_tuple) = try_project(&combined, index_map, &output_targets) {
                            result_extent.insert(out_tuple);
                        }
                    }
                }
            }
        } else {
            // Nested loops for other cases
            for combo in CartesianProductIter::new(&materialized) {
                if let Some(out_tuple) = try_project(&combo, index_map, &output_targets) {
                    result_extent.insert(out_tuple);
                }
            }
        }

        SparseTensor {
            dims: output_dims,
            extent: result_extent,
        }
    }

    /// Iterate over result tuples without full materialization.
    /// (For now, just materializes; future: streaming evaluation)
    pub fn iter(&self) -> impl Iterator<Item = Vec<usize>> {
        self.materialize().extent.into_iter()
    }

    /// Check if result is empty (may short-circuit)
    pub fn is_empty(&self) -> bool {
        // Future: smarter emptiness checking
        self.materialize().is_empty()
    }

    /// Check if result contains a specific tuple
    pub fn contains(&self, tuple: &[usize]) -> bool {
        // Future: smarter containment checking
        self.materialize().contains(tuple)
    }
}

// ============================================================================
// BUILDER HELPERS
// ============================================================================

/// Conjunction of two tensor expressions with variable alignment.
///
/// Given tensors T₁ and T₂ with named variables, compute their conjunction
/// by building Product + Contract to identify shared variables.
pub fn conjunction(
    t1: TensorExpr,
    vars1: &[String],
    t2: TensorExpr,
    vars2: &[String],
) -> (TensorExpr, Vec<String>) {
    // Compute combined variable list and mapping
    let mut combined_vars: Vec<String> = vars1.to_vec();
    let mut var_to_target: HashMap<&str, usize> = HashMap::new();

    for (i, v) in vars1.iter().enumerate() {
        var_to_target.insert(v, i);
    }

    let mut index_map: Vec<usize> = (0..vars1.len()).collect();

    for v in vars2 {
        if let Some(&target) = var_to_target.get(v.as_str()) {
            index_map.push(target);
        } else {
            let new_target = combined_vars.len();
            var_to_target.insert(v, new_target);
            combined_vars.push(v.clone());
            index_map.push(new_target);
        }
    }

    let output: BTreeSet<usize> = (0..combined_vars.len()).collect();

    let expr = TensorExpr::Contract {
        inner: Box::new(TensorExpr::Product(vec![t1, t2])),
        index_map,
        output,
    };

    (expr, combined_vars)
}

/// Existential quantification over a variable.
///
/// Removes the variable by OR-ing over all its values (contraction).
pub fn exists(tensor: TensorExpr, vars: &[String], var: &str) -> (TensorExpr, Vec<String>) {
    let var_idx = vars.iter().position(|v| v == var);

    match var_idx {
        None => (tensor, vars.to_vec()),
        Some(idx) => {
            let fresh_target = vars.len();
            let index_map: Vec<usize> = (0..vars.len())
                .map(|i| if i == idx { fresh_target } else { i })
                .collect();

            let output: BTreeSet<usize> = (0..vars.len()).filter(|&i| i != idx).collect();

            let result_vars: Vec<String> = vars
                .iter()
                .enumerate()
                .filter(|&(i, _)| i != idx)
                .map(|(_, v)| v.clone())
                .collect();

            let expr = TensorExpr::Contract {
                inner: Box::new(tensor),
                index_map,
                output,
            };

            (expr, result_vars)
        }
    }
}

/// Multi-way conjunction with variable alignment.
pub fn conjunction_all(tensors: Vec<(TensorExpr, Vec<String>)>) -> (TensorExpr, Vec<String>) {
    if tensors.is_empty() {
        return (TensorExpr::scalar(true), vec![]);
    }

    let mut result = tensors.into_iter();
    let (mut acc_expr, mut acc_vars) = result.next().unwrap();

    for (expr, vars) in result {
        let (new_expr, new_vars) = conjunction(acc_expr, &acc_vars, expr, &vars);
        acc_expr = new_expr;
        acc_vars = new_vars;
    }

    (acc_expr, acc_vars)
}

// ============================================================================
// INTERNAL HELPERS
// ============================================================================

/// Contract a materialized sparse tensor.
fn contract_sparse(
    tensor: &SparseTensor,
    index_map: &[usize],
    output: &BTreeSet<usize>,
) -> SparseTensor {
    let max_target = index_map.iter().copied().max().unwrap_or(0);
    let mut target_dims: HashMap<usize, usize> = HashMap::new();
    for (i, &target) in index_map.iter().enumerate() {
        target_dims.entry(target).or_insert(tensor.dims[i]);
    }

    let output_targets: Vec<usize> = (0..=max_target)
        .filter(|t| output.contains(t))
        .collect();
    let output_dims: Vec<usize> = output_targets
        .iter()
        .map(|t| *target_dims.get(t).unwrap_or(&1))
        .collect();

    let mut extent: BTreeSet<Vec<usize>> = BTreeSet::new();

    for input_tuple in tensor.iter() {
        if let Some(out_tuple) = try_project(input_tuple, index_map, &output_targets) {
            extent.insert(out_tuple);
        }
    }

    SparseTensor {
        dims: output_dims,
        extent,
    }
}

/// Try to project a combined tuple to output indices.
/// Returns None if identified indices don't match.
fn try_project(
    combined: &[usize],
    index_map: &[usize],
    output_targets: &[usize],
) -> Option<Vec<usize>> {
    let mut target_values: HashMap<usize, usize> = HashMap::new();

    for (i, &val) in combined.iter().enumerate() {
        let target = index_map[i];
        if let Some(&existing) = target_values.get(&target) {
            if existing != val {
                return None; // Inconsistent
            }
        } else {
            target_values.insert(target, val);
        }
    }

    Some(
        output_targets
            .iter()
            .map(|t| *target_values.get(t).unwrap_or(&0))
            .collect(),
    )
}

/// Cartesian product of extents of multiple sparse tensors
fn cartesian_product_of_extents(tensors: &[SparseTensor]) -> BTreeSet<Vec<usize>> {
    CartesianProductIter::new(tensors).collect()
}

/// Iterator over Cartesian product of sparse tensor extents
struct CartesianProductIter<'a> {
    tensors: &'a [SparseTensor],
    iterators: Vec<std::collections::btree_set::Iter<'a, Vec<usize>>>,
    current: Vec<Option<&'a Vec<usize>>>,
    done: bool,
}

impl<'a> CartesianProductIter<'a> {
    fn new(tensors: &'a [SparseTensor]) -> Self {
        if tensors.is_empty() {
            return Self {
                tensors,
                iterators: vec![],
                current: vec![],
                done: false,
            };
        }

        let done = tensors.iter().any(|t| t.is_empty());
        let mut iterators: Vec<_> = tensors.iter().map(|t| t.extent.iter()).collect();
        let current: Vec<_> = iterators.iter_mut().map(|it| it.next()).collect();

        Self {
            tensors,
            iterators,
            current,
            done,
        }
    }
}

impl<'a> Iterator for CartesianProductIter<'a> {
    type Item = Vec<usize>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }

        if self.tensors.is_empty() {
            self.done = true;
            return Some(vec![]);
        }

        // Build result
        let result: Vec<usize> = self
            .current
            .iter()
            .filter_map(|opt| opt.as_ref())
            .flat_map(|tuple| tuple.iter().copied())
            .collect();

        // Advance (odometer style)
        for i in (0..self.tensors.len()).rev() {
            if let Some(next) = self.iterators[i].next() {
                self.current[i] = Some(next);
                break;
            } else {
                self.iterators[i] = self.tensors[i].extent.iter();
                self.current[i] = self.iterators[i].next();
                if i == 0 {
                    self.done = true;
                }
            }
        }

        Some(result)
    }
}

// ============================================================================
// TESTS
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn leaf(t: SparseTensor) -> TensorExpr {
        TensorExpr::leaf(t)
    }

    #[test]
    fn test_sparse_tensor_basic() {
        let mut t = SparseTensor::empty(vec![3, 2]);
        assert_eq!(t.arity(), 2);
        assert!(t.is_empty());

        t.insert(vec![0, 1]);
        t.insert(vec![2, 0]);
        assert_eq!(t.len(), 2);
        assert!(t.contains(&[0, 1]));
        assert!(t.contains(&[2, 0]));
        assert!(!t.contains(&[0, 0]));
    }

    #[test]
    fn test_product_simple() {
        let mut r = SparseTensor::empty(vec![3]);
        r.insert(vec![0]);
        r.insert(vec![2]);

        let mut s = SparseTensor::empty(vec![2]);
        s.insert(vec![1]);

        let expr = TensorExpr::Product(vec![leaf(r), leaf(s)]);
        let result = expr.materialize();

        assert_eq!(result.dims, vec![3, 2]);
        assert_eq!(result.len(), 2);
        assert!(result.contains(&[0, 1]));
        assert!(result.contains(&[2, 1]));
    }

    #[test]
    fn test_contract_reduction() {
        let mut t = SparseTensor::empty(vec![2, 3]);
        t.insert(vec![0, 0]);
        t.insert(vec![0, 2]);
        t.insert(vec![1, 1]);

        let output: BTreeSet<usize> = [0].into_iter().collect();
        let expr = TensorExpr::Contract {
            inner: Box::new(leaf(t)),
            index_map: vec![0, 1],
            output,
        };
        let result = expr.materialize();

        assert_eq!(result.dims, vec![2]);
        assert_eq!(result.len(), 2);
        assert!(result.contains(&[0]));
        assert!(result.contains(&[1]));
    }

    #[test]
    fn test_conjunction() {
        let mut r = SparseTensor::empty(vec![2, 2]);
        r.insert(vec![0, 1]);

        let mut s = SparseTensor::empty(vec![2, 2]);
        s.insert(vec![1, 0]);
        s.insert(vec![1, 1]);

        let vars_r = vec!["x".to_string(), "y".to_string()];
        let vars_s = vec!["y".to_string(), "z".to_string()];

        let (expr, vars) = conjunction(leaf(r), &vars_r, leaf(s), &vars_s);
        let result = expr.materialize();

        assert_eq!(vars, vec!["x", "y", "z"]);
        assert_eq!(result.dims, vec![2, 2, 2]);
        assert_eq!(result.len(), 2);
        assert!(result.contains(&[0, 1, 0]));
        assert!(result.contains(&[0, 1, 1]));
    }

    #[test]
    fn test_exists() {
        let mut t = SparseTensor::empty(vec![2, 2]);
        t.insert(vec![0, 0]);
        t.insert(vec![0, 1]);
        t.insert(vec![1, 1]);

        let vars = vec!["x".to_string(), "y".to_string()];
        let (expr, result_vars) = exists(leaf(t), &vars, "y");
        let result = expr.materialize();

        assert_eq!(result_vars, vec!["x"]);
        assert_eq!(result.dims, vec![2]);
        assert_eq!(result.len(), 2);
    }

    #[test]
    fn test_relational_join() {
        // R(x,y) ⋈ S(y,z) then ∃y
        let mut r = SparseTensor::empty(vec![3, 3]);
        r.insert(vec![0, 1]);
        r.insert(vec![1, 2]);

        let mut s = SparseTensor::empty(vec![3, 3]);
        s.insert(vec![0, 1]);
        s.insert(vec![1, 2]);

        let vars_r = vec!["x".to_string(), "y".to_string()];
        let vars_s = vec!["y".to_string(), "z".to_string()];

        let (conj, vars) = conjunction(leaf(r), &vars_r, leaf(s), &vars_s);
        assert_eq!(vars, vec!["x", "y", "z"]);

        let (result_expr, result_vars) = exists(conj, &vars, "y");
        let result = result_expr.materialize();

        assert_eq!(result_vars, vec!["x", "z"]);
        assert!(result.contains(&[0, 2])); // path 0→1→2
    }

    #[test]
    fn test_fused_join_uses_hash() {
        // Large-ish tensors to verify hash join path works
        let mut r = SparseTensor::empty(vec![100, 100]);
        let mut s = SparseTensor::empty(vec![100, 100]);

        // Sparse data
        for i in 0..50 {
            r.insert(vec![i, i + 1]);
            s.insert(vec![i + 1, i + 2]);
        }

        let vars_r = vec!["x".to_string(), "y".to_string()];
        let vars_s = vec!["y".to_string(), "z".to_string()];

        let (conj, vars) = conjunction(leaf(r), &vars_r, leaf(s), &vars_s);
        let (result_expr, _) = exists(conj, &vars, "y");
        let result = result_expr.materialize();

        // Should have 50 paths: 0→2, 1→3, ..., 49→51
        assert_eq!(result.len(), 50);
        assert!(result.contains(&[0, 2]));
        assert!(result.contains(&[49, 51]));
    }
}
