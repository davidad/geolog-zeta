//! Lazy tensor expressions.

use std::collections::{BTreeSet, HashMap};
use std::rc::Rc;

use super::sparse::{cartesian_product_of_extents, CartesianProductIter, SparseTensor};

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

    /// Lazy disjunction (union of extents)
    /// All children must have the same dimensions.
    /// Result is true wherever ANY child is true (pointwise OR).
    Sum(Vec<TensorExpr>),

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
            TensorExpr::Product(exprs) => exprs.iter().flat_map(|e| e.dims()).collect(),
            TensorExpr::Sum(exprs) => {
                // All children should have same dims; return first or empty
                exprs.first().map(|e| e.dims()).unwrap_or_default()
            }
            TensorExpr::Contract {
                inner,
                index_map,
                output,
            } => {
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
                let materialized: Vec<SparseTensor> =
                    exprs.iter().map(|e| e.materialize()).collect();
                let dims: Vec<usize> = materialized
                    .iter()
                    .flat_map(|t| t.dims.iter().copied())
                    .collect();
                let extent = cartesian_product_of_extents(&materialized);
                SparseTensor { dims, extent }
            }

            TensorExpr::Sum(exprs) => {
                if exprs.is_empty() {
                    // Empty disjunction = false = empty tensor with unknown dims
                    return SparseTensor::scalar(false);
                }
                // Union of extents (pointwise OR)
                let first = exprs[0].materialize();
                let dims = first.dims.clone();
                let mut extent = first.extent;

                for expr in &exprs[1..] {
                    let child = expr.materialize();
                    debug_assert_eq!(child.dims, dims, "Sum children must have same dimensions");
                    extent.extend(child.extent);
                }

                SparseTensor { dims, extent }
            }

            TensorExpr::Contract {
                inner,
                index_map,
                output,
            } => {
                // Check for fusion opportunity: Contract(Product(...))
                if let TensorExpr::Product(children) = inner.as_ref() {
                    return self.fused_join(children, index_map, output);
                }

                // Fusion: Contract(Sum(...)) distributes
                // Contract(Sum(a, b)) = Sum(Contract(a), Contract(b))
                if let TensorExpr::Sum(children) = inner.as_ref() {
                    let contracted_children: Vec<TensorExpr> = children
                        .iter()
                        .map(|child| TensorExpr::Contract {
                            inner: Box::new(child.clone()),
                            index_map: index_map.clone(),
                            output: output.clone(),
                        })
                        .collect();
                    return TensorExpr::Sum(contracted_children).materialize();
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
        let inner_dims: Vec<usize> = materialized
            .iter()
            .flat_map(|t| t.dims.iter().copied())
            .collect();
        let mut target_dims: HashMap<usize, usize> = HashMap::new();
        for (i, &target) in index_map.iter().enumerate() {
            target_dims.entry(target).or_insert(inner_dims[i]);
        }
        let output_targets: Vec<usize> = (0..=max_target).filter(|t| output.contains(t)).collect();
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
                        let combined: Vec<usize> =
                            tuple1.iter().chain(tuple2.iter()).copied().collect();
                        if let Some(out_tuple) = try_project(&combined, index_map, &output_targets)
                        {
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

    let output_targets: Vec<usize> = (0..=max_target).filter(|t| output.contains(t)).collect();
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

#[cfg(test)]
mod tests {
    use super::*;

    fn leaf(t: SparseTensor) -> TensorExpr {
        TensorExpr::leaf(t)
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
    fn test_sum_basic() {
        // R ∨ S where R = {(0,0), (1,1)} and S = {(1,1), (2,2)}
        let mut r = SparseTensor::empty(vec![3, 3]);
        r.insert(vec![0, 0]);
        r.insert(vec![1, 1]);

        let mut s = SparseTensor::empty(vec![3, 3]);
        s.insert(vec![1, 1]);
        s.insert(vec![2, 2]);

        let expr = TensorExpr::Sum(vec![leaf(r), leaf(s)]);
        let result = expr.materialize();

        assert_eq!(result.dims, vec![3, 3]);
        assert_eq!(result.len(), 3); // Union removes duplicates
        assert!(result.contains(&[0, 0]));
        assert!(result.contains(&[1, 1]));
        assert!(result.contains(&[2, 2]));
    }

    #[test]
    fn test_sum_empty() {
        // Empty disjunction = false
        let expr = TensorExpr::Sum(vec![]);
        let result = expr.materialize();

        assert!(result.is_empty());
    }

    #[test]
    fn test_contract_sum_distributes() {
        // Contract(Sum(R, S)) = Sum(Contract(R), Contract(S))
        // Using ∃y. (R(x,y) ∨ S(x,y))
        let mut r = SparseTensor::empty(vec![2, 2]);
        r.insert(vec![0, 0]);
        r.insert(vec![0, 1]);

        let mut s = SparseTensor::empty(vec![2, 2]);
        s.insert(vec![1, 0]);

        let sum = TensorExpr::Sum(vec![leaf(r), leaf(s)]);

        // ∃y: map y to fresh target, output only x
        let output: BTreeSet<usize> = [0].into_iter().collect();
        let expr = TensorExpr::Contract {
            inner: Box::new(sum),
            index_map: vec![0, 2], // x→0, y→2 (fresh)
            output,
        };

        let result = expr.materialize();

        assert_eq!(result.dims, vec![2]);
        assert_eq!(result.len(), 2);
        assert!(result.contains(&[0])); // from R
        assert!(result.contains(&[1])); // from S
    }
}
