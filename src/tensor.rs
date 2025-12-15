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
            TensorExpr::Sum(exprs) => {
                // All children should have same dims; return first or empty
                exprs.first().map(|e| e.dims()).unwrap_or_default()
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

            TensorExpr::Contract { inner, index_map, output } => {
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

/// Disjunction of two tensor expressions with variable alignment.
///
/// Both tensors must have the same variables (possibly in different order).
/// The result is the pointwise OR.
pub fn disjunction(
    t1: TensorExpr,
    vars1: &[String],
    t2: TensorExpr,
    vars2: &[String],
) -> (TensorExpr, Vec<String>) {
    // Check that variables are the same set
    let set1: std::collections::HashSet<_> = vars1.iter().collect();
    let set2: std::collections::HashSet<_> = vars2.iter().collect();

    if set1 != set2 {
        // For disjunction, variables must match. If they don't, we need to
        // align them by extending each tensor with the missing variables
        // (treating them as "any value" via Product with full domain).
        // For now, we require exact match since this is the geometric logic case.
        panic!(
            "disjunction requires same variables; got {:?} vs {:?}",
            vars1, vars2
        );
    }

    // If vars2 is in different order than vars1, reorder t2 via Contract
    if vars1 == vars2 {
        // Same order, just union
        (TensorExpr::Sum(vec![t1, t2]), vars1.to_vec())
    } else {
        // Need to reorder t2 to match vars1 ordering
        // Build index_map from vars2 positions to vars1 positions
        let index_map: Vec<usize> = vars2
            .iter()
            .map(|v| vars1.iter().position(|v1| v1 == v).unwrap())
            .collect();
        let output: BTreeSet<usize> = (0..vars1.len()).collect();

        let t2_reordered = TensorExpr::Contract {
            inner: Box::new(t2),
            index_map,
            output,
        };

        (TensorExpr::Sum(vec![t1, t2_reordered]), vars1.to_vec())
    }
}

/// Multi-way disjunction with variable alignment.
///
/// All tensors must have the same variables.
pub fn disjunction_all(tensors: Vec<(TensorExpr, Vec<String>)>) -> (TensorExpr, Vec<String>) {
    if tensors.is_empty() {
        return (TensorExpr::scalar(false), vec![]);
    }

    let mut result = tensors.into_iter();
    let (mut acc_expr, mut acc_vars) = result.next().unwrap();

    for (expr, vars) in result {
        let (new_expr, new_vars) = disjunction(acc_expr, &acc_vars, expr, &vars);
        acc_expr = new_expr;
        acc_vars = new_vars;
    }

    (acc_expr, acc_vars)
}

// ============================================================================
// FORMULA COMPILATION
// ============================================================================

use crate::core::{Context, DerivedSort, Formula, RelId, Signature, Structure, Term};
use crate::id::{NumericId, Slid};

/// Context for formula compilation, tracking variable names and their dimensions.
#[derive(Clone, Debug)]
pub struct CompileContext {
    /// Variable names in order (these become tensor dimensions)
    pub vars: Vec<String>,
    /// Variable sorts (for looking up cardinalities)
    pub sorts: Vec<DerivedSort>,
}

impl CompileContext {
    pub fn new() -> Self {
        Self {
            vars: vec![],
            sorts: vec![],
        }
    }

    pub fn from_context(ctx: &Context) -> Self {
        Self {
            vars: ctx.vars.iter().map(|(n, _)| n.clone()).collect(),
            sorts: ctx.vars.iter().map(|(_, s)| s.clone()).collect(),
        }
    }

    pub fn lookup(&self, name: &str) -> Option<usize> {
        self.vars.iter().position(|n| n == name)
    }

    pub fn add(&mut self, name: String, sort: DerivedSort) {
        self.vars.push(name);
        self.sorts.push(sort);
    }
}

impl Default for CompileContext {
    fn default() -> Self {
        Self::new()
    }
}

/// Get the cardinality of a base sort in the structure.
pub fn sort_cardinality(structure: &Structure, sort_id: usize) -> usize {
    structure.carriers[sort_id].len() as usize
}

/// Get the cardinality of a derived sort.
pub fn derived_sort_cardinality(structure: &Structure, sort: &DerivedSort) -> usize {
    match sort {
        DerivedSort::Base(sort_id) => sort_cardinality(structure, *sort_id),
        DerivedSort::Product(fields) => {
            // Product cardinality is the product of field cardinalities
            fields
                .iter()
                .map(|(_, s)| derived_sort_cardinality(structure, s))
                .product()
        }
    }
}

/// Build a Slid-to-index map for a sort's carrier.
/// Returns a map from Slid to its position within the carrier.
pub fn build_carrier_index(structure: &Structure, sort_id: usize) -> HashMap<Slid, usize> {
    structure.carriers[sort_id]
        .iter()
        .enumerate()
        .map(|(idx, slid_u64)| (Slid::from_usize(slid_u64 as usize), idx))
        .collect()
}

/// Convert a VecRelation to a SparseTensor.
///
/// The relation has tuples of Slids; we convert to indices using carrier maps.
/// `column_sorts` specifies the sort of each column for looking up carriers.
pub fn relation_to_tensor(
    structure: &Structure,
    rel_id: RelId,
    column_sorts: &[usize], // SortId for each column
) -> SparseTensor {
    let relation = &structure.relations[rel_id];

    // Build carrier index maps for each column
    let carrier_indices: Vec<HashMap<Slid, usize>> = column_sorts
        .iter()
        .map(|&sort_id| build_carrier_index(structure, sort_id))
        .collect();

    // Build dimensions from carrier sizes
    let dims: Vec<usize> = column_sorts
        .iter()
        .map(|&sort_id| structure.carriers[sort_id].len() as usize)
        .collect();

    // Convert tuples
    let mut extent = BTreeSet::new();
    for tuple in relation.iter() {
        let indices: Option<Vec<usize>> = tuple
            .iter()
            .zip(&carrier_indices)
            .map(|(&slid, index_map)| index_map.get(&slid).copied())
            .collect();

        if let Some(idx_tuple) = indices {
            extent.insert(idx_tuple);
        }
        // Skip tuples with elements not in carriers (shouldn't happen in valid data)
    }

    SparseTensor { dims, extent }
}

/// Extract variable names from a term pattern.
/// Returns pairs of (field_position, variable_name).
fn extract_term_vars(term: &Term) -> Vec<(usize, String, DerivedSort)> {
    match term {
        Term::Var(name, sort) => vec![(0, name.clone(), sort.clone())],
        Term::Record(fields) => fields
            .iter()
            .enumerate()
            .flat_map(|(i, (_, t))| {
                extract_term_vars(t)
                    .into_iter()
                    .map(move |(_, name, sort)| (i, name, sort))
            })
            .collect(),
        // For function applications and projections, we'd need more work
        Term::App(_, _) | Term::Project(_, _) => {
            // These are more complex - for now, treat as opaque
            vec![]
        }
    }
}

/// Get the base sort IDs from a relation's domain.
fn relation_column_sorts(sig: &Signature, rel_id: RelId) -> Vec<usize> {
    let rel_sym = &sig.relations[rel_id];
    match &rel_sym.domain {
        DerivedSort::Base(sort_id) => vec![*sort_id],
        DerivedSort::Product(fields) => fields
            .iter()
            .filter_map(|(_, sort)| {
                if let DerivedSort::Base(sort_id) = sort {
                    Some(*sort_id)
                } else {
                    None // Nested products not supported yet
                }
            })
            .collect(),
    }
}

/// Compile a formula to a tensor expression.
///
/// Returns the expression and the list of free variables in order.
pub fn compile_formula(
    formula: &Formula,
    ctx: &CompileContext,
    structure: &Structure,
    sig: &Signature,
) -> (TensorExpr, Vec<String>) {
    match formula {
        Formula::True => (TensorExpr::scalar(true), vec![]),

        Formula::False => (TensorExpr::scalar(false), vec![]),

        Formula::Rel(rel_id, term) => {
            // Extract variables from the term pattern
            let vars_info = extract_term_vars(term);
            let column_sorts = relation_column_sorts(sig, *rel_id);

            // Build the tensor from the relation
            let tensor = relation_to_tensor(structure, *rel_id, &column_sorts);

            // Build variable list (ordered by column position)
            let mut var_info_sorted = vars_info.clone();
            var_info_sorted.sort_by_key(|(pos, _, _)| *pos);

            // Check for repeated variables (same variable in multiple columns)
            // e.g., edge(x, x) should produce a diagonal tensor
            let mut seen_vars: HashMap<String, usize> = HashMap::new();
            let mut unique_vars: Vec<String> = Vec::new();
            let mut index_map: Vec<usize> = Vec::new();

            for (_, name, _) in &var_info_sorted {
                if let Some(&existing_idx) = seen_vars.get(name) {
                    // Repeated variable: map to same target
                    index_map.push(existing_idx);
                } else {
                    // New variable
                    let new_idx = unique_vars.len();
                    seen_vars.insert(name.clone(), new_idx);
                    unique_vars.push(name.clone());
                    index_map.push(new_idx);
                }
            }

            // If all variables are unique, no contraction needed
            if unique_vars.len() == var_info_sorted.len() {
                (TensorExpr::leaf(tensor), unique_vars)
            } else {
                // Need to contract to handle repeated variables (diagonal)
                let output: BTreeSet<usize> = (0..unique_vars.len()).collect();
                let expr = TensorExpr::Contract {
                    inner: Box::new(TensorExpr::leaf(tensor)),
                    index_map,
                    output,
                };
                (expr, unique_vars)
            }
        }

        Formula::Conj(formulas) => {
            if formulas.is_empty() {
                return (TensorExpr::scalar(true), vec![]);
            }

            let compiled: Vec<(TensorExpr, Vec<String>)> = formulas
                .iter()
                .map(|f| compile_formula(f, ctx, structure, sig))
                .collect();

            conjunction_all(compiled)
        }

        Formula::Disj(formulas) => {
            if formulas.is_empty() {
                return (TensorExpr::scalar(false), vec![]);
            }

            let compiled: Vec<(TensorExpr, Vec<String>)> = formulas
                .iter()
                .map(|f| compile_formula(f, ctx, structure, sig))
                .collect();

            disjunction_all(compiled)
        }

        Formula::Exists(var_name, _sort, inner) => {
            // Compile inner formula
            let (inner_expr, inner_vars) = compile_formula(inner, ctx, structure, sig);

            // Apply existential (sum over the variable)
            exists(inner_expr, &inner_vars, var_name)
        }

        Formula::Eq(t1, t2) => {
            // Handle equality - for now, only simple variable equality
            match (t1, t2) {
                (Term::Var(name1, sort1), Term::Var(name2, _sort2)) => {
                    if name1 == name2 {
                        // x = x is always true
                        (TensorExpr::scalar(true), vec![])
                    } else {
                        // x = y: diagonal tensor
                        // Both variables must have the same sort
                        let DerivedSort::Base(sort_id) = sort1 else {
                            panic!("Equality on non-base sorts not yet supported");
                        };
                        let card = sort_cardinality(structure, *sort_id);

                        // Create diagonal: (x, y) where x == y
                        let mut extent = BTreeSet::new();
                        for i in 0..card {
                            extent.insert(vec![i, i]);
                        }

                        let tensor = SparseTensor {
                            dims: vec![card, card],
                            extent,
                        };

                        // Order: alphabetically for consistency
                        let vars = if name1 < name2 {
                            vec![name1.clone(), name2.clone()]
                        } else {
                            vec![name2.clone(), name1.clone()]
                        };

                        // If we swapped order, we need to reorder tensor dimensions
                        let tensor = if name1 < name2 {
                            tensor
                        } else {
                            // Swap dimensions - but for diagonal, it's symmetric!
                            tensor
                        };

                        (TensorExpr::leaf(tensor), vars)
                    }
                }
                _ => {
                    // More complex term equality not yet implemented
                    // For now, panic; later could compile to more complex expressions
                    panic!("Complex term equality not yet supported");
                }
            }
        }
    }
}

// ============================================================================
// SEQUENT CHECKING
// ============================================================================

use crate::core::Sequent;

/// A violation of a sequent: a variable assignment where the premise holds but conclusion doesn't.
#[derive(Clone, Debug)]
pub struct Violation {
    /// The tuple indices representing the variable assignment
    pub assignment: Vec<usize>,
    /// Variable names (for debugging/reporting)
    pub variable_names: Vec<String>,
}

impl Violation {
    pub fn new(assignment: Vec<usize>, variable_names: Vec<String>) -> Self {
        Self {
            assignment,
            variable_names,
        }
    }
}

/// Result of checking a sequent
#[derive(Clone, Debug)]
pub enum CheckResult {
    /// The sequent is satisfied (all assignments that satisfy the premise also satisfy the conclusion)
    Satisfied,
    /// The sequent is violated (some assignments satisfy the premise but not the conclusion)
    Violated(Vec<Violation>),
}

impl CheckResult {
    pub fn is_satisfied(&self) -> bool {
        matches!(self, CheckResult::Satisfied)
    }

    pub fn violations(&self) -> &[Violation] {
        match self {
            CheckResult::Satisfied => &[],
            CheckResult::Violated(vs) => vs,
        }
    }
}

/// Check if a sequent is satisfied by a structure.
///
/// For sequent `∀ctx. premise ⊢ conclusion`:
/// - Compiles both premise and conclusion to TensorExprs
/// - Materializes both (with fusion)
/// - Checks that every tuple in premise is also in conclusion
///
/// Returns `CheckResult::Satisfied` if the sequent holds, or `CheckResult::Violated`
/// with a list of violating assignments.
pub fn check_sequent(
    sequent: &Sequent,
    structure: &Structure,
    sig: &Signature,
) -> CheckResult {
    let ctx = CompileContext::from_context(&sequent.context);

    // Compile premise and conclusion
    let (premise_expr, premise_vars) = compile_formula(&sequent.premise, &ctx, structure, sig);
    let (conclusion_expr, conclusion_vars) = compile_formula(&sequent.conclusion, &ctx, structure, sig);

    // Materialize both
    let premise_tensor = premise_expr.materialize();
    let conclusion_tensor = conclusion_expr.materialize();

    // Handle edge cases
    if premise_tensor.is_empty() {
        // Vacuously true: no assignments satisfy the premise
        return CheckResult::Satisfied;
    }

    // Handle case where conclusion is scalar true (no variables)
    if conclusion_vars.is_empty() && conclusion_tensor.contains(&[]) {
        // Conclusion is just "true" - always satisfied
        return CheckResult::Satisfied;
    }

    // Handle case where premise has no variables (scalar) but conclusion has variables
    // This means premise is "true" and we need to check conclusion holds universally
    if premise_vars.is_empty() && !conclusion_vars.is_empty() {
        // Premise is "true", need to check if conclusion is universally true
        // This means: for all values of conclusion_vars, conclusion holds
        // We need to enumerate the domain from the context

        // Get the domain sizes from conclusion variable sorts
        // We need to look up sorts in the context
        let domain_sizes: Vec<usize> = sequent
            .context
            .vars
            .iter()
            .filter(|(name, _)| conclusion_vars.contains(name))
            .map(|(_, sort)| derived_sort_cardinality(structure, sort))
            .collect();

        // Check that conclusion covers all tuples in the domain
        let expected_count: usize = domain_sizes.iter().product();

        if conclusion_tensor.len() == expected_count {
            // All tuples covered
            return CheckResult::Satisfied;
        }

        // Find violations: tuples in domain not in conclusion
        let mut violations = Vec::new();
        for tuple in DomainIterator::new(&domain_sizes) {
            if !conclusion_tensor.contains(&tuple) {
                violations.push(Violation::new(tuple, conclusion_vars.clone()));
            }
        }

        return if violations.is_empty() {
            CheckResult::Satisfied
        } else {
            CheckResult::Violated(violations)
        };
    }

    // Build mapping from premise vars to conclusion vars
    // Premise might have MORE variables than conclusion (e.g., ∃y quantified out in conclusion)
    // We need to project premise tuples to conclusion variables
    let _projection: Vec<Option<usize>> = premise_vars
        .iter()
        .map(|pv| conclusion_vars.iter().position(|cv| cv == pv))
        .collect();

    // All conclusion vars should be present in premise vars
    // (premise provides the context for checking)
    for cv in &conclusion_vars {
        if !premise_vars.contains(cv) {
            // This shouldn't happen in well-formed sequents
            panic!(
                "Conclusion variable '{}' not found in premise variables {:?}",
                cv, premise_vars
            );
        }
    }

    // Check: for every tuple in premise, the projected tuple should be in conclusion
    let mut violations = Vec::new();

    for tuple in premise_tensor.iter() {
        // Project premise tuple to conclusion vars
        let conclusion_tuple: Vec<usize> = conclusion_vars
            .iter()
            .map(|cv| {
                let premise_idx = premise_vars.iter().position(|pv| pv == cv).unwrap();
                tuple[premise_idx]
            })
            .collect();

        if !conclusion_tensor.contains(&conclusion_tuple) {
            violations.push(Violation::new(tuple.clone(), premise_vars.clone()));
        }
    }

    if violations.is_empty() {
        CheckResult::Satisfied
    } else {
        CheckResult::Violated(violations)
    }
}

/// Check if a sequent is satisfied, returning just a boolean.
pub fn check_sequent_bool(
    sequent: &Sequent,
    structure: &Structure,
    sig: &Signature,
) -> bool {
    check_sequent(sequent, structure, sig).is_satisfied()
}

/// Check multiple sequents (axioms of a theory) against a structure.
/// Returns a list of (sequent_index, violations) for each violated sequent.
pub fn check_theory_axioms(
    axioms: &[Sequent],
    structure: &Structure,
    sig: &Signature,
) -> Vec<(usize, Vec<Violation>)> {
    axioms
        .iter()
        .enumerate()
        .filter_map(|(i, seq)| {
            match check_sequent(seq, structure, sig) {
                CheckResult::Satisfied => None,
                CheckResult::Violated(vs) => Some((i, vs)),
            }
        })
        .collect()
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

/// Iterator over all tuples in a domain (Cartesian product of ranges)
struct DomainIterator {
    dims: Vec<usize>,
    current: Vec<usize>,
    done: bool,
}

impl DomainIterator {
    fn new(dims: &[usize]) -> Self {
        let done = dims.contains(&0);
        Self {
            dims: dims.to_vec(),
            current: vec![0; dims.len()],
            done,
        }
    }
}

impl Iterator for DomainIterator {
    type Item = Vec<usize>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }

        if self.dims.is_empty() {
            self.done = true;
            return Some(vec![]);
        }

        let result = self.current.clone();

        // Advance (odometer style)
        for i in (0..self.dims.len()).rev() {
            self.current[i] += 1;
            if self.current[i] < self.dims[i] {
                break;
            }
            self.current[i] = 0;
            if i == 0 {
                self.done = true;
            }
        }

        Some(result)
    }
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

    /// Helper to create Slid from integer
    fn slid(n: usize) -> Slid {
        Slid::from_usize(n)
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

    // ========================================================================
    // DISJUNCTION TESTS
    // ========================================================================

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
    fn test_disjunction_same_vars() {
        // R(x,y) ∨ S(x,y) with same variable order
        let mut r = SparseTensor::empty(vec![2, 2]);
        r.insert(vec![0, 0]);

        let mut s = SparseTensor::empty(vec![2, 2]);
        s.insert(vec![1, 1]);

        let vars = vec!["x".to_string(), "y".to_string()];

        let (expr, result_vars) = disjunction(leaf(r), &vars, leaf(s), &vars);
        let result = expr.materialize();

        assert_eq!(result_vars, vec!["x", "y"]);
        assert_eq!(result.len(), 2);
        assert!(result.contains(&[0, 0]));
        assert!(result.contains(&[1, 1]));
    }

    #[test]
    fn test_disjunction_reordered_vars() {
        // R(x,y) ∨ S(y,x) - different variable order requires reordering
        let mut r = SparseTensor::empty(vec![2, 3]);
        r.insert(vec![0, 1]); // x=0, y=1

        let mut s = SparseTensor::empty(vec![3, 2]);
        s.insert(vec![2, 1]); // y=2, x=1

        let vars_r = vec!["x".to_string(), "y".to_string()];
        let vars_s = vec!["y".to_string(), "x".to_string()];

        let (expr, result_vars) = disjunction(leaf(r), &vars_r, leaf(s), &vars_s);
        let result = expr.materialize();

        assert_eq!(result_vars, vec!["x", "y"]);
        assert_eq!(result.len(), 2);
        assert!(result.contains(&[0, 1])); // from R
        assert!(result.contains(&[1, 2])); // from S reordered
    }

    #[test]
    fn test_disjunction_all() {
        // R(x) ∨ S(x) ∨ T(x)
        let mut r = SparseTensor::empty(vec![5]);
        r.insert(vec![0]);

        let mut s = SparseTensor::empty(vec![5]);
        s.insert(vec![1]);

        let mut t = SparseTensor::empty(vec![5]);
        t.insert(vec![2]);

        let vars = vec!["x".to_string()];

        let (expr, result_vars) = disjunction_all(vec![
            (leaf(r), vars.clone()),
            (leaf(s), vars.clone()),
            (leaf(t), vars.clone()),
        ]);
        let result = expr.materialize();

        assert_eq!(result_vars, vec!["x"]);
        assert_eq!(result.len(), 3);
        assert!(result.contains(&[0]));
        assert!(result.contains(&[1]));
        assert!(result.contains(&[2]));
    }

    #[test]
    fn test_disjunction_all_empty() {
        // Empty disjunction = false
        let (expr, vars) = disjunction_all(vec![]);
        let result = expr.materialize();

        assert!(vars.is_empty());
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

    #[test]
    fn test_geometric_formula_pattern() {
        // Test pattern from geometric logic: ∃y. (R(x,y) ∧ S(y)) ∨ (T(x))
        // This exercises Sum inside a more complex expression

        // R(x,y): edges 0→1, 1→2
        let mut r = SparseTensor::empty(vec![3, 3]);
        r.insert(vec![0, 1]);
        r.insert(vec![1, 2]);

        // S(y): valid y values {1, 2}
        let mut s = SparseTensor::empty(vec![3]);
        s.insert(vec![1]);
        s.insert(vec![2]);

        // T(x): alternative x values {2}
        let mut t = SparseTensor::empty(vec![3]);
        t.insert(vec![2]);

        // Build: R(x,y) ∧ S(y)
        let vars_r = vec!["x".to_string(), "y".to_string()];
        let vars_s = vec!["y".to_string()];
        let (conj, conj_vars) = conjunction(leaf(r), &vars_r, leaf(s), &vars_s);
        // conj_vars = ["x", "y"]

        // ∃y. (R(x,y) ∧ S(y))
        let (exists_expr, exists_vars) = exists(conj, &conj_vars, "y");
        // exists_vars = ["x"]

        // (∃y. R(x,y) ∧ S(y)) ∨ T(x)
        let vars_t = vec!["x".to_string()];
        let (result_expr, result_vars) = disjunction(exists_expr, &exists_vars, leaf(t), &vars_t);

        let result = result_expr.materialize();

        assert_eq!(result_vars, vec!["x"]);
        // From R ∧ S: x=0 (path 0→1, 1∈S) and x=1 (path 1→2, 2∈S)
        // From T: x=2
        assert_eq!(result.len(), 3);
        assert!(result.contains(&[0]));
        assert!(result.contains(&[1]));
        assert!(result.contains(&[2]));
    }

    // ========================================================================
    // FORMULA COMPILATION TESTS
    // ========================================================================

    use crate::core::{DerivedSort, Formula, Signature, Structure, Term};
    use crate::universe::Universe;

    /// Helper to create a test structure with a single sort and some elements
    fn make_test_structure_with_relation() -> (Structure, Signature) {
        let mut sig = Signature::new();
        let node_id = sig.add_sort("Node".to_string());

        // Add a binary relation: edge(from: Node, to: Node)
        sig.add_relation(
            "edge".to_string(),
            DerivedSort::Product(vec![
                ("from".to_string(), DerivedSort::Base(node_id)),
                ("to".to_string(), DerivedSort::Base(node_id)),
            ]),
        );

        let mut universe = Universe::new();
        let mut structure = Structure::new(1); // 1 sort

        // Add 3 nodes (Slids 0, 1, 2)
        for _ in 0..3 {
            structure.add_element(&mut universe, node_id);
        }

        // Initialize relations
        structure.init_relations(&[2]); // One binary relation

        // Add edges: 0→1, 1→2
        structure.assert_relation(0, vec![slid(0), slid(1)]);
        structure.assert_relation(0, vec![slid(1), slid(2)]);

        (structure, sig)
    }

    #[test]
    fn test_compile_formula_true() {
        let (structure, sig) = make_test_structure_with_relation();
        let ctx = CompileContext::new();

        let (expr, vars) = compile_formula(&Formula::True, &ctx, &structure, &sig);
        let result = expr.materialize();

        assert!(vars.is_empty());
        assert_eq!(result.len(), 1); // scalar true
        assert!(result.contains(&[]));
    }

    #[test]
    fn test_compile_formula_false() {
        let (structure, sig) = make_test_structure_with_relation();
        let ctx = CompileContext::new();

        let (expr, vars) = compile_formula(&Formula::False, &ctx, &structure, &sig);
        let result = expr.materialize();

        assert!(vars.is_empty());
        assert!(result.is_empty());
    }

    #[test]
    fn test_compile_formula_relation() {
        let (structure, sig) = make_test_structure_with_relation();
        let ctx = CompileContext::new();

        // Build: edge(x, y)
        let term = Term::Record(vec![
            ("from".to_string(), Term::Var("x".to_string(), DerivedSort::Base(0))),
            ("to".to_string(), Term::Var("y".to_string(), DerivedSort::Base(0))),
        ]);
        let formula = Formula::Rel(0, term);

        let (expr, vars) = compile_formula(&formula, &ctx, &structure, &sig);
        let result = expr.materialize();

        assert_eq!(vars, vec!["x", "y"]);
        assert_eq!(result.dims, vec![3, 3]); // 3 nodes
        assert_eq!(result.len(), 2); // 2 edges
        assert!(result.contains(&[0, 1])); // 0→1
        assert!(result.contains(&[1, 2])); // 1→2
    }

    #[test]
    fn test_compile_formula_conjunction() {
        let (structure, sig) = make_test_structure_with_relation();
        let ctx = CompileContext::new();

        // Build: edge(x, y) ∧ edge(y, z)
        let edge_xy = Formula::Rel(
            0,
            Term::Record(vec![
                ("from".to_string(), Term::Var("x".to_string(), DerivedSort::Base(0))),
                ("to".to_string(), Term::Var("y".to_string(), DerivedSort::Base(0))),
            ]),
        );
        let edge_yz = Formula::Rel(
            0,
            Term::Record(vec![
                ("from".to_string(), Term::Var("y".to_string(), DerivedSort::Base(0))),
                ("to".to_string(), Term::Var("z".to_string(), DerivedSort::Base(0))),
            ]),
        );

        let formula = Formula::Conj(vec![edge_xy, edge_yz]);

        let (expr, vars) = compile_formula(&formula, &ctx, &structure, &sig);
        let result = expr.materialize();

        assert_eq!(vars, vec!["x", "y", "z"]);
        assert_eq!(result.len(), 1); // Only one 2-hop path: 0→1→2
        assert!(result.contains(&[0, 1, 2]));
    }

    #[test]
    fn test_compile_formula_exists() {
        let (structure, sig) = make_test_structure_with_relation();
        let ctx = CompileContext::new();

        // Build: ∃y. edge(x, y) ∧ edge(y, z)
        // This is 2-hop reachability
        let edge_xy = Formula::Rel(
            0,
            Term::Record(vec![
                ("from".to_string(), Term::Var("x".to_string(), DerivedSort::Base(0))),
                ("to".to_string(), Term::Var("y".to_string(), DerivedSort::Base(0))),
            ]),
        );
        let edge_yz = Formula::Rel(
            0,
            Term::Record(vec![
                ("from".to_string(), Term::Var("y".to_string(), DerivedSort::Base(0))),
                ("to".to_string(), Term::Var("z".to_string(), DerivedSort::Base(0))),
            ]),
        );

        let inner = Formula::Conj(vec![edge_xy, edge_yz]);
        let formula = Formula::Exists(
            "y".to_string(),
            DerivedSort::Base(0),
            Box::new(inner),
        );

        let (expr, vars) = compile_formula(&formula, &ctx, &structure, &sig);
        let result = expr.materialize();

        assert_eq!(vars, vec!["x", "z"]);
        assert_eq!(result.len(), 1); // One 2-hop path: 0→2 (via 1)
        assert!(result.contains(&[0, 2]));
    }

    #[test]
    fn test_compile_formula_equality() {
        let (structure, sig) = make_test_structure_with_relation();
        let ctx = CompileContext::new();

        // Build: x = y (diagonal)
        let formula = Formula::Eq(
            Term::Var("x".to_string(), DerivedSort::Base(0)),
            Term::Var("y".to_string(), DerivedSort::Base(0)),
        );

        let (expr, vars) = compile_formula(&formula, &ctx, &structure, &sig);
        let result = expr.materialize();

        assert_eq!(vars.len(), 2);
        assert_eq!(result.dims, vec![3, 3]);
        assert_eq!(result.len(), 3); // Diagonal: (0,0), (1,1), (2,2)
        assert!(result.contains(&[0, 0]));
        assert!(result.contains(&[1, 1]));
        assert!(result.contains(&[2, 2]));
    }

    #[test]
    fn test_compile_formula_reflexive_identity() {
        let (structure, sig) = make_test_structure_with_relation();
        let ctx = CompileContext::new();

        // Build: x = x (trivially true)
        let formula = Formula::Eq(
            Term::Var("x".to_string(), DerivedSort::Base(0)),
            Term::Var("x".to_string(), DerivedSort::Base(0)),
        );

        let (expr, vars) = compile_formula(&formula, &ctx, &structure, &sig);
        let result = expr.materialize();

        assert!(vars.is_empty());
        assert_eq!(result.len(), 1); // scalar true
        assert!(result.contains(&[]));
    }

    // ========================================================================
    // SEQUENT CHECKING TESTS
    // ========================================================================

    use crate::core::{Context, Sequent};

    #[test]
    fn test_check_sequent_reflexivity() {
        // Axiom: ∀x:Node. true ⊢ edge(x,x) -- reflexivity
        // This should FAIL because our graph doesn't have self-loops
        let (structure, sig) = make_test_structure_with_relation();

        let ctx = Context {
            vars: vec![("x".to_string(), DerivedSort::Base(0))],
        };

        let premise = Formula::True;
        let conclusion = Formula::Rel(
            0,
            Term::Record(vec![
                ("from".to_string(), Term::Var("x".to_string(), DerivedSort::Base(0))),
                ("to".to_string(), Term::Var("x".to_string(), DerivedSort::Base(0))),
            ]),
        );

        let sequent = Sequent {
            context: ctx,
            premise,
            conclusion,
        };

        let result = check_sequent(&sequent, &structure, &sig);

        // Should be violated for all 3 nodes (no self-loops)
        assert!(!result.is_satisfied());
        assert_eq!(result.violations().len(), 3);
    }

    #[test]
    fn test_check_sequent_edge_implies_edge() {
        // Axiom: ∀x,y:Node. edge(x,y) ⊢ edge(x,y) -- tautology
        let (structure, sig) = make_test_structure_with_relation();

        let ctx = Context {
            vars: vec![
                ("x".to_string(), DerivedSort::Base(0)),
                ("y".to_string(), DerivedSort::Base(0)),
            ],
        };

        let edge_xy = Formula::Rel(
            0,
            Term::Record(vec![
                ("from".to_string(), Term::Var("x".to_string(), DerivedSort::Base(0))),
                ("to".to_string(), Term::Var("y".to_string(), DerivedSort::Base(0))),
            ]),
        );

        let sequent = Sequent {
            context: ctx,
            premise: edge_xy.clone(),
            conclusion: edge_xy,
        };

        let result = check_sequent(&sequent, &structure, &sig);

        assert!(result.is_satisfied());
    }

    #[test]
    fn test_check_sequent_transitivity() {
        // Axiom: ∀x,y,z:Node. edge(x,y) ∧ edge(y,z) ⊢ edge(x,z) -- transitivity
        // This should FAIL because we have 0→1→2 but not 0→2
        let (structure, sig) = make_test_structure_with_relation();

        let ctx = Context {
            vars: vec![
                ("x".to_string(), DerivedSort::Base(0)),
                ("y".to_string(), DerivedSort::Base(0)),
                ("z".to_string(), DerivedSort::Base(0)),
            ],
        };

        let edge_xy = Formula::Rel(
            0,
            Term::Record(vec![
                ("from".to_string(), Term::Var("x".to_string(), DerivedSort::Base(0))),
                ("to".to_string(), Term::Var("y".to_string(), DerivedSort::Base(0))),
            ]),
        );
        let edge_yz = Formula::Rel(
            0,
            Term::Record(vec![
                ("from".to_string(), Term::Var("y".to_string(), DerivedSort::Base(0))),
                ("to".to_string(), Term::Var("z".to_string(), DerivedSort::Base(0))),
            ]),
        );
        let edge_xz = Formula::Rel(
            0,
            Term::Record(vec![
                ("from".to_string(), Term::Var("x".to_string(), DerivedSort::Base(0))),
                ("to".to_string(), Term::Var("z".to_string(), DerivedSort::Base(0))),
            ]),
        );

        let premise = Formula::Conj(vec![edge_xy, edge_yz]);

        let sequent = Sequent {
            context: ctx,
            premise,
            conclusion: edge_xz,
        };

        let result = check_sequent(&sequent, &structure, &sig);

        // Should be violated: (0,1,2) satisfies premise but 0→2 is not an edge
        assert!(!result.is_satisfied());
        assert_eq!(result.violations().len(), 1);
        assert_eq!(result.violations()[0].assignment, vec![0, 1, 2]);
    }

    #[test]
    fn test_check_sequent_vacuously_true() {
        // Axiom: ∀x,y:Node. false ⊢ edge(x,y) -- vacuously true
        let (structure, sig) = make_test_structure_with_relation();

        let ctx = Context {
            vars: vec![
                ("x".to_string(), DerivedSort::Base(0)),
                ("y".to_string(), DerivedSort::Base(0)),
            ],
        };

        let sequent = Sequent {
            context: ctx,
            premise: Formula::False,
            conclusion: Formula::Rel(
                0,
                Term::Record(vec![
                    ("from".to_string(), Term::Var("x".to_string(), DerivedSort::Base(0))),
                    ("to".to_string(), Term::Var("y".to_string(), DerivedSort::Base(0))),
                ]),
            ),
        };

        let result = check_sequent(&sequent, &structure, &sig);

        assert!(result.is_satisfied());
    }

    #[test]
    fn test_check_sequent_with_closure() {
        // Add transitive closure edges to make transitivity hold
        let mut sig = Signature::new();
        let node_id = sig.add_sort("Node".to_string());

        sig.add_relation(
            "edge".to_string(),
            DerivedSort::Product(vec![
                ("from".to_string(), DerivedSort::Base(node_id)),
                ("to".to_string(), DerivedSort::Base(node_id)),
            ]),
        );

        let mut universe = Universe::new();
        let mut structure = Structure::new(1);

        for _ in 0..3 {
            structure.add_element(&mut universe, node_id);
        }

        structure.init_relations(&[2]);

        // Add edges: 0→1, 1→2, AND 0→2 (transitive closure)
        structure.assert_relation(0, vec![slid(0), slid(1)]);
        structure.assert_relation(0, vec![slid(1), slid(2)]);
        structure.assert_relation(0, vec![slid(0), slid(2)]); // Closure!

        let ctx = Context {
            vars: vec![
                ("x".to_string(), DerivedSort::Base(0)),
                ("y".to_string(), DerivedSort::Base(0)),
                ("z".to_string(), DerivedSort::Base(0)),
            ],
        };

        let edge_xy = Formula::Rel(
            0,
            Term::Record(vec![
                ("from".to_string(), Term::Var("x".to_string(), DerivedSort::Base(0))),
                ("to".to_string(), Term::Var("y".to_string(), DerivedSort::Base(0))),
            ]),
        );
        let edge_yz = Formula::Rel(
            0,
            Term::Record(vec![
                ("from".to_string(), Term::Var("y".to_string(), DerivedSort::Base(0))),
                ("to".to_string(), Term::Var("z".to_string(), DerivedSort::Base(0))),
            ]),
        );
        let edge_xz = Formula::Rel(
            0,
            Term::Record(vec![
                ("from".to_string(), Term::Var("x".to_string(), DerivedSort::Base(0))),
                ("to".to_string(), Term::Var("z".to_string(), DerivedSort::Base(0))),
            ]),
        );

        let premise = Formula::Conj(vec![edge_xy, edge_yz]);

        let sequent = Sequent {
            context: ctx,
            premise,
            conclusion: edge_xz,
        };

        let result = check_sequent(&sequent, &structure, &sig);

        // Now should be satisfied because we have 0→2
        assert!(result.is_satisfied());
    }

    #[test]
    fn test_check_theory_axioms() {
        let (structure, sig) = make_test_structure_with_relation();

        // Two axioms: one true, one false
        let ctx1 = Context {
            vars: vec![
                ("x".to_string(), DerivedSort::Base(0)),
                ("y".to_string(), DerivedSort::Base(0)),
            ],
        };

        let edge_xy = Formula::Rel(
            0,
            Term::Record(vec![
                ("from".to_string(), Term::Var("x".to_string(), DerivedSort::Base(0))),
                ("to".to_string(), Term::Var("y".to_string(), DerivedSort::Base(0))),
            ]),
        );

        // Axiom 1: edge(x,y) ⊢ edge(x,y) -- tautology (satisfied)
        let axiom1 = Sequent {
            context: ctx1.clone(),
            premise: edge_xy.clone(),
            conclusion: edge_xy.clone(),
        };

        // Axiom 2: true ⊢ edge(x,x) -- reflexivity (violated)
        let ctx2 = Context {
            vars: vec![("x".to_string(), DerivedSort::Base(0))],
        };
        let edge_xx = Formula::Rel(
            0,
            Term::Record(vec![
                ("from".to_string(), Term::Var("x".to_string(), DerivedSort::Base(0))),
                ("to".to_string(), Term::Var("x".to_string(), DerivedSort::Base(0))),
            ]),
        );
        let axiom2 = Sequent {
            context: ctx2,
            premise: Formula::True,
            conclusion: edge_xx,
        };

        let violations = check_theory_axioms(&[axiom1, axiom2], &structure, &sig);

        // Only axiom 2 (index 1) should be violated
        assert_eq!(violations.len(), 1);
        assert_eq!(violations[0].0, 1); // Second axiom
        assert_eq!(violations[0].1.len(), 3); // All 3 nodes violate reflexivity
    }
}
