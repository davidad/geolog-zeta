//! Formula compilation to tensor expressions.

use std::collections::{BTreeSet, HashMap};

use crate::core::{Context, DerivedSort, Formula, RelId, Signature, Structure, Term};
use crate::id::{NumericId, Slid};

use super::builder::{conjunction, conjunction_all, disjunction_all, exists};
use super::expr::TensorExpr;
use super::sparse::SparseTensor;

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

/// Convert a function's graph (extent) to a SparseTensor.
///
/// For function f : A → B, builds a 2D tensor where (i, j) is present
/// iff f(a_i) = b_j (where a_i is the i-th element of A, b_j is j-th of B).
pub fn function_to_tensor(
    structure: &Structure,
    func_id: usize,
    domain_sort_id: usize,
    codomain_sort_id: usize,
) -> SparseTensor {
    use crate::id::{NumericId, Slid};
    use std::collections::BTreeSet;

    let domain_carrier = &structure.carriers[domain_sort_id];
    let codomain_carrier = &structure.carriers[codomain_sort_id];

    let domain_size = domain_carrier.len() as usize;
    let codomain_size = codomain_carrier.len() as usize;

    // Build reverse index for codomain (Slid -> position)
    let codomain_index: HashMap<Slid, usize> = codomain_carrier
        .iter()
        .enumerate()
        .map(|(idx, slid_u64)| (Slid::from_usize(slid_u64 as usize), idx))
        .collect();

    // Iterate over function's extent
    let mut extent = BTreeSet::new();
    for (domain_idx, domain_slid_u64) in domain_carrier.iter().enumerate() {
        let domain_slid = Slid::from_usize(domain_slid_u64 as usize);
        let sort_slid = structure.sort_local_id(domain_slid);

        if let Some(codomain_slid) = structure.get_function(func_id, sort_slid) {
            if let Some(&codomain_idx) = codomain_index.get(&codomain_slid) {
                extent.insert(vec![domain_idx, codomain_idx]);
            }
        }
    }

    SparseTensor {
        dims: vec![domain_size, codomain_size],
        extent,
    }
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
    let mut extent = std::collections::BTreeSet::new();
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
    _ctx: &CompileContext,
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
                .map(|f| compile_formula(f, _ctx, structure, sig))
                .collect();

            conjunction_all(compiled)
        }

        Formula::Disj(formulas) => {
            if formulas.is_empty() {
                return (TensorExpr::scalar(false), vec![]);
            }

            let mut compiled: Vec<(TensorExpr, Vec<String>)> = formulas
                .iter()
                .map(|f| compile_formula(f, _ctx, structure, sig))
                .collect();

            // Collect all variables across all disjuncts
            let all_vars: std::collections::HashSet<&String> = compiled
                .iter()
                .flat_map(|(_, vars)| vars.iter())
                .collect();

            // If all disjuncts have the same variables, we're good
            let need_extension = compiled.iter().any(|(_, vars)| {
                let var_set: std::collections::HashSet<_> = vars.iter().collect();
                var_set != all_vars
            });

            if need_extension {
                // Build a canonical variable ordering
                let all_vars_vec: Vec<String> = {
                    let mut v: Vec<_> = all_vars.iter().cloned().cloned().collect();
                    v.sort(); // Canonical ordering
                    v
                };

                // Extend each disjunct with missing variables
                for (expr, vars) in &mut compiled {
                    let var_set: std::collections::HashSet<_> = vars.iter().collect();
                    let missing: Vec<_> = all_vars_vec
                        .iter()
                        .filter(|v| !var_set.contains(*v))
                        .collect();

                    if !missing.is_empty() {
                        // Create full-domain tensors for missing variables and take product
                        let mut full_domain_tensors = Vec::new();
                        let mut new_vars = vars.clone();

                        for var in missing {
                            // Look up the variable's sort in the context
                            if let Some(idx) = _ctx.vars.iter().position(|v| v == var) {
                                let sort = &_ctx.sorts[idx];
                                let card = derived_sort_cardinality(structure, sort);

                                // Create a 1D tensor with all values [0..card)
                                let mut extent = BTreeSet::new();
                                for i in 0..card {
                                    extent.insert(vec![i]);
                                }
                                let full_tensor = SparseTensor {
                                    dims: vec![card],
                                    extent,
                                };
                                full_domain_tensors.push(TensorExpr::leaf(full_tensor));
                                new_vars.push(var.clone());
                            } else {
                                // Variable not in context - this is an error
                                panic!(
                                    "Variable '{}' in disjunction not found in context. \
                                     Context has: {:?}",
                                    var, _ctx.vars
                                );
                            }
                        }

                        // Take product: original × full_domain_1 × full_domain_2 × ...
                        if !full_domain_tensors.is_empty() {
                            let mut product_parts = vec![std::mem::replace(
                                expr,
                                TensorExpr::scalar(false),
                            )];
                            product_parts.extend(full_domain_tensors);
                            *expr = TensorExpr::Product(product_parts);
                            *vars = new_vars;
                        }
                    }
                }
            }

            disjunction_all(compiled)
        }

        Formula::Exists(var_name, sort, inner) => {
            // Compile inner formula
            let (inner_expr, inner_vars) = compile_formula(inner, _ctx, structure, sig);

            // Check if the quantified variable appears in the inner formula
            if !inner_vars.contains(var_name) {
                // The variable doesn't appear free in the inner formula.
                // For example: ∃x. True  or  ∃x. (y = y)
                //
                // In this case, the existential is:
                // - FALSE if the domain is empty (no witness exists)
                // - Equal to the inner formula otherwise (witness exists vacuously)
                let domain_card = derived_sort_cardinality(structure, sort);
                if domain_card == 0 {
                    // Empty domain: existential is false
                    return (TensorExpr::scalar(false), inner_vars);
                }
                // Non-empty domain: the existential is equivalent to the inner formula
                return (inner_expr, inner_vars);
            }

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
                        let mut extent = std::collections::BTreeSet::new();
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
                        // But for diagonal, it's symmetric!
                        (TensorExpr::leaf(tensor), vars)
                    }
                }
                // f(x) = y: function application equals variable
                (Term::App(func_id, arg), Term::Var(var_name, _var_sort))
                | (Term::Var(var_name, _var_sort), Term::App(func_id, arg)) => {
                    // arg must be a simple variable for now
                    let Term::Var(arg_name, _arg_sort) = arg.as_ref() else {
                        panic!(
                            "Nested function application in equality not yet supported: {:?} = {:?}",
                            t1, t2
                        );
                    };

                    // Get domain and codomain sort IDs
                    let func_sym = &sig.functions[*func_id];
                    let DerivedSort::Base(domain_sort_id) = &func_sym.domain else {
                        panic!("Function with product domain in equality not yet supported");
                    };
                    let DerivedSort::Base(codomain_sort_id) = &func_sym.codomain else {
                        panic!("Function with product codomain in equality not yet supported");
                    };

                    // Build function extent tensor: (arg, result) pairs
                    let func_tensor = function_to_tensor(structure, *func_id, *domain_sort_id, *codomain_sort_id);

                    // Variables: arg_name maps to dim 0, var_name maps to dim 1
                    // Order alphabetically for consistency
                    let (vars, needs_transpose) = if arg_name < var_name {
                        (vec![arg_name.clone(), var_name.clone()], false)
                    } else {
                        (vec![var_name.clone(), arg_name.clone()], true)
                    };

                    let expr = if needs_transpose {
                        // Swap dimensions: (arg, result) -> (result, arg)
                        TensorExpr::Contract {
                            inner: Box::new(TensorExpr::leaf(func_tensor)),
                            index_map: vec![1, 0], // swap dimensions
                            output: (0..2).collect(),
                        }
                    } else {
                        TensorExpr::leaf(func_tensor)
                    };

                    (expr, vars)
                }

                // f(x) = g(y): two function applications equal
                (Term::App(func_id1, arg1), Term::App(func_id2, arg2)) => {
                    // Both args must be simple variables
                    let Term::Var(arg1_name, _arg1_sort) = arg1.as_ref() else {
                        panic!("Nested function application in equality not yet supported");
                    };
                    let Term::Var(arg2_name, _arg2_sort) = arg2.as_ref() else {
                        panic!("Nested function application in equality not yet supported");
                    };

                    // Get function sorts
                    let func1_sym = &sig.functions[*func_id1];
                    let func2_sym = &sig.functions[*func_id2];
                    let DerivedSort::Base(domain1_sort_id) = &func1_sym.domain else {
                        panic!("Function with product domain in equality not yet supported");
                    };
                    let DerivedSort::Base(codomain1_sort_id) = &func1_sym.codomain else {
                        panic!("Function with product codomain in equality not yet supported");
                    };
                    let DerivedSort::Base(domain2_sort_id) = &func2_sym.domain else {
                        panic!("Function with product domain in equality not yet supported");
                    };
                    let DerivedSort::Base(codomain2_sort_id) = &func2_sym.codomain else {
                        panic!("Function with product codomain in equality not yet supported");
                    };

                    // Build function extent tensors
                    let func1_tensor = function_to_tensor(structure, *func_id1, *domain1_sort_id, *codomain1_sort_id);
                    let func2_tensor = function_to_tensor(structure, *func_id2, *domain2_sort_id, *codomain2_sort_id);

                    // f(x) = g(y) means: ∃z. f(x) = z ∧ g(y) = z
                    // func1_tensor has vars [arg1_name, z], func2_tensor has vars [arg2_name, z]
                    // We need to join on z and then existentially quantify z out

                    let vars1 = vec![arg1_name.clone(), "_z".to_string()];
                    let vars2 = vec![arg2_name.clone(), "_z".to_string()];

                    // Conjunction on shared variable _z
                    let (conj_expr, conj_vars) = conjunction(
                        TensorExpr::leaf(func1_tensor),
                        &vars1,
                        TensorExpr::leaf(func2_tensor),
                        &vars2,
                    );

                    // Existentially quantify out _z
                    let (result_expr, result_vars) = exists(conj_expr, &conj_vars, "_z");

                    (result_expr, result_vars)
                }

                _ => {
                    // Records, projections, etc. not yet implemented
                    panic!(
                        "Complex term equality not yet supported: {:?} = {:?}",
                        t1, t2
                    );
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::DerivedSort;
    use crate::id::Slid;
    use crate::universe::Universe;

    /// Helper to create Slid from integer
    fn slid(n: usize) -> Slid {
        Slid::from_usize(n)
    }

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
            (
                "from".to_string(),
                Term::Var("x".to_string(), DerivedSort::Base(0)),
            ),
            (
                "to".to_string(),
                Term::Var("y".to_string(), DerivedSort::Base(0)),
            ),
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
                (
                    "from".to_string(),
                    Term::Var("x".to_string(), DerivedSort::Base(0)),
                ),
                (
                    "to".to_string(),
                    Term::Var("y".to_string(), DerivedSort::Base(0)),
                ),
            ]),
        );
        let edge_yz = Formula::Rel(
            0,
            Term::Record(vec![
                (
                    "from".to_string(),
                    Term::Var("y".to_string(), DerivedSort::Base(0)),
                ),
                (
                    "to".to_string(),
                    Term::Var("z".to_string(), DerivedSort::Base(0)),
                ),
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
                (
                    "from".to_string(),
                    Term::Var("x".to_string(), DerivedSort::Base(0)),
                ),
                (
                    "to".to_string(),
                    Term::Var("y".to_string(), DerivedSort::Base(0)),
                ),
            ]),
        );
        let edge_yz = Formula::Rel(
            0,
            Term::Record(vec![
                (
                    "from".to_string(),
                    Term::Var("y".to_string(), DerivedSort::Base(0)),
                ),
                (
                    "to".to_string(),
                    Term::Var("z".to_string(), DerivedSort::Base(0)),
                ),
            ]),
        );

        let inner = Formula::Conj(vec![edge_xy, edge_yz]);
        let formula = Formula::Exists("y".to_string(), DerivedSort::Base(0), Box::new(inner));

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

    #[test]
    fn test_compile_formula_func_app_equality() {
        // Test: f(x) = y where f is a function
        let mut sig = Signature::new();
        let node_id = sig.add_sort("Node".to_string());

        // Add function f : Node -> Node
        sig.add_function("f".to_string(), DerivedSort::Base(node_id), DerivedSort::Base(node_id));

        let mut universe = Universe::new();
        let mut structure = Structure::new(1);

        // Add 3 nodes
        for _ in 0..3 {
            structure.add_element(&mut universe, node_id);
        }

        // Define f: 0 -> 1, 1 -> 2, 2 -> 0
        structure.init_functions(&[Some(0)]); // f has domain sort 0
        structure.define_function(0, Slid::from_usize(0), Slid::from_usize(1)).unwrap();
        structure.define_function(0, Slid::from_usize(1), Slid::from_usize(2)).unwrap();
        structure.define_function(0, Slid::from_usize(2), Slid::from_usize(0)).unwrap();

        let ctx = CompileContext::new();

        // Build: f(x) = y
        let formula = Formula::Eq(
            Term::App(0, Box::new(Term::Var("x".to_string(), DerivedSort::Base(0)))),
            Term::Var("y".to_string(), DerivedSort::Base(0)),
        );

        let (expr, vars) = compile_formula(&formula, &ctx, &structure, &sig);
        let result = expr.materialize();

        // Variables should be x and y (alphabetical order)
        assert_eq!(vars.len(), 2);
        assert!(vars.contains(&"x".to_string()));
        assert!(vars.contains(&"y".to_string()));

        // Result should have exactly 3 tuples: (0,1), (1,2), (2,0)
        // representing f(0)=1, f(1)=2, f(2)=0
        // But order depends on alphabetical sort of variable names
        assert_eq!(result.len(), 3);
    }

    #[test]
    fn test_compile_formula_two_func_apps_equality() {
        // Test: f(x) = g(y) where f, g are functions
        let mut sig = Signature::new();
        let node_id = sig.add_sort("Node".to_string());

        // Add functions f, g : Node -> Node
        sig.add_function("f".to_string(), DerivedSort::Base(node_id), DerivedSort::Base(node_id));
        sig.add_function("g".to_string(), DerivedSort::Base(node_id), DerivedSort::Base(node_id));

        let mut universe = Universe::new();
        let mut structure = Structure::new(1);

        // Add 3 nodes
        for _ in 0..3 {
            structure.add_element(&mut universe, node_id);
        }

        // Define f: 0 -> 1, 1 -> 1, 2 -> 2
        // Define g: 0 -> 0, 1 -> 1, 2 -> 2
        structure.init_functions(&[Some(0), Some(0)]); // Both have domain sort 0
        structure.define_function(0, Slid::from_usize(0), Slid::from_usize(1)).unwrap();
        structure.define_function(0, Slid::from_usize(1), Slid::from_usize(1)).unwrap();
        structure.define_function(0, Slid::from_usize(2), Slid::from_usize(2)).unwrap();
        structure.define_function(1, Slid::from_usize(0), Slid::from_usize(0)).unwrap();
        structure.define_function(1, Slid::from_usize(1), Slid::from_usize(1)).unwrap();
        structure.define_function(1, Slid::from_usize(2), Slid::from_usize(2)).unwrap();

        let ctx = CompileContext::new();

        // Build: f(x) = g(y)
        // f(x) = g(y) when ∃z. f(x) = z ∧ g(y) = z
        // f(0)=1, f(1)=1, f(2)=2
        // g(0)=0, g(1)=1, g(2)=2
        // So f(x)=g(y) holds for: (0,1), (1,1), (2,2) since f(0)=g(1)=1, f(1)=g(1)=1, f(2)=g(2)=2
        let formula = Formula::Eq(
            Term::App(0, Box::new(Term::Var("x".to_string(), DerivedSort::Base(0)))),
            Term::App(1, Box::new(Term::Var("y".to_string(), DerivedSort::Base(0)))),
        );

        let (expr, vars) = compile_formula(&formula, &ctx, &structure, &sig);
        let result = expr.materialize();

        // Variables should be x and y
        assert_eq!(vars.len(), 2);
        assert!(vars.contains(&"x".to_string()));
        assert!(vars.contains(&"y".to_string()));

        // f(x) = g(y) holds for: (x=0,y=1), (x=1,y=1), (x=2,y=2)
        assert_eq!(result.len(), 3);
    }

    #[test]
    fn test_compile_formula_exists_empty_domain() {
        // When the domain is empty, ∃x. φ should be false even if φ is true
        // This is the case for ∃x. x = x on an empty structure
        let mut sig = Signature::new();
        let node_id = sig.add_sort("Node".to_string());

        // Empty structure (no elements)
        let structure = Structure::new(1);

        let ctx = CompileContext::new();

        // Build: ∃x. x = x
        // Inner formula x = x compiles to scalar true (no variables)
        // But since domain is empty, the existential should be false
        let inner = Formula::Eq(
            Term::Var("x".to_string(), DerivedSort::Base(node_id)),
            Term::Var("x".to_string(), DerivedSort::Base(node_id)),
        );
        let formula = Formula::Exists("x".to_string(), DerivedSort::Base(node_id), Box::new(inner));

        let (expr, vars) = compile_formula(&formula, &ctx, &structure, &sig);
        let result = expr.materialize();

        // Should be FALSE (empty) because there's no witness in empty domain
        assert!(vars.is_empty());
        assert!(result.is_empty(), "∃x. x = x should be false on empty domain");
    }

    #[test]
    fn test_compile_formula_exists_nonempty_domain() {
        // When the domain is non-empty, ∃x. x = x should be true
        let mut sig = Signature::new();
        let node_id = sig.add_sort("Node".to_string());

        let mut universe = Universe::new();
        let mut structure = Structure::new(1);
        structure.add_element(&mut universe, node_id); // Add one element

        let ctx = CompileContext::new();

        // Build: ∃x. x = x
        let inner = Formula::Eq(
            Term::Var("x".to_string(), DerivedSort::Base(node_id)),
            Term::Var("x".to_string(), DerivedSort::Base(node_id)),
        );
        let formula = Formula::Exists("x".to_string(), DerivedSort::Base(node_id), Box::new(inner));

        let (expr, vars) = compile_formula(&formula, &ctx, &structure, &sig);
        let result = expr.materialize();

        // Should be TRUE because there's a witness
        assert!(vars.is_empty());
        assert!(result.contains(&[]), "∃x. x = x should be true on non-empty domain");
    }

    #[test]
    fn test_compile_formula_disjunction_different_vars() {
        // Test disjunction where each disjunct has different variables
        // R(x) \/ S(y) - this used to panic, now should work
        let mut sig = Signature::new();
        let node_id = sig.add_sort("Node".to_string());

        // Add two unary relations
        sig.add_relation("R".to_string(), DerivedSort::Base(node_id));
        sig.add_relation("S".to_string(), DerivedSort::Base(node_id));

        let mut universe = Universe::new();
        let mut structure = Structure::new(1);

        // Add 3 nodes
        for _ in 0..3 {
            structure.add_element(&mut universe, node_id);
        }

        // Initialize relations
        structure.init_relations(&[1, 1]); // Two unary relations

        // R = {0}, S = {1}
        structure.assert_relation(0, vec![Slid::from_usize(0)]);
        structure.assert_relation(1, vec![Slid::from_usize(1)]);

        // Need context with both x and y
        let ctx = CompileContext {
            vars: vec!["x".to_string(), "y".to_string()],
            sorts: vec![DerivedSort::Base(node_id), DerivedSort::Base(node_id)],
        };

        // Build: R(x) \/ S(y)
        let r_x = Formula::Rel(
            0,
            Term::Var("x".to_string(), DerivedSort::Base(0)),
        );
        let s_y = Formula::Rel(
            1,
            Term::Var("y".to_string(), DerivedSort::Base(0)),
        );

        let formula = Formula::Disj(vec![r_x, s_y]);

        let (expr, vars) = compile_formula(&formula, &ctx, &structure, &sig);
        let result = expr.materialize();

        // Result should have both x and y
        assert_eq!(vars.len(), 2);
        assert!(vars.contains(&"x".to_string()));
        assert!(vars.contains(&"y".to_string()));

        // The result is the union of:
        // - R(x) extended with all y: {(0,0), (0,1), (0,2)}
        // - S(y) extended with all x: {(0,1), (1,1), (2,1)}
        // Note: the tuple order depends on variable order
        assert!(result.len() > 0);
    }
}
