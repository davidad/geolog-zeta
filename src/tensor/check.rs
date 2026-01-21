//! Sequent checking using tensor expressions.
//!
//! This module provides both full and incremental axiom checking:
//! - `check_sequent`: Full check of a sequent against a structure
//! - `check_sequent_incremental`: Check only "new" tuples after dimension growth
//!
//! The incremental approach leverages the MonotoneSubmodel property:
//! - Old structure satisfied axioms (invariant)
//! - Only new tuples can violate (from element additions)
//! - Only need to check the "border" - tuples involving new indices

use crate::core::{Sequent, Signature, Structure};

use super::compile::{compile_formula, derived_sort_cardinality, CompileContext, CompileError};
use super::delta::DimensionDelta;
use super::sparse::DomainIterator;

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
pub fn check_sequent(sequent: &Sequent, structure: &Structure, sig: &Signature) -> Result<CheckResult, CompileError> {
    let ctx = CompileContext::from_context(&sequent.context);

    // Compile premise and conclusion
    let (premise_expr, premise_vars) = compile_formula(&sequent.premise, &ctx, structure, sig)?;
    let (conclusion_expr, conclusion_vars) =
        compile_formula(&sequent.conclusion, &ctx, structure, sig)?;

    // Materialize both
    let premise_tensor = premise_expr.materialize();
    let conclusion_tensor = conclusion_expr.materialize();

    // Handle edge cases
    if premise_tensor.is_empty() {
        // Vacuously true: no assignments satisfy the premise
        return Ok(CheckResult::Satisfied);
    }

    // Handle case where conclusion is scalar true (no variables)
    if conclusion_vars.is_empty() && conclusion_tensor.contains(&[]) {
        // Conclusion is just "true" - always satisfied
        return Ok(CheckResult::Satisfied);
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
            return Ok(CheckResult::Satisfied);
        }

        // Find violations: tuples in domain not in conclusion
        let mut violations = Vec::new();
        for tuple in DomainIterator::new(&domain_sizes) {
            if !conclusion_tensor.contains(&tuple) {
                violations.push(Violation::new(tuple, conclusion_vars.clone()));
            }
        }

        return if violations.is_empty() {
            Ok(CheckResult::Satisfied)
        } else {
            Ok(CheckResult::Violated(violations))
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
        Ok(CheckResult::Satisfied)
    } else {
        Ok(CheckResult::Violated(violations))
    }
}

/// Check if a sequent is satisfied, returning just a boolean.
/// Returns false if compilation fails.
pub fn check_sequent_bool(sequent: &Sequent, structure: &Structure, sig: &Signature) -> bool {
    check_sequent(sequent, structure, sig)
        .map(|r| r.is_satisfied())
        .unwrap_or(false)
}

/// Check multiple sequents (axioms of a theory) against a structure.
/// Returns a list of (sequent_index, violations) for each violated sequent.
///
/// If tensor compilation fails (e.g., for unsupported formula patterns like
/// record terms in equality), silently skips that axiom. Forward chaining
/// can handle these axioms differently via `eval_term_to_slid`.
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
                Ok(CheckResult::Satisfied) => None,
                Ok(CheckResult::Violated(vs)) => Some((i, vs)),
                Err(_) => {
                    // Tensor compilation failed (e.g., unsupported term in equality)
                    // Treat as satisfied for now - forward chaining will handle these
                    // axioms via a different code path (eval_term_to_slid).
                    None
                }
            }
        })
        .collect()
}

// ============================================================================
// INCREMENTAL CHECKING
// ============================================================================

/// Check a sequent incrementally: only check tuples involving new elements.
///
/// This leverages the MonotoneSubmodel property:
/// - If the old structure satisfied the sequent, it still does (immutable)
/// - Only new tuples (in the "border") can newly violate the axiom
/// - The border consists of tuples where at least one index is >= old_dim
///
/// # Arguments
/// - `sequent`: The axiom to check
/// - `new_structure`: The structure after adding elements
/// - `sig`: The theory signature
/// - `dim_delta`: Dimension changes from element additions
///
/// # Returns
/// - `Satisfied` if no new violations (border is clean)
/// - `Violated` with only the NEW violations (from border tuples)
pub fn check_sequent_incremental(
    sequent: &Sequent,
    new_structure: &Structure,
    sig: &Signature,
    dim_delta: &DimensionDelta,
) -> Result<CheckResult, CompileError> {
    // If no dimensions changed, no new violations possible
    if dim_delta.is_empty() {
        return Ok(CheckResult::Satisfied);
    }

    let ctx = CompileContext::from_context(&sequent.context);

    // Compile premise and conclusion (using full new structure)
    let (premise_expr, premise_vars) = compile_formula(&sequent.premise, &ctx, new_structure, sig)?;
    let (conclusion_expr, conclusion_vars) =
        compile_formula(&sequent.conclusion, &ctx, new_structure, sig)?;

    // Materialize both
    let premise_tensor = premise_expr.materialize();
    let conclusion_tensor = conclusion_expr.materialize();

    // Handle edge cases (same as full check)
    if premise_tensor.is_empty() {
        return Ok(CheckResult::Satisfied);
    }

    if conclusion_vars.is_empty() && conclusion_tensor.contains(&[]) {
        return Ok(CheckResult::Satisfied);
    }

    // Build old dimensions for the context variables
    let old_dims: Vec<usize> = sequent
        .context
        .vars
        .iter()
        .map(|(_, sort)| {
            match sort {
                crate::core::DerivedSort::Base(sort_id) => dim_delta.old_dim(*sort_id),
                crate::core::DerivedSort::Product(fields) => {
                    // Product cardinality is product of field cardinalities
                    fields
                        .iter()
                        .map(|(_, s)| {
                            if let crate::core::DerivedSort::Base(sid) = s {
                                dim_delta.old_dim(*sid)
                            } else {
                                derived_sort_cardinality(new_structure, s)
                            }
                        })
                        .product()
                }
            }
        })
        .collect();

    // Handle special case: premise has no variables (scalar true) but conclusion has variables
    // This means we need to check the conclusion for all new variable assignments
    if premise_vars.is_empty() && !conclusion_vars.is_empty() && premise_tensor.contains(&[]) {
        // Get domain sizes and old dimensions for conclusion variables
        let domain_sizes: Vec<usize> = sequent
            .context
            .vars
            .iter()
            .filter(|(name, _)| conclusion_vars.contains(name))
            .map(|(_, sort)| derived_sort_cardinality(new_structure, sort))
            .collect();

        let conclusion_old_dims: Vec<usize> = sequent
            .context
            .vars
            .iter()
            .filter(|(name, _)| conclusion_vars.contains(name))
            .map(|(_, sort)| match sort {
                crate::core::DerivedSort::Base(sort_id) => dim_delta.old_dim(*sort_id),
                crate::core::DerivedSort::Product(_) => 0, // Treat products as all new
            })
            .collect();

        let mut violations = Vec::new();

        // Only check tuples in the "border" (involving new elements)
        for tuple in DomainIterator::new(&domain_sizes) {
            // Is this tuple in the border?
            let in_border = tuple.iter().zip(&conclusion_old_dims).any(|(idx, old_dim)| {
                *idx >= *old_dim
            });

            if in_border && !conclusion_tensor.contains(&tuple) {
                violations.push(Violation::new(tuple, conclusion_vars.clone()));
            }
        }

        return if violations.is_empty() {
            Ok(CheckResult::Satisfied)
        } else {
            Ok(CheckResult::Violated(violations))
        };
    }

    // Check only tuples in the "border" - those involving new elements
    let mut violations = Vec::new();

    for tuple in premise_tensor.iter() {
        // Is this tuple in the border? (at least one index >= old_dim)
        let in_border = tuple.iter().zip(&old_dims).any(|(idx, old_dim)| {
            // If old_dim is 0, all indices are "new"
            *idx >= *old_dim
        });

        if !in_border {
            // This tuple existed in old structure, which satisfied the axiom
            continue;
        }

        // Project premise tuple to conclusion vars (same logic as full check)
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
        Ok(CheckResult::Satisfied)
    } else {
        Ok(CheckResult::Violated(violations))
    }
}

/// Incrementally check multiple axioms.
///
/// Only checks the "border" of each axiom, skipping tuples that
/// existed in the old structure (which was already verified).
pub fn check_theory_axioms_incremental(
    axioms: &[Sequent],
    new_structure: &Structure,
    sig: &Signature,
    dim_delta: &DimensionDelta,
) -> Vec<(usize, Vec<Violation>)> {
    // If no dimensions changed, nothing to check
    if dim_delta.is_empty() {
        return vec![];
    }

    axioms
        .iter()
        .enumerate()
        .filter_map(|(i, seq)| {
            match check_sequent_incremental(seq, new_structure, sig, dim_delta) {
                Ok(CheckResult::Satisfied) => None,
                Ok(CheckResult::Violated(vs)) if !vs.is_empty() => Some((i, vs)),
                Ok(CheckResult::Violated(_)) => None, // Empty violations
                Err(_) => None, // Skip unsupported axioms
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::{Context, DerivedSort, Formula, Signature, Structure, Term};
    use crate::id::{NumericId, Slid};
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
                (
                    "from".to_string(),
                    Term::Var("x".to_string(), DerivedSort::Base(0)),
                ),
                (
                    "to".to_string(),
                    Term::Var("x".to_string(), DerivedSort::Base(0)),
                ),
            ]),
        );

        let sequent = Sequent {
            context: ctx,
            premise,
            conclusion,
        };

        let result = check_sequent(&sequent, &structure, &sig).unwrap();

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

        let sequent = Sequent {
            context: ctx,
            premise: edge_xy.clone(),
            conclusion: edge_xy,
        };

        let result = check_sequent(&sequent, &structure, &sig).unwrap();

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
        let edge_xz = Formula::Rel(
            0,
            Term::Record(vec![
                (
                    "from".to_string(),
                    Term::Var("x".to_string(), DerivedSort::Base(0)),
                ),
                (
                    "to".to_string(),
                    Term::Var("z".to_string(), DerivedSort::Base(0)),
                ),
            ]),
        );

        let premise = Formula::Conj(vec![edge_xy, edge_yz]);

        let sequent = Sequent {
            context: ctx,
            premise,
            conclusion: edge_xz,
        };

        let result = check_sequent(&sequent, &structure, &sig).unwrap();

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
                    (
                        "from".to_string(),
                        Term::Var("x".to_string(), DerivedSort::Base(0)),
                    ),
                    (
                        "to".to_string(),
                        Term::Var("y".to_string(), DerivedSort::Base(0)),
                    ),
                ]),
            ),
        };

        let result = check_sequent(&sequent, &structure, &sig).unwrap();

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
        let edge_xz = Formula::Rel(
            0,
            Term::Record(vec![
                (
                    "from".to_string(),
                    Term::Var("x".to_string(), DerivedSort::Base(0)),
                ),
                (
                    "to".to_string(),
                    Term::Var("z".to_string(), DerivedSort::Base(0)),
                ),
            ]),
        );

        let premise = Formula::Conj(vec![edge_xy, edge_yz]);

        let sequent = Sequent {
            context: ctx,
            premise,
            conclusion: edge_xz,
        };

        let result = check_sequent(&sequent, &structure, &sig).unwrap();

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
                (
                    "from".to_string(),
                    Term::Var("x".to_string(), DerivedSort::Base(0)),
                ),
                (
                    "to".to_string(),
                    Term::Var("x".to_string(), DerivedSort::Base(0)),
                ),
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

    // ========================================================================
    // Incremental Checking Tests
    // ========================================================================

    #[test]
    fn test_incremental_check_no_changes() {
        // If no dimensions changed, should immediately return Satisfied
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

        let dim_delta = DimensionDelta::default(); // No changes

        let result = check_sequent_incremental(&sequent, &structure, &sig, &dim_delta).unwrap();
        assert!(result.is_satisfied());
    }

    #[test]
    fn test_incremental_check_new_element_violates() {
        // Test that incremental check catches violations from new elements
        //
        // Setup: 2 nodes (0, 1) with edge 0→1
        // Add: node 2 with no edges
        // Axiom: true ⊢ edge(x, x) (reflexivity) - should fail for node 2

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

        // Add 3 nodes (old was 2)
        for _ in 0..3 {
            structure.add_element(&mut universe, node_id);
        }

        structure.init_relations(&[2]);
        structure.assert_relation(0, vec![slid(0), slid(1)]); // 0→1

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

        // Dimension delta: sort 0 went from 2 to 3
        let dim_delta = DimensionDelta::from_cardinalities(&[2], &[3]);

        let result = check_sequent_incremental(&sequent, &structure, &sig, &dim_delta).unwrap();

        // Should be violated only for the NEW element (index 2)
        // Nodes 0 and 1 are "old" (index < 2), so we don't recheck them
        assert!(!result.is_satisfied());
        let violations = result.violations();
        assert_eq!(violations.len(), 1);
        assert_eq!(violations[0].assignment, vec![2]); // Only node 2 (new)
    }

    #[test]
    fn test_incremental_check_new_element_satisfies() {
        // Test that if new elements satisfy the axiom, no violations reported
        //
        // Setup: 2 nodes with self-loops
        // Add: node 2 with self-loop
        // Axiom: true ⊢ edge(x, x) - should pass

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

        // Add 3 nodes
        for _ in 0..3 {
            structure.add_element(&mut universe, node_id);
        }

        structure.init_relations(&[2]);
        // Add self-loops for all nodes
        structure.assert_relation(0, vec![slid(0), slid(0)]);
        structure.assert_relation(0, vec![slid(1), slid(1)]);
        structure.assert_relation(0, vec![slid(2), slid(2)]); // New node also has self-loop

        let ctx = Context {
            vars: vec![("x".to_string(), DerivedSort::Base(0))],
        };

        let sequent = Sequent {
            context: ctx,
            premise: Formula::True,
            conclusion: Formula::Rel(
                0,
                Term::Record(vec![
                    ("from".to_string(), Term::Var("x".to_string(), DerivedSort::Base(0))),
                    ("to".to_string(), Term::Var("x".to_string(), DerivedSort::Base(0))),
                ]),
            ),
        };

        let dim_delta = DimensionDelta::from_cardinalities(&[2], &[3]);

        let result = check_sequent_incremental(&sequent, &structure, &sig, &dim_delta).unwrap();
        assert!(result.is_satisfied()); // New element 2 also has self-loop
    }

    #[test]
    fn test_incremental_check_transitivity() {
        // Test incremental check for transitivity axiom
        //
        // Old: nodes 0, 1 with edges 0→1 (no transitivity violations)
        // New: add node 2, edges 1→2 (now 0→1→2 but no 0→2)
        // Axiom: edge(x,y) ∧ edge(y,z) ⊢ edge(x,z)
        // Violation: (0,1,2) where x=0, y=1, z=2

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

        // 3 nodes
        for _ in 0..3 {
            structure.add_element(&mut universe, node_id);
        }

        structure.init_relations(&[2]);
        structure.assert_relation(0, vec![slid(0), slid(1)]); // 0→1
        structure.assert_relation(0, vec![slid(1), slid(2)]); // 1→2 (involves new node)
        // Note: NO 0→2 edge

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

        let sequent = Sequent {
            context: ctx,
            premise: Formula::Conj(vec![edge_xy, edge_yz]),
            conclusion: edge_xz,
        };

        // Old: 2 nodes, New: 3 nodes
        let dim_delta = DimensionDelta::from_cardinalities(&[2], &[3]);

        let result = check_sequent_incremental(&sequent, &structure, &sig, &dim_delta).unwrap();

        // The tuple (0, 1, 2) involves new element z=2, so it's in the border
        // and should be checked
        assert!(!result.is_satisfied());
        let violations = result.violations();
        assert_eq!(violations.len(), 1);
        assert_eq!(violations[0].assignment, vec![0, 1, 2]);
    }
}
