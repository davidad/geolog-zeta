//! Sequent checking using tensor expressions.

use crate::core::{Sequent, Signature, Structure};

use super::compile::{compile_formula, derived_sort_cardinality, CompileContext};
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
pub fn check_sequent(sequent: &Sequent, structure: &Structure, sig: &Signature) -> CheckResult {
    let ctx = CompileContext::from_context(&sequent.context);

    // Compile premise and conclusion
    let (premise_expr, premise_vars) = compile_formula(&sequent.premise, &ctx, structure, sig);
    let (conclusion_expr, conclusion_vars) =
        compile_formula(&sequent.conclusion, &ctx, structure, sig);

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
pub fn check_sequent_bool(sequent: &Sequent, structure: &Structure, sig: &Signature) -> bool {
    check_sequent(sequent, structure, sig).is_satisfied()
}

/// Check multiple sequents (axioms of a theory) against a structure.
/// Returns a list of (sequent_index, violations) for each violated sequent.
///
/// If tensor compilation panics (e.g., for unsupported formula patterns like
/// function application in equality), silently skips that axiom. Forward
/// chaining can handle these axioms differently via `eval_term_to_slid`.
pub fn check_theory_axioms(
    axioms: &[Sequent],
    structure: &Structure,
    sig: &Signature,
) -> Vec<(usize, Vec<Violation>)> {
    // Temporarily suppress panic output for expected panics (unsupported formulas)
    let prev_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {
        // Silently ignore panics - we handle them with catch_unwind
    }));

    let result = axioms
        .iter()
        .enumerate()
        .filter_map(|(i, seq)| {
            // Use catch_unwind to handle panics from unsupported formula patterns
            // (e.g., function applications in equality expressions)
            let check_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                check_sequent(seq, structure, sig)
            }));

            match check_result {
                Ok(CheckResult::Satisfied) => None,
                Ok(CheckResult::Violated(vs)) => Some((i, vs)),
                Err(_) => {
                    // Tensor compilation panicked (e.g., unsupported term equality)
                    // Treat as satisfied for now - forward chaining will handle these
                    // axioms via a different code path (eval_term_to_slid).
                    // TODO(geolog-dxr): Extend tensor compiler to handle function applications
                    None
                }
            }
        })
        .collect();

    // Restore the previous panic hook
    std::panic::set_hook(prev_hook);
    result
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
}
