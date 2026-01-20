//! Property tests for the geometric logic solver
//!
//! Tests key properties:
//! - solve(trivial_theory) always finds a model (empty structure)
//! - solve(inconsistent_theory) is always UNSAT
//! - enumerate_models(empty, T) = solve(T)

mod generators;

use std::rc::Rc;

use geolog::core::{
    Context, DerivedSort, ElaboratedTheory, Formula, Sequent, Signature, Term, Theory,
};
use geolog::solver::{solve, enumerate_models, Budget, EnumerationResult};
use geolog::universe::Universe;
use proptest::prelude::*;

// ============================================================================
// Theory Generators
// ============================================================================

/// Generate a theory with no axioms (trivially satisfiable by empty model)
fn arb_trivial_theory() -> impl Strategy<Value = Rc<ElaboratedTheory>> {
    (1usize..=5).prop_map(|num_sorts| {
        let mut sig = Signature::new();
        for i in 0..num_sorts {
            sig.add_sort(format!("S{}", i));
        }
        Rc::new(ElaboratedTheory {
            params: vec![],
            theory: Theory {
                name: "Trivial".to_string(),
                signature: sig,
                axioms: vec![],
            },
        })
    })
}

/// Generate an inconsistent theory (True ⊢ False)
fn arb_inconsistent_theory() -> impl Strategy<Value = Rc<ElaboratedTheory>> {
    (1usize..=3).prop_map(|num_sorts| {
        let mut sig = Signature::new();
        for i in 0..num_sorts {
            sig.add_sort(format!("S{}", i));
        }
        let axiom = Sequent {
            context: Context::new(),
            premise: Formula::True,
            conclusion: Formula::False,
        };
        Rc::new(ElaboratedTheory {
            params: vec![],
            theory: Theory {
                name: "Inconsistent".to_string(),
                signature: sig,
                axioms: vec![axiom],
            },
        })
    })
}

/// Generate a theory with an existential axiom
fn arb_existential_theory() -> impl Strategy<Value = Rc<ElaboratedTheory>> {
    (1usize..=3, 0usize..=2).prop_map(|(num_sorts, rel_count)| {
        let mut sig = Signature::new();
        for i in 0..num_sorts {
            sig.add_sort(format!("S{}", i));
        }
        // Add unary relations
        for i in 0..rel_count {
            sig.add_relation(format!("R{}", i), DerivedSort::Base(0));
        }

        let mut axioms = vec![];

        // Add unconditional existential: |- ∃x:S0. x = x
        // This just requires creating at least one element
        if num_sorts > 0 {
            axioms.push(Sequent {
                context: Context::new(),
                premise: Formula::True,
                conclusion: Formula::Exists(
                    "x".to_string(),
                    DerivedSort::Base(0),
                    Box::new(Formula::Eq(
                        Term::Var("x".to_string(), DerivedSort::Base(0)),
                        Term::Var("x".to_string(), DerivedSort::Base(0)),
                    )),
                ),
            });
        }

        Rc::new(ElaboratedTheory {
            params: vec![],
            theory: Theory {
                name: "Existential".to_string(),
                signature: sig,
                axioms,
            },
        })
    })
}

// ============================================================================
// Property Tests
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]

    /// Trivial theories (no axioms) are always solved with empty model
    #[test]
    fn trivial_theory_always_solved(theory in arb_trivial_theory()) {
        let result = solve(theory.clone(), Budget::quick());
        match result {
            EnumerationResult::Found { model, .. } => {
                // Empty model should have all carriers empty
                for sort_idx in 0..model.num_sorts() {
                    prop_assert_eq!(model.carrier_size(sort_idx), 0);
                }
            }
            _ => prop_assert!(false, "Trivial theory should always be solved"),
        }
    }

    /// Inconsistent theories (True ⊢ False) are always UNSAT
    #[test]
    fn inconsistent_theory_always_unsat(theory in arb_inconsistent_theory()) {
        let result = solve(theory.clone(), Budget::quick());
        match result {
            EnumerationResult::Unsat { .. } => {
                // Expected!
            }
            _ => prop_assert!(false, "Inconsistent theory should always be UNSAT"),
        }
    }

    /// solve(T) equals enumerate_models(empty, T)
    #[test]
    fn solve_equals_enumerate_empty(theory in arb_trivial_theory()) {
        let budget = Budget::quick();

        // Method 1: solve
        let result1 = solve(theory.clone(), budget.clone());

        // Method 2: enumerate_models with empty base
        let num_sorts = theory.theory.signature.sorts.len();
        let empty_base = geolog::core::Structure::new(num_sorts);
        let result2 = enumerate_models(empty_base, Universe::new(), theory, budget);

        // Both should produce equivalent results (both find models or both fail)
        match (&result1, &result2) {
            (EnumerationResult::Found { .. }, EnumerationResult::Found { .. }) => {
                // Both found - good!
            }
            (EnumerationResult::Unsat { .. }, EnumerationResult::Unsat { .. }) => {
                // Both UNSAT - good!
            }
            (EnumerationResult::Incomplete { .. }, EnumerationResult::Incomplete { .. }) => {
                // Both incomplete - acceptable
            }
            _ => prop_assert!(false, "solve and enumerate_models should produce equivalent results"),
        }
    }

    /// Existential theory creates at least one element
    #[test]
    fn existential_creates_elements(theory in arb_existential_theory()) {
        let result = solve(theory.clone(), Budget::quick());
        match result {
            EnumerationResult::Found { model, .. } => {
                // If theory has existential axioms, should have at least one element
                if !theory.theory.axioms.is_empty() {
                    let has_elements = (0..model.num_sorts())
                        .any(|s| model.carrier_size(s) > 0);
                    prop_assert!(has_elements, "Existential theory should have at least one element");
                }
            }
            EnumerationResult::Incomplete { .. } => {
                // Acceptable - budget might be too small
            }
            EnumerationResult::Unsat { .. } => {
                prop_assert!(false, "Existential theory should not be UNSAT");
            }
        }
    }
}

// ============================================================================
// Focused Tests
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]

    /// Budget limits are respected
    #[test]
    fn budget_limits_respected(theory in arb_existential_theory()) {
        // Very small budget
        let tiny_budget = Budget::new(1, 1);
        let result = solve(theory.clone(), tiny_budget);

        // Should either solve quickly or timeout/incomplete
        match result {
            EnumerationResult::Found { time_ms, .. } => {
                // If solved, should be fast
                prop_assert!(time_ms < 100.0, "Solved within reasonable time");
            }
            EnumerationResult::Incomplete { time_ms, .. } => {
                // Should respect budget
                prop_assert!(time_ms < 100.0, "Incomplete within reasonable time");
            }
            EnumerationResult::Unsat { time_ms } => {
                // Should respect budget
                prop_assert!(time_ms < 100.0, "UNSAT within reasonable time");
            }
        }
    }
}
