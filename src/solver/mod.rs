//! Solver infrastructure for instance synthesis
//!
//! This module provides the search tree and tactics for finding instances
//! of geometric theories. The architecture is designed for AI-agent-driven
//! search: the agent manipulates an explicit search tree, running automated
//! tactics for bounded time and providing strategic guidance.
//!
//! # Key Concepts
//!
//! - **Search Tree**: Explicit tree of partial models, not implicit in call stack
//! - **Partial Model**: A `Structure` where carriers can grow, functions can become
//!   more defined, and relations can have more tuples asserted
//! - **Refinement**: Natural preorder on Structures (really a category of partial
//!   models with refinement morphisms)
//! - **Obligation**: When an axiom's premise is satisfied but conclusion isn't,
//!   we have an obligation to witness the conclusion (not a failure!)
//! - **Tactic**: Automated search strategy that runs for bounded time
//! - **Agent Loop**: AI decides which nodes to explore, provides hints, estimates
//!   success probabilities, allocates resources
//!
//! # The Refinement Order
//!
//! A Structure S₁ refines to S₂ (S₁ ≤ S₂) when:
//! - All carriers in S₁ are subsets of corresponding carriers in S₂
//! - All defined function values in S₁ are preserved in S₂
//! - All asserted relation tuples in S₁ are preserved in S₂
//!
//! A search node conjectures: "∃ complete, axiom-satisfying Structure above this one"
//!
//! # Obligations, Equations, and Derivations
//!
//! In geometric logic, axiom consequents are always positive (existentials,
//! disjunctions, atomic relations, equations). The refinement order on partial
//! models includes not just adding facts, but also **quotienting by equations**
//! (merging elements). This means:
//!
//! - **Obligation**: Premise satisfied, conclusion not yet witnessed → need to
//!   witness. Can always potentially be done by refinement.
//!
//! - **Pending Equation**: Two terms must be equal. Resolved by merging elements
//!   and propagating consequences (congruence closure).
//!
//! - **Unsat**: The ONLY way to get true unsatisfiability is if there exists a
//!   **Derivation** of `⊢ False` from the instantiated axioms. This is
//!   proof-theoretic: we need to actually derive False, not just have "conflicts".
//!
//! For example, "function f already maps a to b, but we need f(a) = c" is NOT
//! unsat—it's a pending equation `b = c`. We merge b and c, propagate, and only
//! if this leads to deriving False (via some axiom like `R(x), S(x) ⊢ False`)
//! do we have true unsatisfiability.
//!
//! This is essentially SMT solving with EUF (equality + uninterpreted functions)
//! plus geometric theory axioms, where the goal is to either:
//! 1. Find a complete model satisfying all axioms, or
//! 2. Derive `⊢ False` proving no such model exists
//!
//! # Unified Model Enumeration API
//!
//! The high-level API unifies `:solve` and `:query` under a common abstraction:
//! finding maximal elements of the posetal reflection of the category of models.
//!
//! - [`solve`]: Find models from scratch (base = empty structure)
//! - [`query`]: Find extensions of an existing model to a larger theory
//! - [`enumerate_models`]: Core unified function (both above are wrappers)
//!
//! ```ignore
//! // Find any model of a theory
//! let result = solve(theory, Budget::quick());
//!
//! // Extend an existing model to satisfy additional axioms
//! let result = query(base_structure, universe, extended_theory, budget);
//! ```

mod tactics;
mod tree;
mod types;

// Re-export main types
pub use tactics::{AutoTactic, Budget, CheckTactic, EnumerateFunctionTactic, ForwardChainingTactic, PropagateEquationsTactic, Tactic, TacticResult};
pub use tree::SearchTree;
pub use types::{
    AxiomCheckResult, ConflictClause, CongruenceClosure, EquationReason, NodeDetail, NodeId,
    NodeStatus, Obligation, PendingEquation, SearchNode, SearchSummary,
};

// Unified model enumeration API (see below)
// - enumerate_models: core unified function
// - solve: convenience for :solve (find models from scratch)
// - query: convenience for :query (extend existing models)
// - EnumerationResult: result type

// Re-export union-find for convenience
pub use egglog_union_find::UnionFind;

// ============================================================================
// UNIFIED MODEL ENUMERATION API
// ============================================================================

use std::rc::Rc;
use crate::core::{DerivedSort, ElaboratedTheory, Structure};
use crate::universe::Universe;

/// Result of model enumeration.
#[derive(Debug, Clone)]
pub enum EnumerationResult {
    /// Found a complete model satisfying all axioms.
    Found {
        /// The witness structure (model).
        model: Structure,
        /// Time taken in milliseconds.
        time_ms: f64,
    },
    /// Proved no model exists (derived False).
    Unsat {
        /// Time taken in milliseconds.
        time_ms: f64,
    },
    /// Search incomplete (budget exhausted or still has obligations).
    Incomplete {
        /// Partial structure so far.
        partial: Structure,
        /// Time taken in milliseconds.
        time_ms: f64,
        /// Description of why incomplete.
        reason: String,
    },
}

/// Unified model enumeration: find models of `theory` extending `base`.
///
/// This is the core API that unifies `:solve` and `:query`:
/// - `:solve T` = `enumerate_models(empty, T, budget)`
/// - `:query M T'` = `enumerate_models(M, T', budget)` where T' extends M's theory
///
/// # Arguments
/// - `base`: Starting structure (empty for `:solve`, existing model for `:query`)
/// - `universe`: Universe for Luid allocation (should contain Luids from base)
/// - `theory`: The theory to satisfy
/// - `budget`: Resource limits for the search
///
/// # Returns
/// - `Found` if a complete model was found
/// - `Unsat` if no model exists (derived False)
/// - `Incomplete` if budget exhausted or search blocked
pub fn enumerate_models(
    base: Structure,
    universe: Universe,
    theory: Rc<ElaboratedTheory>,
    budget: Budget,
) -> EnumerationResult {
    let start = std::time::Instant::now();
    let sig = &theory.theory.signature;

    // Create search tree from base
    let mut tree = SearchTree::from_base(theory.clone(), base, universe);

    // Initialize function and relation storage at root (if not already initialized)
    // This preserves any function values that were imported from param instances.
    let num_funcs = sig.functions.len();
    let num_rels = sig.relations.len();

    // Only init functions if not already initialized (or wrong size)
    if tree.nodes[0].structure.functions.len() != num_funcs {
        let domain_sort_ids: Vec<Option<usize>> = sig
            .functions
            .iter()
            .map(|f| match &f.domain {
                DerivedSort::Base(sid) => Some(*sid),
                DerivedSort::Product(_) => None,
            })
            .collect();

        if tree.init_functions(0, &domain_sort_ids).is_err() {
            return EnumerationResult::Incomplete {
                partial: tree.nodes[0].structure.clone(),
                time_ms: start.elapsed().as_secs_f64() * 1000.0,
                reason: "Failed to initialize function storage".to_string(),
            };
        }
    }

    // Only init relations if not already initialized (or wrong size)
    if tree.nodes[0].structure.relations.len() != num_rels {
        let arities: Vec<usize> = sig
            .relations
            .iter()
            .map(|r| match &r.domain {
                DerivedSort::Base(_) => 1,
                DerivedSort::Product(fields) => fields.len(),
            })
            .collect();

        if tree.init_relations(0, &arities).is_err() {
            return EnumerationResult::Incomplete {
                partial: tree.nodes[0].structure.clone(),
                time_ms: start.elapsed().as_secs_f64() * 1000.0,
                reason: "Failed to initialize relation storage".to_string(),
            };
        }
    }

    // Run AutoTactic
    let result = AutoTactic.run(&mut tree, 0, &budget);
    let time_ms = start.elapsed().as_secs_f64() * 1000.0;

    match result {
        TacticResult::Solved => EnumerationResult::Found {
            model: tree.nodes[0].structure.clone(),
            time_ms,
        },
        TacticResult::Unsat(_) => EnumerationResult::Unsat { time_ms },
        TacticResult::HasObligations(obs) => EnumerationResult::Incomplete {
            partial: tree.nodes[0].structure.clone(),
            time_ms,
            reason: format!("Has {} unfulfilled obligations", obs.len()),
        },
        TacticResult::Progress { steps_taken, .. } => EnumerationResult::Incomplete {
            partial: tree.nodes[0].structure.clone(),
            time_ms,
            reason: format!("Made progress ({} steps) but not complete", steps_taken),
        },
        TacticResult::Timeout { steps_taken } => EnumerationResult::Incomplete {
            partial: tree.nodes[0].structure.clone(),
            time_ms,
            reason: format!("Timeout after {} steps", steps_taken),
        },
        TacticResult::Error(e) => EnumerationResult::Incomplete {
            partial: tree.nodes[0].structure.clone(),
            time_ms,
            reason: format!("Error: {}", e),
        },
    }
}

/// Convenience: solve a theory from scratch (find any model).
///
/// Equivalent to `enumerate_models(empty_structure, Universe::new(), theory, budget)`.
pub fn solve(theory: Rc<ElaboratedTheory>, budget: Budget) -> EnumerationResult {
    let num_sorts = theory.theory.signature.sorts.len();
    let base = Structure::new(num_sorts);
    enumerate_models(base, Universe::new(), theory, budget)
}

/// Convenience: query/extend an existing model.
///
/// Equivalent to `enumerate_models(base, universe, extension_theory, budget)`.
pub fn query(
    base: Structure,
    universe: Universe,
    extension_theory: Rc<ElaboratedTheory>,
    budget: Budget,
) -> EnumerationResult {
    enumerate_models(base, universe, extension_theory, budget)
}

#[cfg(test)]
mod unified_api_tests {
    use super::*;
    use crate::core::{Context, Formula, RelationStorage, Sequent, Signature, Term, Theory};

    fn make_existential_theory() -> Rc<ElaboratedTheory> {
        // Theory: Node sort, R relation
        // Axiom: True |- ∃x:Node. R(x)
        let mut sig = Signature::new();
        let node = sig.add_sort("Node".to_string());
        sig.add_relation("R".to_string(), DerivedSort::Base(node));

        let axiom = Sequent {
            context: Context::new(),
            premise: Formula::True,
            conclusion: Formula::Exists(
                "x".to_string(),
                DerivedSort::Base(node),
                Box::new(Formula::Rel(0, Term::Var("x".to_string(), DerivedSort::Base(node)))),
            ),
        };

        Rc::new(ElaboratedTheory {
            params: vec![],
            theory: Theory {
                name: "ExistsR".to_string(),
                signature: sig,
                axioms: vec![axiom],
                axiom_names: vec!["ax/exists_r".to_string()],
            },
        })
    }

    #[test]
    fn test_solve_finds_model() {
        // solve = enumerate_models with empty base
        let theory = make_existential_theory();
        let result = solve(theory, Budget::quick());

        match result {
            EnumerationResult::Found { model, .. } => {
                // Should have at least one element with R
                assert!(model.carrier_size(0) >= 1);
                assert!(!model.relations[0].is_empty());
            }
            other => panic!("Expected Found, got {:?}", other),
        }
    }

    #[test]
    fn test_query_extends_base() {
        // query = enumerate_models with existing base
        let theory = make_existential_theory();

        // Create base with one element, R not yet holding
        let mut universe = Universe::new();
        let mut base = Structure::new(1);
        let (_elem, _) = base.add_element(&mut universe, 0);
        base.init_relations(&[1]);

        // query should extend the base to satisfy the axiom
        let result = query(base, universe, theory, Budget::quick());

        match result {
            EnumerationResult::Found { model, .. } => {
                // R should now have at least one tuple
                assert!(!model.relations[0].is_empty());
            }
            other => panic!("Expected Found, got {:?}", other),
        }
    }

    #[test]
    fn test_unification_equivalence() {
        // Demonstrate: solve(T) = enumerate_models(empty, T)
        let theory = make_existential_theory();
        let budget = Budget::quick();

        // Method 1: solve
        let result1 = solve(theory.clone(), budget.clone());

        // Method 2: enumerate_models with empty base
        let num_sorts = theory.theory.signature.sorts.len();
        let empty_base = Structure::new(num_sorts);
        let result2 = enumerate_models(empty_base, Universe::new(), theory, budget);

        // Both should succeed (find a model)
        match (&result1, &result2) {
            (EnumerationResult::Found { .. }, EnumerationResult::Found { .. }) => {
                // Both found models - the unification works!
            }
            _ => panic!(
                "Expected both to find models, got {:?} and {:?}",
                result1, result2
            ),
        }
    }

    #[test]
    fn test_solve_unsat_theory() {
        // Theory that derives False: forall a:A. |- false
        let mut sig = Signature::new();
        let _sort_a = sig.add_sort("A".to_string());

        // Axiom: forall a:A. |- false
        let axiom = Sequent {
            context: Context::new(),
            premise: Formula::True,
            conclusion: Formula::False,
        };

        let theory = Rc::new(ElaboratedTheory {
            params: vec![],
            theory: Theory {
                name: "Inconsistent".to_string(),
                signature: sig,
                axioms: vec![axiom],
                axiom_names: vec!["ax/inconsistent".to_string()],
            },
        });

        let result = solve(theory, Budget::quick());

        match result {
            EnumerationResult::Unsat { .. } => {
                // Correctly detected UNSAT
            }
            other => panic!("Expected Unsat, got {:?}", other),
        }
    }

    #[test]
    fn test_solve_trivial_theory() {
        // Theory with no axioms - should be trivially satisfied by empty structure
        let mut sig = Signature::new();
        sig.add_sort("A".to_string());
        sig.add_sort("B".to_string());

        let theory = Rc::new(ElaboratedTheory {
            params: vec![],
            theory: Theory {
                name: "Trivial".to_string(),
                signature: sig,
                axioms: vec![],
                axiom_names: vec![],
            },
        });

        let result = solve(theory, Budget::quick());

        match result {
            EnumerationResult::Found { model, .. } => {
                // Empty structure is a valid model
                assert_eq!(model.carrier_size(0), 0);
                assert_eq!(model.carrier_size(1), 0);
            }
            other => panic!("Expected Found with empty model, got {:?}", other),
        }
    }
}
