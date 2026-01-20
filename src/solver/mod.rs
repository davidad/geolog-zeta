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

mod tactics;
mod tree;
mod types;

// Re-export main types
pub use tactics::{Budget, CheckTactic, EnumerateFunctionTactic, ForwardChainingTactic, Tactic, TacticResult};
#[allow(deprecated)]
pub use tactics::PropagationTactic;
pub use tree::SearchTree;
pub use types::{
    AxiomCheckResult, ConflictClause, CongruenceClosure, EquationReason, NodeDetail, NodeId,
    NodeStatus, Obligation, PendingEquation, SearchNode, SearchSummary,
};

// Re-export union-find for convenience
pub use egglog_union_find::UnionFind;
