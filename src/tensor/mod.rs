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
//! - **contract**: along `a:[N]→[M]`, output `O⊆[M]` — identifies indices, sums over non-output
//!
//! Over the Boolean semiring: product = AND, sum = OR.

mod builder;
mod check;
mod compile;
mod expr;
mod sparse;

// Re-export main types
pub use builder::{conjunction, conjunction_all, disjunction, disjunction_all, exists};
pub use check::{check_sequent, check_sequent_bool, check_theory_axioms, CheckResult, Violation};
pub use compile::{
    build_carrier_index, compile_formula, derived_sort_cardinality, relation_to_tensor,
    sort_cardinality, CompileContext, CompileError,
};
pub use expr::TensorExpr;
pub use sparse::SparseTensor;
