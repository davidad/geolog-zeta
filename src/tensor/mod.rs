//! Lazy tensor expressions for axiom checking
//!
//! A tensor indexed by finite sets A₀, A₁, ..., Aₙ₋₁ is a function
//! [∏ᵢ Aᵢ] → S for some ordered semiring S. We represent this sparsely,
//! storing only non-zero entries.
//!
//! Key insight: tensor product followed by contraction should NEVER
//! materialize the intermediate product. Instead, we build expression
//! trees and fuse operations during evaluation.
//!
//! Two primitives suffice for einsum-style operations:
//! - **tensor_product**: ⊗ₖ Sₖ — indexed by all indices, value = ⊗ of contributions
//! - **contract**: along `a:[N]→[M]`, output `O⊆[M]` — identifies indices, sums (⊕) over non-output
//!
//! Over the Boolean semiring: ⊗ = AND, ⊕ = OR.
//!
//! # Architecture
//!
//! - **semiring**: Ordered semirings with change actions for incremental computation
//! - **sparse**: Sparse tensor storage (currently BTreeSet-based, extensible to Roaring, CSR, etc.)
//! - **expr**: Lazy tensor expression trees
//! - **builder**: Convenience constructors for expressions
//! - **compile**: Compile formulas to tensor expressions
//! - **check**: Axiom checking using tensor expressions

pub mod algebra;
mod builder;
mod check;
mod compile;
pub mod delta;
mod expr;
pub mod pattern;
pub mod semiring;
mod sparse;

// Re-export main types
pub use builder::{conjunction, conjunction_all, disjunction, disjunction_all, exists};
pub use check::{
    check_sequent, check_sequent_bool, check_sequent_incremental, check_theory_axioms,
    check_theory_axioms_incremental, CheckResult, Violation,
};
pub use compile::{
    build_carrier_index, compile_formula, derived_sort_cardinality, relation_to_tensor,
    sort_cardinality, CompileContext, CompileError,
};
pub use delta::{
    extract_dimension_changes, patch_to_tensor_deltas, DimensionDelta, PatchTensorDelta,
};
pub use expr::TensorExpr;
pub use sparse::SparseTensor;
