//! Query engine for geolog.
//!
//! **Semantics:** Queries are theory extensions. The result is the set of maximal
//! elements in the posetal reflection of well-formed Ext_M(T') — the category
//! of T'-extensions of base model M.
//!
//! See `loose_thoughts/2026-01-19_18:15_query_semantics.md` for full design.
//!
//! # Query Styles
//!
//! - **∃-style (closed sorts):** New sorts with declared constants.
//!   Well-formedness requires exactly those constants exist.
//!   Maximal elements = one per valid witness assignment.
//!   Implementation: constraint satisfaction.
//!
//! - **∀-style (open sorts):** New sorts with no constants, constrained by
//!   universal axioms. Bounded by constraint, posetal reflection identifies
//!   observationally-equivalent duplicates.
//!   Unique maximal element = cofree model.
//!   Implementation: relational algebra / Datalog.
//!
//! # Implementation Phases
//!
//! 1. **Open sort computation** - what bootstrap_queries does manually
//! 2. **Closed sort enumeration** - constraint satisfaction
//! 3. **Chase for derived relations** - semi-naive fixpoint
//! 4. **Mixed queries** - combine both

mod pattern;
mod exec;
pub mod backend;
pub mod optimize;
pub mod compile;
mod store_queries;

pub use pattern::{Pattern, Constraint, Projection};
pub use exec::{QueryResult, execute_pattern};
pub use backend::{Bag, QueryOp, Predicate, JoinCond, execute, StreamContext, execute_stream};
pub use optimize::optimize;
pub use compile::{Query, QueryBuilder, compile_simple_filter, compile_filter_project};
