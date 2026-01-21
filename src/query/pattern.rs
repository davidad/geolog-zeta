//! Pattern-based query representation.
//!
//! This represents the common pattern from bootstrap_queries:
//! "find all X : Sort where X.func₁ = Y₁ ∧ X.func₂ = Y₂ ∧ ..."
//!
//! In query semantics terms, this is an ∀-style query with an open result sort:
//! ```text
//! theory Query extends Base {
//!     Result : Sort;                           // Open (no constants)
//!     elem : Result → Sort;                    // Projection to base
//!     axiom { r : Result ⊢ elem(r).func₁ = Y₁ ∧ elem(r).func₂ = Y₂ }
//! }
//! ```
//!
//! The unique maximal element (cofree model) is the set of all elements
//! satisfying the constraint.

use crate::id::Slid;

/// A pattern query: find all elements of a sort matching constraints.
///
/// Equivalent to SQL: `SELECT elem FROM Sort WHERE func₁(elem) = v₁ AND ...`
///
/// Uses `usize` for sort/function IDs (internal indices) and `Slid` for
/// element values (external references).
#[derive(Debug, Clone)]
pub struct Pattern {
    /// The sort to scan (sort index)
    pub source_sort: usize,
    /// Constraints: each is (func_index, expected_value)
    pub constraints: Vec<Constraint>,
    /// What to project/return
    pub projection: Projection,
}

/// A constraint: func(elem) must equal expected_value
#[derive(Debug, Clone)]
pub struct Constraint {
    /// Function index to apply to the scanned element
    pub func: usize,
    /// Expected value (must match)
    pub expected: Slid,
}

/// What to return from the query
#[derive(Debug, Clone)]
pub enum Projection {
    /// Return the element itself
    Element,
    /// Return the value of a function applied to the element
    Func(usize),
    /// Return a tuple of function values
    Tuple(Vec<usize>),
}

impl Pattern {
    /// Create a new pattern query.
    ///
    /// # Example
    ///
    /// ```ignore
    /// // Find all Srt where Srt.theory == theory_slid
    /// let pattern = Pattern::new(store.sort_ids.srt.unwrap())
    ///     .filter(store.func_ids.srt_theory.unwrap(), theory_slid);
    /// ```
    pub fn new(source_sort: usize) -> Self {
        Self {
            source_sort,
            constraints: Vec::new(),
            projection: Projection::Element,
        }
    }

    /// Add a constraint: func(elem) must equal value.
    pub fn filter(mut self, func: usize, value: Slid) -> Self {
        self.constraints.push(Constraint {
            func,
            expected: value,
        });
        self
    }

    /// Project a function value instead of the element.
    pub fn project(mut self, func: usize) -> Self {
        self.projection = Projection::Func(func);
        self
    }

    /// Project a tuple of function values.
    pub fn project_tuple(mut self, funcs: Vec<usize>) -> Self {
        self.projection = Projection::Tuple(funcs);
        self
    }
}

// ============================================================================
// Pattern → QueryOp Compilation
// ============================================================================

use super::backend::{QueryOp, Predicate};

impl Pattern {
    /// Compile a Pattern into a QueryOp for the naive backend.
    ///
    /// A Pattern query:
    /// 1. Scans all elements of source_sort
    /// 2. Filters by constraints: func(elem) = expected for each constraint
    /// 3. Projects according to projection type
    ///
    /// We implement this as:
    /// - Scan → single-column tuples (elem)
    /// - For each constraint, use FuncEqConst predicate
    /// - Project to requested columns
    pub fn compile(&self) -> QueryOp {
        // Start with a scan of the sort
        let mut plan = QueryOp::Scan { sort_idx: self.source_sort };

        // Apply constraints as filters
        // Each constraint checks: func(elem) = expected
        for constraint in &self.constraints {
            plan = QueryOp::Filter {
                input: Box::new(plan),
                pred: Predicate::FuncEqConst {
                    func_idx: constraint.func,
                    arg_col: 0,  // The scanned element is always in column 0
                    expected: constraint.expected,
                },
            };
        }

        // Apply projection
        match &self.projection {
            Projection::Element => {
                // Already have the element in col 0, no change needed
            }
            Projection::Func(func_idx) => {
                // Apply function to element, return that instead
                // This requires an Apply operation
                plan = QueryOp::Apply {
                    input: Box::new(plan),
                    func_idx: *func_idx,
                    arg_col: 0,
                };
                // Now we have (elem, func(elem)), project to just col 1
                plan = QueryOp::Project {
                    input: Box::new(plan),
                    columns: vec![1],
                };
            }
            Projection::Tuple(func_indices) => {
                // Apply each function in sequence, then project
                for func_idx in func_indices.iter() {
                    plan = QueryOp::Apply {
                        input: Box::new(plan),
                        func_idx: *func_idx,
                        arg_col: 0, // Always apply to original element
                    };
                }
                // Now we have (elem, f1(elem), f2(elem), ...), project to func results
                // Columns 1, 2, ... are the func results
                let columns: Vec<usize> = (1..=func_indices.len()).collect();
                plan = QueryOp::Project {
                    input: Box::new(plan),
                    columns,
                };
            }
        }

        plan
    }
}
