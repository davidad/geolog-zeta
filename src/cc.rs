//! Congruence Closure for equality reasoning.
//!
//! This module provides a union-find based congruence closure implementation
//! that can be used by both the solver (for model enumeration) and the chase
//! (for computing derived relations with equality saturation).
//!
//! # Key Types
//!
//! - [`CongruenceClosure`]: Main struct wrapping union-find + pending equation queue
//! - [`PendingEquation`]: An equation waiting to be processed
//! - [`EquationReason`]: Why an equation was created (for debugging/explanation)
//!
//! # Usage
//!
//! ```ignore
//! use geolog::cc::{CongruenceClosure, EquationReason};
//!
//! let mut cc = CongruenceClosure::new();
//!
//! // Add equation: a = b
//! cc.add_equation(a, b, EquationReason::UserAsserted);
//!
//! // Process pending equations
//! while let Some(eq) = cc.pop_pending() {
//!     cc.merge(eq.lhs, eq.rhs);
//!     // Check for function conflicts, add congruence equations...
//! }
//!
//! // Query equivalence
//! assert!(cc.are_equal(a, b));
//! ```

use std::collections::VecDeque;

use egglog_union_find::UnionFind;

use crate::id::{NumericId, Slid};

/// A pending equation to be processed.
///
/// Equations arise from:
/// 1. Function conflicts: `f(a) = x` and `f(a) = y` implies `x = y`
/// 2. Axiom consequents: `∀x. P(x) → x = y`
/// 3. Record projections: `[fst: a, snd: b].fst = a`
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PendingEquation {
    /// Left-hand side element
    pub lhs: Slid,
    /// Right-hand side element
    pub rhs: Slid,
    /// Reason for the equation (for debugging/explanation)
    pub reason: EquationReason,
}

/// Reason an equation was created
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EquationReason {
    /// Function already maps domain to different values
    FunctionConflict { func_id: usize, domain: Slid },
    /// Axiom consequent required this equality
    AxiomConsequent { axiom_idx: usize },
    /// User asserted this equation
    UserAsserted,
    /// Congruence: f(a) = f(b) because a = b
    Congruence { func_id: usize },
    /// Chase-derived: equality conclusion in chase
    ChaseConclusion,
}

/// Congruence closure state.
///
/// This wraps a union-find structure and pending equation queue,
/// providing methods for merging elements and tracking equivalence classes.
///
/// Note: This struct handles the union-find bookkeeping but does NOT
/// automatically propagate through function applications. The caller
/// (solver or chase) is responsible for detecting function conflicts
/// and adding congruence equations.
#[derive(Clone)]
pub struct CongruenceClosure {
    /// Union-find for tracking equivalence classes
    /// Uses Slid indices as keys
    pub uf: UnionFind<usize>,
    /// Pending equations to process
    pub pending: VecDeque<PendingEquation>,
    /// Number of merges performed (for statistics)
    pub merge_count: usize,
}

impl std::fmt::Debug for CongruenceClosure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CongruenceClosure")
            .field("pending", &self.pending)
            .field("merge_count", &self.merge_count)
            .finish_non_exhaustive()
    }
}

impl Default for CongruenceClosure {
    fn default() -> Self {
        Self::new()
    }
}

impl CongruenceClosure {
    /// Create a new congruence closure
    pub fn new() -> Self {
        Self {
            uf: UnionFind::default(),
            pending: VecDeque::new(),
            merge_count: 0,
        }
    }

    /// Find the canonical representative of an element
    /// Note: The UnionFind automatically reserves space as needed
    pub fn find(&mut self, slid: Slid) -> usize {
        self.uf.find(slid.index())
    }

    /// Check if two elements are in the same equivalence class
    pub fn are_equal(&mut self, a: Slid, b: Slid) -> bool {
        self.find(a) == self.find(b)
    }

    /// Add a pending equation
    pub fn add_equation(&mut self, lhs: Slid, rhs: Slid, reason: EquationReason) {
        self.pending.push_back(PendingEquation { lhs, rhs, reason });
    }

    /// Pop the next pending equation, if any
    pub fn pop_pending(&mut self) -> Option<PendingEquation> {
        self.pending.pop_front()
    }

    /// Check if there are pending equations
    pub fn has_pending(&self) -> bool {
        !self.pending.is_empty()
    }

    /// Merge two elements, returning true if they were not already equal
    pub fn merge(&mut self, a: Slid, b: Slid) -> bool {
        let a_idx = a.index();
        let b_idx = b.index();

        let ra = self.uf.find(a_idx);
        let rb = self.uf.find(b_idx);

        if ra != rb {
            self.uf.union(ra, rb);
            self.merge_count += 1;
            true
        } else {
            false
        }
    }

    /// Get the canonical Slid for an element
    ///
    /// Note: This returns a Slid with the canonical index, but the actual
    /// element in the Structure is still at the original Slid.
    pub fn canonical(&mut self, slid: Slid) -> Slid {
        let idx = self.find(slid);
        Slid::from_usize(idx)
    }

    /// Get the number of elements tracked
    pub fn num_elements(&self) -> usize {
        self.merge_count + self.pending.len() // approximation
    }

    /// Get statistics about the congruence closure: (merges, pending)
    pub fn stats(&self) -> (usize, usize) {
        (self.merge_count, self.pending.len())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_congruence_closure_basic() {
        let mut cc = CongruenceClosure::new();
        let a = Slid::from_usize(0);
        let b = Slid::from_usize(1);
        let c = Slid::from_usize(2);

        // Initially all different
        assert!(!cc.are_equal(a, b));
        assert!(!cc.are_equal(b, c));
        assert!(!cc.are_equal(a, c));

        // Merge a and b
        assert!(cc.merge(a, b));
        assert!(cc.are_equal(a, b));
        assert!(!cc.are_equal(b, c));

        // Merge b and c (should transitively merge a and c)
        assert!(cc.merge(b, c));
        assert!(cc.are_equal(a, c));
        assert!(cc.are_equal(a, b));
        assert!(cc.are_equal(b, c));

        // Merging already equal elements returns false
        assert!(!cc.merge(a, c));
    }

    #[test]
    fn test_congruence_closure_pending() {
        let mut cc = CongruenceClosure::new();
        let a = Slid::from_usize(0);
        let b = Slid::from_usize(1);

        assert!(!cc.has_pending());

        cc.add_equation(a, b, EquationReason::UserAsserted);
        assert!(cc.has_pending());

        let eq = cc.pop_pending().unwrap();
        assert_eq!(eq.lhs, a);
        assert_eq!(eq.rhs, b);
        assert!(!cc.has_pending());
    }

    #[test]
    fn test_congruence_closure_stats() {
        let mut cc = CongruenceClosure::new();
        let a = Slid::from_usize(0);
        let b = Slid::from_usize(1);

        assert_eq!(cc.stats(), (0, 0));

        cc.merge(a, b);
        assert_eq!(cc.stats(), (1, 0));

        cc.add_equation(a, b, EquationReason::UserAsserted);
        assert_eq!(cc.stats(), (1, 1));
    }

    #[test]
    fn test_canonical() {
        let mut cc = CongruenceClosure::new();
        let a = Slid::from_usize(5);
        let b = Slid::from_usize(10);

        // Before merge, each is its own canonical
        let ca = cc.canonical(a);
        let cb = cc.canonical(b);
        assert_ne!(ca, cb);

        // After merge, both have same canonical
        cc.merge(a, b);
        let ca2 = cc.canonical(a);
        let cb2 = cc.canonical(b);
        assert_eq!(ca2, cb2);
    }
}
