//! Core types for the solver infrastructure.

use std::collections::VecDeque;

use egglog_union_find::UnionFind;

use crate::core::Structure;
use crate::id::{Luid, Slid, NumericId};

/// Unique identifier for a search node
pub type NodeId = usize;

/// A node in the search tree
#[derive(Clone, Debug)]
pub struct SearchNode {
    /// Unique ID for this node
    pub id: NodeId,
    /// Parent node (None for root)
    pub parent: Option<NodeId>,
    /// Children (branches from this node)
    pub children: Vec<NodeId>,
    /// The partial model at this node
    pub structure: Structure,
    /// Congruence closure for tracking element equivalences
    pub cc: CongruenceClosure,
    /// Status of this node
    pub status: NodeStatus,
    /// Agent's estimate of success probability (0.0 to 1.0)
    pub p_success: f64,
    /// Conflict clauses learned at or below this node
    pub conflicts: Vec<ConflictClause>,
    /// Debug/display name for this node
    pub label: Option<String>,
}

/// Status of a search node
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NodeStatus {
    /// Still exploring (frontier node)
    Open,
    /// Found a valid complete instance
    Solved,
    /// Proved unsatisfiable from this point
    Unsat,
    /// Agent decided not to explore further
    Pruned,
}

/// A learned conflict clause (derivation of False)
///
/// Records a combination of commitments from which `⊢ False` was derived.
/// Used for CDCL-style pruning: if a node's commitments subsume a conflict
/// clause, that node can be immediately marked Unsat (since False is derivable).
///
/// Note: This represents a PROOF of unsatisfiability, not mere "conflicts".
/// Even apparent conflicts (like function defined with two different values)
/// just create pending equations—only if propagating those equations leads
/// to deriving False do we have a true conflict clause.
#[derive(Clone, Debug)]
pub struct ConflictClause {
    /// Elements that must exist (sort_id, luid)
    pub required_elements: Vec<(usize, Luid)>,
    /// Function values that must hold (func_id, domain_luid, codomain_luid)
    pub required_functions: Vec<(usize, Luid, Luid)>,
    /// Relation tuples that must be asserted (rel_id, tuple as Luids)
    pub required_relations: Vec<(usize, Vec<Luid>)>,
    /// Which axiom was violated (index into theory's axiom list)
    pub violated_axiom: Option<usize>,
    /// Human-readable explanation
    pub explanation: Option<String>,
}

/// An obligation to fulfill
///
/// Geometric logic consequents are positive (existentials, disjunctions, relations).
/// When an axiom's premise is satisfied but conclusion isn't, we have an OBLIGATION
/// to make the conclusion true. This can always potentially be done by refinement
/// (adding elements, defining functions, asserting relations).
///
/// Only when fulfilling the obligation would CONFLICT with existing commitments
/// is the node truly unsatisfiable.
#[derive(Clone, Debug)]
pub struct Obligation {
    /// Which axiom generated this obligation
    pub axiom_idx: usize,
    /// The variable assignment where premise holds but conclusion doesn't
    /// Maps variable name to (sort_id, slid) in the current structure
    pub assignment: Vec<(String, usize, Slid)>,
    /// Human-readable description of what needs to be witnessed
    pub description: String,
}

/// Result of checking axioms: either all satisfied, or obligations remain
#[derive(Clone, Debug)]
pub enum AxiomCheckResult {
    /// All axioms satisfied for all substitutions
    AllSatisfied,
    /// Some axioms have unsatisfied consequents (obligations to fulfill)
    Obligations(Vec<Obligation>),
}

/// Summary of the current search state (for agent inspection)
#[derive(Debug)]
pub struct SearchSummary {
    /// Total nodes in tree
    pub total_nodes: usize,
    /// Open frontier nodes
    pub frontier_size: usize,
    /// Solved nodes
    pub solved_count: usize,
    /// Unsat nodes
    pub unsat_count: usize,
    /// Top-k frontier nodes by probability
    pub top_frontier: Vec<(NodeId, f64, Option<String>)>,
}

/// Detailed information about a search node
#[derive(Debug)]
pub struct NodeDetail {
    pub id: NodeId,
    pub parent: Option<NodeId>,
    pub children: Vec<NodeId>,
    pub status: NodeStatus,
    pub p_success: f64,
    pub label: Option<String>,
    pub carrier_sizes: Vec<usize>,
    pub num_function_values: Vec<usize>,
    pub num_relation_tuples: Vec<usize>,
    pub conflicts: Vec<ConflictClause>,
}

// ============================================================================
// CONGRUENCE CLOSURE
// ============================================================================

/// A pending equation that needs to be resolved.
///
/// Equations arise from:
/// 1. Function conflicts: `f(a) = b` and `f(a) = c` implies `b = c`
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
}

/// Congruence closure state for a search node.
///
/// This wraps a union-find structure and pending equation queue,
/// providing methods for merging elements and propagating through
/// function applications.
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
        // Create a Slid with the canonical index
        // This is a bit of a hack - in reality we'd want proper
        // canonicalization of the Structure
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

// ============================================================================
// TESTS
// ============================================================================

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
}
