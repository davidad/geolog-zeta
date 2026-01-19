//! Core types for the solver infrastructure.

use crate::core::Structure;
use crate::id::{Luid, Slid};

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
