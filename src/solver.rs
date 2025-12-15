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

use std::rc::Rc;

use crate::core::{ElaboratedTheory, RelationStorage, Signature, Structure};
use crate::id::{Luid, NumericId, Slid, Uuid};
use crate::tensor::{CheckResult, Violation};
use crate::universe::Universe;

// Re-export for convenience
pub use egglog_union_find::UnionFind;

// ============================================================================
// NODE AND TREE TYPES
// ============================================================================

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

/// The search tree
#[derive(Debug)]
pub struct SearchTree {
    /// All nodes, indexed by NodeId
    nodes: Vec<SearchNode>,
    /// The theory we're trying to instantiate
    pub theory: Rc<ElaboratedTheory>,
    /// Universe for Luid allocation
    pub universe: Universe,
}

impl SearchTree {
    /// Create a new search tree for instantiating a theory
    ///
    /// The root node contains an empty Structure with the right number of
    /// sorts but no elements.
    pub fn new(theory: Rc<ElaboratedTheory>) -> Self {
        let num_sorts = theory.theory.signature.sorts.len();
        let root_structure = Structure::new(num_sorts);

        let root = SearchNode {
            id: 0,
            parent: None,
            children: Vec::new(),
            structure: root_structure,
            status: NodeStatus::Open,
            p_success: 0.5, // Prior: 50% chance of solution existing
            conflicts: Vec::new(),
            label: Some("root".to_string()),
        };

        Self {
            nodes: vec![root],
            theory,
            universe: Universe::new(),
        }
    }

    /// Get the root node ID
    pub fn root(&self) -> NodeId {
        0
    }

    /// Get a node by ID
    pub fn get(&self, id: NodeId) -> Option<&SearchNode> {
        self.nodes.get(id)
    }

    /// Get a mutable reference to a node
    pub fn get_mut(&mut self, id: NodeId) -> Option<&mut SearchNode> {
        self.nodes.get_mut(id)
    }

    /// Get the signature of the theory
    pub fn signature(&self) -> &Signature {
        &self.theory.theory.signature
    }

    /// Get all open frontier nodes
    pub fn frontier(&self) -> Vec<NodeId> {
        self.nodes
            .iter()
            .filter(|n| n.status == NodeStatus::Open && n.children.is_empty())
            .map(|n| n.id)
            .collect()
    }

    /// Get frontier nodes sorted by p_success (descending)
    pub fn frontier_by_probability(&self) -> Vec<NodeId> {
        let mut frontier = self.frontier();
        frontier.sort_by(|&a, &b| {
            let pa = self.nodes[a].p_success;
            let pb = self.nodes[b].p_success;
            pb.partial_cmp(&pa).unwrap_or(std::cmp::Ordering::Equal)
        });
        frontier
    }

    /// Create a child node by cloning the parent's structure
    ///
    /// Returns the new node's ID. The child starts with the same structure
    /// as the parent (will be refined by subsequent operations).
    pub fn branch(&mut self, parent: NodeId, label: Option<String>) -> NodeId {
        let parent_node = &self.nodes[parent];
        let child_structure = parent_node.structure.clone();
        let child_p = parent_node.p_success;

        let child_id = self.nodes.len();
        let child = SearchNode {
            id: child_id,
            parent: Some(parent),
            children: Vec::new(),
            structure: child_structure,
            status: NodeStatus::Open,
            p_success: child_p,
            conflicts: Vec::new(),
            label,
        };

        self.nodes.push(child);
        self.nodes[parent].children.push(child_id);
        child_id
    }

    /// Mark a node as solved (found valid instance)
    pub fn mark_solved(&mut self, id: NodeId) {
        if let Some(node) = self.nodes.get_mut(id) {
            node.status = NodeStatus::Solved;
        }
    }

    /// Mark a node as unsatisfiable
    pub fn mark_unsat(&mut self, id: NodeId, conflict: Option<ConflictClause>) {
        if let Some(node) = self.nodes.get_mut(id) {
            node.status = NodeStatus::Unsat;
            if let Some(c) = conflict {
                node.conflicts.push(c);
            }
        }
    }

    /// Mark a node as pruned (agent decided not to explore)
    pub fn mark_pruned(&mut self, id: NodeId) {
        if let Some(node) = self.nodes.get_mut(id) {
            node.status = NodeStatus::Pruned;
        }
    }

    /// Update a node's success probability estimate
    pub fn set_probability(&mut self, id: NodeId, p: f64) {
        if let Some(node) = self.nodes.get_mut(id) {
            node.p_success = p.clamp(0.0, 1.0);
        }
    }

    /// Check if any node has been solved
    pub fn has_solution(&self) -> Option<NodeId> {
        self.nodes
            .iter()
            .find(|n| n.status == NodeStatus::Solved)
            .map(|n| n.id)
    }

    /// Get the path from root to a node (list of NodeIds)
    pub fn path_to(&self, id: NodeId) -> Vec<NodeId> {
        let mut path = Vec::new();
        let mut current = Some(id);
        while let Some(nid) = current {
            path.push(nid);
            current = self.nodes[nid].parent;
        }
        path.reverse();
        path
    }
}

// ============================================================================
// REFINEMENT OPERATIONS
// ============================================================================

/// Operations for refining a partial model (moving up in the refinement order)
impl SearchTree {
    /// Add a new element to a sort in a node's structure
    ///
    /// Returns the (Slid, Luid) of the new element.
    pub fn add_element(
        &mut self,
        node: NodeId,
        sort_id: usize,
    ) -> Result<(Slid, Luid), String> {
        let node = self.nodes.get_mut(node).ok_or("Invalid node ID")?;
        if node.status != NodeStatus::Open {
            return Err("Cannot refine a non-open node".to_string());
        }
        Ok(node.structure.add_element(&mut self.universe, sort_id))
    }

    /// Add a new element with a specific UUID
    pub fn add_element_with_uuid(
        &mut self,
        node: NodeId,
        uuid: Uuid,
        sort_id: usize,
    ) -> Result<(Slid, Luid), String> {
        let node = self.nodes.get_mut(node).ok_or("Invalid node ID")?;
        if node.status != NodeStatus::Open {
            return Err("Cannot refine a non-open node".to_string());
        }
        Ok(node.structure.add_element_with_uuid(&mut self.universe, uuid, sort_id))
    }

    /// Define a function value: f(domain) = codomain
    ///
    /// The function must not already be defined at this domain element
    /// (that would be a conflict, not a refinement).
    pub fn define_function(
        &mut self,
        node: NodeId,
        func_id: usize,
        domain_slid: Slid,
        codomain_slid: Slid,
    ) -> Result<(), String> {
        let node = self.nodes.get_mut(node).ok_or("Invalid node ID")?;
        if node.status != NodeStatus::Open {
            return Err("Cannot refine a non-open node".to_string());
        }
        node.structure.define_function(func_id, domain_slid, codomain_slid)
    }

    /// Assert a relation tuple: R(tuple) = true
    pub fn assert_relation(
        &mut self,
        node: NodeId,
        rel_id: usize,
        tuple: Vec<Slid>,
    ) -> Result<bool, String> {
        let node = self.nodes.get_mut(node).ok_or("Invalid node ID")?;
        if node.status != NodeStatus::Open {
            return Err("Cannot refine a non-open node".to_string());
        }
        Ok(node.structure.assert_relation(rel_id, tuple))
    }

    /// Initialize function storage for a node (call after adding elements)
    pub fn init_functions(
        &mut self,
        node: NodeId,
        domain_sort_ids: &[Option<usize>],
    ) -> Result<(), String> {
        let node = self.nodes.get_mut(node).ok_or("Invalid node ID")?;
        node.structure.init_functions(domain_sort_ids);
        Ok(())
    }

    /// Initialize relation storage for a node
    pub fn init_relations(
        &mut self,
        node: NodeId,
        arities: &[usize],
    ) -> Result<(), String> {
        let node = self.nodes.get_mut(node).ok_or("Invalid node ID")?;
        node.structure.init_relations(arities);
        Ok(())
    }
}

// ============================================================================
// CONSTRAINT CHECKING
// ============================================================================

impl SearchTree {
    /// Check all axioms against a node's current structure
    ///
    /// Returns Ok(()) if all axioms are satisfied, or Err with violations.
    pub fn check_axioms(&self, node: NodeId) -> Result<(), Vec<(usize, Vec<Violation>)>> {
        let node = self.nodes.get(node).ok_or_else(|| vec![])?;
        let violations = crate::tensor::check_theory_axioms(
            &self.theory.theory.axioms,
            &node.structure,
            &self.theory.theory.signature,
        );
        if violations.is_empty() {
            Ok(())
        } else {
            Err(violations)
        }
    }

    /// Check a single axiom
    pub fn check_axiom(&self, node: NodeId, axiom_idx: usize) -> CheckResult {
        let node = match self.nodes.get(node) {
            Some(n) => n,
            None => return CheckResult::Satisfied, // Invalid node = vacuously true?
        };
        let axiom = match self.theory.theory.axioms.get(axiom_idx) {
            Some(a) => a,
            None => return CheckResult::Satisfied,
        };
        crate::tensor::check_sequent(axiom, &node.structure, &self.theory.theory.signature)
    }

    /// Check if a structure is "complete" (all functions total, all axioms satisfied)
    ///
    /// A complete structure is a valid model of the theory.
    pub fn is_complete(&self, node: NodeId) -> Result<bool, String> {
        let node = self.nodes.get(node).ok_or("Invalid node ID")?;
        let sig = &self.theory.theory.signature;

        // Check all functions are total
        for (func_id, func_sym) in sig.functions.iter().enumerate() {
            if func_id >= node.structure.functions.len() {
                return Ok(false); // Function storage not initialized
            }

            // Get domain size
            let domain_size = match &func_sym.domain {
                crate::core::DerivedSort::Base(sort_id) => {
                    node.structure.carrier_size(*sort_id)
                }
                crate::core::DerivedSort::Product(_) => {
                    // Product domains: need to compute cardinality
                    // For now, skip (TODO: handle product domains properly)
                    continue;
                }
            };

            // Check all domain elements have values
            if node.structure.functions[func_id].len() < domain_size {
                return Ok(false);
            }
            for opt in &node.structure.functions[func_id] {
                if opt.is_none() {
                    return Ok(false);
                }
            }
        }

        // Check all axioms
        match self.check_axioms(node.id) {
            Ok(()) => Ok(true),
            Err(_) => Ok(false),
        }
    }
}

// ============================================================================
// TACTICS
// ============================================================================

/// Budget for tactic execution
#[derive(Clone, Debug)]
pub struct Budget {
    /// Maximum wall-clock time in milliseconds
    pub time_ms: u64,
    /// Maximum number of refinement steps
    pub steps: usize,
}

impl Budget {
    pub fn new(time_ms: u64, steps: usize) -> Self {
        Self { time_ms, steps }
    }

    /// A short budget for quick checks
    pub fn quick() -> Self {
        Self { time_ms: 100, steps: 100 }
    }

    /// A medium budget for exploratory search
    pub fn medium() -> Self {
        Self { time_ms: 1000, steps: 1000 }
    }

    /// A longer budget for deeper search
    pub fn long() -> Self {
        Self { time_ms: 5000, steps: 10000 }
    }
}

/// Result of running a tactic
#[derive(Clone, Debug)]
pub enum TacticResult {
    /// Found a valid complete instance at this node
    Solved,
    /// Proved this node has no solution (with optional conflict clause)
    /// This only happens when fulfilling obligations would CONFLICT with
    /// existing commitments, not merely because axioms aren't yet satisfied.
    Unsat(Option<ConflictClause>),
    /// Axioms have unsatisfied consequents that need to be witnessed.
    /// This is NOT failure—the agent should fulfill these obligations
    /// (add elements, define functions, assert relations) to make progress.
    HasObligations(Vec<Obligation>),
    /// Made progress, can continue with more budget
    Progress {
        /// Number of refinement steps taken
        steps_taken: usize,
        /// Number of branches created
        branches_created: usize,
    },
    /// Budget exhausted without conclusive result
    Timeout {
        /// Where we got to
        steps_taken: usize,
    },
    /// Error during execution
    Error(String),
}

/// A tactic for automated search
///
/// Tactics implement specific search strategies. They run for bounded time/steps
/// and return a result. The agent orchestrates tactics across the search tree.
pub trait Tactic {
    /// Run the tactic on a node with the given budget
    fn run(
        &mut self,
        tree: &mut SearchTree,
        node: NodeId,
        budget: &Budget,
    ) -> TacticResult;

    /// Human-readable name for this tactic
    fn name(&self) -> &str;
}

// ============================================================================
// BUILT-IN TACTICS
// ============================================================================

/// Check tactic: check axioms and report obligations
///
/// In geometric logic, axiom "violations" are really OBLIGATIONS to fulfill.
/// The consequent is always positive, so we can potentially satisfy it by
/// adding elements, defining functions, or asserting relations.
///
/// This tactic checks current state and returns:
/// - Solved if complete and all axioms satisfied
/// - HasObligations if there are consequents to witness
/// - Progress if incomplete but no current obligations
pub struct CheckTactic;

impl Tactic for CheckTactic {
    fn run(&mut self, tree: &mut SearchTree, node: NodeId, _budget: &Budget) -> TacticResult {
        match tree.check_axioms(node) {
            Ok(()) => {
                // No violations - check if complete
                match tree.is_complete(node) {
                    Ok(true) => {
                        tree.mark_solved(node);
                        TacticResult::Solved
                    }
                    Ok(false) => TacticResult::Progress {
                        steps_taken: 1,
                        branches_created: 0,
                    },
                    Err(e) => TacticResult::Error(e),
                }
            }
            Err(violations) => {
                // Convert violations to obligations
                // Violations mean: premise satisfied, conclusion not yet satisfied
                // This is an OBLIGATION to witness the conclusion, not unsat!
                let obligations: Vec<Obligation> = violations
                    .iter()
                    .flat_map(|(axiom_idx, viols)| {
                        viols.iter().map(move |v| Obligation {
                            axiom_idx: *axiom_idx,
                            // Convert variable assignment to (name, sort_id, slid)
                            // For now, we don't have sort info in Violation, so approximate
                            assignment: v.variable_names.iter().zip(v.assignment.iter())
                                .map(|(name, &idx)| (name.clone(), 0, Slid::from_usize(idx))) // sort_id=0 is placeholder
                                .collect(),
                            description: format!(
                                "Axiom {} needs consequent witnessed for assignment {:?}",
                                axiom_idx, v.assignment
                            ),
                        })
                    })
                    .collect();

                TacticResult::HasObligations(obligations)
            }
        }
    }

    fn name(&self) -> &str {
        "check"
    }
}

/// Legacy alias for CheckTactic
#[deprecated(note = "Use CheckTactic instead - violations are obligations, not unsat")]
pub type PropagationTactic = CheckTactic;

/// Enumeration tactic: try all values for an undefined function
pub struct EnumerateFunctionTactic {
    pub func_id: usize,
}

impl Tactic for EnumerateFunctionTactic {
    fn run(&mut self, tree: &mut SearchTree, node: NodeId, budget: &Budget) -> TacticResult {
        let start = std::time::Instant::now();
        let mut steps = 0;
        let mut branches = 0;

        let sig = tree.signature().clone();
        let func_sym = match sig.functions.get(self.func_id) {
            Some(f) => f,
            None => return TacticResult::Error("Invalid function ID".to_string()),
        };

        // Get domain and codomain sorts
        let (domain_sort, codomain_sort) = match (&func_sym.domain, &func_sym.codomain) {
            (crate::core::DerivedSort::Base(d), crate::core::DerivedSort::Base(c)) => (*d, *c),
            _ => return TacticResult::Error("Only base sorts supported for now".to_string()),
        };

        // Find undefined function applications
        let node_ref = match tree.get(node) {
            Some(n) => n,
            None => return TacticResult::Error("Invalid node ID".to_string()),
        };

        if self.func_id >= node_ref.structure.functions.len() {
            return TacticResult::Error("Function storage not initialized".to_string());
        }

        // Find first undefined domain element
        let mut undefined_domain: Option<Slid> = None;
        for slid_u64 in node_ref.structure.carriers[domain_sort].iter() {
            let slid = Slid::from_usize(slid_u64 as usize);
            let sort_slid = node_ref.structure.sort_local_id(slid);
            if sort_slid.index() < node_ref.structure.functions[self.func_id].len() {
                if node_ref.structure.functions[self.func_id][sort_slid.index()].is_none() {
                    undefined_domain = Some(slid);
                    break;
                }
            }
        }

        let domain_slid = match undefined_domain {
            Some(d) => d,
            None => {
                // All defined - check current state
                return CheckTactic.run(tree, node, budget);
            }
        };

        // Enumerate codomain values
        let codomain_elements: Vec<Slid> = node_ref.structure.carriers[codomain_sort]
            .iter()
            .map(|x| Slid::from_usize(x as usize))
            .collect();

        if codomain_elements.is_empty() {
            return TacticResult::Error("Empty codomain - need to add elements first".to_string());
        }

        // Create a branch for each possible value
        for &codomain_slid in &codomain_elements {
            if start.elapsed().as_millis() as u64 > budget.time_ms || steps >= budget.steps {
                return TacticResult::Timeout { steps_taken: steps };
            }

            let child = tree.branch(node, Some(format!(
                "f{}({})={}",
                self.func_id, domain_slid, codomain_slid
            )));

            if let Err(e) = tree.define_function(child, self.func_id, domain_slid, codomain_slid) {
                tree.mark_unsat(child, Some(ConflictClause {
                    required_elements: vec![],
                    required_functions: vec![],
                    required_relations: vec![],
                    violated_axiom: None,
                    explanation: Some(e),
                }));
            }

            steps += 1;
            branches += 1;
        }

        // Mark parent as non-leaf (it has children now)
        // Parent stays Open but is no longer on frontier

        TacticResult::Progress {
            steps_taken: steps,
            branches_created: branches,
        }
    }

    fn name(&self) -> &str {
        "enumerate_function"
    }
}

// ============================================================================
// AGENT INTERFACE
// ============================================================================

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

impl SearchTree {
    /// Get a summary of the search state
    pub fn summary(&self, top_k: usize) -> SearchSummary {
        let frontier = self.frontier_by_probability();
        let top_frontier: Vec<_> = frontier
            .iter()
            .take(top_k)
            .map(|&id| {
                let node = &self.nodes[id];
                (id, node.p_success, node.label.clone())
            })
            .collect();

        SearchSummary {
            total_nodes: self.nodes.len(),
            frontier_size: frontier.len(),
            solved_count: self.nodes.iter().filter(|n| n.status == NodeStatus::Solved).count(),
            unsat_count: self.nodes.iter().filter(|n| n.status == NodeStatus::Unsat).count(),
            top_frontier,
        }
    }

    /// Get detailed info about a node (for agent inspection)
    pub fn node_detail(&self, id: NodeId) -> Option<NodeDetail> {
        let node = self.nodes.get(id)?;
        Some(NodeDetail {
            id: node.id,
            parent: node.parent,
            children: node.children.clone(),
            status: node.status.clone(),
            p_success: node.p_success,
            label: node.label.clone(),
            carrier_sizes: node.structure.carriers.iter().map(|c| c.len() as usize).collect(),
            num_function_values: node.structure.functions.iter().map(|f| {
                f.iter().filter(|opt| opt.is_some()).count()
            }).collect(),
            num_relation_tuples: node.structure.relations.iter().map(|r| r.len()).collect(),
            conflicts: node.conflicts.clone(),
        })
    }
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
// TESTS
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::{DerivedSort, Signature, Theory};

    fn make_simple_theory() -> Rc<ElaboratedTheory> {
        // A simple theory with one sort and one function
        let mut sig = Signature::new();
        let node_id = sig.add_sort("Node".to_string());
        sig.add_function(
            "f".to_string(),
            DerivedSort::Base(node_id),
            DerivedSort::Base(node_id),
        );

        Rc::new(ElaboratedTheory {
            params: vec![],
            theory: Theory {
                name: "Simple".to_string(),
                signature: sig,
                axioms: vec![],
            },
        })
    }

    #[test]
    fn test_search_tree_creation() {
        let theory = make_simple_theory();
        let tree = SearchTree::new(theory);

        assert_eq!(tree.nodes.len(), 1);
        assert_eq!(tree.root(), 0);
        assert_eq!(tree.frontier(), vec![0]);
    }

    #[test]
    fn test_branching() {
        let theory = make_simple_theory();
        let mut tree = SearchTree::new(theory);

        let child1 = tree.branch(0, Some("child1".to_string()));
        let child2 = tree.branch(0, Some("child2".to_string()));

        assert_eq!(tree.nodes.len(), 3);
        assert_eq!(tree.nodes[0].children, vec![child1, child2]);
        assert_eq!(tree.nodes[child1].parent, Some(0));
        assert_eq!(tree.nodes[child2].parent, Some(0));

        // Frontier should now be the children
        let frontier = tree.frontier();
        assert!(frontier.contains(&child1));
        assert!(frontier.contains(&child2));
        assert!(!frontier.contains(&0)); // Parent no longer on frontier (has children)
    }

    #[test]
    fn test_add_elements() {
        let theory = make_simple_theory();
        let mut tree = SearchTree::new(theory);

        // Add elements to root
        let (slid1, _luid1) = tree.add_element(0, 0).unwrap();
        let (slid2, _luid2) = tree.add_element(0, 0).unwrap();

        assert_eq!(slid1, Slid::from_usize(0));
        assert_eq!(slid2, Slid::from_usize(1));
        assert_eq!(tree.nodes[0].structure.carrier_size(0), 2);
    }

    #[test]
    fn test_check_tactic() {
        let theory = make_simple_theory();
        let mut tree = SearchTree::new(theory);

        // Empty structure should be "incomplete" but no obligations (no axioms)
        let result = CheckTactic.run(&mut tree, 0, &Budget::quick());

        // No axioms means no obligations, but also not complete (no elements, no function values)
        match result {
            TacticResult::Progress { .. } => {} // Expected
            other => panic!("Unexpected result: {:?}", other),
        }
    }

    #[test]
    fn test_summary() {
        let theory = make_simple_theory();
        let mut tree = SearchTree::new(theory);

        tree.branch(0, Some("a".to_string()));
        tree.branch(0, Some("b".to_string()));

        let summary = tree.summary(5);
        assert_eq!(summary.total_nodes, 3);
        assert_eq!(summary.frontier_size, 2);
        assert_eq!(summary.solved_count, 0);
    }

    #[test]
    fn test_union_find_with_slid() {
        use crate::id::Slid;

        // Helper for cleaner syntax
        fn s(n: usize) -> Slid { Slid::from_usize(n) }

        // Verify egglog's union-find works with our Slid type (which is usize)
        let mut uf: UnionFind<Slid> = UnionFind::default();

        // Union some elements
        let (parent, child) = uf.union(s(0), s(1));
        assert_eq!(parent, s(0)); // union-by-min: smaller id becomes parent
        assert_eq!(child, s(1));

        // Find should return canonical representative
        assert_eq!(uf.find(s(0)), s(0));
        assert_eq!(uf.find(s(1)), s(0));

        // Add more elements and union
        let (parent2, child2) = uf.union(s(2), s(3));
        assert_eq!(parent2, s(2));
        assert_eq!(child2, s(3));

        // Union the two equivalence classes
        let (parent3, child3) = uf.union(s(1), s(3));
        // Now 0, 1, 2, 3 should all be in same class with 0 as root
        assert_eq!(parent3, s(0)); // find(1) = 0, find(3) = 2, min(0,2) = 0
        assert_eq!(child3, s(2));

        assert_eq!(uf.find(s(0)), s(0));
        assert_eq!(uf.find(s(1)), s(0));
        assert_eq!(uf.find(s(2)), s(0));
        assert_eq!(uf.find(s(3)), s(0));
    }
}
