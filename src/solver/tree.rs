//! Search tree for instance synthesis.

use std::rc::Rc;

use crate::core::{ElaboratedTheory, RelationStorage, Signature, Structure};
use crate::id::{Luid, Slid, Uuid};
use crate::tensor::{CheckResult, Violation};
use crate::universe::Universe;

use super::types::{
    ConflictClause, CongruenceClosure, NodeDetail, NodeId, NodeStatus, SearchNode, SearchSummary,
};

/// The search tree
#[derive(Debug)]
pub struct SearchTree {
    /// All nodes, indexed by NodeId
    pub(crate) nodes: Vec<SearchNode>,
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
            cc: CongruenceClosure::new(),
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
        let child_cc = parent_node.cc.clone();
        let child_p = parent_node.p_success;

        let child_id = self.nodes.len();
        let child = SearchNode {
            id: child_id,
            parent: Some(parent),
            children: Vec::new(),
            structure: child_structure,
            cc: child_cc,
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
    pub fn add_element(&mut self, node: NodeId, sort_id: usize) -> Result<(Slid, Luid), String> {
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
        Ok(node
            .structure
            .add_element_with_uuid(&mut self.universe, uuid, sort_id))
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
        node.structure
            .define_function(func_id, domain_slid, codomain_slid)
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
    pub fn init_relations(&mut self, node: NodeId, arities: &[usize]) -> Result<(), String> {
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
        let node = self.nodes.get(node).ok_or_else(Vec::new)?;
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
                crate::core::DerivedSort::Base(sort_id) => node.structure.carrier_size(*sort_id),
                crate::core::DerivedSort::Product(_) => {
                    // Product domains: need to compute cardinality
                    // For now, skip (TODO: handle product domains properly)
                    continue;
                }
            };

            // Check all domain elements have values (local functions only for now)
            let func_col = &node.structure.functions[func_id];
            if func_col.len() < domain_size {
                return Ok(false);
            }
            if let Some(local_col) = func_col.as_local() {
                for opt in local_col {
                    if opt.is_none() {
                        return Ok(false);
                    }
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
// AGENT INTERFACE
// ============================================================================

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
            solved_count: self
                .nodes
                .iter()
                .filter(|n| n.status == NodeStatus::Solved)
                .count(),
            unsat_count: self
                .nodes
                .iter()
                .filter(|n| n.status == NodeStatus::Unsat)
                .count(),
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
            carrier_sizes: node
                .structure
                .carriers
                .iter()
                .map(|c| c.len() as usize)
                .collect(),
            num_function_values: node
                .structure
                .functions
                .iter()
                .map(|f| match f {
                    crate::core::FunctionColumn::Local(col) => {
                        col.iter().filter(|opt| opt.is_some()).count()
                    }
                    crate::core::FunctionColumn::External(col) => {
                        col.iter().filter(|opt| opt.is_some()).count()
                    }
                    crate::core::FunctionColumn::ProductLocal { storage, .. } => {
                        storage.defined_count()
                    }
                })
                .collect(),
            num_relation_tuples: node.structure.relations.iter().map(|r| r.len()).collect(),
            conflicts: node.conflicts.clone(),
        })
    }
}
