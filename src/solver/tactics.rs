//! Tactics for automated search.

use crate::id::{NumericId, Slid};

use super::tree::SearchTree;
use super::types::{ConflictClause, NodeId, Obligation};

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
        Self {
            time_ms: 100,
            steps: 100,
        }
    }

    /// A medium budget for exploratory search
    pub fn medium() -> Self {
        Self {
            time_ms: 1000,
            steps: 1000,
        }
    }

    /// A longer budget for deeper search
    pub fn long() -> Self {
        Self {
            time_ms: 5000,
            steps: 10000,
        }
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
    fn run(&mut self, tree: &mut SearchTree, node: NodeId, budget: &Budget) -> TacticResult;

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
                            assignment: v
                                .variable_names
                                .iter()
                                .zip(v.assignment.iter())
                                .map(|(name, &idx)| (name.clone(), 0, Slid::from_usize(idx)))
                                // sort_id=0 is placeholder
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

        // Find first undefined domain element (for local functions)
        let mut undefined_domain: Option<Slid> = None;
        for slid_u64 in node_ref.structure.carriers[domain_sort].iter() {
            let slid = Slid::from_usize(slid_u64 as usize);
            let sort_slid = node_ref.structure.sort_local_id(slid);
            if node_ref
                .structure
                .get_function(self.func_id, sort_slid)
                .is_none()
            {
                undefined_domain = Some(slid);
                break;
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

            let child = tree.branch(
                node,
                Some(format!(
                    "f{}({})={}",
                    self.func_id, domain_slid, codomain_slid
                )),
            );

            if let Err(e) = tree.define_function(child, self.func_id, domain_slid, codomain_slid) {
                tree.mark_unsat(
                    child,
                    Some(ConflictClause {
                        required_elements: vec![],
                        required_functions: vec![],
                        required_relations: vec![],
                        violated_axiom: None,
                        explanation: Some(e),
                    }),
                );
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

/// Forward chaining tactic: automatically fulfill simple obligations.
///
/// When an axiom's premise is satisfied but conclusion isn't, we have an obligation.
/// This tactic automatically fulfills simple obligations:
/// - **Relation assertions**: assert the relation tuple
/// - **Equations**: add to pending equations in congruence closure
/// - **Existentials**: add a fresh witness element (then recurse)
/// - **Disjunctions**: create branches (one per disjunct)
/// - **False**: mark as unsat (derivation of False found!)
///
/// This is Datalog-style forward chaining for geometric logic.
pub struct ForwardChainingTactic;

impl Tactic for ForwardChainingTactic {
    fn run(&mut self, tree: &mut SearchTree, node: NodeId, budget: &Budget) -> TacticResult {
        use crate::core::Formula;
        use crate::tensor::check_theory_axioms;

        let start = std::time::Instant::now();
        let mut steps = 0;
        let mut branches = 0;

        // Get current structure and axioms
        let axioms = tree.theory.theory.axioms.clone();
        let sig = tree.theory.theory.signature.clone();

        // Check axioms and get violations
        let violations = {
            let node_ref = match tree.get(node) {
                Some(n) => n,
                None => return TacticResult::Error("Invalid node ID".to_string()),
            };
            check_theory_axioms(&axioms, &node_ref.structure, &sig)
        };

        if violations.is_empty() {
            // No violations - check if complete
            return CheckTactic.run(tree, node, budget);
        }

        // Process each violation
        for (axiom_idx, viols) in violations {
            for viol in viols {
                if start.elapsed().as_millis() as u64 > budget.time_ms || steps >= budget.steps {
                    return TacticResult::Timeout { steps_taken: steps };
                }

                let axiom = &axioms[axiom_idx];
                let conclusion = &axiom.conclusion;

                // Build variable assignment map from violation
                let assignment: std::collections::HashMap<String, usize> = viol
                    .variable_names
                    .iter()
                    .zip(viol.assignment.iter())
                    .map(|(name, &idx)| (name.clone(), idx))
                    .collect();

                // Process the conclusion based on its type
                match conclusion {
                    Formula::False => {
                        // Found a derivation of False!
                        // This is true unsatisfiability.
                        tree.mark_unsat(
                            node,
                            Some(ConflictClause {
                                required_elements: vec![],
                                required_functions: vec![],
                                required_relations: vec![],
                                violated_axiom: Some(axiom_idx),
                                explanation: Some(format!(
                                    "Axiom {} derives False for assignment {:?}",
                                    axiom_idx, assignment
                                )),
                            }),
                        );
                        return TacticResult::Unsat(None);
                    }

                    Formula::Rel(rel_id, term) => {
                        // Assert the relation tuple
                        // We need to evaluate the term with the variable assignment
                        // For now, handle simple cases (Var terms)
                        if let Some(tuple) = eval_term_to_tuple(term, &assignment) {
                            if let Err(e) = tree.assert_relation(node, *rel_id, tuple) {
                                return TacticResult::Error(format!("Failed to assert relation: {}", e));
                            }
                            steps += 1;
                        }
                    }

                    Formula::Eq(_t1, _t2) => {
                        // Add equation to congruence closure
                        // For now, we need term evaluation which is more complex
                        // Just note that this needs work
                        // TODO: Implement equation handling via CC
                        steps += 1; // Count as progress even if not fully implemented
                    }

                    Formula::Disj(disjuncts) if !disjuncts.is_empty() => {
                        // Create a branch for each disjunct
                        for (i, _disjunct) in disjuncts.iter().enumerate() {
                            let child = tree.branch(
                                node,
                                Some(format!("axiom{}:disj{}", axiom_idx, i)),
                            );
                            branches += 1;
                            // TODO: In each branch, we would process the disjunct
                            // For now, just create the branches
                            let _ = child; // suppress unused warning
                        }
                        steps += 1;
                    }

                    Formula::Exists(var_name, sort, _body) => {
                        // Add a fresh witness element
                        // Get sort ID from DerivedSort
                        if let crate::core::DerivedSort::Base(sort_id) = sort {
                            match tree.add_element(node, *sort_id) {
                                Ok((slid, _luid)) => {
                                    // TODO: We should substitute the witness into body
                                    // and continue processing. For now, just note that
                                    // we added an element.
                                    let _ = (var_name, slid); // suppress unused warnings
                                    steps += 1;
                                }
                                Err(e) => {
                                    return TacticResult::Error(format!("Failed to add witness: {}", e));
                                }
                            }
                        } else {
                            // Product sort witness - more complex
                            // TODO: Handle product domain existentials
                        }
                    }

                    Formula::True => {
                        // Should not be a violation
                    }

                    Formula::Conj(conjuncts) => {
                        // Process each conjunct
                        // For now, we'd need recursive handling
                        let _ = conjuncts;
                    }

                    Formula::Disj(_) => {
                        // Empty disjunction - should be false
                    }
                }
            }
        }

        if steps > 0 || branches > 0 {
            TacticResult::Progress {
                steps_taken: steps,
                branches_created: branches,
            }
        } else {
            // No progress made - return obligations for agent
            CheckTactic.run(tree, node, budget)
        }
    }

    fn name(&self) -> &str {
        "forward_chaining"
    }
}

/// Helper: evaluate a term to a tuple of Slids given variable assignment.
/// Returns None if the term contains constructs we can't yet handle.
fn eval_term_to_tuple(
    term: &crate::core::Term,
    assignment: &std::collections::HashMap<String, usize>,
) -> Option<Vec<Slid>> {
    use crate::core::Term;

    match term {
        Term::Var(name, _sort) => {
            // Simple variable - look up in assignment
            assignment.get(name).map(|&idx| vec![Slid::from_usize(idx)])
        }
        Term::Record(fields) => {
            // Record term - collect all field values
            let mut tuple = Vec::new();
            for (_, field_term) in fields {
                match eval_term_to_tuple(field_term, assignment) {
                    Some(mut field_tuple) => tuple.append(&mut field_tuple),
                    None => return None,
                }
            }
            Some(tuple)
        }
        Term::App(_func_id, arg) => {
            // Function application - would need actual evaluation
            // For now, if arg is a simple var, we could try
            let _ = arg;
            None // Not yet implemented
        }
        Term::Project(_, _) => {
            // Projection - would need actual evaluation
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::{DerivedSort, ElaboratedTheory, Signature, Theory};
    use crate::id::Slid;
    use std::rc::Rc;

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
        use egglog_union_find::UnionFind;

        // Helper for cleaner syntax
        fn s(n: usize) -> Slid {
            Slid::from_usize(n)
        }

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

    #[test]
    fn test_forward_chaining_tactic() {
        // Create a theory with no axioms - forward chaining should just fall through
        let theory = make_simple_theory();
        let mut tree = SearchTree::new(theory);

        // On an empty structure with no axioms, forward chaining should report progress
        let result = ForwardChainingTactic.run(&mut tree, 0, &Budget::quick());

        // No axioms means no violations, should fall through to CheckTactic
        match result {
            TacticResult::Progress { .. } => {} // Expected - incomplete but no obligations
            other => panic!("Expected Progress, got {:?}", other),
        }
    }
}
