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
                    Ok(false) => {
                        // Model is incomplete (e.g., undefined functions) but no axiom violations.
                        // Don't report progress - we need external help (function enumeration)
                        // or the model can be considered valid with partial functions.
                        TacticResult::Progress {
                            steps_taken: 0,
                            branches_created: 0,
                        }
                    }
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

                    Formula::Disj(disjuncts) if !disjuncts.is_empty() => {
                        // Create a branch for each disjunct and process in that branch
                        for (i, disjunct) in disjuncts.iter().enumerate() {
                            let child = tree.branch(
                                node,
                                Some(format!("axiom{}:disj{}", axiom_idx, i)),
                            );
                            branches += 1;
                            // Process the disjunct in the child branch
                            let mut processor = FormulaProcessor::new(
                                tree,
                                child,
                                assignment.clone(),
                                axiom_idx,
                            );
                            if let Err(e) = processor.process(disjunct) {
                                return TacticResult::Error(e);
                            }
                            steps += processor.steps;
                        }
                    }

                    Formula::Disj(_) => {
                        // Empty disjunction - should be handled as False
                        // For now, skip (shouldn't happen in well-formed theories)
                    }

                    // For Rel, Eq, Exists, Conj, True - use recursive processor
                    other_formula => {
                        let mut processor = FormulaProcessor::new(
                            tree,
                            node,
                            assignment.clone(),
                            axiom_idx,
                        );
                        if let Err(e) = processor.process(other_formula) {
                            return TacticResult::Error(e);
                        }
                        steps += processor.steps;
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

/// Equation propagation tactic: process pending equations in the congruence closure.
///
/// This tactic:
/// 1. Pops pending equations from the CC queue
/// 2. Merges the equivalence classes
/// 3. Checks for function conflicts (f(a) = x and f(b) = y where a = b implies x = y)
/// 4. Adds any new equations discovered via congruence
///
/// This is a simplified version that doesn't do full congruence closure,
/// but handles the basic case of merging and detecting function conflicts.
pub struct PropagateEquationsTactic;

impl Tactic for PropagateEquationsTactic {
    fn run(&mut self, tree: &mut SearchTree, node: NodeId, budget: &Budget) -> TacticResult {
        let start = std::time::Instant::now();
        let mut steps = 0;
        #[allow(unused_variables)]
        let mut new_equations = 0;

        // Process pending equations
        loop {
            if start.elapsed().as_millis() as u64 > budget.time_ms || steps >= budget.steps {
                return TacticResult::Timeout { steps_taken: steps };
            }

            // Pop next equation
            let eq = {
                let node = match tree.get_mut(node) {
                    Some(n) => n,
                    None => return TacticResult::Error("Invalid node ID".to_string()),
                };
                node.cc.pop_pending()
            };

            let eq = match eq {
                Some(e) => e,
                None => break, // No more pending equations
            };

            // Merge the equivalence classes
            let merged = {
                let node = tree.get_mut(node).unwrap();
                node.cc.merge(eq.lhs, eq.rhs)
            };

            if merged {
                steps += 1;

                // Check for function conflicts
                // For each function f, if f(a) and f(b) are both defined and a = b,
                // then we need f(a) = f(b) (congruence)
                let sig = tree.signature().clone();
                let conflicts: Vec<(Slid, Slid, usize)> = {
                    let node = tree.get(node).unwrap();
                    let mut conflicts = Vec::new();

                    for func_id in 0..sig.functions.len() {
                        if func_id >= node.structure.functions.len() {
                            continue;
                        }

                        // Get values for eq.lhs and eq.rhs
                        let lhs_sort_slid = node.structure.sort_local_id(eq.lhs);
                        let rhs_sort_slid = node.structure.sort_local_id(eq.rhs);

                        let lhs_val = node.structure.get_function(func_id, lhs_sort_slid);
                        let rhs_val = node.structure.get_function(func_id, rhs_sort_slid);

                        if let (Some(lv), Some(rv)) = (lhs_val, rhs_val)
                            && lv != rv
                        {
                            // Function conflict: f(a) = lv and f(b) = rv, but a = b
                            // Add equation lv = rv with func_id for debugging
                            conflicts.push((lv, rv, func_id));
                        }
                    }
                    conflicts
                };

                // Add conflict-induced equations
                for (lv, rv, func_id) in conflicts {
                    tree.add_pending_equation(
                        node,
                        lv,
                        rv,
                        super::types::EquationReason::Congruence { func_id },
                    );
                    new_equations += 1;
                }
            }
        }

        if steps > 0 {
            TacticResult::Progress {
                steps_taken: steps,
                branches_created: 0,
            }
        } else {
            // No pending equations - fall through to check
            CheckTactic.run(tree, node, budget)
        }
    }

    fn name(&self) -> &str {
        "propagate_equations"
    }
}

/// Automatic solving tactic: runs forward chaining and equation propagation to fixpoint.
///
/// This composite tactic:
/// 1. Runs ForwardChainingTactic until no progress
/// 2. Runs PropagateEquationsTactic until no progress
/// 3. Repeats until fixpoint (no more progress from either)
///
/// This is the main "auto-solve" tactic for geometric logic.
pub struct AutoTactic;

impl Tactic for AutoTactic {
    fn run(&mut self, tree: &mut SearchTree, node: NodeId, budget: &Budget) -> TacticResult {
        let start = std::time::Instant::now();
        let mut total_steps = 0;
        let mut total_branches = 0;
        let mut iterations = 0;

        loop {
            if start.elapsed().as_millis() as u64 > budget.time_ms {
                return TacticResult::Timeout { steps_taken: total_steps };
            }

            iterations += 1;
            let mut made_progress = false;

            // Run forward chaining
            let remaining_budget = Budget {
                time_ms: budget.time_ms.saturating_sub(start.elapsed().as_millis() as u64),
                steps: budget.steps.saturating_sub(total_steps),
            };

            match ForwardChainingTactic.run(tree, node, &remaining_budget) {
                TacticResult::Progress { steps_taken, branches_created } => {
                    total_steps += steps_taken;
                    total_branches += branches_created;
                    if steps_taken > 0 || branches_created > 0 {
                        made_progress = true;
                    }
                }
                TacticResult::Solved => return TacticResult::Solved,
                TacticResult::Unsat(clause) => return TacticResult::Unsat(clause),
                TacticResult::Timeout { steps_taken } => {
                    total_steps += steps_taken;
                    return TacticResult::Timeout { steps_taken: total_steps };
                }
                TacticResult::Error(e) => return TacticResult::Error(e),
                TacticResult::HasObligations(_) => {
                    // Has obligations but made no progress - continue to propagation
                }
            }

            // Run equation propagation
            let remaining_budget = Budget {
                time_ms: budget.time_ms.saturating_sub(start.elapsed().as_millis() as u64),
                steps: budget.steps.saturating_sub(total_steps),
            };

            match PropagateEquationsTactic.run(tree, node, &remaining_budget) {
                TacticResult::Progress { steps_taken, .. } => {
                    total_steps += steps_taken;
                    if steps_taken > 0 {
                        made_progress = true;
                    }
                }
                TacticResult::Solved => return TacticResult::Solved,
                TacticResult::Unsat(clause) => return TacticResult::Unsat(clause),
                TacticResult::Timeout { steps_taken } => {
                    total_steps += steps_taken;
                    return TacticResult::Timeout { steps_taken: total_steps };
                }
                TacticResult::Error(e) => return TacticResult::Error(e),
                TacticResult::HasObligations(_) => {
                    // Has obligations but made no progress - continue to next iteration
                }
            }

            // Check for fixpoint
            if !made_progress {
                break;
            }

            // Safety limit on iterations
            if iterations > 1000 {
                return TacticResult::Error("AutoTactic exceeded iteration limit".to_string());
            }
        }

        TacticResult::Progress {
            steps_taken: total_steps,
            branches_created: total_branches,
        }
    }

    fn name(&self) -> &str {
        "auto"
    }
}

/// Recursive formula processor for forward chaining.
///
/// Processes a positive geometric formula by:
/// - Asserting relation tuples
/// - Adding pending equations
/// - Adding witness elements for existentials (and recursively processing bodies)
/// - Processing conjuncts
/// - NOT handling disjunctions (those need branching at a higher level)
struct FormulaProcessor<'a> {
    tree: &'a mut SearchTree,
    node: NodeId,
    assignment: std::collections::HashMap<String, usize>,
    axiom_idx: usize,
    steps: usize,
}

impl<'a> FormulaProcessor<'a> {
    fn new(
        tree: &'a mut SearchTree,
        node: NodeId,
        assignment: std::collections::HashMap<String, usize>,
        axiom_idx: usize,
    ) -> Self {
        Self {
            tree,
            node,
            assignment,
            axiom_idx,
            steps: 0,
        }
    }

    /// Process a formula, accumulating steps. Returns Err on failure.
    fn process(&mut self, formula: &crate::core::Formula) -> Result<(), String> {
        use crate::core::Formula;

        match formula {
            Formula::True => {
                // Nothing to do
                Ok(())
            }

            Formula::Rel(rel_id, term) => {
                // Assert relation tuple
                let tuple = self.tree.get(self.node).and_then(|n| {
                    eval_term_to_tuple(term, &self.assignment, &n.structure)
                });
                if let Some(tuple) = tuple {
                    self.tree.assert_relation(self.node, *rel_id, tuple)?;
                    self.steps += 1;
                }
                Ok(())
            }

            Formula::Eq(t1, t2) => {
                // Add equation to congruence closure if not already equal
                let eq_slids = self.tree.get(self.node).and_then(|n| {
                    let lhs = eval_term_to_slid(t1, &self.assignment, &n.structure)?;
                    let rhs = eval_term_to_slid(t2, &self.assignment, &n.structure)?;
                    Some((lhs, rhs))
                });
                if let Some((lhs, rhs)) = eq_slids {
                    let search_node = self.tree.get_mut(self.node).ok_or("Invalid node")?;
                    if !search_node.cc.are_equal(lhs, rhs) {
                        search_node.cc.add_equation(
                            lhs,
                            rhs,
                            super::types::EquationReason::AxiomConsequent {
                                axiom_idx: self.axiom_idx,
                            },
                        );
                        self.steps += 1;
                    }
                }
                Ok(())
            }

            Formula::Conj(conjuncts) => {
                // Process each conjunct recursively
                for conjunct in conjuncts {
                    self.process(conjunct)?;
                }
                Ok(())
            }

            Formula::Exists(var_name, sort, body) => {
                // Add fresh witness and recursively process body
                if let crate::core::DerivedSort::Base(sort_id) = sort {
                    match self.tree.add_element(self.node, *sort_id) {
                        Ok((slid, _luid)) => {
                            // Add witness to assignment
                            self.assignment.insert(var_name.clone(), slid.index());
                            self.steps += 1;
                            // Recursively process body with updated assignment
                            self.process(body)
                        }
                        Err(e) => Err(format!("Failed to add witness: {}", e)),
                    }
                } else {
                    // Product sort witness - not yet implemented
                    Ok(())
                }
            }

            Formula::False | Formula::Disj(_) => {
                // These should be handled at a higher level
                // False triggers unsat, Disj triggers branching
                Ok(())
            }
        }
    }
}

/// Helper: evaluate a term to a single Slid given variable assignment and structure.
/// Returns None if the term contains constructs we can't handle or if evaluation fails.
fn eval_term_to_slid(
    term: &crate::core::Term,
    assignment: &std::collections::HashMap<String, usize>,
    structure: &crate::core::Structure,
) -> Option<Slid> {
    use crate::core::Term;

    match term {
        Term::Var(name, _sort) => {
            // Simple variable - look up in assignment
            assignment.get(name).map(|&idx| Slid::from_usize(idx))
        }
        Term::App(func_id, arg) => {
            // Function application: evaluate arg, then look up function value
            let arg_slid = eval_term_to_slid(arg, assignment, structure)?;
            let sort_slid = structure.sort_local_id(arg_slid);
            structure.get_function(*func_id, sort_slid)
        }
        Term::Record(_fields) => {
            // Records evaluate to product elements - not a single Slid
            // Would need product element lookup
            None
        }
        Term::Project(base, field_name) => {
            // Projection: evaluate base (must be a record element), then project
            // This would require looking up the product element's components
            let _ = (base, field_name);
            None // Not yet implemented - needs product element storage
        }
    }
}

/// Helper: evaluate a term to a tuple of Slids given variable assignment.
/// Used for relation assertions where the domain may be a product.
fn eval_term_to_tuple(
    term: &crate::core::Term,
    assignment: &std::collections::HashMap<String, usize>,
    structure: &crate::core::Structure,
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
                match eval_term_to_tuple(field_term, assignment, structure) {
                    Some(mut field_tuple) => tuple.append(&mut field_tuple),
                    None => return None,
                }
            }
            Some(tuple)
        }
        Term::App(_func_id, _arg) => {
            // Function application - evaluate to single value, wrap in vec
            eval_term_to_slid(term, assignment, structure).map(|s| vec![s])
        }
        Term::Project(_, _) => {
            // Projection - would need product element storage
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

    #[test]
    fn test_forward_chaining_detects_false() {
        use crate::core::{Context, Formula, Sequent};

        // Create a theory with an axiom: True |- False
        // This means any model is immediately unsat
        let mut sig = Signature::new();
        sig.add_sort("Node".to_string());

        let axiom = Sequent {
            context: Context::new(),
            premise: Formula::True,
            conclusion: Formula::False,
        };

        let theory = Rc::new(ElaboratedTheory {
            params: vec![],
            theory: Theory {
                name: "Inconsistent".to_string(),
                signature: sig,
                axioms: vec![axiom],
            },
        });

        let mut tree = SearchTree::new(theory);

        // Forward chaining should detect the derivation of False
        let result = ForwardChainingTactic.run(&mut tree, 0, &Budget::quick());

        match result {
            TacticResult::Unsat(_) => {} // Expected - True |- False is violated
            other => panic!("Expected Unsat, got {:?}", other),
        }
    }

    #[test]
    fn test_forward_chaining_adds_equations() {
        use crate::core::{Context, Formula, Sequent, Term};

        // Create a theory with an axiom: ∀x:Node, y:Node. True |- x = y
        // (Every two nodes are equal)
        let mut sig = Signature::new();
        sig.add_sort("Node".to_string());

        let ctx = Context::new()
            .extend("x".to_string(), DerivedSort::Base(0))
            .extend("y".to_string(), DerivedSort::Base(0));

        let axiom = Sequent {
            context: ctx,
            premise: Formula::True,
            conclusion: Formula::Eq(
                Term::Var("x".to_string(), DerivedSort::Base(0)),
                Term::Var("y".to_string(), DerivedSort::Base(0)),
            ),
        };

        let theory = Rc::new(ElaboratedTheory {
            params: vec![],
            theory: Theory {
                name: "AllEqual".to_string(),
                signature: sig,
                axioms: vec![axiom],
            },
        });

        let mut tree = SearchTree::new(theory);

        // Add two elements
        let (a, _) = tree.add_element(0, 0).unwrap();
        let (b, _) = tree.add_element(0, 0).unwrap();
        assert_ne!(a, b);

        // Forward chaining should detect the equation obligation and add pending equations
        let result = ForwardChainingTactic.run(&mut tree, 0, &Budget::quick());

        match result {
            TacticResult::Progress { steps_taken, .. } => {
                assert!(steps_taken > 0, "Should have made progress");
            }
            other => panic!("Expected Progress, got {:?}", other),
        }

        // Check that pending equations were added to congruence closure
        let node = tree.get(0).unwrap();
        assert!(!node.cc.pending.is_empty(), "Should have pending equations");
    }

    #[test]
    fn test_propagate_equations_merges() {
        use crate::core::{Context, Formula, Sequent, Term};

        // Create a theory with an axiom: ∀x:Node, y:Node. True |- x = y
        let mut sig = Signature::new();
        sig.add_sort("Node".to_string());

        let ctx = Context::new()
            .extend("x".to_string(), DerivedSort::Base(0))
            .extend("y".to_string(), DerivedSort::Base(0));

        let axiom = Sequent {
            context: ctx,
            premise: Formula::True,
            conclusion: Formula::Eq(
                Term::Var("x".to_string(), DerivedSort::Base(0)),
                Term::Var("y".to_string(), DerivedSort::Base(0)),
            ),
        };

        let theory = Rc::new(ElaboratedTheory {
            params: vec![],
            theory: Theory {
                name: "AllEqual".to_string(),
                signature: sig,
                axioms: vec![axiom],
            },
        });

        let mut tree = SearchTree::new(theory);

        // Add two elements
        let (a, _) = tree.add_element(0, 0).unwrap();
        let (b, _) = tree.add_element(0, 0).unwrap();

        // First run forward chaining to add equations
        ForwardChainingTactic.run(&mut tree, 0, &Budget::quick());

        // Verify equations are pending
        assert!(!tree.get(0).unwrap().cc.pending.is_empty());

        // Run equation propagation
        let result = PropagateEquationsTactic.run(&mut tree, 0, &Budget::quick());

        match result {
            TacticResult::Progress { steps_taken, .. } => {
                assert!(steps_taken > 0, "Should have processed equations");
            }
            other => panic!("Expected Progress, got {:?}", other),
        }

        // Check that a and b are now in the same equivalence class
        let node = tree.get_mut(0).unwrap();
        assert!(node.cc.are_equal(a, b), "a and b should be equal after propagation");
    }

    #[test]
    fn test_auto_tactic() {
        use crate::core::{Context, Formula, Sequent, Term};

        // Create a theory where all elements are equal
        let mut sig = Signature::new();
        sig.add_sort("Node".to_string());

        let ctx = Context::new()
            .extend("x".to_string(), DerivedSort::Base(0))
            .extend("y".to_string(), DerivedSort::Base(0));

        let axiom = Sequent {
            context: ctx,
            premise: Formula::True,
            conclusion: Formula::Eq(
                Term::Var("x".to_string(), DerivedSort::Base(0)),
                Term::Var("y".to_string(), DerivedSort::Base(0)),
            ),
        };

        let theory = Rc::new(ElaboratedTheory {
            params: vec![],
            theory: Theory {
                name: "AllEqual".to_string(),
                signature: sig,
                axioms: vec![axiom],
            },
        });

        let mut tree = SearchTree::new(theory);

        // Add three elements
        let (a, _) = tree.add_element(0, 0).unwrap();
        let (b, _) = tree.add_element(0, 0).unwrap();
        let (c, _) = tree.add_element(0, 0).unwrap();

        // Run AutoTactic - should do forward chaining + propagation to fixpoint
        let result = AutoTactic.run(&mut tree, 0, &Budget::quick());

        match result {
            TacticResult::Progress { steps_taken, .. } => {
                assert!(steps_taken > 0, "Should have made progress");
            }
            other => panic!("Expected Progress, got {:?}", other),
        }

        // All three should be in the same equivalence class
        let node = tree.get_mut(0).unwrap();
        assert!(node.cc.are_equal(a, b), "a and b should be equal");
        assert!(node.cc.are_equal(b, c), "b and c should be equal");
        assert!(node.cc.are_equal(a, c), "a and c should be equal (transitively)");
    }

    #[test]
    fn test_existential_body_processing() {
        use crate::core::{Context, Formula, RelationStorage, Sequent, Term};

        // Create a theory with:
        // - Sort: Node
        // - Relation: R : Node -> Prop
        // - Axiom: True |- ∃x:Node. R(x)
        // This should add a witness and assert R(witness)

        let mut sig = Signature::new();
        sig.add_sort("Node".to_string());
        sig.add_relation("R".to_string(), DerivedSort::Base(0));

        let axiom = Sequent {
            context: Context::new(),
            premise: Formula::True,
            conclusion: Formula::Exists(
                "x".to_string(),
                DerivedSort::Base(0),
                Box::new(Formula::Rel(
                    0, // R
                    Term::Var("x".to_string(), DerivedSort::Base(0)),
                )),
            ),
        };

        let theory = Rc::new(ElaboratedTheory {
            params: vec![],
            theory: Theory {
                name: "ExistsR".to_string(),
                signature: sig,
                axioms: vec![axiom],
            },
        });

        let mut tree = SearchTree::new(theory);
        tree.init_relations(0, &[1]).unwrap(); // R has arity 1

        // Initially no elements
        assert_eq!(tree.get(0).unwrap().structure.carrier_size(0), 0);

        // Run forward chaining
        let result = ForwardChainingTactic.run(&mut tree, 0, &Budget::quick());

        match result {
            TacticResult::Progress { steps_taken, .. } => {
                assert!(steps_taken >= 2, "Should have added witness AND asserted R");
            }
            other => panic!("Expected Progress, got {:?}", other),
        }

        // Should now have one element (the witness)
        let node = tree.get(0).unwrap();
        assert_eq!(node.structure.carrier_size(0), 1, "Should have one witness");

        // R(witness) should be asserted
        let witness = Slid::from_usize(0);
        assert!(
            node.structure.relations[0].contains(&[witness]),
            "R(witness) should be asserted"
        );
    }

    #[test]
    fn test_nested_existential_body() {
        use crate::core::{Context, Formula, RelationStorage, Sequent, Term};

        // Create a theory with:
        // - Sort: Node
        // - Relation: E : Node × Node -> Prop
        // - Axiom: True |- ∃x:Node. ∃y:Node. E(x, y)
        // This should add two witnesses and assert E(w1, w2)

        let mut sig = Signature::new();
        sig.add_sort("Node".to_string());
        // E : Node × Node -> Prop (binary relation as product domain)
        sig.add_relation(
            "E".to_string(),
            DerivedSort::Product(vec![
                ("0".to_string(), DerivedSort::Base(0)),
                ("1".to_string(), DerivedSort::Base(0)),
            ]),
        );

        let axiom = Sequent {
            context: Context::new(),
            premise: Formula::True,
            conclusion: Formula::Exists(
                "x".to_string(),
                DerivedSort::Base(0),
                Box::new(Formula::Exists(
                    "y".to_string(),
                    DerivedSort::Base(0),
                    Box::new(Formula::Rel(
                        0, // E
                        Term::Record(vec![
                            ("0".to_string(), Term::Var("x".to_string(), DerivedSort::Base(0))),
                            ("1".to_string(), Term::Var("y".to_string(), DerivedSort::Base(0))),
                        ]),
                    )),
                )),
            ),
        };

        let theory = Rc::new(ElaboratedTheory {
            params: vec![],
            theory: Theory {
                name: "ExistsEdge".to_string(),
                signature: sig,
                axioms: vec![axiom],
            },
        });

        let mut tree = SearchTree::new(theory);
        tree.init_relations(0, &[2]).unwrap(); // E has arity 2

        // Run forward chaining
        let result = ForwardChainingTactic.run(&mut tree, 0, &Budget::quick());

        match result {
            TacticResult::Progress { steps_taken, .. } => {
                assert!(steps_taken >= 3, "Should have added 2 witnesses AND asserted E");
            }
            other => panic!("Expected Progress, got {:?}", other),
        }

        // Should have two elements
        let node = tree.get(0).unwrap();
        assert_eq!(node.structure.carrier_size(0), 2, "Should have two witnesses");

        // E(w1, w2) should be asserted
        let w1 = Slid::from_usize(0);
        let w2 = Slid::from_usize(1);
        assert!(
            node.structure.relations[0].contains(&[w1, w2]),
            "E(w1, w2) should be asserted"
        );
    }

    #[test]
    fn test_from_base_preserves_structure() {
        // Test that from_base preserves the base structure's elements and facts
        use crate::core::Structure;
        use crate::universe::Universe;

        let theory = make_simple_theory();

        // Create a base structure with some elements
        let mut universe = Universe::new();
        let mut base = Structure::new(1);
        let (elem_a, _) = base.add_element(&mut universe, 0);
        let (elem_b, _) = base.add_element(&mut universe, 0);

        // Initialize function storage and define f(a) = b
        base.init_functions(&[Some(0)]);
        base.define_function(0, elem_a, elem_b).unwrap();

        // Create search tree from base
        let tree = SearchTree::from_base(theory, base, universe);

        // The root should preserve the base structure
        let root = tree.get(0).unwrap();
        assert_eq!(root.structure.carrier_size(0), 2, "Should have 2 elements from base");
        let sort_slid_a = root.structure.sort_local_id(elem_a);
        assert_eq!(
            root.structure.get_function(0, sort_slid_a),
            Some(elem_b),
            "f(a) = b should be preserved"
        );
    }

    #[test]
    fn test_from_base_solver_can_extend() {
        // Test that the solver can extend a base structure to satisfy axioms
        use crate::core::{Context, Formula, RelationStorage, Sequent, Structure, Term};
        use crate::universe::Universe;

        // Theory: Node sort with relation R : Node -> Prop
        // Axiom: ∀x:Node. ∃y:Node. R(y)
        // (every existing element implies existence of some R-element)
        let mut sig = Signature::new();
        let node = sig.add_sort("Node".to_string());
        sig.add_relation("R".to_string(), DerivedSort::Base(node));

        let axiom = Sequent {
            context: Context {
                vars: vec![("x".to_string(), DerivedSort::Base(node))],
            },
            premise: Formula::True,
            conclusion: Formula::Exists(
                "y".to_string(),
                DerivedSort::Base(node),
                Box::new(Formula::Rel(
                    0, // R
                    Term::Var("y".to_string(), DerivedSort::Base(node)),
                )),
            ),
        };

        let theory = Rc::new(ElaboratedTheory {
            params: vec![],
            theory: Theory {
                name: "ExistsR".to_string(),
                signature: sig,
                axioms: vec![axiom],
            },
        });

        // Create base structure with one element, R not yet holding
        let mut universe = Universe::new();
        let mut base = Structure::new(1);
        let (_elem_a, _) = base.add_element(&mut universe, 0);
        base.init_relations(&[1]); // R has arity 1

        // Create search tree from base
        let mut tree = SearchTree::from_base(theory, base, universe);

        // Verify starting state: one element, R is empty
        assert_eq!(tree.get(0).unwrap().structure.carrier_size(0), 1);
        assert!(tree.get(0).unwrap().structure.relations[0].is_empty());

        // Run forward chaining - should create witness for R(y)
        let result = ForwardChainingTactic.run(&mut tree, 0, &Budget::quick());

        match result {
            TacticResult::Progress { .. } => {
                let node = tree.get(0).unwrap();
                // Should have at least one R-element now
                assert!(
                    !node.structure.relations[0].is_empty(),
                    "R should have at least one tuple after forward chaining"
                );
            }
            other => panic!("Expected Progress, got {:?}", other),
        }
    }
}
