//! Chase algorithm for computing derived relations.
//!
//! The chase takes a structure and a set of axioms (sequents) and repeatedly
//! applies the axioms until a fixpoint is reached.
//!
//! # Axiom Structure
//!
//! Axioms are sequents of the form `premise ⊢ conclusion` where:
//! - **premise** (body): conditions that must hold
//! - **conclusion** (head): what to add when conditions hold
//!
//! # Supported Axioms
//!
//! Currently supports Horn clauses (no disjunctions/existentials in head):
//! - `R(x,y), S(y,z) ⊢ T(x,z)` — add to relation
//! - `R(x,y), f(x)=a ⊢ g(y)=b` — function extension
//!
//! Existential support (creating new elements) is TODO.
//!
//! # Algorithm
//!
//! ```text
//! while changed:
//!     for each axiom (premise ⊢ conclusion):
//!         matches = query(premise)  // using RelAlgIR
//!         for each binding in matches:
//!             changed |= fire(conclusion, binding)
//! ```

use std::collections::HashMap;

use crate::core::{Context, DerivedSort, ElaboratedTheory, Formula, RelId, RelationStorage, Sequent, Signature, Structure, Term};
use crate::id::{NumericId, Slid};
use crate::universe::Universe;
use crate::query::backend::{QueryOp, Predicate};

/// Error type for chase operations
#[derive(Debug, Clone)]
pub enum ChaseError {
    /// Unsupported formula in premise
    UnsupportedPremise(String),
    /// Unsupported formula in conclusion
    UnsupportedConclusion(String),
    /// Variable not bound
    UnboundVariable(String),
    /// Sort mismatch
    SortMismatch(String),
    /// Query execution failed
    QueryFailed(String),
}

impl std::fmt::Display for ChaseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnsupportedPremise(s) => write!(f, "Unsupported premise: {s}"),
            Self::UnsupportedConclusion(s) => write!(f, "Unsupported conclusion: {s}"),
            Self::UnboundVariable(s) => write!(f, "Unbound variable: {s}"),
            Self::SortMismatch(s) => write!(f, "Sort mismatch: {s}"),
            Self::QueryFailed(s) => write!(f, "Query failed: {s}"),
        }
    }
}

impl std::error::Error for ChaseError {}

/// A compiled chase rule
#[derive(Debug, Clone)]
pub struct ChaseRule {
    /// Human-readable name for debugging
    pub name: String,
    /// Variable names and their column indices in match results
    pub var_indices: HashMap<String, usize>,
    /// The query to find matches (compiled from premise)
    pub query: QueryOp,
    /// What to do when the rule fires
    pub head: ChaseHead,
}

/// What to do when a chase rule fires
#[derive(Debug, Clone)]
pub enum ChaseHead {
    /// Add a tuple to a relation: R(term_1, ..., term_n)
    AddRelation {
        rel_id: RelId,
        /// Column indices for the relation tuple
        arg_indices: Vec<usize>,
    },
    /// Set a function value: f(arg) = result
    SetFunction {
        func_idx: usize,
        arg_col: usize,
        result_col: usize,
    },
    /// Create a new element (existential)
    CreateElement {
        sort_idx: usize,
        /// Bindings for functions on the new element
        function_bindings: Vec<(usize, usize)>, // (func_idx, result_col)
    },
    /// Multiple heads (conjunction in conclusion)
    Multi(Vec<ChaseHead>),
}

/// Compile a sequent into a chase rule
pub fn compile_axiom(
    sequent: &Sequent,
    sig: &Signature,
    name: String,
) -> Result<ChaseRule, ChaseError> {
    // Build variable-to-column mapping from context
    let mut var_indices: HashMap<String, usize> = HashMap::new();
    for (idx, (var_name, _sort)) in sequent.context.vars.iter().enumerate() {
        var_indices.insert(var_name.clone(), idx);
    }

    // Compile premise to query
    let query = compile_premise(&sequent.premise, &var_indices, &sequent.context, sig)?;

    // Compile conclusion to head
    let head = compile_conclusion(&sequent.conclusion, &var_indices, sig)?;

    Ok(ChaseRule {
        name,
        var_indices,
        query,
        head,
    })
}

/// Compile a premise formula to a QueryOp
fn compile_premise(
    formula: &Formula,
    var_indices: &HashMap<String, usize>,
    context: &Context,
    sig: &Signature,
) -> Result<QueryOp, ChaseError> {
    match formula {
        Formula::True => {
            // True premise: scan all elements of first variable's sort
            if context.vars.is_empty() {
                // No variables: this is a ground check, return empty scan
                // (The rule fires once if conclusion can be added)
                Ok(QueryOp::Empty)
            } else {
                // Scan the sort of the first variable
                let (_, sort) = &context.vars[0];
                let sort_idx = resolve_sort_index(sort, sig)?;
                Ok(QueryOp::Scan { sort_idx })
            }
        }

        Formula::Rel(rel_id, _arg) => {
            // Relation: scan the relation's sort, filter by membership
            // TODO: Use _arg to extract column bindings
            let rel = &sig.relations[*rel_id];
            let sort_idx = resolve_sort_index(&rel.domain, sig)?;

            // For a relation R(x), we need to scan elements and check membership
            // This becomes: Scan(sort) filtered by R(col)
            let scan = QueryOp::Scan { sort_idx };

            // TODO: Add relation membership predicate
            // For now, just return the scan (assumes relation is total)
            Ok(scan)
        }

        Formula::Conj(formulas) => {
            // Conjunction: build a join tree
            if formulas.is_empty() {
                return compile_premise(&Formula::True, var_indices, context, sig);
            }

            let mut ops: Vec<QueryOp> = Vec::new();
            for f in formulas {
                ops.push(compile_premise(f, var_indices, context, sig)?);
            }

            // Build left-deep join tree
            let mut result = ops.remove(0);
            for op in ops {
                result = QueryOp::Join {
                    left: Box::new(result),
                    right: Box::new(op),
                    cond: crate::query::backend::JoinCond::Cross,
                };
            }

            Ok(result)
        }

        Formula::Eq(left, right) => {
            // Equality: becomes a filter predicate
            let left_col = term_to_column(left, var_indices)?;
            let right_col = term_to_column(right, var_indices)?;

            // Need a base scan first
            if context.vars.is_empty() {
                return Err(ChaseError::UnsupportedPremise(
                    "Equality without variables".to_string()
                ));
            }

            let (_, sort) = &context.vars[0];
            let sort_idx = resolve_sort_index(sort, sig)?;
            let scan = QueryOp::Scan { sort_idx };

            Ok(QueryOp::Filter {
                input: Box::new(scan),
                pred: Predicate::ColEqCol { left: left_col, right: right_col },
            })
        }

        Formula::False => {
            // False premise: never fires
            Ok(QueryOp::Empty)
        }

        Formula::Disj(_) => {
            Err(ChaseError::UnsupportedPremise(
                "Disjunction in premise not yet supported".to_string()
            ))
        }

        Formula::Exists(_, _, _) => {
            Err(ChaseError::UnsupportedPremise(
                "Existential in premise not yet supported".to_string()
            ))
        }
    }
}

/// Compile a conclusion formula to a ChaseHead
fn compile_conclusion(
    formula: &Formula,
    var_indices: &HashMap<String, usize>,
    sig: &Signature,
) -> Result<ChaseHead, ChaseError> {
    match formula {
        Formula::True => {
            // True conclusion: nothing to add
            Ok(ChaseHead::Multi(vec![]))
        }

        Formula::Rel(rel_id, arg) => {
            // Add to relation
            let arg_indices = term_to_columns(arg, var_indices)?;
            Ok(ChaseHead::AddRelation {
                rel_id: *rel_id,
                arg_indices,
            })
        }

        Formula::Conj(formulas) => {
            // Multiple things to add
            let mut heads = Vec::new();
            for f in formulas {
                let head = compile_conclusion(f, var_indices, sig)?;
                match head {
                    ChaseHead::Multi(sub) => heads.extend(sub),
                    _ => heads.push(head),
                }
            }
            Ok(ChaseHead::Multi(heads))
        }

        Formula::Eq(left, right) => {
            // Function assignment: f(x) = y
            match (left, right) {
                (Term::App(func_idx, arg), _) => {
                    let arg_col = term_to_column(arg, var_indices)?;
                    let result_col = term_to_column(right, var_indices)?;
                    Ok(ChaseHead::SetFunction {
                        func_idx: *func_idx,
                        arg_col,
                        result_col,
                    })
                }
                (_, Term::App(func_idx, arg)) => {
                    let arg_col = term_to_column(arg, var_indices)?;
                    let result_col = term_to_column(left, var_indices)?;
                    Ok(ChaseHead::SetFunction {
                        func_idx: *func_idx,
                        arg_col,
                        result_col,
                    })
                }
                _ => {
                    Err(ChaseError::UnsupportedConclusion(
                        "Equality must have a function application".to_string()
                    ))
                }
            }
        }

        Formula::Exists(var_name, sort, body) => {
            // Create new element
            let sort_idx = resolve_sort_index(sort, sig)?;

            // Parse body for function bindings
            // e.g., ∃x:S. f(x) = y becomes CreateElement with f bound to y's column
            let mut function_bindings = Vec::new();
            extract_function_bindings(body, var_name, var_indices, &mut function_bindings)?;

            Ok(ChaseHead::CreateElement {
                sort_idx,
                function_bindings,
            })
        }

        Formula::False => {
            Err(ChaseError::UnsupportedConclusion(
                "False in conclusion (contradiction)".to_string()
            ))
        }

        Formula::Disj(_) => {
            Err(ChaseError::UnsupportedConclusion(
                "Disjunction in conclusion requires branching chase".to_string()
            ))
        }
    }
}

/// Extract function bindings from an existential body
fn extract_function_bindings(
    formula: &Formula,
    new_var: &str,
    var_indices: &HashMap<String, usize>,
    bindings: &mut Vec<(usize, usize)>,
) -> Result<(), ChaseError> {
    match formula {
        Formula::Eq(left, right) => {
            match (left, right) {
                (Term::App(func_idx, arg), result) if is_var(arg, new_var) => {
                    let result_col = term_to_column(result, var_indices)?;
                    bindings.push((*func_idx, result_col));
                }
                (result, Term::App(func_idx, arg)) if is_var(arg, new_var) => {
                    let result_col = term_to_column(result, var_indices)?;
                    bindings.push((*func_idx, result_col));
                }
                _ => {}
            }
            Ok(())
        }
        Formula::Conj(fs) => {
            for f in fs {
                extract_function_bindings(f, new_var, var_indices, bindings)?;
            }
            Ok(())
        }
        _ => Ok(()),
    }
}

/// Check if a term is a specific variable
fn is_var(term: &Term, var_name: &str) -> bool {
    matches!(term, Term::Var(n, _) if n == var_name)
}

/// Convert a term to a column index
fn term_to_column(term: &Term, var_indices: &HashMap<String, usize>) -> Result<usize, ChaseError> {
    match term {
        Term::Var(name, _) => {
            var_indices.get(name).copied()
                .ok_or_else(|| ChaseError::UnboundVariable(name.clone()))
        }
        _ => Err(ChaseError::UnsupportedPremise(
            format!("Complex term {:?} in column position", term)
        )),
    }
}

/// Convert a term to multiple column indices (for product terms)
fn term_to_columns(term: &Term, var_indices: &HashMap<String, usize>) -> Result<Vec<usize>, ChaseError> {
    match term {
        Term::Var(name, _) => {
            let idx = var_indices.get(name).copied()
                .ok_or_else(|| ChaseError::UnboundVariable(name.clone()))?;
            Ok(vec![idx])
        }
        Term::Record(fields) => {
            let mut indices = Vec::new();
            for (_, t) in fields {
                indices.extend(term_to_columns(t, var_indices)?);
            }
            Ok(indices)
        }
        _ => Err(ChaseError::UnsupportedPremise(
            format!("Complex term {:?} in relation argument", term)
        )),
    }
}

/// Resolve a DerivedSort to a sort index
fn resolve_sort_index(sort: &DerivedSort, _sig: &Signature) -> Result<usize, ChaseError> {
    match sort {
        DerivedSort::Base(idx) => Ok(*idx),
        DerivedSort::Product(_) => {
            Err(ChaseError::SortMismatch("Product sorts not yet supported".to_string()))
        }
    }
}

/// Execute one step of the chase
pub fn chase_step(
    rules: &[ChaseRule],
    structure: &mut Structure,
    universe: &mut Universe,
    sig: &Signature,
) -> Result<bool, ChaseError> {
    let mut changed = false;

    for rule in rules {
        // Execute the query to find matches
        let matches = crate::query::backend::execute(&rule.query, structure);

        // Fire the rule for each match
        for (tuple, _multiplicity) in matches.iter() {
            changed |= fire_head(&rule.head, tuple, structure, universe, sig)?;
        }
    }

    Ok(changed)
}

/// Fire a chase head for a given binding
#[allow(clippy::only_used_in_recursion)] // sig will be needed for future extensions
fn fire_head(
    head: &ChaseHead,
    binding: &[Slid],
    structure: &mut Structure,
    universe: &mut Universe,
    sig: &Signature,
) -> Result<bool, ChaseError> {
    match head {
        ChaseHead::AddRelation { rel_id, arg_indices } => {
            // Build the tuple from binding
            let tuple: Vec<Slid> = arg_indices.iter()
                .map(|&idx| binding.get(idx).copied())
                .collect::<Option<Vec<_>>>()
                .ok_or_else(|| ChaseError::UnboundVariable("column index out of bounds".to_string()))?;

            // Check if already present
            let rel = structure.relations.get(*rel_id)
                .ok_or_else(|| ChaseError::QueryFailed(format!("Relation {} not found", *rel_id)))?;

            if rel.contains(&tuple) {
                return Ok(false);
            }

            // Add the tuple
            structure.relations.get_mut(*rel_id)
                .ok_or_else(|| ChaseError::QueryFailed(format!("Relation {} not found", *rel_id)))?
                .insert(tuple);

            Ok(true)
        }

        ChaseHead::SetFunction { func_idx, arg_col, result_col } => {
            let arg = binding.get(*arg_col).copied()
                .ok_or_else(|| ChaseError::UnboundVariable("arg column out of bounds".to_string()))?;
            let result = binding.get(*result_col).copied()
                .ok_or_else(|| ChaseError::UnboundVariable("result column out of bounds".to_string()))?;

            // Check if already set
            let func = structure.functions.get(*func_idx)
                .ok_or_else(|| ChaseError::QueryFailed(format!("Function {} not found", func_idx)))?;

            let local_idx = structure.sort_local_id(arg).index();
            if let Some(existing) = crate::id::get_slid(func.get_local(local_idx)) {
                if existing == result {
                    return Ok(false);
                }
                // Function already has a different value - this is a conflict
                return Err(ChaseError::QueryFailed(
                    format!("Function {} already defined at {:?}", func_idx, arg)
                ));
            }

            // Set the function value
            structure.define_function(*func_idx, arg, result)
                .map_err(ChaseError::QueryFailed)?;
            Ok(true)
        }

        ChaseHead::CreateElement { sort_idx, function_bindings } => {
            // Create a new element
            let (elem, _luid) = structure.add_element(universe, *sort_idx);

            // Set function values
            for &(func_idx, result_col) in function_bindings {
                let result = binding.get(result_col).copied()
                    .ok_or_else(|| ChaseError::UnboundVariable("result column out of bounds".to_string()))?;
                structure.define_function(func_idx, elem, result)
                    .map_err(ChaseError::QueryFailed)?;
            }

            Ok(true)
        }

        ChaseHead::Multi(heads) => {
            let mut changed = false;
            for h in heads {
                changed |= fire_head(h, binding, structure, universe, sig)?;
            }
            Ok(changed)
        }
    }
}

/// Run the chase to fixpoint
pub fn chase_fixpoint(
    rules: &[ChaseRule],
    structure: &mut Structure,
    universe: &mut Universe,
    sig: &Signature,
    max_iterations: usize,
) -> Result<usize, ChaseError> {
    let mut iterations = 0;

    loop {
        if iterations >= max_iterations {
            return Err(ChaseError::QueryFailed(
                format!("Chase did not converge after {} iterations", max_iterations)
            ));
        }

        let changed = chase_step(rules, structure, universe, sig)?;
        iterations += 1;

        if !changed {
            break;
        }
    }

    Ok(iterations)
}

/// Compile all axioms in a theory to chase rules
pub fn compile_theory_axioms(theory: &ElaboratedTheory) -> Result<Vec<ChaseRule>, ChaseError> {
    let mut rules = Vec::new();

    for (idx, axiom) in theory.theory.axioms.iter().enumerate() {
        let name = format!("axiom_{}", idx);
        let rule = compile_axiom(axiom, &theory.theory.signature, name)?;
        rules.push(rule);
    }

    Ok(rules)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_chase_rule_compilation() {
        // This is a placeholder - we'll add real tests once we have test fixtures
    }
}
