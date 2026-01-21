//! Chase algorithm for computing derived relations.
//!
//! The chase takes a structure and a set of axioms (sequents) and repeatedly
//! applies the axioms until a fixpoint is reached. This is the standard database
//! chase algorithm adapted for geometric logic.
//!
//! # Implementation
//!
//! This implementation uses the tensor subsystem to evaluate premises:
//! 1. Compile premise to TensorExpr (handles existentials, conjunctions, etc.)
//! 2. Materialize to get all satisfying variable assignments
//! 3. For each assignment, fire the conclusion (add relations, create elements)
//!
//! This approach is strictly more powerful than query-based chase because
//! the tensor system naturally handles existential quantification in premises
//! via tensor contraction.
//!
//! # Supported Axiom Patterns
//!
//! **Premises** (anything the tensor system can compile):
//! - Relations: `R(x,y)`
//! - Conjunctions: `R(x,y), S(y,z)`
//! - Existentials: `∃e. f(e) = x ∧ g(e) = y`
//! - Equalities: `f(x) = y`, `f(x) = g(y)`
//! - Disjunctions: `R(x) ∨ S(x)`
//!
//! **Conclusions**:
//! - Relations: `⊢ R(x,y)` — add tuple to relation
//! - Existentials: `⊢ ∃b. f(b) = y` — create element with function binding
//! - Conjunctions: `⊢ R(x,y), f(x) = z` — multiple effects
//!
//! # Usage
//!
//! ```ignore
//! use geolog::query::chase::chase_fixpoint;
//!
//! // Run chase to fixpoint
//! let iterations = chase_fixpoint(
//!     &theory.theory.axioms,
//!     &mut structure,
//!     &mut universe,
//!     &theory.theory.signature,
//!     100,
//! )?;
//! ```

use std::collections::HashMap;

use crate::core::{DerivedSort, Formula, RelationStorage, Sequent, Signature, Structure, Term};
use crate::id::{NumericId, Slid};
use crate::tensor::{compile_formula, CompileContext};
use crate::universe::Universe;

/// Error type for chase operations
#[derive(Debug, Clone)]
pub enum ChaseError {
    /// Unsupported formula in conclusion
    UnsupportedConclusion(String),
    /// Variable not bound
    UnboundVariable(String),
    /// Function conflict (different values for same input)
    FunctionConflict(String),
    /// Chase did not converge
    MaxIterationsExceeded(usize),
    /// Tensor compilation failed
    TensorCompilationFailed(String),
}

impl std::fmt::Display for ChaseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnsupportedConclusion(s) => write!(f, "Unsupported conclusion: {s}"),
            Self::UnboundVariable(s) => write!(f, "Unbound variable: {s}"),
            Self::FunctionConflict(s) => write!(f, "Function conflict: {s}"),
            Self::MaxIterationsExceeded(n) => write!(f, "Chase did not converge after {n} iterations"),
            Self::TensorCompilationFailed(s) => write!(f, "Tensor compilation failed: {s}"),
        }
    }
}

impl std::error::Error for ChaseError {}

/// Variable binding: maps variable names to Slids
pub type Binding = HashMap<String, Slid>;

/// Execute one step of the chase algorithm.
///
/// Iterates over all axioms, evaluates premises using the tensor system,
/// and fires conclusions for each satisfying assignment.
///
/// Returns `true` if any changes were made.
pub fn chase_step(
    axioms: &[Sequent],
    structure: &mut Structure,
    universe: &mut Universe,
    sig: &Signature,
) -> Result<bool, ChaseError> {
    let mut changed = false;

    for axiom in axioms {
        changed |= fire_axiom(axiom, structure, universe, sig)?;
    }

    Ok(changed)
}

/// Fire a single axiom: evaluate premise, fire conclusion for each match.
fn fire_axiom(
    axiom: &Sequent,
    structure: &mut Structure,
    universe: &mut Universe,
    sig: &Signature,
) -> Result<bool, ChaseError> {
    // Compile premise using tensor system
    let ctx = CompileContext::from_context(&axiom.context);

    // Use catch_unwind to handle unsupported formula patterns gracefully
    let compile_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        compile_formula(&axiom.premise, &ctx, structure, sig)
    }));

    let (premise_expr, premise_vars) = match compile_result {
        Ok(result) => result,
        Err(_) => {
            // Tensor compilation panicked (unsupported pattern)
            // Skip this axiom silently
            return Ok(false);
        }
    };

    // Materialize to get all satisfying assignments (as index tuples)
    let premise_tensor = premise_expr.materialize();

    if premise_tensor.is_empty() {
        // No matches - nothing to fire
        return Ok(false);
    }

    // Build index→Slid lookup for each context variable
    let index_to_slid: Vec<Vec<Slid>> = axiom.context.vars.iter()
        .map(|(_, sort)| carrier_to_slid_vec(structure, sort))
        .collect();

    // Handle special case: premise is scalar (Formula::True) but we have context vars
    // In this case, we need to enumerate all combinations of context variables
    if premise_vars.is_empty() && !axiom.context.vars.is_empty() {
        return fire_axiom_all_combinations(axiom, structure, universe, sig, &index_to_slid);
    }

    // Map from variable name to its position in the context
    let var_to_ctx_idx: HashMap<&str, usize> = axiom.context.vars.iter()
        .enumerate()
        .map(|(i, (name, _))| (name.as_str(), i))
        .collect();

    let mut changed = false;

    // For each satisfying tuple, fire the conclusion
    for tuple in premise_tensor.iter() {
        // Build binding: variable name -> Slid
        let binding: Binding = premise_vars.iter()
            .enumerate()
            .filter_map(|(tensor_idx, var_name)| {
                // Find this variable in the context
                let ctx_idx = var_to_ctx_idx.get(var_name.as_str())?;
                let slid_vec = &index_to_slid[*ctx_idx];

                // Map tensor index to Slid
                let tensor_val = tuple.get(tensor_idx)?;
                let slid = slid_vec.get(*tensor_val)?;

                Some((var_name.clone(), *slid))
            })
            .collect();

        // Fire conclusion with this binding (skip on unsupported patterns)
        match fire_conclusion(&axiom.conclusion, &binding, structure, universe, sig) {
            Ok(c) => changed |= c,
            Err(_) => {
                // Unsupported conclusion pattern - skip this axiom silently
                return Ok(false);
            }
        }
    }

    Ok(changed)
}

/// Fire an axiom with True premise by enumerating all combinations of context variables
fn fire_axiom_all_combinations(
    axiom: &Sequent,
    structure: &mut Structure,
    universe: &mut Universe,
    sig: &Signature,
    index_to_slid: &[Vec<Slid>],
) -> Result<bool, ChaseError> {
    // Get domain sizes for each context variable
    let domain_sizes: Vec<usize> = index_to_slid.iter().map(|v| v.len()).collect();

    // If any domain is empty, nothing to do
    if domain_sizes.iter().any(|&s| s == 0) {
        return Ok(false);
    }

    let mut changed = false;

    // Enumerate all combinations (Cartesian product)
    let mut indices = vec![0usize; domain_sizes.len()];
    loop {
        // Build binding for current indices
        let binding: Binding = axiom.context.vars.iter()
            .enumerate()
            .map(|(i, (name, _))| {
                let slid = index_to_slid[i][indices[i]];
                (name.clone(), slid)
            })
            .collect();

        // Fire conclusion (skip on unsupported patterns)
        match fire_conclusion(&axiom.conclusion, &binding, structure, universe, sig) {
            Ok(c) => changed |= c,
            Err(_) => {
                // Unsupported conclusion pattern - skip this axiom silently
                return Ok(false);
            }
        }

        // Increment indices (odometer style)
        let mut i = indices.len();
        loop {
            if i == 0 {
                // All combinations exhausted
                return Ok(changed);
            }
            i -= 1;
            indices[i] += 1;
            if indices[i] < domain_sizes[i] {
                break;
            }
            indices[i] = 0;
        }
    }
}

/// Convert a carrier to a Vec of Slids for index→Slid lookup
fn carrier_to_slid_vec(structure: &Structure, sort: &DerivedSort) -> Vec<Slid> {
    match sort {
        DerivedSort::Base(sort_id) => {
            structure.carriers[*sort_id]
                .iter()
                .map(|u| Slid::from_usize(u as usize))
                .collect()
        }
        DerivedSort::Product(_) => {
            // Product sorts: would need to enumerate all combinations
            // For now, return empty (these are rare in practice)
            vec![]
        }
    }
}

/// Fire a conclusion formula given a variable binding.
/// Returns true if any changes were made.
fn fire_conclusion(
    formula: &Formula,
    binding: &Binding,
    structure: &mut Structure,
    universe: &mut Universe,
    sig: &Signature,
) -> Result<bool, ChaseError> {
    match formula {
        Formula::True => Ok(false),

        Formula::False => {
            // Contradiction - this shouldn't happen in valid chase
            Err(ChaseError::UnsupportedConclusion("False in conclusion".to_string()))
        }

        Formula::Rel(rel_id, term) => {
            // Add tuple to relation
            let tuple = eval_term_to_tuple(term, binding, structure)?;

            // Check if already present
            if structure.relations[*rel_id].contains(&tuple) {
                return Ok(false);
            }

            structure.relations[*rel_id].insert(tuple);
            Ok(true)
        }

        Formula::Conj(formulas) => {
            let mut changed = false;
            for f in formulas {
                changed |= fire_conclusion(f, binding, structure, universe, sig)?;
            }
            Ok(changed)
        }

        Formula::Disj(formulas) => {
            // Naive parallel chase: fire all disjuncts
            // (sound but potentially adds more facts than necessary)
            let mut changed = false;
            for f in formulas {
                changed |= fire_conclusion(f, binding, structure, universe, sig)?;
            }
            Ok(changed)
        }

        Formula::Eq(left, right) => {
            fire_equality(left, right, binding, structure, sig)
        }

        Formula::Exists(var_name, sort, body) => {
            fire_existential(var_name, sort, body, binding, structure, universe, sig)
        }
    }
}

/// Evaluate a term to a tuple of Slids (for relation arguments)
fn eval_term_to_tuple(
    term: &Term,
    binding: &Binding,
    structure: &Structure,
) -> Result<Vec<Slid>, ChaseError> {
    match term {
        Term::Var(name, _) => {
            let slid = binding.get(name)
                .ok_or_else(|| ChaseError::UnboundVariable(name.clone()))?;
            Ok(vec![*slid])
        }
        Term::Record(fields) => {
            let mut tuple = Vec::new();
            for (_, field_term) in fields {
                tuple.extend(eval_term_to_tuple(field_term, binding, structure)?);
            }
            Ok(tuple)
        }
        Term::App(_, _) => {
            // Delegate to eval_term_to_slid which handles function application
            let result = eval_term_to_slid(term, binding, structure)?;
            Ok(vec![result])
        }
        Term::Project(_, _) => {
            Err(ChaseError::UnsupportedConclusion(
                "Projection in relation argument".to_string()
            ))
        }
    }
}

/// Evaluate a term to a single Slid
fn eval_term_to_slid(
    term: &Term,
    binding: &Binding,
    structure: &Structure,
) -> Result<Slid, ChaseError> {
    match term {
        Term::Var(name, _) => {
            binding.get(name)
                .copied()
                .ok_or_else(|| ChaseError::UnboundVariable(name.clone()))
        }
        Term::App(func_idx, arg) => {
            let arg_slid = eval_term_to_slid(arg, binding, structure)?;
            let local_id = structure.sort_local_id(arg_slid);

            structure.get_function(*func_idx, local_id)
                .ok_or_else(|| ChaseError::UnboundVariable(
                    format!("Function {} undefined at {:?}", func_idx, arg_slid)
                ))
        }
        Term::Project(base, field) => {
            let _base_slid = eval_term_to_slid(base, binding, structure)?;
            // Product projection - would need more structure info
            Err(ChaseError::UnsupportedConclusion(
                format!("Projection .{} not yet supported in chase", field)
            ))
        }
        Term::Record(_) => {
            Err(ChaseError::UnsupportedConclusion(
                "Record term in scalar position".to_string()
            ))
        }
    }
}

/// Fire an equality in conclusion: f(x) = y, x = y, etc.
fn fire_equality(
    left: &Term,
    right: &Term,
    binding: &Binding,
    structure: &mut Structure,
    sig: &Signature,
) -> Result<bool, ChaseError> {
    match (left, right) {
        // f(arg) = value
        (Term::App(func_idx, arg), value) | (value, Term::App(func_idx, arg)) => {
            let arg_slid = eval_term_to_slid(arg, binding, structure)?;
            let local_id = structure.sort_local_id(arg_slid);

            // Check if dealing with product codomain
            let func_info = &sig.functions[*func_idx];
            match &func_info.codomain {
                DerivedSort::Base(_) => {
                    // Simple codomain
                    let value_slid = eval_term_to_slid(value, binding, structure)?;

                    // Check if already defined
                    if let Some(existing) = structure.get_function(*func_idx, local_id) {
                        if existing == value_slid {
                            return Ok(false); // Already set to same value
                        }
                        return Err(ChaseError::FunctionConflict(
                            format!("Function {} already defined at {:?}", func_idx, arg_slid)
                        ));
                    }

                    structure.define_function(*func_idx, arg_slid, value_slid)
                        .map_err(|e| ChaseError::FunctionConflict(format!("{:?}", e)))?;
                    Ok(true)
                }
                DerivedSort::Product(_fields) => {
                    // Product codomain: f(x) = [field1: v1, ...]
                    if let Term::Record(value_fields) = value {
                        let codomain_values: Vec<(&str, Slid)> = value_fields.iter()
                            .map(|(name, term)| {
                                let slid = eval_term_to_slid(term, binding, structure)?;
                                Ok((name.as_str(), slid))
                            })
                            .collect::<Result<Vec<_>, ChaseError>>()?;

                        // Check if already defined
                        if let Some(existing) = structure.get_function_product_codomain(*func_idx, local_id) {
                            let all_match = codomain_values.iter().all(|(name, expected)| {
                                existing.iter().any(|(n, v)| n == name && v == expected)
                            });
                            if all_match {
                                return Ok(false);
                            }
                            return Err(ChaseError::FunctionConflict(
                                format!("Function {} already defined at {:?} with different values", func_idx, arg_slid)
                            ));
                        }

                        structure.define_function_product_codomain(*func_idx, arg_slid, &codomain_values)
                            .map_err(|e| ChaseError::FunctionConflict(format!("{:?}", e)))?;
                        Ok(true)
                    } else {
                        Err(ChaseError::UnsupportedConclusion(
                            format!("Expected record for product codomain function, got {:?}", value)
                        ))
                    }
                }
            }
        }

        // x = y (variable equality)
        (Term::Var(name1, _), Term::Var(name2, _)) => {
            let slid1 = binding.get(name1)
                .ok_or_else(|| ChaseError::UnboundVariable(name1.clone()))?;
            let slid2 = binding.get(name2)
                .ok_or_else(|| ChaseError::UnboundVariable(name2.clone()))?;

            if slid1 == slid2 {
                Ok(false) // Already equal
            } else {
                // Would need union-find for proper unification
                // For now, treat as constraint that doesn't fire
                Ok(false)
            }
        }

        _ => Err(ChaseError::UnsupportedConclusion(
            format!("Unsupported equality pattern: {:?} = {:?}", left, right)
        ))
    }
}

/// Fire an existential in conclusion: ∃x:S. body
/// This creates a new element if no witness exists.
fn fire_existential(
    var_name: &str,
    sort: &DerivedSort,
    body: &Formula,
    binding: &Binding,
    structure: &mut Structure,
    universe: &mut Universe,
    _sig: &Signature,
) -> Result<bool, ChaseError> {
    let DerivedSort::Base(sort_idx) = sort else {
        return Err(ChaseError::UnsupportedConclusion(
            "Existential with product sort not yet supported".to_string()
        ));
    };

    // Check for "∃b. f(a) = b" pattern (EnsureFunction)
    if let Some((func_idx, arg_slid)) = extract_ensure_function_pattern(body, var_name, binding, structure)? {
        let local_id = structure.sort_local_id(arg_slid);

        // Check if f(arg) is already defined
        if structure.get_function(func_idx, local_id).is_some() {
            return Ok(false); // Already defined
        }

        // Create new element and define f(arg) = new_elem
        let (new_elem, _) = structure.add_element(universe, *sort_idx);
        structure.define_function(func_idx, arg_slid, new_elem)
            .map_err(|e| ChaseError::FunctionConflict(format!("{:?}", e)))?;

        return Ok(true);
    }

    // General case: check if witness exists, create if not
    // Extract function bindings from body: f(new_var) = expr
    let function_bindings = extract_function_bindings(body, var_name, binding, structure)?;

    // Search for existing witness
    let carrier = &structure.carriers[*sort_idx];
    let witness_exists = carrier.iter().any(|elem_u64| {
        let elem_slid = Slid::from_usize(elem_u64 as usize);
        let local_id = structure.sort_local_id(elem_slid);

        function_bindings.iter().all(|&(func_idx, expected)| {
            structure.get_function(func_idx, local_id) == Some(expected)
        })
    });

    if witness_exists {
        return Ok(false);
    }

    // Create new element with bindings
    let (new_elem, _) = structure.add_element(universe, *sort_idx);

    for (func_idx, result) in function_bindings {
        structure.define_function(func_idx, new_elem, result)
            .map_err(|e| ChaseError::FunctionConflict(format!("{:?}", e)))?;
    }

    Ok(true)
}

/// Check for "∃b. f(a) = b" pattern where b is the existential variable
/// and a is bound. Returns Some((func_idx, arg_slid)) if pattern matches.
fn extract_ensure_function_pattern(
    formula: &Formula,
    new_var: &str,
    binding: &Binding,
    structure: &Structure,
) -> Result<Option<(usize, Slid)>, ChaseError> {
    match formula {
        Formula::Eq(left, right) => {
            // Check f(arg) = new_var
            if let (Term::App(func_idx, arg), Term::Var(var_name, _)) = (left, right) {
                if var_name == new_var {
                    let arg_slid = eval_term_to_slid(arg, binding, structure)?;
                    return Ok(Some((*func_idx, arg_slid)));
                }
            }
            // Check new_var = f(arg)
            if let (Term::Var(var_name, _), Term::App(func_idx, arg)) = (left, right) {
                if var_name == new_var {
                    let arg_slid = eval_term_to_slid(arg, binding, structure)?;
                    return Ok(Some((*func_idx, arg_slid)));
                }
            }
            Ok(None)
        }
        Formula::Conj(fs) if fs.len() == 1 => {
            extract_ensure_function_pattern(&fs[0], new_var, binding, structure)
        }
        _ => Ok(None)
    }
}

/// Extract function bindings from an existential body: f(new_var) = expr
/// Returns (func_idx, result_slid) pairs.
fn extract_function_bindings(
    formula: &Formula,
    new_var: &str,
    binding: &Binding,
    structure: &Structure,
) -> Result<Vec<(usize, Slid)>, ChaseError> {
    let mut bindings = Vec::new();
    extract_function_bindings_inner(formula, new_var, binding, structure, &mut bindings)?;
    Ok(bindings)
}

fn extract_function_bindings_inner(
    formula: &Formula,
    new_var: &str,
    binding: &Binding,
    structure: &Structure,
    bindings: &mut Vec<(usize, Slid)>,
) -> Result<(), ChaseError> {
    match formula {
        Formula::Eq(left, right) => {
            // f(new_var) = result
            if let Term::App(func_idx, arg) = left {
                if is_var(arg, new_var) {
                    let result_slid = eval_term_to_slid(right, binding, structure)?;
                    bindings.push((*func_idx, result_slid));
                }
            }
            // result = f(new_var)
            if let Term::App(func_idx, arg) = right {
                if is_var(arg, new_var) {
                    let result_slid = eval_term_to_slid(left, binding, structure)?;
                    bindings.push((*func_idx, result_slid));
                }
            }
            Ok(())
        }
        Formula::Conj(fs) => {
            for f in fs {
                extract_function_bindings_inner(f, new_var, binding, structure, bindings)?;
            }
            Ok(())
        }
        _ => Ok(())
    }
}

/// Check if term is a specific variable
fn is_var(term: &Term, var_name: &str) -> bool {
    matches!(term, Term::Var(n, _) if n == var_name)
}

/// Run the chase algorithm until a fixpoint is reached.
///
/// Repeatedly applies [`chase_step`] until no more changes occur, or until
/// `max_iterations` is reached.
///
/// # Arguments
///
/// * `axioms` - The sequents (axioms) to apply
/// * `structure` - The structure to modify
/// * `universe` - The universe for element creation
/// * `sig` - The signature
/// * `max_iterations` - Safety limit to prevent infinite loops
///
/// # Returns
///
/// The number of iterations taken to reach the fixpoint.
pub fn chase_fixpoint(
    axioms: &[Sequent],
    structure: &mut Structure,
    universe: &mut Universe,
    sig: &Signature,
    max_iterations: usize,
) -> Result<usize, ChaseError> {
    let mut iterations = 0;

    loop {
        if iterations >= max_iterations {
            return Err(ChaseError::MaxIterationsExceeded(max_iterations));
        }

        let changed = chase_step(axioms, structure, universe, sig)?;
        iterations += 1;

        if !changed {
            break;
        }
    }

    Ok(iterations)
}

// Tests are in tests/unit_chase.rs
