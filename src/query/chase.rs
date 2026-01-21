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

use crate::cc::{CongruenceClosure, EquationReason};
use crate::core::{DerivedSort, Formula, RelationStorage, Sequent, Signature, Structure, Term};
use crate::id::{NumericId, Slid};
use crate::tensor::{check_sequent, CheckResult};
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
    cc: &mut CongruenceClosure,
    universe: &mut Universe,
    sig: &Signature,
) -> Result<bool, ChaseError> {
    let mut changed = false;

    for axiom in axioms {
        changed |= fire_axiom(axiom, structure, cc, universe, sig)?;
    }

    Ok(changed)
}

/// Fire a single axiom: find violations using tensor system, fire conclusion only for violations.
///
/// This is the key to correct chase semantics: we only create fresh elements when
/// the tensor system confirms there is NO existing witness for the conclusion.
fn fire_axiom(
    axiom: &Sequent,
    structure: &mut Structure,
    cc: &mut CongruenceClosure,
    universe: &mut Universe,
    sig: &Signature,
) -> Result<bool, ChaseError> {
    // Use catch_unwind to handle unsupported formula patterns gracefully
    let check_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        check_sequent(axiom, structure, sig)
    }));

    let violations = match check_result {
        Ok(CheckResult::Satisfied) => {
            // Axiom is already satisfied - nothing to fire
            return Ok(false);
        }
        Ok(CheckResult::Violated(vs)) => vs,
        Err(_) => {
            // Tensor compilation panicked (unsupported pattern)
            // Skip this axiom silently
            return Ok(false);
        }
    };

    if violations.is_empty() {
        return Ok(false);
    }

    // Build index→Slid lookup for each context variable
    let index_to_slid: Vec<Vec<Slid>> = axiom.context.vars.iter()
        .map(|(_, sort)| carrier_to_slid_vec(structure, sort))
        .collect();

    // Map from variable name to its position in the context
    let var_to_ctx_idx: HashMap<&str, usize> = axiom.context.vars.iter()
        .enumerate()
        .map(|(i, (name, _))| (name.as_str(), i))
        .collect();

    let mut changed = false;

    // Fire conclusion ONLY for violations (where premise holds but conclusion doesn't)
    for violation in violations {
        // Build binding from violation assignment
        let binding: Binding = violation.variable_names.iter()
            .enumerate()
            .filter_map(|(tensor_idx, var_name)| {
                let ctx_idx = var_to_ctx_idx.get(var_name.as_str())?;
                let slid_vec = &index_to_slid[*ctx_idx];
                let tensor_val = violation.assignment.get(tensor_idx)?;
                let slid = slid_vec.get(*tensor_val)?;
                Some((var_name.clone(), *slid))
            })
            .collect();

        // Fire conclusion with this binding
        match fire_conclusion(&axiom.conclusion, &binding, structure, cc, universe, sig) {
            Ok(c) => changed |= c,
            Err(_) => {
                // Unsupported conclusion pattern - skip this axiom silently
                return Ok(false);
            }
        }
    }

    Ok(changed)
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
    cc: &mut CongruenceClosure,
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

            // Check if already present (using canonical representatives)
            let canonical_tuple: Vec<Slid> = tuple.iter()
                .map(|&s| cc.canonical(s))
                .collect();

            // Check if a canonically-equivalent tuple exists
            let exists = structure.relations[*rel_id].iter().any(|existing| {
                if existing.len() != canonical_tuple.len() {
                    return false;
                }
                existing.iter().zip(canonical_tuple.iter()).all(|(e, c)| {
                    cc.canonical(*e) == *c
                })
            });

            if exists {
                return Ok(false);
            }

            structure.relations[*rel_id].insert(tuple);
            Ok(true)
        }

        Formula::Conj(formulas) => {
            let mut changed = false;
            for f in formulas {
                changed |= fire_conclusion(f, binding, structure, cc, universe, sig)?;
            }
            Ok(changed)
        }

        Formula::Disj(formulas) => {
            // Naive parallel chase: fire all disjuncts
            // (sound but potentially adds more facts than necessary)
            let mut changed = false;
            for f in formulas {
                changed |= fire_conclusion(f, binding, structure, cc, universe, sig)?;
            }
            Ok(changed)
        }

        Formula::Eq(left, right) => {
            fire_equality(left, right, binding, structure, cc, sig)
        }

        Formula::Exists(var_name, sort, body) => {
            fire_existential(var_name, sort, body, binding, structure, cc, universe, sig)
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
    cc: &mut CongruenceClosure,
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
                        // Check if values are equal (using CC)
                        if cc.are_equal(existing, value_slid) {
                            return Ok(false); // Already set to equivalent value
                        }
                        // Function conflict: add equation to CC instead of error
                        // (this is how we propagate equalities through functions)
                        cc.add_equation(existing, value_slid, EquationReason::FunctionConflict {
                            func_id: *func_idx,
                            domain: arg_slid,
                        });
                        return Ok(true); // Changed (added equation)
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
                                existing.iter().any(|(n, v)| n == name && cc.are_equal(*v, *expected))
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

        // x = y (variable equality) - add to congruence closure!
        (Term::Var(name1, _), Term::Var(name2, _)) => {
            let slid1 = binding.get(name1)
                .ok_or_else(|| ChaseError::UnboundVariable(name1.clone()))?;
            let slid2 = binding.get(name2)
                .ok_or_else(|| ChaseError::UnboundVariable(name2.clone()))?;

            // Check if already equal in CC
            if cc.are_equal(*slid1, *slid2) {
                Ok(false) // Already equivalent
            } else {
                // Add equation to congruence closure
                cc.add_equation(*slid1, *slid2, EquationReason::ChaseConclusion);
                Ok(true) // Changed!
            }
        }

        _ => Err(ChaseError::UnsupportedConclusion(
            format!("Unsupported equality pattern: {:?} = {:?}", left, right)
        ))
    }
}

/// Check if a formula is satisfied given a variable binding.
/// This is used for witness search in existential conclusions.
/// Uses CC for canonical relation lookups and equality checks.
fn check_formula_satisfied(
    formula: &Formula,
    binding: &Binding,
    structure: &Structure,
    cc: &mut CongruenceClosure,
) -> bool {
    match formula {
        Formula::True => true,
        Formula::False => false,

        Formula::Rel(rel_id, term) => {
            // Check if the tuple is in the relation (using canonical representatives)
            if let Ok(tuple) = eval_term_to_tuple(term, binding, structure) {
                let canonical_tuple: Vec<Slid> = tuple.iter()
                    .map(|&s| cc.canonical(s))
                    .collect();

                // Check if a canonically-equivalent tuple exists
                structure.relations[*rel_id].iter().any(|existing| {
                    if existing.len() != canonical_tuple.len() {
                        return false;
                    }
                    existing.iter().zip(canonical_tuple.iter()).all(|(e, c)| {
                        cc.canonical(*e) == *c
                    })
                })
            } else {
                false // Couldn't evaluate term (unbound variable)
            }
        }

        Formula::Conj(fs) => {
            fs.iter().all(|f| check_formula_satisfied(f, binding, structure, cc))
        }

        Formula::Disj(fs) => {
            fs.iter().any(|f| check_formula_satisfied(f, binding, structure, cc))
        }

        Formula::Eq(t1, t2) => {
            // Check if both terms evaluate to equivalent values (using CC)
            match (eval_term_to_slid(t1, binding, structure), eval_term_to_slid(t2, binding, structure)) {
                (Ok(s1), Ok(s2)) => cc.are_equal(s1, s2),
                _ => false // Couldn't evaluate (unbound variable or undefined function)
            }
        }

        Formula::Exists(inner_var, inner_sort, inner_body) => {
            // Check if any witness exists in the carrier
            let DerivedSort::Base(sort_idx) = inner_sort else {
                return false; // Product sorts not supported
            };

            structure.carriers[*sort_idx].iter().any(|w_u64| {
                let witness = Slid::from_usize(w_u64 as usize);
                let mut extended = binding.clone();
                extended.insert(inner_var.clone(), witness);
                check_formula_satisfied(inner_body, &extended, structure, cc)
            })
        }
    }
}

/// Fire an existential in conclusion: ∃x:S. body
/// This creates a new element if no witness exists.
///
/// The algorithm:
/// 1. Search the carrier of S for an existing witness w where body[x↦w] holds
/// 2. If found, do nothing (witness exists)
/// 3. If not found, create a fresh element w and fire body as conclusion with x↦w
fn fire_existential(
    var_name: &str,
    sort: &DerivedSort,
    body: &Formula,
    binding: &Binding,
    structure: &mut Structure,
    cc: &mut CongruenceClosure,
    universe: &mut Universe,
    sig: &Signature,
) -> Result<bool, ChaseError> {
    let DerivedSort::Base(sort_idx) = sort else {
        return Err(ChaseError::UnsupportedConclusion(
            "Existential with product sort not yet supported".to_string()
        ));
    };

    // Search for existing witness by checking if body is satisfied (using CC for canonical lookups)
    let carrier = &structure.carriers[*sort_idx];
    let witness_found = carrier.iter().any(|elem_u64| {
        let elem_slid = Slid::from_usize(elem_u64 as usize);
        let mut extended_binding = binding.clone();
        extended_binding.insert(var_name.to_string(), elem_slid);
        check_formula_satisfied(body, &extended_binding, structure, cc)
    });

    if witness_found {
        return Ok(false); // Witness already exists, nothing to do
    }

    // No witness exists - create a fresh element
    let (new_elem, _) = structure.add_element(universe, *sort_idx);

    // Fire body as conclusion with the new element bound to var_name
    let mut extended_binding = binding.clone();
    extended_binding.insert(var_name.to_string(), new_elem);

    // Use fire_conclusion to make the body true
    // This handles relations, equalities, conjunctions uniformly
    fire_conclusion(body, &extended_binding, structure, cc, universe, sig)?;

    Ok(true)
}

/// Run the chase algorithm until a fixpoint is reached, with congruence closure.
///
/// Repeatedly applies [`chase_step`] and propagates equations until no more changes occur.
///
/// # Arguments
///
/// * `axioms` - The sequents (axioms) to apply
/// * `structure` - The structure to modify
/// * `cc` - Congruence closure for equality reasoning
/// * `universe` - The universe for element creation
/// * `sig` - The signature
/// * `max_iterations` - Safety limit to prevent infinite loops
///
/// # Returns
///
/// The number of iterations taken to reach the fixpoint.
pub fn chase_fixpoint_with_cc(
    axioms: &[Sequent],
    structure: &mut Structure,
    cc: &mut CongruenceClosure,
    universe: &mut Universe,
    sig: &Signature,
    max_iterations: usize,
) -> Result<usize, ChaseError> {
    let mut iterations = 0;

    loop {
        if iterations >= max_iterations {
            return Err(ChaseError::MaxIterationsExceeded(max_iterations));
        }

        // Fire axiom conclusions
        let axiom_changed = chase_step(axioms, structure, cc, universe, sig)?;

        // Propagate pending equations in CC
        let eq_changed = propagate_equations(structure, cc, sig);

        iterations += 1;

        if !axiom_changed && !eq_changed {
            break;
        }
    }

    Ok(iterations)
}

/// Propagate pending equations in the congruence closure.
///
/// This merges equivalence classes and detects function conflicts
/// (which add new equations via congruence).
fn propagate_equations(
    structure: &Structure,
    cc: &mut CongruenceClosure,
    sig: &Signature,
) -> bool {
    let mut changed = false;

    while let Some(eq) = cc.pop_pending() {
        // Merge the equivalence classes
        if cc.merge(eq.lhs, eq.rhs) {
            changed = true;

            // Check for function conflicts (congruence propagation)
            // If f(a) = x and f(b) = y, and a = b (just merged), then x = y
            for func_id in 0..sig.functions.len() {
                if func_id >= structure.functions.len() {
                    continue;
                }

                let lhs_local = structure.sort_local_id(eq.lhs);
                let rhs_local = structure.sort_local_id(eq.rhs);

                let lhs_val = structure.get_function(func_id, lhs_local);
                let rhs_val = structure.get_function(func_id, rhs_local);

                if let (Some(lv), Some(rv)) = (lhs_val, rhs_val)
                    && !cc.are_equal(lv, rv) {
                        // Congruence: f(a) = lv, f(b) = rv, a = b implies lv = rv
                        cc.add_equation(lv, rv, EquationReason::Congruence { func_id });
                    }
            }
        }
    }

    changed
}

/// Canonicalize the structure based on the congruence closure.
///
/// After the chase, some elements may have been merged in the CC but the
/// structure still contains distinct elements. This function:
/// 1. Removes non-canonical elements from carriers
/// 2. Replaces relation tuples with their canonical forms
fn canonicalize_structure(structure: &mut Structure, cc: &mut CongruenceClosure) {
    use crate::core::{RelationStorage, VecRelation};

    // 1. Canonicalize carriers: keep only canonical representatives
    for carrier in &mut structure.carriers {
        let elements: Vec<u64> = carrier.iter().collect();
        carrier.clear();
        for elem in elements {
            let slid = Slid::from_usize(elem as usize);
            let canonical = cc.canonical(slid);
            // Only keep if this element is its own canonical representative
            if canonical == slid {
                carrier.insert(elem);
            }
        }
    }

    // 2. Canonicalize relations: replace tuples with canonical forms
    for rel in &mut structure.relations {
        let canonical_tuples: Vec<Vec<Slid>> = rel.iter()
            .map(|tuple| tuple.iter().map(|&s| cc.canonical(s)).collect())
            .collect();

        let arity = rel.arity();
        let mut new_rel = VecRelation::new(arity);
        for tuple in canonical_tuples {
            new_rel.insert(tuple);
        }

        *rel = new_rel;
    }
}

/// Run the chase algorithm until a fixpoint is reached.
///
/// This is a convenience wrapper that creates a fresh congruence closure.
/// Use [`chase_fixpoint_with_cc`] if you need to provide your own CC.
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
    let mut cc = CongruenceClosure::new();
    let iterations = chase_fixpoint_with_cc(axioms, structure, &mut cc, universe, sig, max_iterations)?;

    // Canonicalize structure to reflect CC merges before returning
    canonicalize_structure(structure, &mut cc);

    Ok(iterations)
}

// Tests are in tests/unit_chase.rs
