//! Chase algorithm for computing derived relations.
//!
//! The chase takes a structure and a set of axioms (sequents) and repeatedly
//! applies the axioms until a fixpoint is reached. This is the standard database
//! chase algorithm adapted for geometric logic.
//!
//! # Axiom Structure
//!
//! Axioms are sequents of the form `premise ⊢ conclusion` where:
//! - **premise** (body): conditions that must hold (conjunction of relations/equalities)
//! - **conclusion** (head): what to add when conditions hold
//!
//! # Supported Axioms
//!
//! Currently supports Horn clauses (no disjunctions/existentials in head):
//! - **Relation rules**: `R(x,y), S(y,z) ⊢ T(x,z)` — add to relation
//! - **Function rules**: `R(x,y), f(x)=a ⊢ g(y)=b` — function extension
//! - **Reflexivity**: `|- R(x,x)` — add reflexive closure
//! - **Transitivity**: `R(x,y), R(y,z) ⊢ R(x,z)` — add transitive closure
//!
//! Existential support (creating new elements) is TODO.
//!
//! # Algorithm
//!
//! ```text
//! while changed:
//!     for each axiom (premise ⊢ conclusion):
//!         matches = query(premise)  // compiled to QueryOp
//!         for each binding in matches:
//!             changed |= fire(conclusion, binding)
//! ```
//!
//! # Key Implementation Details
//!
//! ## Variable Binding and Column Mapping
//!
//! The chase compiles axiom premises to QueryOp plans which produce tuples.
//! A key challenge is mapping between context variables and query output columns:
//!
//! - **Context variables**: Named variables in the axiom (e.g., x, y, z)
//! - **Output columns**: Positions in the query result tuples
//!
//! For conjunctions of relation atoms with shared variables (like transitivity),
//! we use equi-join filters to enforce that shared variables match:
//!
//! ```text
//! [x:x, y:y] R, [x:y, y:z] R  ⊢  [x:x, y:z] R
//!
//! Query plan:
//!   ScanRelation(R)           → columns [x, y]  (vars 0, 1)
//!   ScanRelation(R)           → columns [y, z]  (vars 1, 2)
//!   Cross Join                → columns [x, y, y', z]
//!   Filter(col1 = col2)       → enforces y = y' (shared variable)
//!
//! Conclusion accesses: col0 (x) and col3 (z) for the result tuple
//! ```
//!
//! # Usage
//!
//! ```ignore
//! use geolog::query::chase::{compile_theory_axioms, chase_fixpoint};
//!
//! // Compile theory axioms to chase rules
//! let rules = compile_theory_axioms(&theory)?;
//!
//! // Run chase to fixpoint
//! let iterations = chase_fixpoint(&rules, &mut structure, &mut universe, &sig, 100)?;
//!
//! // Or use the :chase REPL command
//! // :chase <instance> [max_iterations]
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
    /// Create a new element (existential) - old style, always creates
    CreateElement {
        sort_idx: usize,
        /// Bindings for functions on the new element: f(new_elem) = col
        function_bindings: Vec<(usize, usize)>, // (func_idx, result_col)
    },
    /// Ensure a function value exists via skolemization.
    /// For axioms like "forall a. exists b. f(a) = b":
    /// - Check if f(arg) is already defined
    /// - If not, create a new element of the given sort and define f(arg) = new_elem
    EnsureFunction {
        func_idx: usize,
        arg_col: usize,
        new_sort_idx: usize,
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
    // Build variable-to-context-index mapping from context
    let mut var_indices: HashMap<String, usize> = HashMap::new();
    for (idx, (var_name, _sort)) in sequent.context.vars.iter().enumerate() {
        var_indices.insert(var_name.clone(), idx);
    }

    // Compile premise to query and get column mapping (output column → context var index)
    let (query, column_mapping) = compile_premise_with_mapping(
        &sequent.premise,
        &var_indices,
        &sequent.context,
        sig,
    )?;

    // Build reverse mapping: context var index → output column index
    // This is needed for the conclusion to know which column to read for each variable
    let mut var_to_col: HashMap<String, usize> = HashMap::new();
    for (col_idx, &var_idx) in column_mapping.iter().enumerate() {
        // Find the variable name for this context index
        for (var_name, &ctx_idx) in &var_indices {
            if ctx_idx == var_idx && !var_to_col.contains_key(var_name) {
                // Use the first column that maps to this variable
                var_to_col.insert(var_name.clone(), col_idx);
            }
        }
    }

    // Compile conclusion to head using the column mapping
    let head = compile_conclusion(&sequent.conclusion, &var_to_col, sig)?;

    Ok(ChaseRule {
        name,
        var_indices,
        query,
        head,
    })
}

/// Column mapping: which context variable does each output column represent?
/// Maps output column index -> context variable index
type ColumnMapping = Vec<usize>;

/// Compile a premise formula to a QueryOp and its column mapping
fn compile_premise_with_mapping(
    formula: &Formula,
    var_indices: &HashMap<String, usize>,
    context: &Context,
    sig: &Signature,
) -> Result<(QueryOp, ColumnMapping), ChaseError> {
    match formula {
        Formula::True => {
            // True premise: scan all elements of first variable's sort
            if context.vars.is_empty() {
                Ok((QueryOp::Empty, vec![]))
            } else {
                let (_, sort) = &context.vars[0];
                let sort_idx = resolve_sort_index(sort, sig)?;
                // Output column 0 corresponds to context variable 0
                Ok((QueryOp::Scan { sort_idx }, vec![0]))
            }
        }

        Formula::Rel(rel_id, arg) => {
            // Extract column-to-variable mapping from the record argument
            let mapping = extract_rel_column_mapping(arg, var_indices)?;
            Ok((QueryOp::ScanRelation { rel_id: *rel_id }, mapping))
        }

        Formula::Conj(formulas) => {
            if formulas.is_empty() {
                return compile_premise_with_mapping(&Formula::True, var_indices, context, sig);
            }

            // Compile each formula and track column mappings
            let mut ops_with_mappings: Vec<(QueryOp, ColumnMapping)> = Vec::new();
            for f in formulas {
                ops_with_mappings.push(compile_premise_with_mapping(f, var_indices, context, sig)?);
            }

            // Build join tree with filters for shared variables
            let (mut result_op, mut result_mapping) = ops_with_mappings.remove(0);

            for (right_op, right_mapping) in ops_with_mappings {
                // Find shared variables between current result and right side
                let left_width = result_mapping.len();
                let mut equi_conditions: Vec<(usize, usize)> = Vec::new();

                for (right_col, &right_var) in right_mapping.iter().enumerate() {
                    // Check if this variable appears in the left side
                    for (left_col, &left_var) in result_mapping.iter().enumerate() {
                        if left_var == right_var {
                            // Shared variable! Need to match these columns
                            // Right column is at offset left_width after join
                            equi_conditions.push((left_col, left_width + right_col));
                            break;
                        }
                    }
                }

                // Create the join
                result_op = QueryOp::Join {
                    left: Box::new(result_op),
                    right: Box::new(right_op),
                    cond: crate::query::backend::JoinCond::Cross,
                };

                // Update mapping: concatenate left and right mappings
                result_mapping.extend(right_mapping.iter().copied());

                // Add filters for shared variables
                for (left_col, right_col) in equi_conditions {
                    result_op = QueryOp::Filter {
                        input: Box::new(result_op),
                        pred: Predicate::ColEqCol { left: left_col, right: right_col },
                    };
                }
            }

            Ok((result_op, result_mapping))
        }

        Formula::Eq(left, right) => {
            let left_col = term_to_column(left, var_indices)?;
            let right_col = term_to_column(right, var_indices)?;

            if context.vars.is_empty() {
                return Err(ChaseError::UnsupportedPremise(
                    "Equality without variables".to_string()
                ));
            }

            let (_, sort) = &context.vars[0];
            let sort_idx = resolve_sort_index(sort, sig)?;
            let scan = QueryOp::Scan { sort_idx };

            Ok((
                QueryOp::Filter {
                    input: Box::new(scan),
                    pred: Predicate::ColEqCol { left: left_col, right: right_col },
                },
                vec![0], // Single-element scan
            ))
        }

        Formula::False => Ok((QueryOp::Empty, vec![])),

        Formula::Disj(_) => Err(ChaseError::UnsupportedPremise(
            "Disjunction in premise not yet supported".to_string()
        )),

        Formula::Exists(_, _, _) => Err(ChaseError::UnsupportedPremise(
            "Existential in premise not yet supported".to_string()
        )),
    }
}

/// Extract column-to-variable mapping from a relation argument term
fn extract_rel_column_mapping(
    arg: &Term,
    var_indices: &HashMap<String, usize>,
) -> Result<ColumnMapping, ChaseError> {
    match arg {
        Term::Var(name, _) => {
            // Single variable: maps to its context index
            let idx = var_indices.get(name).ok_or_else(|| {
                ChaseError::UnboundVariable(name.clone())
            })?;
            Ok(vec![*idx])
        }
        Term::Record(fields) => {
            // Record: extract each field's variable mapping in order
            let mut mapping = Vec::new();
            for (_, term) in fields {
                let field_mapping = extract_rel_column_mapping(term, var_indices)?;
                mapping.extend(field_mapping);
            }
            Ok(mapping)
        }
        Term::App(_, _) | Term::Project(_, _) => {
            // Function application in relation argument - complex case
            // For now, return an error; we'd need to track function outputs
            Err(ChaseError::UnsupportedPremise(
                "Function application in relation argument not yet supported".to_string()
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
            // Handle existential quantification in conclusion
            let sort_idx = resolve_sort_index(sort, sig)?;

            // Check for common patterns:
            // 1. "exists b. f(a) = b" - ensure f(a) is defined (skolem)
            // 2. "exists b. f(b) = y" - create element with function binding

            // Try to detect "f(arg) = new_var" pattern for EnsureFunction
            if let Some((func_idx, arg_col)) = extract_ensure_function_pattern(body, var_name, var_indices)? {
                // Pattern: exists b. f(a) = b
                // Use EnsureFunction - only create if f(a) is undefined
                return Ok(ChaseHead::EnsureFunction {
                    func_idx,
                    arg_col,
                    new_sort_idx: sort_idx,
                });
            }

            // Fall back to the old CreateElement behavior for other patterns
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

        Formula::Disj(disjuncts) => {
            // Naive/parallel chase: add all disjuncts
            // This is sound but may add more facts than strictly necessary
            // A proper branching chase would enumerate all possibilities
            let mut heads = Vec::new();
            for d in disjuncts {
                let head = compile_conclusion(d, var_indices, sig)?;
                match head {
                    ChaseHead::Multi(sub) => heads.extend(sub),
                    _ => heads.push(head),
                }
            }
            Ok(ChaseHead::Multi(heads))
        }
    }
}

/// Try to extract the "f(arg) = new_var" pattern from an existential body.
/// Returns Some((func_idx, arg_col)) if the body is exactly "f(arg) = new_var"
/// where arg is a bound variable and new_var is the existential variable.
fn extract_ensure_function_pattern(
    formula: &Formula,
    new_var: &str,
    var_indices: &HashMap<String, usize>,
) -> Result<Option<(usize, usize)>, ChaseError> {
    match formula {
        Formula::Eq(left, right) => {
            // Check for f(arg) = new_var
            if let (Term::App(func_idx, arg), Term::Var(var_name, _)) = (left, right) {
                if var_name == new_var {
                    // Found: f(arg) = new_var
                    let arg_col = term_to_column(arg, var_indices)?;
                    return Ok(Some((*func_idx, arg_col)));
                }
            }
            // Check for new_var = f(arg)
            if let (Term::Var(var_name, _), Term::App(func_idx, arg)) = (left, right) {
                if var_name == new_var {
                    // Found: new_var = f(arg)
                    let arg_col = term_to_column(arg, var_indices)?;
                    return Ok(Some((*func_idx, arg_col)));
                }
            }
            Ok(None)
        }
        // Handle conjunction - look for the pattern in any conjunct
        Formula::Conj(conjuncts) if conjuncts.len() == 1 => {
            extract_ensure_function_pattern(&conjuncts[0], new_var, var_indices)
        }
        _ => Ok(None),
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

/// Execute one step of the chase algorithm.
///
/// A chase step iterates over all rules, finds matches for each rule's premise,
/// and fires the conclusion for each match. This may add new tuples to relations
/// or define new function values.
///
/// # Arguments
///
/// * `rules` - The compiled chase rules to apply
/// * `structure` - The structure to modify (relations and functions)
/// * `universe` - The universe for creating new elements (if needed)
/// * `sig` - The signature (for element creation)
///
/// # Returns
///
/// Returns `true` if any changes were made to the structure, `false` if the
/// structure is already at a fixpoint with respect to the given rules.
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

        ChaseHead::EnsureFunction { func_idx, arg_col, new_sort_idx } => {
            // Skolem chase for existentials:
            // "forall a. exists b. f(a) = b" means we need f to be defined for all a
            let arg = binding.get(*arg_col).copied()
                .ok_or_else(|| ChaseError::UnboundVariable("arg column out of bounds".to_string()))?;

            // Check if f(arg) is already defined
            let func = structure.functions.get(*func_idx)
                .ok_or_else(|| ChaseError::QueryFailed(format!("Function {} not found", func_idx)))?;

            let local_idx = structure.sort_local_id(arg).index();
            if crate::id::get_slid(func.get_local(local_idx)).is_some() {
                // Already defined - no change needed
                return Ok(false);
            }

            // Not defined - create new element and define f(arg) = new_elem
            let (new_elem, _luid) = structure.add_element(universe, *new_sort_idx);
            structure.define_function(*func_idx, arg, new_elem)
                .map_err(ChaseError::QueryFailed)?;

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

/// Run the chase algorithm until a fixpoint is reached.
///
/// Repeatedly applies [`chase_step`] until no more changes occur, or until
/// `max_iterations` is reached. This is the main entry point for computing
/// derived relations and function values from a theory's axioms.
///
/// # Arguments
///
/// * `rules` - The compiled chase rules (from [`compile_theory_axioms`])
/// * `structure` - The structure to modify
/// * `universe` - The universe for element creation
/// * `sig` - The signature
/// * `max_iterations` - Safety limit to prevent infinite loops
///
/// # Returns
///
/// The number of iterations taken to reach the fixpoint.
///
/// # Errors
///
/// Returns [`ChaseError`] if:
/// - `max_iterations` is exceeded (possible infinite chase)
/// - A rule fires with inconsistent results (function conflicts)
///
/// # Example
///
/// ```ignore
/// // Compute reflexive-transitive closure of a preorder
/// let rules = compile_theory_axioms(&preorder_theory)?;
/// let iterations = chase_fixpoint(&rules, &mut structure, &mut universe, &sig, 100)?;
/// println!("Chase converged in {} iterations", iterations);
/// ```
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

/// Compile all axioms in a theory to chase rules.
///
/// This is a convenience function that iterates over all axioms in the theory
/// and compiles each one to a [`ChaseRule`]. Axioms that cannot be compiled
/// (e.g., due to unsupported formula types) will cause an error.
///
/// # Arguments
///
/// * `theory` - The elaborated theory containing axioms to compile
///
/// # Returns
///
/// A vector of [`ChaseRule`]s, one for each axiom in the theory.
///
/// # Errors
///
/// Returns [`ChaseError`] if any axiom contains unsupported formulas:
/// - Disjunction in premise
/// - Existential quantification in premise
/// - Function application in relation arguments
pub fn compile_theory_axioms(theory: &ElaboratedTheory) -> Result<Vec<ChaseRule>, ChaseError> {
    let mut rules = Vec::new();

    for (idx, axiom) in theory.theory.axioms.iter().enumerate() {
        let name = format!("axiom_{}", idx);
        let rule = compile_axiom(axiom, &theory.theory.signature, name)?;
        rules.push(rule);
    }

    Ok(rules)
}

// Tests are in tests/unit_chase.rs
