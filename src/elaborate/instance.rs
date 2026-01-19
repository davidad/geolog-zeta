//! Instance elaboration.

use std::collections::HashMap;

use crate::ast;
use crate::core::*;
use crate::id::{NumericId, Slid};
use crate::workspace::Workspace;

use super::env::Env;
use super::error::{ElabError, ElabResult};

/// Elaborate an instance declaration into a Structure.
///
/// This is the workspace-aware version that supports cross-instance references.
/// For parameterized instances like `marking0 : ExampleNet Marking`, elements
/// from param instances (ExampleNet) are imported into the new structure.
pub fn elaborate_instance_ws(
    workspace: &mut Workspace,
    instance: &ast::InstanceDecl,
) -> ElabResult<Structure> {
    // Build Env from workspace.theories for theory lookups
    let env = Env {
        theories: workspace.theories.clone(),
        ..Env::new()
    };

    // 1. Resolve the theory type (handles parameterized types like `ExampleNet ReachabilityProblem`)
    let resolved = resolve_instance_type(&env, &instance.theory)?;
    let theory = env
        .theories
        .get(&resolved.theory_name)
        .ok_or_else(|| ElabError::UnknownTheory(resolved.theory_name.clone()))?;

    // 2. Initialize structure (functions will be initialized after first pass)
    let mut structure = Structure::new(theory.theory.signature.sorts.len());

    // Track name → Slid for resolving references within this instance
    // Also track Slid → name for error messages
    let mut name_to_slid: HashMap<String, Slid> = HashMap::new();
    let mut slid_to_name: HashMap<Slid, String> = HashMap::new();

    // 2b. Import elements from param instances
    // For each param binding (N, ExampleNet), import all elements from ExampleNet
    // with their sorts mapped to the local signature (N/P, N/T, etc.)
    //
    // Also build a mapping from (param_slid -> local_slid) for each param instance
    // so we can later import function values.
    let mut param_slid_to_local: HashMap<(String, Slid), Slid> = HashMap::new();

    for (param_name, instance_name) in &resolved.arguments {
        if let Some(param_entry) = workspace.instances.get(instance_name) {
            // Get the param theory to know sort mappings
            let param_theory_name = &param_entry.theory_name;
            if let Some(param_theory) = workspace.theories.get(param_theory_name) {
                // For each element in the param instance, import it
                for (&slid, elem_name) in &param_entry.slid_to_name {
                    // Get the element's sort in the param instance
                    let param_sort_id = param_entry.structure.sorts[slid.index()];
                    let param_sort_name = &param_theory.theory.signature.sorts[param_sort_id];

                    // Map to local sort: N/P where N is param_name
                    let local_sort_name = format!("{}/{}", param_name, param_sort_name);
                    let local_sort_id = theory
                        .theory
                        .signature
                        .lookup_sort(&local_sort_name)
                        .ok_or_else(|| ElabError::UnknownSort(local_sort_name.clone()))?;

                    // Get the Luid for this element
                    let luid = param_entry.structure.get_luid(slid);

                    // Add to local structure with the SAME Luid
                    let local_slid = structure.add_element_with_luid(luid, local_sort_id);

                    // Register names: both "N/elemname" and "InstanceName/elemname"
                    let qualified_param = format!("{}/{}", param_name, elem_name);
                    let qualified_instance = format!("{}/{}", instance_name, elem_name);

                    name_to_slid.insert(qualified_param.clone(), local_slid);
                    name_to_slid.insert(qualified_instance.clone(), local_slid);
                    slid_to_name.insert(local_slid, qualified_instance);

                    // Record mapping for function value import
                    param_slid_to_local.insert((instance_name.clone(), slid), local_slid);
                }
            }
        }
    }

    // 3. First pass: create elements (new elements declared in this instance)
    for item in &instance.body {
        if let ast::InstanceItem::Element(name, sort_expr) = &item.node {
            // Resolve the sort
            let sort_id = resolve_instance_sort(&theory.theory.signature, sort_expr)?;

            // Add element to structure (returns Slid, Luid)
            let (slid, _luid) = structure.add_element(&mut workspace.universe, sort_id);
            name_to_slid.insert(name.clone(), slid);
            slid_to_name.insert(slid, name.clone());
        }
    }

    // 3b. Initialize function storage now that carrier sizes are known
    // Extract domain sort IDs for each function (None for product domains)
    let domain_sort_ids: Vec<Option<SortId>> = theory
        .theory
        .signature
        .functions
        .iter()
        .map(|func| match &func.domain {
            DerivedSort::Base(id) => Some(*id),
            DerivedSort::Product(_) => None, // Defer product domains
        })
        .collect();
    structure.init_functions(&domain_sort_ids);

    // 3c. Import function values from param instances
    // For each param (N, ExampleNet), for each function in param theory (src, tgt),
    // import the function values using the local func name (N/src, N/tgt).
    for (param_name, instance_name) in &resolved.arguments {
        if let Some(param_entry) = workspace.instances.get(instance_name) {
            let param_theory_name = &param_entry.theory_name;
            if let Some(param_theory) = workspace.theories.get(param_theory_name) {
                // For each function in the param theory
                for (param_func_id, param_func) in
                    param_theory.theory.signature.functions.iter().enumerate()
                {
                    // Find the corresponding local function: N/func_name
                    let local_func_name = format!("{}/{}", param_name, param_func.name);
                    let local_func_id = theory
                        .theory
                        .signature
                        .lookup_func(&local_func_name)
                        .ok_or_else(|| ElabError::UnknownFunction(local_func_name.clone()))?;

                    // For each element in the domain, copy the function value
                    if let DerivedSort::Base(param_domain_sort) = &param_func.domain {
                        for param_domain_slid in
                            param_entry.structure.carriers[*param_domain_sort].iter()
                        {
                            let param_domain_slid = Slid::from_usize(param_domain_slid as usize);

                            // Get the function value in the param instance
                            let param_sort_local_id =
                                param_entry.structure.sort_local_id(param_domain_slid);
                            if let Some(param_value_slid) = param_entry
                                .structure
                                .get_function(param_func_id, param_sort_local_id)
                            {
                                // Map both domain and codomain slids to local
                                if let (Some(&local_domain_slid), Some(&local_value_slid)) = (
                                    param_slid_to_local
                                        .get(&(instance_name.clone(), param_domain_slid)),
                                    param_slid_to_local
                                        .get(&(instance_name.clone(), param_value_slid)),
                                ) {
                                    // Define the function value in the local structure
                                    let _ = structure.define_function(
                                        local_func_id,
                                        local_domain_slid,
                                        local_value_slid,
                                    );
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    // 4. Second pass: process equations (define function values) with type checking
    for item in &instance.body {
        if let ast::InstanceItem::Equation(lhs, rhs) = &item.node {
            // Decompose lhs: should be `element func_path`
            // e.g., `ab_in in/src` → element="ab_in", func="in/src"
            let (elem_slid, func_id) =
                decompose_func_app(lhs, &name_to_slid, &theory.theory.signature)?;

            // Resolve rhs to an element
            let value_slid = resolve_instance_element(rhs, &name_to_slid)?;

            // Type checking: verify element sort matches function domain
            let func = &theory.theory.signature.functions[func_id];
            let elem_sort_id = structure.sorts[elem_slid.index()];
            if let DerivedSort::Base(expected_domain) = &func.domain
                && elem_sort_id != *expected_domain
            {
                return Err(ElabError::DomainMismatch {
                    func_name: func.name.clone(),
                    element_name: slid_to_name
                        .get(&elem_slid)
                        .cloned()
                        .unwrap_or_else(|| format!("slid_{}", elem_slid)),
                    expected_sort: theory.theory.signature.sorts[*expected_domain].clone(),
                    actual_sort: theory.theory.signature.sorts[elem_sort_id].clone(),
                });
            }

            // Type checking: verify value sort matches function codomain
            let value_sort_id = structure.sorts[value_slid.index()];
            if let DerivedSort::Base(expected_codomain) = &func.codomain
                && value_sort_id != *expected_codomain
            {
                return Err(ElabError::CodomainMismatch {
                    func_name: func.name.clone(),
                    element_name: slid_to_name
                        .get(&value_slid)
                        .cloned()
                        .unwrap_or_else(|| format!("slid_{}", value_slid)),
                    expected_sort: theory.theory.signature.sorts[*expected_codomain].clone(),
                    actual_sort: theory.theory.signature.sorts[value_sort_id].clone(),
                });
            }

            // Define the function value
            structure
                .define_function(func_id, elem_slid, value_slid)
                .map_err(ElabError::DuplicateDefinition)?;
        }
    }

    // 5. Third pass: nested instances (TODO for Phase 2)
    for item in &instance.body {
        if let ast::InstanceItem::NestedInstance(name, _nested) = &item.node {
            // For now, just note that we're skipping these
            return Err(ElabError::UnsupportedFeature(format!(
                "nested instance: {}",
                name
            )));
        }
    }

    // 6. Validate totality: all functions must be defined on all elements of their domain
    validate_totality(&structure, &theory.theory.signature, &slid_to_name)?;

    Ok(structure)
}

/// Legacy elaborate_instance - for non-parameterized instances only.
/// Use elaborate_instance_ws for full cross-instance reference support.
#[deprecated(note = "Use elaborate_instance_ws for parameterized instance support")]
pub fn elaborate_instance(
    env: &Env,
    instance: &ast::InstanceDecl,
    universe: &mut crate::universe::Universe,
) -> ElabResult<Structure> {
    // This is the old version without workspace access.
    // It only works for non-parameterized instances.
    let resolved = resolve_instance_type(env, &instance.theory)?;

    if !resolved.arguments.is_empty() {
        return Err(ElabError::UnsupportedFeature(
            "parameterized instances require elaborate_instance_ws with Workspace access"
                .to_string(),
        ));
    }

    let theory = env
        .theories
        .get(&resolved.theory_name)
        .ok_or_else(|| ElabError::UnknownTheory(resolved.theory_name.clone()))?;

    let mut structure = Structure::new(theory.theory.signature.sorts.len());
    let mut name_to_slid: HashMap<String, Slid> = HashMap::new();
    let mut slid_to_name: HashMap<Slid, String> = HashMap::new();

    // First pass: create elements
    for item in &instance.body {
        if let ast::InstanceItem::Element(name, sort_expr) = &item.node {
            let sort_id = resolve_instance_sort(&theory.theory.signature, sort_expr)?;
            let (slid, _luid) = structure.add_element(universe, sort_id);
            name_to_slid.insert(name.clone(), slid);
            slid_to_name.insert(slid, name.clone());
        }
    }

    // Initialize function storage
    let domain_sort_ids: Vec<Option<SortId>> = theory
        .theory
        .signature
        .functions
        .iter()
        .map(|func| match &func.domain {
            DerivedSort::Base(id) => Some(*id),
            DerivedSort::Product(_) => None,
        })
        .collect();
    structure.init_functions(&domain_sort_ids);

    // Second pass: process equations
    for item in &instance.body {
        if let ast::InstanceItem::Equation(lhs, rhs) = &item.node {
            let (elem_slid, func_id) =
                decompose_func_app(lhs, &name_to_slid, &theory.theory.signature)?;
            let value_slid = resolve_instance_element(rhs, &name_to_slid)?;

            let func = &theory.theory.signature.functions[func_id];
            let elem_sort_id = structure.sorts[elem_slid.index()];
            if let DerivedSort::Base(expected_domain) = &func.domain
                && elem_sort_id != *expected_domain
            {
                return Err(ElabError::DomainMismatch {
                    func_name: func.name.clone(),
                    element_name: slid_to_name
                        .get(&elem_slid)
                        .cloned()
                        .unwrap_or_else(|| format!("slid_{}", elem_slid)),
                    expected_sort: theory.theory.signature.sorts[*expected_domain].clone(),
                    actual_sort: theory.theory.signature.sorts[elem_sort_id].clone(),
                });
            }

            let value_sort_id = structure.sorts[value_slid.index()];
            if let DerivedSort::Base(expected_codomain) = &func.codomain
                && value_sort_id != *expected_codomain
            {
                return Err(ElabError::CodomainMismatch {
                    func_name: func.name.clone(),
                    element_name: slid_to_name
                        .get(&value_slid)
                        .cloned()
                        .unwrap_or_else(|| format!("slid_{}", value_slid)),
                    expected_sort: theory.theory.signature.sorts[*expected_codomain].clone(),
                    actual_sort: theory.theory.signature.sorts[value_sort_id].clone(),
                });
            }

            structure
                .define_function(func_id, elem_slid, value_slid)
                .map_err(ElabError::DuplicateDefinition)?;
        }
    }

    // Third pass: nested instances
    for item in &instance.body {
        if let ast::InstanceItem::NestedInstance(name, _nested) = &item.node {
            return Err(ElabError::UnsupportedFeature(format!(
                "nested instance: {}",
                name
            )));
        }
    }

    validate_totality(&structure, &theory.theory.signature, &slid_to_name)?;
    Ok(structure)
}

// ============================================================================
// HELPER TYPES AND FUNCTIONS
// ============================================================================

/// Result of resolving a (possibly parameterized) instance type.
///
/// For `ExampleNet ReachabilityProblem`:
/// - theory_name = "ReachabilityProblem"
/// - arguments = vec![("N", "ExampleNet")]
///
/// For simple `PetriNet`:
/// - theory_name = "PetriNet"
/// - arguments = vec![]
struct ResolvedInstanceType {
    theory_name: String,
    /// (param_name, instance_name) pairs
    arguments: Vec<(String, String)>,
}

/// Resolve a type expression to a theory name and its arguments.
///
/// In curried application syntax, the theory is at the end:
/// - Simple: `PetriNet` -> ("PetriNet", [])
/// - Single param: `ExampleNet Marking` -> ("Marking", [("N", "ExampleNet")])
/// - Multiple params: `ExampleNet problem0 ReachabilityProblem/Solution` -> ("ReachabilityProblem/Solution", [("N", "ExampleNet"), ("RP", "problem0")])
///
/// AST structure for `A B C`:
/// - App(App(A, B), C) where C is the "function" being applied
/// - So we need to collect: theory=C, args=[A, B]
fn resolve_instance_type(env: &Env, ty: &ast::TypeExpr) -> ElabResult<ResolvedInstanceType> {
    match ty {
        ast::TypeExpr::Path(path) => {
            // Simple theory name
            Ok(ResolvedInstanceType {
                theory_name: path.to_string(),
                arguments: vec![],
            })
        }
        ast::TypeExpr::App(_base, _arg) => {
            // Theory application: `arg1 arg2 ... theory`
            // In AST: App(App(...App(arg1, arg2)..., argN), theory)
            //
            // The rightmost is the theory, everything else are arguments.
            // We walk down collecting all paths, then the last one is the theory.
            let mut all_paths = vec![];
            let mut current = ty;

            // Walk down the App chain
            while let ast::TypeExpr::App(inner_base, inner_arg) = current {
                // The inner_arg should be a Path
                if let ast::TypeExpr::Path(arg_path) = inner_arg.as_ref() {
                    all_paths.push(arg_path.to_string());
                } else {
                    return Err(ElabError::UnsupportedFeature(
                        "complex theory application argument".to_string(),
                    ));
                }
                current = inner_base;
            }

            // After unwinding, `current` should be the leftmost path (first argument)
            if let ast::TypeExpr::Path(first_path) = current {
                all_paths.push(first_path.to_string());
            } else {
                return Err(ElabError::UnsupportedFeature(
                    "complex theory application base".to_string(),
                ));
            }

            // Now all_paths contains [rightmost, ..., leftmost]
            // We want: theory = rightmost, args = [leftmost, ..., second-to-rightmost]
            // So reverse to get [leftmost, ..., rightmost], then pop the theory
            all_paths.reverse();
            let theory_name = all_paths.pop().expect("at least one path");
            let args = all_paths; // [leftmost, ..., second-to-rightmost] = arguments in order

            // Look up the theory to get parameter names
            let theory = env
                .theories
                .get(&theory_name)
                .ok_or_else(|| ElabError::UnknownTheory(theory_name.clone()))?;

            // Match up arguments with parameters
            if args.len() != theory.params.len() {
                return Err(ElabError::UnsupportedFeature(format!(
                    "theory {} expects {} parameters, got {}",
                    theory_name,
                    theory.params.len(),
                    args.len()
                )));
            }

            let arguments: Vec<(String, String)> = theory
                .params
                .iter()
                .zip(args.iter())
                .map(|(param, arg)| (param.name.clone(), arg.clone()))
                .collect();

            Ok(ResolvedInstanceType {
                theory_name,
                arguments,
            })
        }
        _ => Err(ElabError::NotASort(format!("{:?}", ty))),
    }
}

/// Resolve a sort expression within an instance (using the theory's signature)
fn resolve_instance_sort(sig: &Signature, sort_expr: &ast::TypeExpr) -> ElabResult<SortId> {
    match sort_expr {
        ast::TypeExpr::Path(path) if path.segments.len() == 1 => {
            let name = &path.segments[0];
            sig.lookup_sort(name)
                .ok_or_else(|| ElabError::UnknownSort(name.clone()))
        }
        _ => Err(ElabError::UnsupportedFeature(format!(
            "complex sort: {:?}",
            sort_expr
        ))),
    }
}

/// Decompose a function application term like `ab_in in/src`
/// Returns (element_slid, func_id)
fn decompose_func_app(
    term: &ast::Term,
    name_to_slid: &HashMap<String, Slid>,
    sig: &Signature,
) -> ElabResult<(Slid, FuncId)> {
    match term {
        ast::Term::App(base, func) => {
            // base should be an element name, func should be a function path
            let elem_slid = resolve_instance_element(base, name_to_slid)?;

            let func_id = match func.as_ref() {
                ast::Term::Path(path) => {
                    let func_name = path.to_string();
                    sig.lookup_func(&func_name)
                        .ok_or(ElabError::UnknownFunction(func_name))
                }
                _ => Err(ElabError::NotAFunction(format!("{:?}", func))),
            }?;

            Ok((elem_slid, func_id))
        }
        _ => Err(ElabError::NotAFunction(format!(
            "expected function application, got {:?}",
            term
        ))),
    }
}

/// Resolve a term to an element Slid
///
/// Handles both simple names ("v1") and qualified paths ("ExampleNet/t1").
/// For multi-segment paths, joins with "/" and looks up in name_to_slid.
fn resolve_instance_element(
    term: &ast::Term,
    name_to_slid: &HashMap<String, Slid>,
) -> ElabResult<Slid> {
    match term {
        ast::Term::Path(path) => {
            // Join all segments with "/" for lookup
            // This handles both "v1" and "ExampleNet/t1"
            let name = path.segments.join("/");
            name_to_slid
                .get(&name)
                .copied()
                .ok_or(ElabError::UnknownVariable(name))
        }
        _ => Err(ElabError::UnsupportedFeature(format!(
            "complex element reference: {:?}",
            term
        ))),
    }
}

/// Check that all functions in the structure are total (defined on every element of their domain)
fn validate_totality(
    structure: &Structure,
    sig: &Signature,
    slid_to_name: &HashMap<Slid, String>,
) -> ElabResult<()> {
    use crate::core::FunctionColumn;

    for (func_id, func_sym) in sig.functions.iter().enumerate() {
        // Get the domain sort (only handle base sorts for now)
        let domain_sort_id = match &func_sym.domain {
            DerivedSort::Base(id) => *id,
            DerivedSort::Product(_) => {
                // Skip product domains for now — they'd require enumerating all tuples
                continue;
            }
        };

        // Check that every slot in the columnar function storage is defined
        let mut missing = Vec::new();
        let func_col = &structure.functions[func_id];

        match func_col {
            FunctionColumn::Local(col) => {
                for (sort_slid, opt_slid) in col.iter().enumerate() {
                    if opt_slid.is_none() {
                        // Reverse lookup: sort_slid → slid
                        let slid = Slid::from_usize(
                            structure.carriers[domain_sort_id]
                                .select(sort_slid as u64)
                                .expect("sort_slid should be valid") as usize,
                        );
                        let name = slid_to_name
                            .get(&slid)
                            .cloned()
                            .unwrap_or_else(|| format!("element#{}", slid));
                        missing.push(name);
                    }
                }
            }
            FunctionColumn::External(col) => {
                // For external codomains, check that all Luid refs are defined
                for (sort_slid, opt_luid) in col.iter().enumerate() {
                    if opt_luid.is_none() {
                        let slid = Slid::from_usize(
                            structure.carriers[domain_sort_id]
                                .select(sort_slid as u64)
                                .expect("sort_slid should be valid") as usize,
                        );
                        let name = slid_to_name
                            .get(&slid)
                            .cloned()
                            .unwrap_or_else(|| format!("element#{}", slid));
                        missing.push(name);
                    }
                }
            }
        }

        if !missing.is_empty() {
            return Err(ElabError::PartialFunction {
                func_name: func_sym.name.clone(),
                missing_elements: missing,
            });
        }
    }

    Ok(())
}
