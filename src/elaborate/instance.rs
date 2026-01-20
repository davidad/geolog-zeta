//! Instance elaboration.

use std::collections::HashMap;
use std::rc::Rc;

use crate::ast;
use crate::core::*;
use crate::id::{NumericId, Slid};
use crate::universe::Universe;

use super::env::Env;
use super::error::{ElabError, ElabResult};

/// Minimal context for instance elaboration - what we need from the caller.
///
/// This replaces the old `Workspace` dependency, making elaboration more modular.
pub struct ElaborationContext<'a> {
    /// Available theories
    pub theories: &'a HashMap<String, Rc<ElaboratedTheory>>,
    /// Existing instances (for parameterized instance support)
    pub instances: &'a HashMap<String, InstanceEntry>,
    /// Universe for allocating new Luids
    pub universe: &'a mut Universe,
}

/// Result of elaborating an instance.
///
/// Contains the structure and element name mappings.
#[derive(Debug)]
pub struct InstanceElaborationResult {
    /// The elaborated structure
    pub structure: Structure,
    /// Mapping from Slid to element name (for display)
    pub slid_to_name: HashMap<Slid, String>,
    /// Mapping from element name to Slid (for lookups)
    pub name_to_slid: HashMap<String, Slid>,
}

/// An instance entry for elaboration context.
///
/// This is a simpler version than what's in the REPL - just enough for elaboration.
pub struct InstanceEntry {
    /// The structure containing the instance data
    pub structure: Structure,
    /// The theory name this instance is of
    pub theory_name: String,
    /// Map from element names to Slids
    pub element_names: HashMap<String, Slid>,
    /// Reverse map from Slids to names
    pub slid_to_name: HashMap<Slid, String>,
}

impl InstanceEntry {
    /// Create a new instance entry
    pub fn new(structure: Structure, theory_name: String) -> Self {
        Self {
            structure,
            theory_name,
            element_names: HashMap::new(),
            slid_to_name: HashMap::new(),
        }
    }

    /// Register an element with a name
    pub fn register_element(&mut self, name: String, slid: Slid) {
        self.element_names.insert(name.clone(), slid);
        self.slid_to_name.insert(slid, name);
    }

    /// Look up element by local name
    pub fn get_element(&self, name: &str) -> Option<Slid> {
        self.element_names.get(name).copied()
    }

    /// Get name for Slid
    pub fn get_name(&self, slid: Slid) -> Option<&str> {
        self.slid_to_name.get(&slid).map(|s| s.as_str())
    }
}

/// Elaborate an instance declaration into a Structure with element name mappings.
///
/// This is the context-aware version that supports cross-instance references.
/// For parameterized instances like `marking0 : ExampleNet Marking`, elements
/// from param instances (ExampleNet) are imported into the new structure.
///
/// Returns both the structure and the element name mappings, so the caller
/// can track names for both local and imported elements.
pub fn elaborate_instance_ctx(
    ctx: &mut ElaborationContext<'_>,
    instance: &ast::InstanceDecl,
) -> ElabResult<InstanceElaborationResult> {
    elaborate_instance_ctx_inner(ctx, instance, false)
}

/// Elaborate an instance without validating totality.
/// Use this when the chase algorithm will fill in missing function values.
pub fn elaborate_instance_ctx_partial(
    ctx: &mut ElaborationContext<'_>,
    instance: &ast::InstanceDecl,
) -> ElabResult<InstanceElaborationResult> {
    elaborate_instance_ctx_inner(ctx, instance, true)
}

fn elaborate_instance_ctx_inner(
    ctx: &mut ElaborationContext<'_>,
    instance: &ast::InstanceDecl,
    skip_totality: bool,
) -> ElabResult<InstanceElaborationResult> {
    // Build Env from context theories for theory lookups
    let env = Env {
        theories: ctx.theories.clone(),
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

    // Initialize relation storage from signature
    let relation_arities: Vec<usize> = theory
        .theory
        .signature
        .relations
        .iter()
        .map(|rel| rel.domain.arity())
        .collect();
    structure.init_relations(&relation_arities);

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
        if let Some(param_entry) = ctx.instances.get(instance_name) {
            // Get the param theory to know sort mappings
            let param_theory_name = &param_entry.theory_name;
            if let Some(param_theory) = ctx.theories.get(param_theory_name) {
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
            let (slid, _luid) = structure.add_element(ctx.universe, sort_id);
            name_to_slid.insert(name.clone(), slid);
            slid_to_name.insert(slid, name.clone());
        }
    }

    // 3b. Initialize function storage now that carrier sizes are known
    // Extract domain info for each function (base or product)
    let domains: Vec<FunctionDomainInfo> = theory
        .theory
        .signature
        .functions
        .iter()
        .map(|func| match &func.domain {
            DerivedSort::Base(id) => FunctionDomainInfo::Base(*id),
            DerivedSort::Product(fields) => {
                let field_sorts: Vec<SortId> = fields
                    .iter()
                    .filter_map(|(_, ds)| match ds {
                        DerivedSort::Base(id) => Some(*id),
                        DerivedSort::Product(_) => None, // Nested products not supported
                    })
                    .collect();
                FunctionDomainInfo::Product(field_sorts)
            }
        })
        .collect();
    structure.init_functions_full(&domains);

    // 3c. Import function values from param instances
    // For each param (N, ExampleNet), for each function in param theory (src, tgt),
    // import the function values using the local func name (N/src, N/tgt).
    for (param_name, instance_name) in &resolved.arguments {
        if let Some(param_entry) = ctx.instances.get(instance_name) {
            let param_theory_name = &param_entry.theory_name;
            if let Some(param_theory) = ctx.theories.get(param_theory_name) {
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
            // Decompose lhs: `element func_path` or `[x: a, y: b] func_path`
            let decomposed =
                decompose_func_app(lhs, &name_to_slid, &theory.theory.signature)?;

            // Resolve rhs to an element
            let value_slid = resolve_instance_element(rhs, &name_to_slid)?;

            match decomposed {
                DecomposedFuncApp::Base { elem, func_id } => {
                    // Type checking: verify element sort matches function domain
                    let func = &theory.theory.signature.functions[func_id];
                    let elem_sort_id = structure.sorts[elem.index()];
                    if let DerivedSort::Base(expected_domain) = &func.domain
                        && elem_sort_id != *expected_domain
                    {
                        return Err(ElabError::DomainMismatch {
                            func_name: func.name.clone(),
                            element_name: slid_to_name
                                .get(&elem)
                                .cloned()
                                .unwrap_or_else(|| format!("slid_{}", elem)),
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
                        .define_function(func_id, elem, value_slid)
                        .map_err(ElabError::DuplicateDefinition)?;
                }

                DecomposedFuncApp::Product { tuple, func_id } => {
                    let func = &theory.theory.signature.functions[func_id];

                    // Type checking: verify tuple elements match product domain fields
                    if let DerivedSort::Product(fields) = &func.domain {
                        if tuple.len() != fields.len() {
                            return Err(ElabError::UnsupportedFeature(format!(
                                "product domain arity mismatch: expected {}, got {}",
                                fields.len(),
                                tuple.len()
                            )));
                        }

                        for (slid, (field_name, field_sort)) in tuple.iter().zip(fields.iter()) {
                            let elem_sort_id = structure.sorts[slid.index()];
                            if let DerivedSort::Base(expected_sort) = field_sort
                                && elem_sort_id != *expected_sort {
                                    return Err(ElabError::DomainMismatch {
                                        func_name: func.name.clone(),
                                        element_name: format!(
                                            "field {} ({})",
                                            field_name,
                                            slid_to_name
                                                .get(slid)
                                                .cloned()
                                                .unwrap_or_else(|| format!("slid_{}", slid))
                                        ),
                                        expected_sort: theory.theory.signature.sorts[*expected_sort]
                                            .clone(),
                                        actual_sort: theory.theory.signature.sorts[elem_sort_id]
                                            .clone(),
                                    });
                                }
                        }
                    } else {
                        return Err(ElabError::UnsupportedFeature(format!(
                            "function {} has product LHS but non-product domain {:?}",
                            func.name, func.domain
                        )));
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

                    // Define the function value for product domain
                    structure
                        .define_function_product(func_id, &tuple, value_slid)
                        .map_err(ElabError::DuplicateDefinition)?;
                }
            }
        }
    }

    // 5. Third pass: relation assertions (assert relation tuples)
    for item in &instance.body {
        if let ast::InstanceItem::RelationAssertion(term, rel_name) = &item.node {
            // Find the relation in the signature
            let rel_id = theory
                .theory
                .signature
                .lookup_rel(rel_name)
                .ok_or_else(|| ElabError::UnknownRel(rel_name.clone()))?;

            let rel = &theory.theory.signature.relations[rel_id];

            // Build the tuple of Slids from the term
            let domain = &rel.domain;
            let tuple = match (term, domain) {
                // Unary relation with simple element: `element relation;`
                (ast::Term::Path(_), DerivedSort::Product(expected_fields))
                    if expected_fields.len() == 1 =>
                {
                    let slid = resolve_instance_element(term, &name_to_slid)?;

                    // Type check
                    let elem_sort_id = structure.sorts[slid.index()];
                    if let &DerivedSort::Base(expected_sort_id) = &expected_fields[0].1
                        && elem_sort_id != expected_sort_id {
                            return Err(ElabError::DomainMismatch {
                                func_name: rel_name.clone(),
                                element_name: slid_to_name
                                    .get(&slid)
                                    .cloned()
                                    .unwrap_or_else(|| format!("slid_{}", slid)),
                                expected_sort: theory.theory.signature.sorts[expected_sort_id]
                                    .clone(),
                                actual_sort: theory.theory.signature.sorts[elem_sort_id].clone(),
                            });
                        }
                    vec![slid]
                }

                // Multi-ary relation with record: `[field: value, ...] relation;`
                (ast::Term::Record(fields), DerivedSort::Product(expected_fields)) => {
                    if fields.len() != expected_fields.len() {
                        return Err(ElabError::UnsupportedFeature(format!(
                            "relation {} expects {} fields, got {}",
                            rel_name,
                            expected_fields.len(),
                            fields.len()
                        )));
                    }

                    // Build tuple in the correct field order
                    let mut tuple = Vec::with_capacity(expected_fields.len());
                    for (expected_name, expected_sort) in expected_fields {
                        let field_value = fields
                            .iter()
                            .find(|(name, _)| name == expected_name.as_str())
                            .ok_or_else(|| {
                                ElabError::UnsupportedFeature(format!(
                                    "missing field '{}' in relation assertion",
                                    expected_name
                                ))
                            })?;

                        // Resolve the field value to a Slid
                        let slid = resolve_instance_element(&field_value.1, &name_to_slid)?;

                        // Type check: verify element sort matches field sort
                        let elem_sort_id = structure.sorts[slid.index()];
                        if let &DerivedSort::Base(expected_sort_id) = expected_sort
                            && elem_sort_id != expected_sort_id {
                                return Err(ElabError::DomainMismatch {
                                    func_name: rel_name.clone(),
                                    element_name: slid_to_name
                                        .get(&slid)
                                        .cloned()
                                        .unwrap_or_else(|| format!("slid_{}", slid)),
                                    expected_sort: theory.theory.signature.sorts[expected_sort_id]
                                        .clone(),
                                    actual_sort: theory.theory.signature.sorts[elem_sort_id].clone(),
                                });
                            }

                        tuple.push(slid);
                    }
                    tuple
                }

                // Mismatch: using simple element for non-unary relation
                (ast::Term::Path(_), DerivedSort::Product(expected_fields)) => {
                    return Err(ElabError::UnsupportedFeature(format!(
                        "relation {} has {} fields, use record syntax [field: value, ...]",
                        rel_name,
                        expected_fields.len()
                    )));
                }

                _ => {
                    return Err(ElabError::UnsupportedFeature(format!(
                        "relation {} has non-product domain {:?}",
                        rel_name, domain
                    )));
                }
            };

            // Assert the relation tuple
            structure.assert_relation(rel_id, tuple);
        }
    }

    // 6. Fourth pass: nested instances
    // For each nested instance like `initial_marking = { t : Token; ... };`
    // 1. Find the instance field declaration in the theory
    // 2. Resolve its theory type (e.g., "N Marking") with parameter substitution
    // 3. Recursively elaborate the nested instance body
    // 4. Store in the parent structure's `nested` HashMap
    for item in &instance.body {
        if let ast::InstanceItem::NestedInstance(field_name, nested_decl) = &item.node {
            // 1. Look up the instance field in the parent theory signature
            let field_idx = theory
                .theory
                .signature
                .lookup_instance_field(field_name)
                .ok_or_else(|| {
                    ElabError::UnknownVariable(format!("nested instance field: {}", field_name))
                })?;

            let instance_field = &theory.theory.signature.instance_fields[field_idx];

            // 2. Resolve the theory type with parameter substitution
            // The theory_type string is like "N Marking"
            // We need to substitute parameter names with actual instance names
            let mut resolved_theory_type = instance_field.theory_type.clone();
            for (param_name, actual_instance_name) in &resolved.arguments {
                // Simple substitution: replace param name at word boundaries
                resolved_theory_type = resolved_theory_type.replace(param_name, actual_instance_name);
            }

            // 3. Find the resolved theory
            // Parse the resolved type string to get the theory name
            // For "ExampleNet Marking", we need to get the "Marking" theory
            let nested_theory_name = resolved_theory_type
                .split_whitespace()
                .last()
                .unwrap_or(&resolved_theory_type)
                .to_string();

            let nested_theory = ctx.theories.get(&nested_theory_name).ok_or_else(|| {
                ElabError::UnknownTheory(format!(
                    "nested instance theory: {} (from field type: {})",
                    nested_theory_name, instance_field.theory_type
                ))
            })?;

            // 4. Create a new instance declaration with the resolved type
            // Build the type expression from the resolved string
            let nested_instance_decl = ast::InstanceDecl {
                theory: parse_type_expr_from_string(&resolved_theory_type)?,
                name: format!("{}_{}", instance.name, field_name),
                body: nested_decl.body.clone(),
            };

            // 5. Recursively elaborate the nested instance
            let nested_result = elaborate_instance_ctx(ctx, &nested_instance_decl)?;

            // 6. Store the nested structure using the field name as the key
            structure.nested.insert(field_name.clone(), nested_result.structure);

            // Suppress unused variable warning
            let _ = nested_theory; // Used for type checking (could add validation later)
        }
    }

    // 6. Validate totality: all functions must be defined on all elements of their domain
    // Skip this check when creating instances for chase (which will fill in missing values)
    if !skip_totality {
        validate_totality(&structure, &theory.theory.signature, &slid_to_name)?;
    }

    Ok(InstanceElaborationResult {
        structure,
        slid_to_name,
        name_to_slid,
    })
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
        ast::TypeExpr::Path(path) => {
            // Join path segments with "/" to handle qualified names like "Base/X"
            let name = path.segments.join("/");
            sig.lookup_sort(&name)
                .ok_or(ElabError::UnknownSort(name))
        }
        _ => Err(ElabError::UnsupportedFeature(format!(
            "complex sort: {:?}",
            sort_expr
        ))),
    }
}

/// Result of decomposing a function application's LHS
enum DecomposedFuncApp {
    /// Base domain: `element func` → single element
    Base { elem: Slid, func_id: FuncId },
    /// Product domain: `[x: a, y: b] func` → tuple of elements
    Product { tuple: Vec<Slid>, func_id: FuncId },
}

/// Decompose a function application term like `ab_in in/src` or `[x: u, y: u] mul`
/// Returns either Base (single element) or Product (tuple of elements) with func_id
fn decompose_func_app(
    term: &ast::Term,
    name_to_slid: &HashMap<String, Slid>,
    sig: &Signature,
) -> ElabResult<DecomposedFuncApp> {
    match term {
        ast::Term::App(base, func) => {
            // func should be a function path
            let func_id = match func.as_ref() {
                ast::Term::Path(path) => {
                    let func_name = path.to_string();
                    sig.lookup_func(&func_name)
                        .ok_or(ElabError::UnknownFunction(func_name))
                }
                _ => Err(ElabError::NotAFunction(format!("{:?}", func))),
            }?;

            // base can be either:
            // - a single element name (base domain)
            // - a record like [x: a, y: b] (product domain)
            match base.as_ref() {
                ast::Term::Record(fields) => {
                    // Product domain: [x: a, y: b] func
                    let tuple: Vec<Slid> = fields
                        .iter()
                        .map(|(_, term)| resolve_instance_element(term, name_to_slid))
                        .collect::<ElabResult<Vec<_>>>()?;
                    Ok(DecomposedFuncApp::Product { tuple, func_id })
                }
                _ => {
                    // Base domain: element func
                    let elem_slid = resolve_instance_element(base, name_to_slid)?;
                    Ok(DecomposedFuncApp::Base {
                        elem: elem_slid,
                        func_id,
                    })
                }
            }
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
        let mut missing = Vec::new();
        let func_col = &structure.functions[func_id];

        match (&func_sym.domain, func_col) {
            // Base domain with local codomain
            (DerivedSort::Base(domain_sort_id), FunctionColumn::Local(col)) => {
                for (sort_slid, opt_slid) in col.iter().enumerate() {
                    if opt_slid.is_none() {
                        let slid = Slid::from_usize(
                            structure.carriers[*domain_sort_id]
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

            // Base domain with external codomain
            (DerivedSort::Base(domain_sort_id), FunctionColumn::External(col)) => {
                for (sort_slid, opt_luid) in col.iter().enumerate() {
                    if opt_luid.is_none() {
                        let slid = Slid::from_usize(
                            structure.carriers[*domain_sort_id]
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

            // Product domain: check all tuples in the cartesian product
            (DerivedSort::Product(fields), FunctionColumn::ProductLocal { storage, .. }) => {
                // Collect carriers for each field
                let field_carriers: Vec<Vec<Slid>> = fields
                    .iter()
                    .map(|(_, ds)| match ds {
                        DerivedSort::Base(sort_id) => structure.carriers[*sort_id]
                            .iter()
                            .map(|s| Slid::from_usize(s as usize))
                            .collect(),
                        DerivedSort::Product(_) => {
                            // Nested products not yet supported
                            vec![]
                        }
                    })
                    .collect();

                // Enumerate all tuples via cartesian product
                for tuple in cartesian_product(&field_carriers) {
                    // Convert Slids to sort-local indices for storage lookup
                    let local_indices: Vec<usize> = tuple
                        .iter()
                        .map(|slid| structure.sort_local_id(*slid).index())
                        .collect();

                    if storage.get(&local_indices).is_none() {
                        // Format the missing tuple nicely
                        let tuple_str: Vec<String> = tuple
                            .iter()
                            .zip(fields.iter())
                            .map(|(slid, (field_name, _))| {
                                let elem_name = slid_to_name
                                    .get(slid)
                                    .cloned()
                                    .unwrap_or_else(|| format!("#{}", slid));
                                format!("{}: {}", field_name, elem_name)
                            })
                            .collect();
                        missing.push(format!("[{}]", tuple_str.join(", ")));
                    }
                }
            }

            // Mismatched domain/column types (shouldn't happen if init is correct)
            (DerivedSort::Base(_), FunctionColumn::ProductLocal { .. }) => {
                return Err(ElabError::UnsupportedFeature(format!(
                    "function {} has base domain but product storage",
                    func_sym.name
                )));
            }
            (DerivedSort::Product(_), FunctionColumn::Local(_) | FunctionColumn::External(_)) => {
                return Err(ElabError::UnsupportedFeature(format!(
                    "function {} has product domain but columnar storage",
                    func_sym.name
                )));
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

/// Generate cartesian product of vectors
fn cartesian_product(sets: &[Vec<Slid>]) -> Vec<Vec<Slid>> {
    if sets.is_empty() {
        return vec![vec![]]; // Single empty tuple for nullary product
    }

    let mut result = vec![vec![]];
    for set in sets {
        let mut new_result = Vec::new();
        for tuple in &result {
            for &elem in set {
                let mut new_tuple = tuple.clone();
                new_tuple.push(elem);
                new_result.push(new_tuple);
            }
        }
        result = new_result;
    }
    result
}

/// Parse a simple type expression from a string like "ExampleNet Marking"
///
/// This handles:
/// - Simple paths: "PetriNet" -> Path(["PetriNet"])
/// - Applied types: "ExampleNet Marking" -> App(Path(["ExampleNet"]), Path(["Marking"]))
fn parse_type_expr_from_string(s: &str) -> ElabResult<ast::TypeExpr> {
    let tokens: Vec<&str> = s.split_whitespace().collect();

    if tokens.is_empty() {
        return Err(ElabError::UnsupportedFeature(
            "empty type expression".to_string(),
        ));
    }

    if tokens.len() == 1 {
        // Simple path
        Ok(ast::TypeExpr::Path(ast::Path::single(
            tokens[0].to_string(),
        )))
    } else {
        // Applied type: "A B C" -> App(App(A, B), C)
        // Actually in our AST, App(base, arg) so "A B C" parses as App(App(A, B), C)
        // meaning C is applied to (A applied to B)
        let mut result = ast::TypeExpr::Path(ast::Path::single(tokens[0].to_string()));
        for &token in &tokens[1..] {
            result = ast::TypeExpr::App(
                Box::new(result),
                Box::new(ast::TypeExpr::Path(ast::Path::single(token.to_string()))),
            );
        }
        Ok(result)
    }
}
