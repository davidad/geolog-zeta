//! Instance elaboration.

use std::collections::HashMap;
use std::rc::Rc;

use crate::ast;
use crate::core::*;
use crate::id::{NumericId, Slid};
use crate::query::chase::{chase_fixpoint, compile_theory_axioms_lenient};
use crate::tensor::check_theory_axioms;
use crate::universe::Universe;

use super::env::Env;
use super::error::{ElabError, ElabResult};

// Re-use remapping utilities from theory elaboration
use super::theory::{collect_type_args_from_theory_type, build_param_subst, remap_sort_for_param_import};

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
    /// The base theory name this instance is of (e.g., "ReachabilityProblem")
    pub theory_name: String,
    /// The full theory type string (e.g., "ExampleNet ReachabilityProblem")
    /// This is needed to compute parameter substitutions when importing elements.
    pub theory_type: String,
    /// Map from element names to Slids
    pub element_names: HashMap<String, Slid>,
    /// Reverse map from Slids to names
    pub slid_to_name: HashMap<Slid, String>,
}

impl InstanceEntry {
    /// Create a new instance entry
    pub fn new(structure: Structure, theory_name: String, theory_type: String) -> Self {
        Self {
            structure,
            theory_name,
            theory_type,
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
    // If needs_chase is set, we skip totality (chase will fill in missing values)
    elaborate_instance_ctx_inner(ctx, instance, instance.needs_chase)
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

    for (param_name, arg_value) in &resolved.arguments {
        // Case 1: argument is an instance name (e.g., "ExampleNet" for N : PetriNet instance)
        if let Some(param_entry) = ctx.instances.get(arg_value) {
            // Get the param theory to know sort mappings
            let param_theory_name = &param_entry.theory_name;
            if let Some(param_theory) = ctx.theories.get(param_theory_name) {
                // Build parameter substitution map for this param instance
                // This tells us how to remap sorts from the param instance to local sorts.
                //
                // For example, if param_entry is `problem0 : ExampleNet ReachabilityProblem`:
                // - param_theory = ReachabilityProblem, which has param (N : PetriNet)
                // - type_args = ["ExampleNet"] (from problem0's theory_type)
                // - param_subst = {"N" -> "ExampleNet"}
                let type_args = collect_type_args_from_theory_type(&param_entry.theory_type);
                let param_subst = build_param_subst(param_theory, &type_args);

                // For each element in the param instance, import it
                for (&slid, elem_name) in &param_entry.slid_to_name {
                    // Get the element's sort in the param instance
                    let param_sort_id = param_entry.structure.sorts[slid.index()];
                    let param_sort_name = &param_theory.theory.signature.sorts[param_sort_id];

                    // Map to local sort using parameter substitution
                    // This handles cases like "N/P" in problem0 -> "N/P" in solution0
                    // (not "RP/N/P" which doesn't exist)
                    let local_sort_name = remap_sort_for_param_import(
                        param_sort_name,
                        param_name,
                        &param_subst,
                        &resolved.arguments,
                    );
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
                    // Also register unqualified "elemname" for convenient access
                    // (local elements declared later will shadow these if there's a collision)
                    let qualified_param = format!("{}/{}", param_name, elem_name);
                    let qualified_instance = format!("{}/{}", arg_value, elem_name);

                    name_to_slid.insert(elem_name.clone(), local_slid);
                    name_to_slid.insert(qualified_param.clone(), local_slid);
                    name_to_slid.insert(qualified_instance.clone(), local_slid);
                    slid_to_name.insert(local_slid, qualified_instance);

                    // Record mapping for function value import
                    param_slid_to_local.insert((arg_value.clone(), slid), local_slid);
                }
            }
        }
        // Case 2: argument is a sort path like "As/a" (for Sort params)
        // Parse as InstanceName/SortName and import elements of that sort
        else if let Some((source_instance_name, source_sort_name)) = arg_value.split_once('/') {
            if let Some(source_entry) = ctx.instances.get(source_instance_name) {
                let source_theory_name = &source_entry.theory_name;
                if let Some(source_theory) = ctx.theories.get(source_theory_name) {
                    // Find the sort ID in the source theory
                    if let Some(source_sort_id) = source_theory.theory.signature.lookup_sort(source_sort_name) {
                        // Import elements of this sort
                        for (&slid, elem_name) in &source_entry.slid_to_name {
                            let elem_sort_id = source_entry.structure.sorts[slid.index()];
                            if elem_sort_id == source_sort_id {
                                // Map to local sort (param_name is the local sort name, e.g., "X")
                                let local_sort_id = theory
                                    .theory
                                    .signature
                                    .lookup_sort(param_name)
                                    .ok_or_else(|| ElabError::UnknownSort(param_name.clone()))?;

                                // Get the Luid for this element
                                let luid = source_entry.structure.get_luid(slid);

                                // Add to local structure with the SAME Luid
                                let local_slid = structure.add_element_with_luid(luid, local_sort_id);

                                // Register names
                                let qualified_source = format!("{}/{}", source_instance_name, elem_name);

                                name_to_slid.insert(elem_name.clone(), local_slid);
                                name_to_slid.insert(qualified_source.clone(), local_slid);
                                slid_to_name.insert(local_slid, qualified_source.clone());

                                // Record mapping for function value import
                                param_slid_to_local.insert((source_instance_name.to_string(), slid), local_slid);
                            }
                        }
                    }
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
    // Extract both domain and codomain info for each function
    let func_infos: Vec<FunctionFullInfo> = theory
        .theory
        .signature
        .functions
        .iter()
        .map(|func| {
            let domain = match &func.domain {
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
            };
            let codomain = match &func.codomain {
                DerivedSort::Base(id) => FunctionCodomainInfo::Local(*id),
                DerivedSort::Product(fields) => {
                    let field_names: Vec<String> = fields.iter().map(|(name, _)| name.clone()).collect();
                    let field_sorts: Vec<SortId> = fields
                        .iter()
                        .filter_map(|(_, ds)| match ds {
                            DerivedSort::Base(id) => Some(*id),
                            DerivedSort::Product(_) => None, // Nested products not supported
                        })
                        .collect();
                    FunctionCodomainInfo::Product { field_names, field_sorts }
                }
            };
            FunctionFullInfo { domain, codomain }
        })
        .collect();
    structure.init_functions_complete(&func_infos);

    // 3c. Import function values from param instances
    // For each param (N, ExampleNet), for each function in param theory (src, tgt),
    // import the function values using the local func name (N/src, N/tgt).
    for (param_name, instance_name) in &resolved.arguments {
        if let Some(param_entry) = ctx.instances.get(instance_name) {
            let param_theory_name = &param_entry.theory_name;
            if let Some(param_theory) = ctx.theories.get(param_theory_name) {
                // Build parameter substitution map (same as for element import)
                let type_args = collect_type_args_from_theory_type(&param_entry.theory_type);
                let param_subst = build_param_subst(param_theory, &type_args);

                // For each function in the param theory
                for (param_func_id, param_func) in
                    param_theory.theory.signature.functions.iter().enumerate()
                {
                    // Find the corresponding local function using the same remapping logic
                    let local_func_name = remap_sort_for_param_import(
                        &param_func.name,
                        param_name,
                        &param_subst,
                        &resolved.arguments,
                    );
                    let local_func_id = match theory.theory.signature.lookup_func(&local_func_name) {
                        Some(id) => id,
                        None => {
                            // Function might be from a shared param and already imported
                            // (e.g., N/in/src when N is shared between params)
                            continue;
                        }
                    };

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

                    // Check if codomain is a product (needs Record RHS) or base (needs element RHS)
                    match &func.codomain {
                        DerivedSort::Base(expected_codomain) => {
                            // Base codomain: resolve RHS to single element
                            let value_slid = resolve_instance_element(rhs, &name_to_slid)?;
                            let value_sort_id = structure.sorts[value_slid.index()];
                            if value_sort_id != *expected_codomain {
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
                        DerivedSort::Product(codomain_fields) => {
                            // Product codomain: RHS must be a Record
                            let rhs_fields = match rhs {
                                ast::Term::Record(fields) => fields,
                                _ => return Err(ElabError::UnsupportedFeature(format!(
                                    "function {} has product codomain, RHS must be a record literal like [field1: v1, field2: v2], got {:?}",
                                    func.name, rhs
                                ))),
                            };

                            // Resolve each field value and type-check
                            let mut codomain_values: Vec<(&str, Slid)> = Vec::with_capacity(rhs_fields.len());
                            for (field_name, field_term) in rhs_fields {
                                // Find the expected sort for this field
                                let expected_sort = codomain_fields.iter()
                                    .find(|(name, _)| name == field_name)
                                    .ok_or_else(|| ElabError::UnsupportedFeature(format!(
                                        "unknown field '{}' in codomain of function {} (expected: {:?})",
                                        field_name, func.name,
                                        codomain_fields.iter().map(|(n, _)| n).collect::<Vec<_>>()
                                    )))?;

                                let value_slid = resolve_instance_element(field_term, &name_to_slid)?;
                                let value_sort_id = structure.sorts[value_slid.index()];

                                if let DerivedSort::Base(expected_sort_id) = &expected_sort.1
                                    && value_sort_id != *expected_sort_id {
                                        return Err(ElabError::CodomainMismatch {
                                            func_name: func.name.clone(),
                                            element_name: format!("field '{}': {}", field_name,
                                                slid_to_name.get(&value_slid).cloned().unwrap_or_else(|| format!("slid_{}", value_slid))),
                                            expected_sort: theory.theory.signature.sorts[*expected_sort_id].clone(),
                                            actual_sort: theory.theory.signature.sorts[value_sort_id].clone(),
                                        });
                                    }

                                codomain_values.push((field_name.as_str(), value_slid));
                            }

                            // Define the product codomain function value
                            structure
                                .define_function_product_codomain(func_id, elem, &codomain_values)
                                .map_err(ElabError::DuplicateDefinition)?;
                        }
                    }
                }

                DecomposedFuncApp::Product { tuple, func_id } => {
                    let func = &theory.theory.signature.functions[func_id];

                    // Type checking: verify tuple elements match product domain fields
                    if let DerivedSort::Product(domain_fields) = &func.domain {
                        if tuple.len() != domain_fields.len() {
                            return Err(ElabError::UnsupportedFeature(format!(
                                "product domain arity mismatch: expected {}, got {}",
                                domain_fields.len(),
                                tuple.len()
                            )));
                        }

                        for (slid, (field_name, field_sort)) in tuple.iter().zip(domain_fields.iter()) {
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

                    // Handle codomain: base vs product
                    match &func.codomain {
                        DerivedSort::Base(expected_codomain) => {
                            // Resolve RHS to single element
                            let value_slid = resolve_instance_element(rhs, &name_to_slid)?;
                            let value_sort_id = structure.sorts[value_slid.index()];
                            if value_sort_id != *expected_codomain {
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
                        DerivedSort::Product(_) => {
                            // Product domain with product codomain: not yet supported
                            return Err(ElabError::UnsupportedFeature(format!(
                                "function {} has both product domain and product codomain (not yet supported)",
                                func.name
                            )));
                        }
                    }
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
            // Use word-boundary aware replacement to avoid replacing "T" in "Token"
            let resolved_theory_type = {
                let mut parts: Vec<String> = instance_field
                    .theory_type
                    .split_whitespace()
                    .map(|s| s.to_string())
                    .collect();
                for (param_name, actual_instance_name) in &resolved.arguments {
                    for part in &mut parts {
                        if part == param_name {
                            *part = actual_instance_name.clone();
                        }
                    }
                }
                parts.join(" ")
            };

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
                needs_chase: false, // Nested instances don't separately chase
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

    // 7. Run chase if requested (fills in missing values according to axioms)
    if instance.needs_chase {
        // Use lenient compilation: skip axioms that can't be compiled
        // (e.g., those with complex term applications in premises)
        let chase_rules = compile_theory_axioms_lenient(theory.as_ref());

        if !chase_rules.is_empty() {
            const MAX_CHASE_ITERATIONS: usize = 1000;
            chase_fixpoint(&chase_rules, &mut structure, ctx.universe, &theory.theory.signature, MAX_CHASE_ITERATIONS)
                .map_err(|e| ElabError::ChaseFailed(e.to_string()))?;
        }
    }

    // 8. Check axioms - all instances must satisfy the theory's axioms
    let axioms: Vec<_> = theory.theory.axioms.clone();
    let violations = check_theory_axioms(&axioms, &structure, &theory.theory.signature);

    if !violations.is_empty() {
        // Report the first violation (could be extended to report all)
        let (axiom_idx, violation_list) = &violations[0];
        return Err(ElabError::AxiomViolation {
            axiom_index: *axiom_idx,
            axiom_name: Some(format!("axiom_{}", axiom_idx)),
            num_violations: violation_list.len(),
        });
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
/// With concatenative parsing, tokens are in order: [arg1, arg2, ..., theory_name]
/// The last path token is the theory name, earlier ones are arguments.
fn resolve_instance_type(env: &Env, ty: &ast::TypeExpr) -> ElabResult<ResolvedInstanceType> {
    use crate::ast::TypeToken;

    // Collect all path tokens (the theory and its arguments)
    let paths: Vec<String> = ty
        .tokens
        .iter()
        .filter_map(|t| match t {
            TypeToken::Path(p) => Some(p.to_string()),
            _ => None,
        })
        .collect();

    if paths.is_empty() {
        return Err(ElabError::TypeExprError(
            "no theory name in type expression".to_string(),
        ));
    }

    // Last path is the theory name
    let theory_name = paths.last().unwrap().clone();

    // Earlier paths are arguments (in order)
    let args: Vec<String> = paths[..paths.len() - 1].to_vec();

    // Look up the theory to get parameter names
    let theory = env
        .theories
        .get(&theory_name)
        .ok_or_else(|| ElabError::UnknownTheory(theory_name.clone()))?;

    // Match up arguments with parameters
    if args.len() != theory.params.len() {
        return Err(ElabError::NotEnoughArgs {
            name: theory_name,
            expected: theory.params.len(),
            got: args.len(),
        });
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

/// Resolve a sort expression within an instance (using the theory's signature)
fn resolve_instance_sort(sig: &Signature, sort_expr: &ast::TypeExpr) -> ElabResult<SortId> {
    use crate::ast::TypeToken;

    // For sort expressions, we expect a single path token
    if let Some(path) = sort_expr.as_single_path() {
        let name = path.to_string();
        sig.lookup_sort(&name)
            .ok_or(ElabError::UnknownSort(name))
    } else {
        // Check if there's any path token at all
        for token in &sort_expr.tokens {
            if let TypeToken::Path(path) = token {
                let name = path.to_string();
                return sig
                    .lookup_sort(&name)
                    .ok_or(ElabError::UnknownSort(name));
            }
        }
        Err(ElabError::TypeExprError(format!(
            "no path in sort expression: {:?}",
            sort_expr
        )))
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

            // Base domain with product codomain: check all field columns
            (DerivedSort::Base(domain_sort_id), FunctionColumn::ProductCodomain { field_columns, field_names, .. }) => {
                // For product codomains, a value is defined if ALL fields are defined
                let carrier_size = structure.carrier_size(*domain_sort_id);
                for sort_slid in 0..carrier_size {
                    // Check if any field is undefined for this element
                    let all_defined = field_columns.iter().all(|col| {
                        col.get(sort_slid)
                            .and_then(|opt| crate::id::get_slid(*opt))
                            .is_some()
                    });
                    if !all_defined {
                        let slid = Slid::from_usize(
                            structure.carriers[*domain_sort_id]
                                .select(sort_slid as u64)
                                .expect("sort_slid should be valid") as usize,
                        );
                        let name = slid_to_name
                            .get(&slid)
                            .cloned()
                            .unwrap_or_else(|| format!("element#{}", slid));
                        // Find which fields are missing
                        let missing_fields: Vec<_> = field_columns.iter()
                            .zip(field_names.iter())
                            .filter(|(col, _)| {
                                col.get(sort_slid)
                                    .and_then(|opt| crate::id::get_slid(*opt))
                                    .is_none()
                            })
                            .map(|(_, name)| name.as_str())
                            .collect();
                        missing.push(format!("{} (fields: {:?})", name, missing_fields));
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
            (DerivedSort::Product(_), FunctionColumn::ProductCodomain { .. }) => {
                return Err(ElabError::UnsupportedFeature(format!(
                    "function {} has product domain with product codomain (not yet supported)",
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
/// With concatenative parsing, this just creates a flat list of path tokens.
fn parse_type_expr_from_string(s: &str) -> ElabResult<ast::TypeExpr> {
    use crate::ast::TypeToken;

    let tokens: Vec<&str> = s.split_whitespace().collect();

    if tokens.is_empty() {
        return Err(ElabError::TypeExprError(
            "empty type expression".to_string(),
        ));
    }

    // Simply create a TypeToken::Path for each token
    let type_tokens: Vec<TypeToken> = tokens
        .iter()
        .map(|&t| TypeToken::Path(ast::Path::single(t.to_string())))
        .collect();

    Ok(ast::TypeExpr { tokens: type_tokens })
}
