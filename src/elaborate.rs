//! Elaboration: surface syntax → typed core representation
//!
//! This module transforms the untyped AST into the typed core representation,
//! performing name resolution and type checking along the way.

use std::collections::HashMap;
use std::rc::Rc;

use crate::ast;
use crate::core::*;
use crate::id::NumericId;

/// Elaboration errors
#[derive(Clone, Debug)]
pub enum ElabError {
    UnknownSort(String),
    UnknownTheory(String),
    UnknownFunction(String),
    UnknownRel(String),
    UnknownVariable(String),
    TypeMismatch {
        expected: DerivedSort,
        got: DerivedSort,
    },
    NotASort(String),
    NotAFunction(String),
    NotARecord(String),
    NoSuchField {
        record: String,
        field: String,
    },
    InvalidPath(String),
    DuplicateDefinition(String),
    UnsupportedFeature(String),
    PartialFunction {
        func_name: String,
        missing_elements: Vec<String>,
    },
    /// Type error in function application: element's sort doesn't match function's domain
    DomainMismatch {
        func_name: String,
        element_name: String,
        expected_sort: String,
        actual_sort: String,
    },
    /// Type error in equation: RHS sort doesn't match function's codomain
    CodomainMismatch {
        func_name: String,
        element_name: String,
        expected_sort: String,
        actual_sort: String,
    },
}

impl std::fmt::Display for ElabError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ElabError::UnknownSort(s) => write!(f, "unknown sort: {}", s),
            ElabError::UnknownTheory(s) => write!(f, "unknown theory: {}", s),
            ElabError::UnknownFunction(s) => write!(f, "unknown function: {}", s),
            ElabError::UnknownRel(s) => write!(f, "unknown relation: {}", s),
            ElabError::UnknownVariable(s) => write!(f, "unknown variable: {}", s),
            ElabError::TypeMismatch { expected, got } => {
                write!(f, "type mismatch: expected {}, got {}", expected, got)
            }
            ElabError::NotASort(s) => write!(f, "not a sort: {}", s),
            ElabError::NotAFunction(s) => write!(f, "not a function: {}", s),
            ElabError::NotARecord(s) => write!(f, "not a record type: {}", s),
            ElabError::NoSuchField { record, field } => {
                write!(f, "no field '{}' in record {}", field, record)
            }
            ElabError::InvalidPath(s) => write!(f, "invalid path: {}", s),
            ElabError::DuplicateDefinition(s) => write!(f, "duplicate definition: {}", s),
            ElabError::UnsupportedFeature(s) => write!(f, "unsupported feature: {}", s),
            ElabError::PartialFunction {
                func_name,
                missing_elements,
            } => {
                write!(
                    f,
                    "partial function '{}': missing definitions for {:?}",
                    func_name, missing_elements
                )
            }
            ElabError::DomainMismatch {
                func_name,
                element_name,
                expected_sort,
                actual_sort,
            } => {
                write!(
                    f,
                    "type error: '{}' has sort '{}', but function '{}' expects domain sort '{}'",
                    element_name, actual_sort, func_name, expected_sort
                )
            }
            ElabError::CodomainMismatch {
                func_name,
                element_name,
                expected_sort,
                actual_sort,
            } => {
                write!(
                    f,
                    "type error: '{}' has sort '{}', but function '{}' has codomain sort '{}'",
                    element_name, actual_sort, func_name, expected_sort
                )
            }
        }
    }
}

type ElabResult<T> = Result<T, ElabError>;

/// Environment for elaboration — tracks what's in scope
#[derive(Clone, Debug, Default)]
pub struct Env {
    /// Known theories, by name
    pub theories: HashMap<String, Rc<ElaboratedTheory>>,
    /// Current theory being elaborated (if any)
    pub current_theory: Option<String>,
    /// Local signature being built
    pub signature: Signature,
    /// Parameters in scope (for parameterized theories)
    pub params: Vec<(String, Rc<ElaboratedTheory>)>,
}

impl Env {
    pub fn new() -> Self {
        Self::default()
    }

    /// Resolve a path like "N/P" where N is a parameter and P is a sort in N's theory.
    ///
    /// All param sorts are copied into the local signature with qualified names (e.g., "N/P"),
    /// so we just need to look up the joined path in the current signature.
    pub fn resolve_sort_path(&self, path: &ast::Path) -> ElabResult<DerivedSort> {
        // Join all segments with "/" — this handles both simple names like "F"
        // and qualified names like "N/P"
        let full_name = path.segments.join("/");
        if let Some(id) = self.signature.lookup_sort(&full_name) {
            return Ok(DerivedSort::Base(id));
        }
        Err(ElabError::UnknownSort(full_name))
    }

    /// Resolve a function path like "N/in/src" or "F/of".
    ///
    /// All param functions are copied into the local signature with qualified names,
    /// so we just need to look up the joined path.
    pub fn resolve_func_path(&self, path: &ast::Path) -> ElabResult<FuncId> {
        let full_name = path.segments.join("/");
        if let Some(id) = self.signature.lookup_func(&full_name) {
            return Ok(id);
        }
        Err(ElabError::UnknownFunction(full_name))
    }
}

/// Elaborate a type expression into a DerivedSort
pub fn elaborate_type(env: &Env, ty: &ast::TypeExpr) -> ElabResult<DerivedSort> {
    match ty {
        ast::TypeExpr::Sort => {
            // "Sort" is the kind of sorts, not a sort itself
            Err(ElabError::NotASort(
                "Sort is a kind, not a type".to_string(),
            ))
        }
        ast::TypeExpr::Prop => {
            // "Prop" is the kind for relation codomains, not a sort itself
            Err(ElabError::NotASort(
                "Prop is a kind, not a type".to_string(),
            ))
        }
        ast::TypeExpr::Path(path) => env.resolve_sort_path(path),
        ast::TypeExpr::Record(fields) => {
            let elab_fields: Result<Vec<_>, _> = fields
                .iter()
                .map(|(name, ty)| elaborate_type(env, ty).map(|s| (name.clone(), s)))
                .collect();
            Ok(DerivedSort::Product(elab_fields?))
        }
        ast::TypeExpr::App(_, _) => {
            // Type application — for things like "N Marking"
            // This is used for parameterized types, which we'll handle later
            Err(ElabError::UnsupportedFeature(
                "type application".to_string(),
            ))
        }
        ast::TypeExpr::Arrow(_, _) => {
            // Function types aren't sorts in this sense
            Err(ElabError::NotASort("arrow types are not sorts".to_string()))
        }
        ast::TypeExpr::Instance(_) => {
            // "T instance" is the type of instances of theory T
            Err(ElabError::UnsupportedFeature(
                "instance types in sort position".to_string(),
            ))
        }
    }
}

/// Elaborate a term in a given context
pub fn elaborate_term(env: &Env, ctx: &Context, term: &ast::Term) -> ElabResult<Term> {
    match term {
        ast::Term::Path(path) => {
            if path.segments.len() == 1 {
                // Simple variable
                let name = &path.segments[0];
                if let Some((_, sort)) = ctx.lookup(name) {
                    return Ok(Term::Var(name.clone(), sort.clone()));
                }
                return Err(ElabError::UnknownVariable(name.clone()));
            }
            // Qualified path — could be a variable or a function reference
            // For now, treat as variable lookup failure
            Err(ElabError::UnknownVariable(path.to_string()))
        }
        ast::Term::App(base, func) => {
            // In surface syntax, application is postfix: `x f` means apply f to x
            // So App(base, func) where base is the argument and func is the function
            // First, elaborate the base (the argument)
            let elab_arg = elaborate_term(env, ctx, base)?;
            let arg_sort = elab_arg.sort(&env.signature);

            // Then figure out what the function is
            match func.as_ref() {
                ast::Term::Path(path) => {
                    let func_id = env.resolve_func_path(path)?;
                    let func_sym = &env.signature.functions[func_id];

                    // Type check: argument sort must match function domain
                    if arg_sort != func_sym.domain {
                        return Err(ElabError::TypeMismatch {
                            expected: func_sym.domain.clone(),
                            got: arg_sort,
                        });
                    }

                    Ok(Term::App(func_id, Box::new(elab_arg)))
                }
                _ => {
                    // Higher-order application — not supported yet
                    Err(ElabError::UnsupportedFeature(
                        "higher-order application".to_string(),
                    ))
                }
            }
        }
        ast::Term::Project(base, field) => {
            let elab_base = elaborate_term(env, ctx, base)?;
            Ok(Term::Project(Box::new(elab_base), field.clone()))
        }
        ast::Term::Record(fields) => {
            let elab_fields: Result<Vec<_>, _> = fields
                .iter()
                .map(|(name, term)| elaborate_term(env, ctx, term).map(|t| (name.clone(), t)))
                .collect();
            Ok(Term::Record(elab_fields?))
        }
    }
}

/// Elaborate a formula
pub fn elaborate_formula(env: &Env, ctx: &Context, formula: &ast::Formula) -> ElabResult<Formula> {
    match formula {
        ast::Formula::True => Ok(Formula::True),
        ast::Formula::False => Ok(Formula::False),
        ast::Formula::Eq(lhs, rhs) => {
            let elab_lhs = elaborate_term(env, ctx, lhs)?;
            let elab_rhs = elaborate_term(env, ctx, rhs)?;

            // Type check: both sides must have the same sort
            let lhs_sort = elab_lhs.sort(&env.signature);
            let rhs_sort = elab_rhs.sort(&env.signature);
            if lhs_sort != rhs_sort {
                return Err(ElabError::TypeMismatch {
                    expected: lhs_sort,
                    got: rhs_sort,
                });
            }

            Ok(Formula::Eq(elab_lhs, elab_rhs))
        }
        ast::Formula::And(conjuncts) => {
            let elab: Result<Vec<_>, _> = conjuncts
                .iter()
                .map(|f| elaborate_formula(env, ctx, f))
                .collect();
            Ok(Formula::Conj(elab?))
        }
        ast::Formula::Or(disjuncts) => {
            let elab: Result<Vec<_>, _> = disjuncts
                .iter()
                .map(|f| elaborate_formula(env, ctx, f))
                .collect();
            Ok(Formula::Disj(elab?))
        }
        ast::Formula::Exists(vars, body) => {
            // Extend context with quantified variables
            let mut extended_ctx = ctx.clone();
            for qv in vars {
                let sort = elaborate_type(env, &qv.ty)?;
                for name in &qv.names {
                    extended_ctx = extended_ctx.extend(name.clone(), sort.clone());
                }
            }
            let elab_body = elaborate_formula(env, &extended_ctx, body)?;

            // Build nested existentials (one for each variable)
            let mut result = elab_body;
            for qv in vars.iter().rev() {
                let sort = elaborate_type(env, &qv.ty)?;
                for name in qv.names.iter().rev() {
                    result = Formula::Exists(name.clone(), sort.clone(), Box::new(result));
                }
            }
            Ok(result)
        }
        ast::Formula::RelApp(rel_name, arg) => {
            // Look up the relation
            let rel_id = env
                .signature
                .lookup_rel(rel_name)
                .ok_or_else(|| ElabError::UnknownRel(rel_name.clone()))?;

            // Elaborate the argument
            let elab_arg = elaborate_term(env, ctx, arg)?;

            // Type check: argument must match relation domain
            let rel_sym = &env.signature.relations[rel_id];
            let arg_sort = elab_arg.sort(&env.signature);
            if arg_sort != rel_sym.domain {
                return Err(ElabError::TypeMismatch {
                    expected: rel_sym.domain.clone(),
                    got: arg_sort,
                });
            }

            Ok(Formula::Rel(rel_id, elab_arg))
        }
    }
}

/// Remap a DerivedSort from one signature namespace to another.
///
/// When copying sorts/functions from a param theory into the local signature,
/// the sort IDs need to be remapped. For example, if PetriNet has sort P at id=0,
/// and we copy it as "N/P" into local signature at id=2, then any DerivedSort::Base(0)
/// needs to become DerivedSort::Base(2).
fn remap_derived_sort(
    sort: &DerivedSort,
    source_sig: &Signature,
    target_sig: &Signature,
    param_name: &str,
) -> DerivedSort {
    match sort {
        DerivedSort::Base(source_id) => {
            // Look up the sort name in the source signature
            let sort_name = &source_sig.sorts[*source_id];
            // Find the corresponding qualified name in target signature
            let qualified_name = format!("{}/{}", param_name, sort_name);
            let target_id = target_sig
                .lookup_sort(&qualified_name)
                .expect("qualified sort should have been added");
            DerivedSort::Base(target_id)
        }
        DerivedSort::Product(fields) => {
            let remapped_fields = fields
                .iter()
                .map(|(name, s)| {
                    (
                        name.clone(),
                        remap_derived_sort(s, source_sig, target_sig, param_name),
                    )
                })
                .collect();
            DerivedSort::Product(remapped_fields)
        }
    }
}

/// Elaborate a theory declaration
pub fn elaborate_theory(env: &mut Env, theory: &ast::TheoryDecl) -> ElabResult<ElaboratedTheory> {
    // Set up the environment for this theory
    let mut local_env = env.clone();
    local_env.current_theory = Some(theory.name.clone());
    local_env.signature = Signature::new();

    // Process parameters
    // When we have `theory (N : PetriNet instance) Trace { ... }`, we need to:
    // 1. Copy all sorts from PetriNet into local signature with qualified names (N/P, N/T, etc.)
    // 2. Copy all functions with qualified names (N/in/src, etc.)
    // This ensures all sort/func IDs are in a single namespace.
    let mut params = Vec::new();
    for param in &theory.params {
        match &param.ty {
            // "T instance" parameters — the theory depends on an instance of another theory
            ast::TypeExpr::Instance(inner) => {
                if let ast::TypeExpr::Path(path) = inner.as_ref() {
                    let theory_name = path.to_string();
                    if let Some(base_theory) = env.theories.get(&theory_name) {
                        // Copy all sorts from param theory into local signature with qualified names
                        for sort_name in &base_theory.theory.signature.sorts {
                            let qualified_name = format!("{}/{}", param.name, sort_name);
                            local_env.signature.add_sort(qualified_name);
                        }

                        // Copy all functions from param theory with qualified names
                        for func in &base_theory.theory.signature.functions {
                            let qualified_name = format!("{}/{}", param.name, func.name);
                            // Remap domain and codomain to use local signature's sort IDs
                            let domain = remap_derived_sort(
                                &func.domain,
                                &base_theory.theory.signature,
                                &local_env.signature,
                                &param.name,
                            );
                            let codomain = remap_derived_sort(
                                &func.codomain,
                                &base_theory.theory.signature,
                                &local_env.signature,
                                &param.name,
                            );
                            local_env
                                .signature
                                .add_function(qualified_name, domain, codomain);
                        }

                        // Copy all relations from param theory with qualified names
                        for rel in &base_theory.theory.signature.relations {
                            let qualified_name = format!("{}/{}", param.name, rel.name);
                            let domain = remap_derived_sort(
                                &rel.domain,
                                &base_theory.theory.signature,
                                &local_env.signature,
                                &param.name,
                            );
                            local_env.signature.add_relation(qualified_name, domain);
                        }

                        params.push(TheoryParam {
                            name: param.name.clone(),
                            theory_name: theory_name.clone(),
                        });
                        local_env
                            .params
                            .push((param.name.clone(), base_theory.clone()));
                    } else {
                        return Err(ElabError::UnknownTheory(theory_name));
                    }
                }
            }
            // "Sort" parameters — the theory is parameterized over a sort
            ast::TypeExpr::Sort => {
                // Add the parameter as a sort in the local signature
                local_env.signature.add_sort(param.name.clone());
                // Also record it as a "sort parameter" for the theory
                params.push(TheoryParam {
                    name: param.name.clone(),
                    theory_name: "Sort".to_string(), // Special marker
                });
            }
            _ => {
                return Err(ElabError::UnsupportedFeature(format!(
                    "parameter type {:?}",
                    param.ty
                )));
            }
        }
    }

    // First pass: collect all sorts
    for item in &theory.body {
        if let ast::TheoryItem::Sort(name) = &item.node {
            local_env.signature.add_sort(name.clone());
        }
    }

    // Second pass: collect all functions and relations
    for item in &theory.body {
        match &item.node {
            ast::TheoryItem::Function(f) => {
                // Check if codomain is Prop — if so, this is a relation declaration
                if matches!(f.codomain, ast::TypeExpr::Prop) {
                    let domain = elaborate_type(&local_env, &f.domain)?;
                    local_env
                        .signature
                        .add_relation(f.name.to_string(), domain);
                } else {
                    let domain = elaborate_type(&local_env, &f.domain)?;
                    let codomain = elaborate_type(&local_env, &f.codomain)?;
                    local_env
                        .signature
                        .add_function(f.name.to_string(), domain, codomain);
                }
            }
            // Legacy: A Field with a Record type is a relation declaration
            // (kept for backwards compatibility, may remove later)
            ast::TheoryItem::Field(name, ty @ ast::TypeExpr::Record(_)) => {
                let domain = elaborate_type(&local_env, ty)?;
                local_env.signature.add_relation(name.clone(), domain);
            }
            _ => {}
        }
    }

    // Third pass: elaborate axioms
    let mut axioms = Vec::new();
    for item in &theory.body {
        if let ast::TheoryItem::Axiom(ax) = &item.node {
            // Build context from quantified variables
            let mut ctx = Context::new();
            for qv in &ax.quantified {
                let sort = elaborate_type(&local_env, &qv.ty)?;
                for name in &qv.names {
                    ctx = ctx.extend(name.clone(), sort.clone());
                }
            }

            // Elaborate hypothesis (conjunction of all hypotheses)
            let premise = if ax.hypotheses.is_empty() {
                Formula::True
            } else {
                let hyps: Result<Vec<_>, _> = ax
                    .hypotheses
                    .iter()
                    .map(|h| elaborate_formula(&local_env, &ctx, h))
                    .collect();
                Formula::Conj(hyps?)
            };

            // Elaborate conclusion
            let conclusion = elaborate_formula(&local_env, &ctx, &ax.conclusion)?;

            axioms.push(Sequent {
                context: ctx,
                premise,
                conclusion,
            });
        }
    }

    Ok(ElaboratedTheory {
        params,
        theory: Theory {
            name: theory.name.clone(),
            signature: local_env.signature,
            axioms,
        },
    })
}

// ============ Instance Elaboration ============

use crate::id::Slid;

/// Elaborate an instance declaration into a Structure
pub fn elaborate_instance(
    env: &Env,
    instance: &ast::InstanceDecl,
    universe: &mut crate::universe::Universe,
) -> ElabResult<Structure> {
    // 1. Resolve the theory type (handles parameterized types like `ExampleNet ReachabilityProblem`)
    let resolved = resolve_instance_type(env, &instance.theory)?;
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

    // For parameterized theories, we note the bindings but don't import elements yet.
    // Cross-instance references (like `ExampleNet/A`) will be handled when we have
    // access to Workspace. For now, we just validate the parameter count.
    for (param_name, instance_name) in &resolved.arguments {
        // TODO: When Workspace is available, import elements from param instances
        // For now, just note that we have these bindings
        let _ = (param_name, instance_name);
    }

    // 3. First pass: create elements
    for item in &instance.body {
        if let ast::InstanceItem::Element(name, sort_expr) = &item.node {
            // Resolve the sort
            let sort_id = resolve_instance_sort(&theory.theory.signature, sort_expr)?;

            // Add element to structure (returns Slid, Luid)
            let (slid, _luid) = structure.add_element(universe, sort_id);
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
                && elem_sort_id != *expected_domain {
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
                && value_sort_id != *expected_codomain {
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
fn resolve_instance_type(
    env: &Env,
    ty: &ast::TypeExpr,
) -> ElabResult<ResolvedInstanceType> {
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
fn resolve_instance_element(
    term: &ast::Term,
    name_to_slid: &HashMap<String, Slid>,
) -> ElabResult<Slid> {
    match term {
        ast::Term::Path(path) if path.segments.len() == 1 => {
            let name = &path.segments[0];
            name_to_slid
                .get(name)
                .copied()
                .ok_or_else(|| ElabError::UnknownVariable(name.clone()))
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
        for (sort_slid, opt_slid) in structure.functions[func_id].iter().enumerate() {
            if opt_slid.is_none() {
                // Reverse lookup: sort_slid → slid
                // Find the slid that has this sort_slid in this domain sort
                let slid = Slid::from_usize(
                    structure.carriers[domain_sort_id]
                        .select(sort_slid as u64)
                        .expect("sort_slid should be valid") as usize
                );
                // Look up element name if available, otherwise fallback to slid
                let name = slid_to_name
                    .get(&slid)
                    .cloned()
                    .unwrap_or_else(|| format!("element#{}", slid));
                missing.push(name);
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

// Unit tests moved to tests/unit_elaborate.rs
