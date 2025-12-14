//! Elaboration: surface syntax → typed core representation
//!
//! This module transforms the untyped AST into the typed core representation,
//! performing name resolution and type checking along the way.

use std::collections::HashMap;
use std::rc::Rc;

use crate::ast;
use crate::core::*;

/// Elaboration errors
#[derive(Clone, Debug)]
pub enum ElabError {
    UnknownSort(String),
    UnknownFunction(String),
    UnknownVariable(String),
    TypeMismatch { expected: DerivedSort, got: DerivedSort },
    NotASort(String),
    NotAFunction(String),
    NotARecord(String),
    NoSuchField { record: String, field: String },
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
            ElabError::UnknownFunction(s) => write!(f, "unknown function: {}", s),
            ElabError::UnknownVariable(s) => write!(f, "unknown variable: {}", s),
            ElabError::TypeMismatch { expected, got } =>
                write!(f, "type mismatch: expected {}, got {}", expected, got),
            ElabError::NotASort(s) => write!(f, "not a sort: {}", s),
            ElabError::NotAFunction(s) => write!(f, "not a function: {}", s),
            ElabError::NotARecord(s) => write!(f, "not a record type: {}", s),
            ElabError::NoSuchField { record, field } =>
                write!(f, "no field '{}' in record {}", field, record),
            ElabError::InvalidPath(s) => write!(f, "invalid path: {}", s),
            ElabError::DuplicateDefinition(s) => write!(f, "duplicate definition: {}", s),
            ElabError::UnsupportedFeature(s) => write!(f, "unsupported feature: {}", s),
            ElabError::PartialFunction { func_name, missing_elements } => {
                write!(f, "partial function '{}': missing definitions for {:?}", func_name, missing_elements)
            }
            ElabError::DomainMismatch { func_name, element_name, expected_sort, actual_sort } => {
                write!(f, "type error: '{}' has sort '{}', but function '{}' expects domain sort '{}'",
                    element_name, actual_sort, func_name, expected_sort)
            }
            ElabError::CodomainMismatch { func_name, element_name, expected_sort, actual_sort } => {
                write!(f, "type error: '{}' has sort '{}', but function '{}' has codomain sort '{}'",
                    element_name, actual_sort, func_name, expected_sort)
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

    /// Resolve a path like "N/P" where N is a parameter and P is a sort in N's theory
    pub fn resolve_sort_path(&self, path: &ast::Path) -> ElabResult<DerivedSort> {
        if path.segments.len() == 1 {
            // Simple name — look in current signature
            let name = &path.segments[0];
            if let Some(id) = self.signature.lookup_sort(name) {
                return Ok(DerivedSort::Base(id));
            }
            return Err(ElabError::UnknownSort(name.clone()));
        }

        // Qualified path — first segment should be a parameter name
        let param_name = &path.segments[0];
        let param_theory = self.params.iter()
            .find(|(n, _)| n == param_name)
            .map(|(_, t)| t.clone())
            .ok_or_else(|| ElabError::InvalidPath(path.to_string()))?;

        // Rest of path is within that theory
        let rest = &path.segments[1..];
        if rest.len() == 1 {
            let sort_name = &rest[0];
            if let Some(id) = param_theory.theory.signature.lookup_sort(sort_name) {
                // Return a sort reference — but we need to track that it's from a parameter
                // For now, just return a placeholder
                // TODO: proper handling of parameterized sorts
                return Ok(DerivedSort::Base(id));
            }
            return Err(ElabError::UnknownSort(format!("{}/{}", param_name, sort_name)));
        }

        Err(ElabError::InvalidPath(path.to_string()))
    }

    /// Resolve a function path
    pub fn resolve_func_path(&self, path: &ast::Path) -> ElabResult<FuncId> {
        if path.segments.len() == 1 {
            let name = &path.segments[0];
            if let Some(id) = self.signature.lookup_func(name) {
                return Ok(id);
            }
            return Err(ElabError::UnknownFunction(name.clone()));
        }

        // Qualified path — could be param/func or current/qualified/func
        // For now, try joining with / and looking up
        let full_name = path.segments.join("/");
        if let Some(id) = self.signature.lookup_func(&full_name) {
            return Ok(id);
        }

        // Try looking in parameter theories
        let param_name = &path.segments[0];
        if let Some((_, param_theory)) = self.params.iter().find(|(n, _)| n == param_name) {
            let func_name = path.segments[1..].join("/");
            if let Some(id) = param_theory.theory.signature.lookup_func(&func_name) {
                return Ok(id);
            }
        }

        Err(ElabError::UnknownFunction(path.to_string()))
    }
}

/// Elaborate a type expression into a DerivedSort
pub fn elaborate_type(env: &Env, ty: &ast::TypeExpr) -> ElabResult<DerivedSort> {
    match ty {
        ast::TypeExpr::Sort => {
            // "Sort" is the kind of sorts, not a sort itself
            Err(ElabError::NotASort("Sort is a kind, not a type".to_string()))
        }
        ast::TypeExpr::Path(path) => {
            env.resolve_sort_path(path)
        }
        ast::TypeExpr::Record(fields) => {
            let elab_fields: Result<Vec<_>, _> = fields.iter()
                .map(|(name, ty)| {
                    elaborate_type(env, ty).map(|s| (name.clone(), s))
                })
                .collect();
            Ok(DerivedSort::Product(elab_fields?))
        }
        ast::TypeExpr::App(_, _) => {
            // Type application — for things like "N Marking"
            // This is used for parameterized types, which we'll handle later
            Err(ElabError::UnsupportedFeature("type application".to_string()))
        }
        ast::TypeExpr::Arrow(_, _) => {
            // Function types aren't sorts in this sense
            Err(ElabError::NotASort("arrow types are not sorts".to_string()))
        }
        ast::TypeExpr::Instance(_) => {
            // "T instance" is the type of instances of theory T
            Err(ElabError::UnsupportedFeature("instance types in sort position".to_string()))
        }
    }
}

/// Elaborate a term in a given context
pub fn elaborate_term(
    env: &Env,
    ctx: &Context,
    term: &ast::Term,
) -> ElabResult<Term> {
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
                    Err(ElabError::UnsupportedFeature("higher-order application".to_string()))
                }
            }
        }
        ast::Term::Project(base, field) => {
            let elab_base = elaborate_term(env, ctx, base)?;
            Ok(Term::Project(Box::new(elab_base), field.clone()))
        }
        ast::Term::Record(fields) => {
            let elab_fields: Result<Vec<_>, _> = fields.iter()
                .map(|(name, term)| {
                    elaborate_term(env, ctx, term).map(|t| (name.clone(), t))
                })
                .collect();
            Ok(Term::Record(elab_fields?))
        }
    }
}

/// Elaborate a formula
pub fn elaborate_formula(
    env: &Env,
    ctx: &Context,
    formula: &ast::Formula,
) -> ElabResult<Formula> {
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
            let elab: Result<Vec<_>, _> = conjuncts.iter()
                .map(|f| elaborate_formula(env, ctx, f))
                .collect();
            Ok(Formula::Conj(elab?))
        }
        ast::Formula::Or(disjuncts) => {
            let elab: Result<Vec<_>, _> = disjuncts.iter()
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
    }
}

/// Elaborate a theory declaration
pub fn elaborate_theory(env: &mut Env, theory: &ast::TheoryDecl) -> ElabResult<ElaboratedTheory> {
    // Set up the environment for this theory
    let mut local_env = env.clone();
    local_env.current_theory = Some(theory.name.clone());
    local_env.signature = Signature::new();

    // Process parameters
    let mut params = Vec::new();
    for param in &theory.params {
        match &param.ty {
            // "T instance" parameters — the theory depends on an instance of another theory
            ast::TypeExpr::Instance(inner) => {
                if let ast::TypeExpr::Path(path) = inner.as_ref() {
                    let theory_name = path.to_string();
                    if let Some(base_theory) = env.theories.get(&theory_name) {
                        params.push(TheoryParam {
                            name: param.name.clone(),
                            theory_name: theory_name.clone(),
                        });
                        local_env.params.push((param.name.clone(), base_theory.clone()));
                    } else {
                        return Err(ElabError::UnknownSort(theory_name));
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
                return Err(ElabError::UnsupportedFeature(
                    format!("parameter type {:?}", param.ty)
                ));
            }
        }
    }

    // First pass: collect all sorts
    for item in &theory.body {
        if let ast::TheoryItem::Sort(name) = &item.node {
            local_env.signature.add_sort(name.clone());
        }
    }

    // Second pass: collect all functions
    for item in &theory.body {
        if let ast::TheoryItem::Function(f) = &item.node {
            let domain = elaborate_type(&local_env, &f.domain)?;
            let codomain = elaborate_type(&local_env, &f.codomain)?;
            local_env.signature.add_function(f.name.to_string(), domain, codomain);
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
                let hyps: Result<Vec<_>, _> = ax.hypotheses.iter()
                    .map(|h| elaborate_formula(&local_env, &ctx, h))
                    .collect();
                Formula::Conj(hyps?)
            };

            // Elaborate conclusion
            let conclusion = elaborate_formula(&local_env, &ctx, &ax.conclusion)?;

            axioms.push(Sequent { context: ctx, premise, conclusion });
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
    // 1. Resolve the theory type
    // For now, handle simple paths only (not `ExampleNet ReachabilityProblem`)
    let theory_name = type_expr_to_theory_name(&instance.theory)?;
    let theory = env.theories.get(&theory_name)
        .ok_or_else(|| ElabError::UnknownSort(theory_name.clone()))?;

    // 2. Initialize structure (functions will be initialized after first pass)
    let mut structure = Structure::new(
        theory_name.clone(),
        theory.theory.signature.sorts.len(),
    );

    // Track name → Slid for resolving references within this instance
    let mut name_to_slid: HashMap<String, Slid> = HashMap::new();

    // 3. First pass: create elements
    for item in &instance.body {
        if let ast::InstanceItem::Element(name, sort_expr) = &item.node {
            // Resolve the sort
            let sort_id = resolve_instance_sort(&theory.theory.signature, sort_expr)?;

            // Add element to structure
            let slid = structure.add_element(universe, name.clone(), sort_id);
            name_to_slid.insert(name.clone(), slid);
        }
    }

    // 3b. Initialize function storage now that carrier sizes are known
    // Extract domain sort IDs for each function (None for product domains)
    let domain_sort_ids: Vec<Option<SortId>> = theory.theory.signature.functions
        .iter()
        .map(|func| match &func.domain {
            DerivedSort::Base(id) => Some(*id),
            DerivedSort::Product(_) => None,  // Defer product domains
        })
        .collect();
    structure.init_functions(&domain_sort_ids);

    // 4. Second pass: process equations (define function values) with type checking
    for item in &instance.body {
        if let ast::InstanceItem::Equation(lhs, rhs) = &item.node {
            // Decompose lhs: should be `element func_path`
            // e.g., `ab_in in/src` → element="ab_in", func="in/src"
            let (elem_slid, func_id) = decompose_func_app(
                lhs,
                &name_to_slid,
                &theory.theory.signature,
            )?;

            // Resolve rhs to an element
            let value_slid = resolve_instance_element(rhs, &name_to_slid)?;

            // Type checking: verify element sort matches function domain
            let func = &theory.theory.signature.functions[func_id];
            let elem_sort_id = structure.sorts[elem_slid];
            if let DerivedSort::Base(expected_domain) = &func.domain {
                if elem_sort_id != *expected_domain {
                    return Err(ElabError::DomainMismatch {
                        func_name: func.name.clone(),
                        element_name: structure.names[elem_slid].clone(),
                        expected_sort: theory.theory.signature.sorts[*expected_domain].clone(),
                        actual_sort: theory.theory.signature.sorts[elem_sort_id].clone(),
                    });
                }
            }

            // Type checking: verify value sort matches function codomain
            let value_sort_id = structure.sorts[value_slid];
            if let DerivedSort::Base(expected_codomain) = &func.codomain {
                if value_sort_id != *expected_codomain {
                    return Err(ElabError::CodomainMismatch {
                        func_name: func.name.clone(),
                        element_name: structure.names[value_slid].clone(),
                        expected_sort: theory.theory.signature.sorts[*expected_codomain].clone(),
                        actual_sort: theory.theory.signature.sorts[value_sort_id].clone(),
                    });
                }
            }

            // Define the function value
            structure.define_function(func_id, elem_slid, value_slid)
                .map_err(|msg| ElabError::DuplicateDefinition(msg))?;
        }
    }

    // 5. Third pass: nested instances (TODO for Phase 2)
    for item in &instance.body {
        if let ast::InstanceItem::NestedInstance(name, _nested) = &item.node {
            // For now, just note that we're skipping these
            return Err(ElabError::UnsupportedFeature(
                format!("nested instance: {}", name)
            ));
        }
    }

    // 6. Validate totality: all functions must be defined on all elements of their domain
    validate_totality(&structure, &theory.theory.signature)?;

    Ok(structure)
}

/// Extract a simple theory name from a type expression
fn type_expr_to_theory_name(ty: &ast::TypeExpr) -> ElabResult<String> {
    match ty {
        ast::TypeExpr::Path(path) => Ok(path.to_string()),
        ast::TypeExpr::App(_, _) => {
            // For now, don't support parameterized instance types
            Err(ElabError::UnsupportedFeature("parameterized instance types".to_string()))
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
        _ => Err(ElabError::UnsupportedFeature(format!("complex sort: {:?}", sort_expr))),
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
                        .ok_or_else(|| ElabError::UnknownFunction(func_name))
                }
                _ => Err(ElabError::NotAFunction(format!("{:?}", func))),
            }?;

            Ok((elem_slid, func_id))
        }
        _ => Err(ElabError::NotAFunction(format!("expected function application, got {:?}", term))),
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
            name_to_slid.get(name)
                .copied()
                .ok_or_else(|| ElabError::UnknownVariable(name.clone()))
        }
        _ => Err(ElabError::UnsupportedFeature(format!("complex element reference: {:?}", term))),
    }
}

/// Check that all functions in the structure are total (defined on every element of their domain)
fn validate_totality(structure: &Structure, sig: &Signature) -> ElabResult<()> {
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
                // Reverse lookup: sort_slid → slid → name
                // Find the slid that has this sort_slid in this domain sort
                let slid = structure.carriers[domain_sort_id]
                    .select(sort_slid as u64)
                    .expect("sort_slid should be valid") as Slid;
                missing.push(structure.names[slid].clone());
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse;
    use crate::universe::Universe;

    #[test]
    fn test_elaborate_simple_theory() {
        let input = r#"
theory PetriNet {
    P : Sort;
    T : Sort;
    src : P -> T;
}
"#;
        let file = parse(input).expect("parse failed");
        let mut env = Env::new();

        if let ast::Declaration::Theory(t) = &file.declarations[0].node {
            let elab = elaborate_theory(&mut env, t).expect("elaboration failed");
            assert_eq!(elab.theory.name, "PetriNet");
            assert_eq!(elab.theory.signature.sorts.len(), 2);
            assert_eq!(elab.theory.signature.functions.len(), 1);
        } else {
            panic!("expected theory");
        }
    }

    #[test]
    fn test_elaborate_parameterized_theory() {
        let input = r#"
theory PetriNet {
    P : Sort;
    T : Sort;
}

theory (N : PetriNet instance) Marking {
    token : Sort;
    token/of : token -> N/P;
}
"#;
        let file = parse(input).expect("parse failed");
        let mut env = Env::new();

        // First elaborate PetriNet
        if let ast::Declaration::Theory(t) = &file.declarations[0].node {
            let elab = elaborate_theory(&mut env, t).expect("elaboration failed");
            env.theories.insert(elab.theory.name.clone(), Rc::new(elab));
        }

        // Then elaborate Marking (which depends on PetriNet)
        if let ast::Declaration::Theory(t) = &file.declarations[1].node {
            let elab = elaborate_theory(&mut env, t).expect("elaboration failed");
            assert_eq!(elab.theory.name, "Marking");
            assert_eq!(elab.params.len(), 1);
            assert_eq!(elab.params[0].name, "N");
            assert_eq!(elab.params[0].theory_name, "PetriNet");
            assert_eq!(elab.theory.signature.sorts.len(), 1); // token
            assert_eq!(elab.theory.signature.functions.len(), 1); // token/of
        } else {
            panic!("expected theory");
        }
    }

    #[test]
    fn test_elaborate_theory_with_axiom() {
        let input = r#"
theory Iso {
    X : Sort;
    Y : Sort;
    fwd : X -> Y;
    bwd : Y -> X;
    fb : forall x : X. |- x fwd bwd = x;
}
"#;
        let file = parse(input).expect("parse failed");
        let mut env = Env::new();

        if let ast::Declaration::Theory(t) = &file.declarations[0].node {
            let elab = elaborate_theory(&mut env, t).expect("elaboration failed");
            assert_eq!(elab.theory.name, "Iso");
            assert_eq!(elab.theory.signature.sorts.len(), 2);
            assert_eq!(elab.theory.signature.functions.len(), 2);
            assert_eq!(elab.theory.axioms.len(), 1);

            // Check the axiom structure
            let ax = &elab.theory.axioms[0];
            assert_eq!(ax.context.vars.len(), 1);
            assert_eq!(ax.context.vars[0].0, "x");
        } else {
            panic!("expected theory");
        }
    }

    #[test]
    fn test_axiom_function_type_error() {
        // x is of sort X, but bwd expects Y
        let input = r#"
theory BadIso {
    X : Sort;
    Y : Sort;
    fwd : X -> Y;
    bwd : Y -> X;
    bad : forall x : X. |- x bwd = x;
}
"#;
        let file = parse(input).expect("parse failed");
        let mut env = Env::new();

        if let ast::Declaration::Theory(t) = &file.declarations[0].node {
            let result = elaborate_theory(&mut env, t);
            assert!(result.is_err(), "expected type error in axiom");

            let err = result.unwrap_err();
            match err {
                ElabError::TypeMismatch { expected, got } => {
                    // expected Y (bwd's domain), got X
                    assert_eq!(expected, DerivedSort::Base(1)); // Y
                    assert_eq!(got, DerivedSort::Base(0));      // X
                }
                other => panic!("expected TypeMismatch error, got: {}", other),
            }
        } else {
            panic!("expected theory");
        }
    }

    #[test]
    fn test_axiom_equality_type_error() {
        // LHS is X, RHS is Y — can't compare different sorts
        let input = r#"
theory BadEq {
    X : Sort;
    Y : Sort;
    fwd : X -> Y;
    bad : forall x : X. |- x = x fwd;
}
"#;
        let file = parse(input).expect("parse failed");
        let mut env = Env::new();

        if let ast::Declaration::Theory(t) = &file.declarations[0].node {
            let result = elaborate_theory(&mut env, t);
            assert!(result.is_err(), "expected type error in equality");

            let err = result.unwrap_err();
            match err {
                ElabError::TypeMismatch { expected, got } => {
                    // LHS is X, RHS is Y
                    assert_eq!(expected, DerivedSort::Base(0)); // X
                    assert_eq!(got, DerivedSort::Base(1));      // Y
                }
                other => panic!("expected TypeMismatch error, got: {}", other),
            }
        } else {
            panic!("expected theory");
        }
    }

    #[test]
    fn test_elaborate_instance() {
        let input = r#"
theory PetriNet {
    P : Sort;
    T : Sort;
    in : Sort;
    out : Sort;
    in/src : in -> P;
    in/tgt : in -> T;
    out/src : out -> T;
    out/tgt : out -> P;
}

instance ExampleNet : PetriNet = {
    A : P;
    B : P;
    C : P;
    ab : T;
    ab_in : in;
    ab_in in/src = A;
    ab_in in/tgt = ab;
    ab_out : out;
    ab_out out/src = ab;
    ab_out out/tgt = B;
}
"#;
        let file = parse(input).expect("parse failed");
        let mut env = Env::new();
        let mut universe = Universe::new();

        // First elaborate PetriNet theory
        if let ast::Declaration::Theory(t) = &file.declarations[0].node {
            let elab = elaborate_theory(&mut env, t).expect("theory elaboration failed");
            env.theories.insert(elab.theory.name.clone(), Rc::new(elab));
        }

        // Then elaborate ExampleNet instance
        if let ast::Declaration::Instance(i) = &file.declarations[1].node {
            let structure = elaborate_instance(&env, i, &mut universe).expect("instance elaboration failed");

            assert_eq!(structure.theory_name, "PetriNet");
            assert_eq!(structure.len(), 6); // A, B, C, ab, ab_in, ab_out

            // Check carriers
            assert_eq!(structure.carrier_size(0), 3); // P: A, B, C
            assert_eq!(structure.carrier_size(1), 1); // T: ab
            assert_eq!(structure.carrier_size(2), 1); // in: ab_in
            assert_eq!(structure.carrier_size(3), 1); // out: ab_out

            // Check function definitions using the new columnar API
            let ab_in_slid = structure.lookup("ab_in").expect("ab_in not found");
            let a_slid = structure.lookup("A").expect("A not found");
            let ab_slid = structure.lookup("ab").expect("ab not found");

            // Get the sort-local ID for ab_in
            let ab_in_sort_slid = structure.sort_local_id(ab_in_slid);

            // in/src is function 0, ab_in maps to A
            assert_eq!(structure.get_function(0, ab_in_sort_slid), Some(a_slid));
            // in/tgt is function 1, ab_in maps to ab
            assert_eq!(structure.get_function(1, ab_in_sort_slid), Some(ab_slid));
        } else {
            panic!("expected instance");
        }
    }

    #[test]
    fn test_partial_function_error() {
        // This instance is missing the definition for ab_in in/tgt
        // (ab_in is in the domain of in/tgt but has no value defined)
        let input = r#"
theory PetriNet {
    P : Sort;
    T : Sort;
    in : Sort;
    in/src : in -> P;
    in/tgt : in -> T;
}

instance PartialNet : PetriNet = {
    A : P;
    ab : T;
    ab_in : in;
    ab_in in/src = A;
    // Missing: ab_in in/tgt = ab;
}
"#;
        let file = parse(input).expect("parse failed");
        let mut env = Env::new();
        let mut universe = Universe::new();

        // First elaborate PetriNet theory
        if let ast::Declaration::Theory(t) = &file.declarations[0].node {
            let elab = elaborate_theory(&mut env, t).expect("theory elaboration failed");
            env.theories.insert(elab.theory.name.clone(), Rc::new(elab));
        }

        // Then try to elaborate the partial instance — should fail
        if let ast::Declaration::Instance(i) = &file.declarations[1].node {
            let result = elaborate_instance(&env, i, &mut universe);
            assert!(result.is_err(), "expected error for partial function");

            let err = result.unwrap_err();
            match err {
                ElabError::PartialFunction { func_name, missing_elements } => {
                    assert_eq!(func_name, "in/tgt");
                    assert_eq!(missing_elements, vec!["ab_in"]);
                }
                other => panic!("expected PartialFunction error, got: {}", other),
            }
        } else {
            panic!("expected instance");
        }
    }

    #[test]
    fn test_domain_type_error() {
        // ab is of sort T, but in/src expects domain sort `in`
        let input = r#"
theory PetriNet {
    P : Sort;
    T : Sort;
    in : Sort;
    in/src : in -> P;
}

instance BadNet : PetriNet = {
    A : P;
    ab : T;
    ab in/src = A;
}
"#;
        let file = parse(input).expect("parse failed");
        let mut env = Env::new();
        let mut universe = Universe::new();

        if let ast::Declaration::Theory(t) = &file.declarations[0].node {
            let elab = elaborate_theory(&mut env, t).expect("theory elaboration failed");
            env.theories.insert(elab.theory.name.clone(), Rc::new(elab));
        }

        if let ast::Declaration::Instance(i) = &file.declarations[1].node {
            let result = elaborate_instance(&env, i, &mut universe);
            assert!(result.is_err(), "expected domain type error");

            let err = result.unwrap_err();
            match err {
                ElabError::DomainMismatch { func_name, element_name, expected_sort, actual_sort } => {
                    assert_eq!(func_name, "in/src");
                    assert_eq!(element_name, "ab");
                    assert_eq!(expected_sort, "in");
                    assert_eq!(actual_sort, "T");
                }
                other => panic!("expected DomainMismatch error, got: {}", other),
            }
        } else {
            panic!("expected instance");
        }
    }

    #[test]
    fn test_codomain_type_error() {
        // ab is of sort T, but in/src has codomain P
        let input = r#"
theory PetriNet {
    P : Sort;
    T : Sort;
    in : Sort;
    in/src : in -> P;
}

instance BadNet : PetriNet = {
    A : P;
    ab : T;
    ab_in : in;
    ab_in in/src = ab;
}
"#;
        let file = parse(input).expect("parse failed");
        let mut env = Env::new();
        let mut universe = Universe::new();

        if let ast::Declaration::Theory(t) = &file.declarations[0].node {
            let elab = elaborate_theory(&mut env, t).expect("theory elaboration failed");
            env.theories.insert(elab.theory.name.clone(), Rc::new(elab));
        }

        if let ast::Declaration::Instance(i) = &file.declarations[1].node {
            let result = elaborate_instance(&env, i, &mut universe);
            assert!(result.is_err(), "expected codomain type error");

            let err = result.unwrap_err();
            match err {
                ElabError::CodomainMismatch { func_name, element_name, expected_sort, actual_sort } => {
                    assert_eq!(func_name, "in/src");
                    assert_eq!(element_name, "ab");
                    assert_eq!(expected_sort, "P");
                    assert_eq!(actual_sort, "T");
                }
                other => panic!("expected CodomainMismatch error, got: {}", other),
            }
        } else {
            panic!("expected instance");
        }
    }
}
