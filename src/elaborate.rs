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

            // Then figure out what the function is
            match func.as_ref() {
                ast::Term::Path(path) => {
                    let func_id = env.resolve_func_path(path)?;
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
            // TODO: check that sorts match
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse;

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
}
