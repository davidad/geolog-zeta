//! Elaboration environment and basic elaboration functions.

use std::collections::HashMap;
use std::rc::Rc;

use crate::ast;
use crate::core::*;

use super::error::{ElabError, ElabResult};

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
pub(crate) fn remap_derived_sort(
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
