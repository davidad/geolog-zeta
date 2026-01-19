//! Theory elaboration.

use crate::ast;
use crate::core::*;

use super::env::{elaborate_formula, elaborate_type, remap_derived_sort, Env};
use super::error::{ElabError, ElabResult};

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
