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

    // Track extended theories for transitive closure semantics
    let mut extends_chain: Vec<String> = Vec::new();

    // Process extends clause (if any)
    // This is like a parameter, but:
    // 1. Uses the parent theory name as the qualifier (e.g., GeologMeta/Srt)
    // 2. Establishes an "is-a" relationship with transitive closure
    //
    // For transitive extends (A extends B extends C), we use "requalified" semantics:
    // - Sorts/funcs already qualified (from grandparents) keep their original qualifier
    // - Only unqualified items (parent's own) get the parent prefix
    // This gives A: { C/X, C/Y, B/Foo } rather than { B/C/X, B/C/Y, B/Foo }
    if let Some(ref parent_path) = theory.extends {
        let parent_name = parent_path.segments.join("/");
        if let Some(parent_theory) = env.theories.get(&parent_name) {
            // Record the extends relationship (including transitive parents)
            extends_chain.push(parent_name.clone());

            // Helper: check if a name is already qualified from a grandparent
            // A name like "Grandparent/X" is grandparent-qualified if "Grandparent" is NOT
            // a sort in the parent theory (i.e., it's a theory name, not a naming convention).
            // Names like "Func/dom" where "Func" IS a sort use '/' as naming convention.
            let is_grandparent_qualified = |name: &str| -> bool {
                if let Some((prefix, _)) = name.split_once('/') {
                    // If the prefix is a sort in parent, it's naming convention, not grandparent
                    parent_theory.theory.signature.lookup_sort(prefix).is_none()
                } else {
                    false
                }
            };

            // Helper: qualify a name - only prefix if not already qualified from grandparent
            let qualify = |name: &str| -> String {
                if is_grandparent_qualified(name) {
                    // Already qualified from grandparent - keep as-is
                    name.to_string()
                } else {
                    // Parent's own item (possibly with naming convention '/') - add parent prefix
                    format!("{}/{}", parent_name, name)
                }
            };

            // Copy all sorts with requalified names
            for sort_name in &parent_theory.theory.signature.sorts {
                let qualified_name = qualify(sort_name);
                local_env.signature.add_sort(qualified_name);
            }

            // Copy all functions with requalified names
            for func in &parent_theory.theory.signature.functions {
                let qualified_name = qualify(&func.name);
                // For domain/codomain remapping, always use parent_name because
                // the source signature uses the parent's namespace. The
                // preserve_existing_prefix flag handles grandparent-qualified sorts.
                let domain = remap_derived_sort(
                    &func.domain,
                    &parent_theory.theory.signature,
                    &local_env.signature,
                    &parent_name,
                    true, // preserve_existing_prefix for extends
                );
                let codomain = remap_derived_sort(
                    &func.codomain,
                    &parent_theory.theory.signature,
                    &local_env.signature,
                    &parent_name,
                    true, // preserve_existing_prefix for extends
                );
                local_env
                    .signature
                    .add_function(qualified_name, domain, codomain);
            }

            // Copy all relations with requalified names
            for rel in &parent_theory.theory.signature.relations {
                let qualified_name = qualify(&rel.name);
                // Same as functions: always use parent_name for remapping
                let domain = remap_derived_sort(
                    &rel.domain,
                    &parent_theory.theory.signature,
                    &local_env.signature,
                    &parent_name,
                    true, // preserve_existing_prefix for extends
                );
                local_env.signature.add_relation(qualified_name, domain);
            }

            // Note: axioms are inherited but we don't copy them yet
            // (they reference the parent's sort/func IDs which need remapping)
        } else {
            return Err(ElabError::UnknownTheory(parent_name));
        }
    }

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
                                false, // instance params always re-prefix
                            );
                            let codomain = remap_derived_sort(
                                &func.codomain,
                                &base_theory.theory.signature,
                                &local_env.signature,
                                &param.name,
                                false, // instance params always re-prefix
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
                                false, // instance params always re-prefix
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
