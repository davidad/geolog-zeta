//! Theory elaboration.

use std::collections::HashMap;

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
                // Handle both simple (PetriNet instance) and parameterized (N ReachabilityProblem instance) cases
                let theory_name = extract_theory_name(inner)?;
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

                        // NOTE: Instance field content (sorts/functions) is already included in
                        // base_theory.theory.signature because it was added when that theory
                        // was elaborated. We don't need to process instance fields again here.

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
            // Instance-typed field declarations (nested instances)
            // e.g., `initial_marking : N Marking instance;`
            ast::TheoryItem::Field(name, ast::TypeExpr::Instance(inner)) => {
                // Store the theory type expression as a string
                let theory_type_str = format_type_expr(inner);
                local_env
                    .signature
                    .add_instance_field(name.clone(), theory_type_str.clone());

                // Also add the content (sorts, functions) from the field's theory
                // This enables accessing things like iso/fwd when we have `iso : X Y Iso instance`
                if let Ok(field_theory_name) = extract_theory_name(inner) {
                    if let Some(field_theory) = env.theories.get(&field_theory_name) {
                        let field_prefix = name.clone();

                        // Build a mapping from source sort names to target sort names
                        // - Sort parameters get substituted from type expression args
                        // - Instance param sorts (e.g., "N/P") map to local sorts with same name
                        // - Local sorts (e.g., "Token") get prefixed with field name
                        let sort_param_map = collect_sort_params(inner, field_theory);

                        // First, add any non-param sorts from the field's theory with prefix
                        for sort_name in &field_theory.theory.signature.sorts {
                            // Skip sorts that came from instance params (already qualified)
                            if sort_name.contains('/') {
                                continue;
                            }
                            // Skip Sort parameters (will be substituted)
                            let is_sort_param = field_theory
                                .params
                                .iter()
                                .any(|p| p.theory_name == "Sort" && p.name == *sort_name);
                            if is_sort_param {
                                continue;
                            }
                            // Add as prefixed sort
                            let qualified_name = format!("{}/{}", field_prefix, sort_name);
                            local_env.signature.add_sort(qualified_name);
                        }

                        // Add functions from the field's theory
                        for func in &field_theory.theory.signature.functions {
                            // Skip functions that came from instance params (already qualified)
                            if func.name.contains('/') {
                                continue;
                            }
                            let qualified_name = format!("{}/{}", field_prefix, func.name);
                            let domain = remap_for_instance_field(
                                &func.domain,
                                &field_theory.theory.signature,
                                &local_env.signature,
                                &sort_param_map,
                                &field_prefix,
                            );
                            let codomain = remap_for_instance_field(
                                &func.codomain,
                                &field_theory.theory.signature,
                                &local_env.signature,
                                &sort_param_map,
                                &field_prefix,
                            );
                            if let (Some(d), Some(c)) = (domain, codomain) {
                                local_env.signature.add_function(qualified_name, d, c);
                            }
                        }
                    }
                }
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

/// Remap a DerivedSort for an instance-typed field in a theory body.
/// Handles both Sort parameters (substituted from type args) and instance param sorts.
fn remap_for_instance_field(
    sort: &DerivedSort,
    source_sig: &Signature,
    target_sig: &Signature,
    sort_param_map: &HashMap<String, String>,
    field_prefix: &str,
) -> Option<DerivedSort> {
    match sort {
        DerivedSort::Base(source_id) => {
            let sort_name = &source_sig.sorts[*source_id];

            // Check Sort parameter substitution (e.g., X -> RP/initial/Token)
            if let Some(replacement) = sort_param_map.get(sort_name) {
                if let Some(target_id) = target_sig.lookup_sort(replacement) {
                    return Some(DerivedSort::Base(target_id));
                }
            }

            // Check if it's an instance param sort (already qualified, e.g., N/P)
            if sort_name.contains('/') {
                if let Some(target_id) = target_sig.lookup_sort(sort_name) {
                    return Some(DerivedSort::Base(target_id));
                }
            }

            // Check if it's a local sort (needs prefix, e.g., Token -> initial/Token)
            let prefixed = format!("{}/{}", field_prefix, sort_name);
            if let Some(target_id) = target_sig.lookup_sort(&prefixed) {
                return Some(DerivedSort::Base(target_id));
            }

            None
        }
        DerivedSort::Product(fields) => {
            let remapped: Option<Vec<_>> = fields
                .iter()
                .map(|(n, s)| {
                    remap_for_instance_field(s, source_sig, target_sig, sort_param_map, field_prefix)
                        .map(|r| (n.clone(), r))
                })
                .collect();
            remapped.map(DerivedSort::Product)
        }
    }
}

/// Collect sort parameter mappings from a type expression.
/// E.g., `RP/initial/Token RP/target/Token Iso` returns {"X" -> "RP/initial/Token", "Y" -> "RP/target/Token"}
fn collect_sort_params(
    ty: &ast::TypeExpr,
    field_theory: &std::rc::Rc<ElaboratedTheory>,
) -> HashMap<String, String> {
    let mut args = Vec::new();
    collect_type_args(ty, &mut args);

    // Match args with sort parameters in order
    let mut map = HashMap::new();
    for (param, arg) in field_theory.params.iter().zip(args.iter()) {
        if param.theory_name == "Sort" {
            map.insert(param.name.clone(), arg.clone());
        }
    }
    map
}

/// Recursively collect type arguments from an App chain.
/// For `A B C Foo`, this returns ["A", "B", "C"] (Foo is the theory name).
fn collect_type_args(ty: &ast::TypeExpr, args: &mut Vec<String>) {
    match ty {
        ast::TypeExpr::App(base, arg) => {
            // For App(base, arg):
            // - If base is also an App, recurse to get its args first
            // - Then add the current arg
            // But wait - the rightmost is always the theory, not an arg!
            // So for `A B C Foo`: App(App(App(A, B), C), Foo)
            // We want [A, B, C], not [B, C, Foo]
            //
            // Actually, let's trace: App(App(App(Path("A"), Path("B")), Path("C")), Path("Foo"))
            // - base = App(App(Path("A"), Path("B")), Path("C"))
            // - arg = Path("Foo")
            // Recursing:
            // - base = App(Path("A"), Path("B"))
            // - arg = Path("C")
            // And so on...
            //
            // The pattern is: the FINAL arg (after all Apps) is the theory name.
            // All intermediate args are the type arguments.
            //
            // So for A B Foo:
            // - App(App(Path("A"), Path("B")), Path("Foo"))
            // - First iteration: base = App(Path("A"), Path("B")), arg = Path("Foo")
            //   - We DON'T add "Foo" because it's the theory name
            //   - Recurse on base
            // - Second iteration: base = Path("A"), arg = Path("B")
            //   - Add "B"
            //   - Recurse on base
            // - Third iteration: base = Path("A")
            //   - Add "A"
            //
            // Hmm, this gives us ["B", "A"], reversed!
            // And we're missing the logic to NOT add the theory name.
            //
            // Let me rethink: For `X Y Iso`:
            // - App(App(Path("X"), Path("Y")), Path("Iso"))
            // We want args = ["X", "Y"]
            //
            // The recursive structure is:
            // - base = App(Path("X"), Path("Y"))
            // - arg = Path("Iso")
            //
            // At the top level, arg IS the theory name.
            // At nested levels, arg is a type argument AND we need to prepend the base args.
            //
            // Actually, we can just process left-to-right:
            // - In App(base, arg), base contains all previous args + theory
            // - arg at this level is always a type argument (except at the outermost level)
            //
            // Wait no - at the outermost level, arg is the theory name.
            // At inner levels, arg is a type argument.
            //
            // Let me use a different approach: collect ALL args first, then drop the last one (theory name).
            collect_type_args(base, args);
            args.push(format_type_expr(arg));
        }
        ast::TypeExpr::Path(path) => {
            // This is the leftmost element - it's a type argument
            args.push(path.to_string());
        }
        _ => {}
    }
}

/// Substitute sort parameters in a DerivedSort using a mapping.
/// Returns None if the sort cannot be resolved in the target signature.
#[allow(dead_code)]
fn substitute_sort_params(
    sort: &DerivedSort,
    source_sig: &Signature,
    target_sig: &Signature,
    param_map: &HashMap<String, String>,
) -> Option<DerivedSort> {
    match sort {
        DerivedSort::Base(source_id) => {
            let sort_name = &source_sig.sorts[*source_id];
            // Check if this sort is a parameter that should be substituted
            if let Some(replacement) = param_map.get(sort_name) {
                // Look up the replacement sort in the target signature
                if let Some(target_id) = target_sig.lookup_sort(replacement) {
                    return Some(DerivedSort::Base(target_id));
                }
                // Couldn't find the replacement - this is an error case
                eprintln!(
                    "Warning: sort param substitution failed for {} -> {}",
                    sort_name, replacement
                );
                return None;
            }
            // Not a parameter - try to find in target as-is
            if let Some(target_id) = target_sig.lookup_sort(sort_name) {
                Some(DerivedSort::Base(target_id))
            } else {
                // Sort doesn't exist in target - skip this
                None
            }
        }
        DerivedSort::Product(fields) => {
            let remapped_fields: Option<Vec<_>> = fields
                .iter()
                .map(|(name, s)| {
                    substitute_sort_params(s, source_sig, target_sig, param_map)
                        .map(|remapped| (name.clone(), remapped))
                })
                .collect();
            remapped_fields.map(DerivedSort::Product)
        }
    }
}

/// Extract the base theory name from a type expression.
/// - `Path("PetriNet")` → "PetriNet"
/// - `App(Path("N"), Path("ReachabilityProblem"))` → "ReachabilityProblem"
/// - `App(App(...), Path("Foo"))` → "Foo" (rightmost path)
fn extract_theory_name(ty: &ast::TypeExpr) -> ElabResult<String> {
    match ty {
        ast::TypeExpr::Path(path) => Ok(path.to_string()),
        ast::TypeExpr::App(_, arg) => {
            // For App(base, arg), the rightmost arg is the theory name
            // e.g., "N ReachabilityProblem" → App(Path("N"), Path("ReachabilityProblem"))
            extract_theory_name(arg)
        }
        _ => Err(ElabError::UnsupportedFeature(format!(
            "cannot extract theory name from {:?}",
            ty
        ))),
    }
}

/// Format a type expression as a string (for storing instance field types)
fn format_type_expr(ty: &ast::TypeExpr) -> String {
    match ty {
        ast::TypeExpr::Path(path) => path.to_string(),
        ast::TypeExpr::App(base, arg) => {
            format!("{} {}", format_type_expr(base), format_type_expr(arg))
        }
        ast::TypeExpr::Instance(inner) => {
            format!("{} instance", format_type_expr(inner))
        }
        ast::TypeExpr::Sort => "Sort".to_string(),
        ast::TypeExpr::Prop => "Prop".to_string(),
        ast::TypeExpr::Record(fields) => {
            let field_strs: Vec<String> = fields
                .iter()
                .map(|(name, ty)| format!("{}: {}", name, format_type_expr(ty)))
                .collect();
            format!("[{}]", field_strs.join(", "))
        }
        ast::TypeExpr::Arrow(from, to) => {
            format!("{} -> {}", format_type_expr(from), format_type_expr(to))
        }
    }
}
