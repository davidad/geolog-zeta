//! Property tests for semantic roundtrip (parse -> elaborate -> pretty -> parse -> elaborate)
//!
//! These tests verify that the pretty-printer produces output that, when reparsed
//! and re-elaborated, yields semantically equivalent results. This is more robust
//! than AST equality since different surface syntax can represent the same semantics.

use geolog::elaborate::elaborate_theories;
use geolog::parse;
use geolog::pretty::pretty_print;
use proptest::prelude::*;

/// Test that a theory survives the roundtrip: parse -> elaborate -> pretty -> parse -> elaborate
/// The two elaborated theories should have equivalent signatures and axioms.
fn roundtrip_theory(source: &str) -> Result<(), String> {
    // Parse original
    let ast1 = parse(source).map_err(|e| format!("Initial parse failed: {:?}", e))?;

    // Elaborate original
    let env1 = elaborate_theories(&ast1).map_err(|e| format!("Initial elaboration failed: {:?}", e))?;

    // Pretty-print
    let printed = pretty_print(&ast1);

    // Reparse
    let ast2 = parse(&printed).map_err(|e| format!("Reparse failed: {:?}\nPrinted: {}", e, printed))?;

    // Re-elaborate
    let env2 = elaborate_theories(&ast2)
        .map_err(|e| format!("Re-elaboration failed: {:?}\nPrinted: {}", e, printed))?;

    // Compare elaborated theories
    // The theories should match by name
    for name in env1.theories.keys() {
        let t1 = env1.theories.get(name).ok_or_else(|| format!("Theory {} missing in env1", name))?;
        let t2 = env2.theories.get(name).ok_or_else(|| format!("Theory {} missing in env2", name))?;

        // Compare signatures
        if t1.theory.signature != t2.theory.signature {
            return Err(format!(
                "Signature mismatch for theory {}:\n  Original: {:?}\n  Reprinted: {:?}",
                name, t1.theory.signature, t2.theory.signature
            ));
        }

        // Compare axiom count (axiom equality is more complex due to naming)
        if t1.theory.axioms.len() != t2.theory.axioms.len() {
            return Err(format!(
                "Axiom count mismatch for theory {}: {} vs {}",
                name, t1.theory.axioms.len(), t2.theory.axioms.len()
            ));
        }

        // Compare axioms (they should be semantically equivalent)
        for (i, (ax1, ax2)) in t1.theory.axioms.iter().zip(t2.theory.axioms.iter()).enumerate() {
            if ax1 != ax2 {
                return Err(format!(
                    "Axiom {} mismatch in theory {}:\n  Original: {:?}\n  Reprinted: {:?}",
                    i, name, ax1, ax2
                ));
            }
        }
    }

    Ok(())
}

// ============================================================================
// Fixed Test Cases
// ============================================================================

#[test]
fn test_roundtrip_simple_theory() {
    let source = r#"
theory Graph {
    V : Sort;
    E : Sort;
    src : E -> V;
    tgt : E -> V;
}
"#;
    roundtrip_theory(source).unwrap();
}

#[test]
fn test_roundtrip_theory_with_relation() {
    let source = r#"
theory Preorder {
    X : Sort;
    leq : [x: X, y: X] -> Prop;
    ax/refl : forall x : X. |- [x: x, y: x] leq;
    ax/trans : forall x : X, y : X, z : X. [x: x, y: y] leq, [x: y, y: z] leq |- [x: x, y: z] leq;
}
"#;
    roundtrip_theory(source).unwrap();
}

#[test]
fn test_roundtrip_theory_with_existential() {
    let source = r#"
theory Chain {
    X : Sort;
    leq : [from: X, to: X] -> Prop;
    ax/total : forall x : X, y : X. |- [from: x, to: y] leq \/ [from: y, to: x] leq;
}
"#;
    roundtrip_theory(source).unwrap();
}

#[test]
fn test_roundtrip_petri_net() {
    let source = r#"
theory PetriNet {
    P : Sort;
    T : Sort;
    in : Sort;
    out : Sort;
    in/src : in -> T;
    in/tgt : in -> P;
    out/src : out -> T;
    out/tgt : out -> P;
}
"#;
    roundtrip_theory(source).unwrap();
}

// ============================================================================
// Property-Based Tests
// ============================================================================

/// Generate a random valid theory name
fn arb_theory_name() -> impl Strategy<Value = String> {
    "[A-Z][a-zA-Z0-9]{0,10}".prop_map(String::from)
}

/// Generate a random valid sort name
fn arb_sort_name() -> impl Strategy<Value = String> {
    "[A-Z][a-zA-Z0-9]{0,5}".prop_map(String::from)
}

/// Generate a random valid function name
fn arb_func_name() -> impl Strategy<Value = String> {
    "[a-z][a-z0-9_]{0,8}".prop_map(String::from)
}

/// Generate a simple theory with N sorts and M functions
fn arb_simple_theory(max_sorts: usize, max_funcs: usize) -> impl Strategy<Value = String> {
    (
        arb_theory_name(),
        prop::collection::vec(arb_sort_name(), 1..=max_sorts),
    )
        .prop_flat_map(move |(name, sorts)| {
            // Generate functions between sorts
            let sort_count = sorts.len();
            let func_gen = if sort_count > 0 {
                prop::collection::vec(
                    (arb_func_name(), 0..sort_count, 0..sort_count),
                    0..=max_funcs,
                )
                .boxed()
            } else {
                Just(vec![]).boxed()
            };

            (Just(name), Just(sorts), func_gen)
        })
        .prop_map(|(name, sorts, funcs)| {
            let mut source = format!("theory {} {{\n", name);

            // Declare sorts
            for sort in &sorts {
                source.push_str(&format!("    {} : Sort;\n", sort));
            }

            // Declare functions (ensuring unique names)
            let mut used_names = std::collections::HashSet::new();
            for (fname, dom, cod) in funcs {
                if !used_names.contains(&fname) && dom < sorts.len() && cod < sorts.len() {
                    source.push_str(&format!(
                        "    {} : {} -> {};\n",
                        fname, sorts[dom], sorts[cod]
                    ));
                    used_names.insert(fname);
                }
            }

            source.push_str("}\n");
            source
        })
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]

    #[test]
    fn roundtrip_generated_theory(source in arb_simple_theory(5, 10)) {
        // Skip if the source doesn't parse (generator might create invalid combos)
        if let Ok(()) = roundtrip_theory(&source) {
            // Test passed
        } else if parse(&source).is_err() {
            // Generator created invalid source, skip
        } else {
            // Parse succeeded but roundtrip failed - this is a real failure
            roundtrip_theory(&source).unwrap();
        }
    }
}
