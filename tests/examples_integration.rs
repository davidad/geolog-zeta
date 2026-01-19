//! Integration tests for example .geolog files
//!
//! These tests ensure that the example files in `examples/geolog/` remain
//! valid as the language evolves. They serve as living documentation.

use geolog::repl::ReplState;
use std::fs;
use std::path::Path;

/// Helper to load and execute a .geolog file, returning the REPL state
fn load_geolog_file(path: &Path) -> Result<ReplState, String> {
    let content = fs::read_to_string(path)
        .map_err(|e| format!("Failed to read {}: {}", path.display(), e))?;

    let mut state = ReplState::new();

    // Execute the file content
    // The REPL processes complete inputs, so we feed it all at once
    let file = geolog::parse(&content)
        .map_err(|e| format!("Parse error in {}: {}", path.display(), e))?;

    // Process each declaration
    for decl in &file.declarations {
        match &decl.node {
            geolog::Declaration::Theory(t) => {
                // Build env from existing theories
                let mut env = geolog::elaborate::Env::new();
                for (name, theory) in &state.workspace.theories {
                    env.theories.insert(name.clone(), theory.clone());
                }

                let elab = geolog::elaborate::elaborate_theory(&mut env, t)
                    .map_err(|e| format!("Theory elaboration error in {}: {}", path.display(), e))?;

                state.workspace.add_theory(elab);
            }
            geolog::Declaration::Instance(inst) => {
                let structure = geolog::elaborate::elaborate_instance_ws(&mut state.workspace, inst)
                    .map_err(|e| format!("Instance elaboration error in {}: {}", path.display(), e))?;

                let theory_name = match &inst.theory {
                    geolog::TypeExpr::Path(p) => p.segments.join("/"),
                    _ => "Unknown".to_string(),
                };

                let entry = geolog::workspace::InstanceEntry::new(structure, theory_name);
                state.workspace.add_instance(inst.name.clone(), entry);
            }
            geolog::Declaration::Namespace(_) => {
                // Namespaces are currently no-ops
            }
            geolog::Declaration::Query(_) => {
                return Err(format!("Queries not yet supported in {}", path.display()));
            }
        }
    }

    Ok(state)
}

// ============================================================================
// Graph examples
// ============================================================================

#[test]
fn test_graph_example_parses() {
    let path = Path::new("examples/geolog/graph.geolog");
    let state = load_geolog_file(path).expect("graph.geolog should parse and elaborate");

    // Check theory
    let graph = state.workspace.theories.get("Graph").expect("Graph theory should exist");
    assert_eq!(graph.theory.signature.sorts.len(), 2, "Graph should have 2 sorts (V, E)");
    assert_eq!(graph.theory.signature.functions.len(), 2, "Graph should have 2 functions (src, tgt)");

    // Check instances
    assert!(state.workspace.instances.contains_key("Triangle"), "Triangle instance should exist");
    assert!(state.workspace.instances.contains_key("Loop"), "Loop instance should exist");
    assert!(state.workspace.instances.contains_key("Arrow"), "Arrow instance should exist");
    assert!(state.workspace.instances.contains_key("Diamond"), "Diamond instance should exist");
}

#[test]
fn test_graph_triangle_structure() {
    let path = Path::new("examples/geolog/graph.geolog");
    let state = load_geolog_file(path).unwrap();

    let triangle = state.workspace.instances.get("Triangle").unwrap();

    // Triangle has 3 vertices + 3 edges = 6 elements
    assert_eq!(triangle.structure.len(), 6, "Triangle should have 6 elements");

    // Check carrier sizes: V has 3, E has 3
    assert_eq!(triangle.structure.carrier_size(0), 3, "Triangle should have 3 vertices");
    assert_eq!(triangle.structure.carrier_size(1), 3, "Triangle should have 3 edges");
}

#[test]
fn test_graph_diamond_structure() {
    let path = Path::new("examples/geolog/graph.geolog");
    let state = load_geolog_file(path).unwrap();

    let diamond = state.workspace.instances.get("Diamond").unwrap();

    // Diamond has 4 vertices + 4 edges = 8 elements
    assert_eq!(diamond.structure.len(), 8, "Diamond should have 8 elements");
    assert_eq!(diamond.structure.carrier_size(0), 4, "Diamond should have 4 vertices");
    assert_eq!(diamond.structure.carrier_size(1), 4, "Diamond should have 4 edges");
}

// ============================================================================
// Petri net examples
// ============================================================================

#[test]
fn test_petri_net_example_parses() {
    let path = Path::new("examples/geolog/petri_net.geolog");
    let state = load_geolog_file(path).expect("petri_net.geolog should parse and elaborate");

    // Check theory
    let petri = state.workspace.theories.get("PetriNet").expect("PetriNet theory should exist");
    assert_eq!(petri.theory.signature.sorts.len(), 4, "PetriNet should have 4 sorts (P, T, In, Out)");
    assert_eq!(petri.theory.signature.functions.len(), 4, "PetriNet should have 4 functions");

    // Check instances
    assert!(state.workspace.instances.contains_key("ProducerConsumer"));
    assert!(state.workspace.instances.contains_key("MutualExclusion"));
}

#[test]
fn test_petri_net_producer_consumer() {
    let path = Path::new("examples/geolog/petri_net.geolog");
    let state = load_geolog_file(path).unwrap();

    let pc = state.workspace.instances.get("ProducerConsumer").unwrap();

    // ProducerConsumer: 3 places + 2 transitions + 2 input arcs + 2 output arcs = 9
    assert_eq!(pc.structure.len(), 9, "ProducerConsumer should have 9 elements");
}

#[test]
fn test_petri_net_mutual_exclusion() {
    let path = Path::new("examples/geolog/petri_net.geolog");
    let state = load_geolog_file(path).unwrap();

    let mutex = state.workspace.instances.get("MutualExclusion").unwrap();

    // MutualExclusion: 5 places + 4 transitions + 6 input arcs + 6 output arcs = 21
    assert_eq!(mutex.structure.len(), 21, "MutualExclusion should have 21 elements");
}

// ============================================================================
// Monoid example (theory only - instances need geolog-ulh)
// ============================================================================

#[test]
fn test_monoid_example_parses() {
    let path = Path::new("examples/geolog/monoid.geolog");
    let state = load_geolog_file(path).expect("monoid.geolog should parse and elaborate");

    // Check theory
    let monoid = state.workspace.theories.get("Monoid").expect("Monoid theory should exist");
    assert_eq!(monoid.theory.signature.sorts.len(), 1, "Monoid should have 1 sort (M)");
    assert_eq!(monoid.theory.signature.functions.len(), 2, "Monoid should have 2 functions (mul, id)");
    assert_eq!(monoid.theory.axioms.len(), 4, "Monoid should have 4 axioms");
}

// ============================================================================
// Preorder example
// ============================================================================

#[test]
fn test_preorder_example_parses() {
    let path = Path::new("examples/geolog/preorder.geolog");
    let state = load_geolog_file(path).expect("preorder.geolog should parse and elaborate");

    // Check theory
    let preorder = state.workspace.theories.get("Preorder").expect("Preorder theory should exist");
    assert_eq!(preorder.theory.signature.sorts.len(), 1, "Preorder should have 1 sort (X)");
    assert_eq!(preorder.theory.signature.relations.len(), 1, "Preorder should have 1 relation (leq)");
    assert_eq!(preorder.theory.axioms.len(), 2, "Preorder should have 2 axioms (refl, trans)");

    // Check instances
    assert!(state.workspace.instances.contains_key("Discrete3"));
    assert!(state.workspace.instances.contains_key("Chain3"));
}

// ============================================================================
// Meta-test: all examples should parse
// ============================================================================

#[test]
fn test_all_examples_parse() {
    let examples_dir = Path::new("examples/geolog");

    if !examples_dir.exists() {
        panic!("examples/geolog directory does not exist");
    }

    let mut failures = Vec::new();

    for entry in fs::read_dir(examples_dir).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();

        if path.extension().map_or(false, |ext| ext == "geolog") {
            if let Err(e) = load_geolog_file(&path) {
                failures.push(format!("{}: {}", path.display(), e));
            }
        }
    }

    if !failures.is_empty() {
        panic!(
            "The following example files failed to parse/elaborate:\n{}",
            failures.join("\n")
        );
    }
}
