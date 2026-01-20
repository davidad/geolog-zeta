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

    // Use execute_geolog which handles everything correctly
    state
        .execute_geolog(&content)
        .map_err(|e| format!("Error in {}: {}", path.display(), e))?;

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
    let graph = state.theories.get("Graph").expect("Graph theory should exist");
    assert_eq!(graph.theory.signature.sorts.len(), 2, "Graph should have 2 sorts (V, E)");
    assert_eq!(graph.theory.signature.functions.len(), 2, "Graph should have 2 functions (src, tgt)");

    // Check instances
    assert!(state.instances.contains_key("Triangle"), "Triangle instance should exist");
    assert!(state.instances.contains_key("Loop"), "Loop instance should exist");
    assert!(state.instances.contains_key("Arrow"), "Arrow instance should exist");
    assert!(state.instances.contains_key("Diamond"), "Diamond instance should exist");
}

#[test]
fn test_graph_triangle_structure() {
    let path = Path::new("examples/geolog/graph.geolog");
    let state = load_geolog_file(path).unwrap();

    let triangle = state.instances.get("Triangle").unwrap();

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

    let diamond = state.instances.get("Diamond").unwrap();

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
    let petri = state.theories.get("PetriNet").expect("PetriNet theory should exist");
    assert_eq!(petri.theory.signature.sorts.len(), 4, "PetriNet should have 4 sorts (P, T, In, Out)");
    assert_eq!(petri.theory.signature.functions.len(), 4, "PetriNet should have 4 functions");

    // Check instances
    assert!(state.instances.contains_key("ProducerConsumer"));
    assert!(state.instances.contains_key("MutualExclusion"));
}

#[test]
fn test_petri_net_producer_consumer() {
    let path = Path::new("examples/geolog/petri_net.geolog");
    let state = load_geolog_file(path).unwrap();

    let pc = state.instances.get("ProducerConsumer").unwrap();

    // ProducerConsumer: 3 places + 2 transitions + 2 input arcs + 2 output arcs = 9
    assert_eq!(pc.structure.len(), 9, "ProducerConsumer should have 9 elements");
}

#[test]
fn test_petri_net_mutual_exclusion() {
    let path = Path::new("examples/geolog/petri_net.geolog");
    let state = load_geolog_file(path).unwrap();

    let mutex = state.instances.get("MutualExclusion").unwrap();

    // MutualExclusion: 5 places + 4 transitions + 6 input arcs + 6 output arcs = 21
    assert_eq!(mutex.structure.len(), 21, "MutualExclusion should have 21 elements");
}

// ============================================================================
// Monoid example (with product domain function support)
// ============================================================================

#[test]
fn test_monoid_example_parses() {
    let path = Path::new("examples/geolog/monoid.geolog");
    let state = load_geolog_file(path).expect("monoid.geolog should parse and elaborate");

    // Check theory
    let monoid = state.theories.get("Monoid").expect("Monoid theory should exist");
    assert_eq!(monoid.theory.signature.sorts.len(), 1, "Monoid should have 1 sort (M)");
    assert_eq!(monoid.theory.signature.functions.len(), 2, "Monoid should have 2 functions (mul, id)");
    assert_eq!(monoid.theory.axioms.len(), 4, "Monoid should have 4 axioms");

    // Check instances (product domain support via geolog-ulh)
    assert!(state.instances.contains_key("Trivial"), "Trivial monoid should exist");
    assert!(state.instances.contains_key("BoolAnd"), "BoolAnd monoid should exist");
    assert!(state.instances.contains_key("BoolOr"), "BoolOr monoid should exist");
}

#[test]
fn test_monoid_trivial_structure() {
    let path = Path::new("examples/geolog/monoid.geolog");
    let state = load_geolog_file(path).unwrap();

    let trivial = state.instances.get("Trivial").unwrap();

    // Trivial monoid has 1 element
    assert_eq!(trivial.structure.carrier_size(0), 1, "Trivial monoid should have 1 element");

    // Check id function (base domain: M -> M)
    // id: e -> e
    assert!(trivial.structure.functions[1].as_local().is_some(), "id should be a local function");
    let id_col = trivial.structure.functions[1].as_local().unwrap();
    assert_eq!(id_col.len(), 1, "id should have 1 entry");
    assert!(id_col[0].is_some(), "id(e) should be defined");

    // Check mul function (product domain: M × M -> M)
    // mul: (e,e) -> e
    if let geolog::core::FunctionColumn::ProductLocal { storage, field_sorts } = &trivial.structure.functions[0] {
        assert_eq!(field_sorts.len(), 2, "mul should have 2-element domain");
        assert_eq!(storage.defined_count(), 1, "mul should have 1 entry defined");
    } else {
        panic!("mul should be a ProductLocal function");
    }
}

#[test]
fn test_monoid_bool_and_structure() {
    let path = Path::new("examples/geolog/monoid.geolog");
    let state = load_geolog_file(path).unwrap();

    let bool_and = state.instances.get("BoolAnd").unwrap();

    // BoolAnd has 2 elements (T, F)
    assert_eq!(bool_and.structure.carrier_size(0), 2, "BoolAnd should have 2 elements");

    // Check mul function (product domain): all 4 entries should be defined
    if let geolog::core::FunctionColumn::ProductLocal { storage, .. } = &bool_and.structure.functions[0] {
        assert_eq!(storage.defined_count(), 4, "mul should have all 4 entries defined (2×2)");

        // Verify it's total
        assert!(storage.is_total(&[2, 2]), "mul should be total on 2×2 domain");
    } else {
        panic!("mul should be a ProductLocal function");
    }

    // Check id function (base domain): both entries defined
    let id_col = bool_and.structure.functions[1].as_local().unwrap();
    assert_eq!(id_col.len(), 2, "id should have 2 entries");
    assert!(id_col.iter().all(|opt| opt.is_some()), "id should be total");
}

#[test]
fn test_monoid_bool_or_structure() {
    let path = Path::new("examples/geolog/monoid.geolog");
    let state = load_geolog_file(path).unwrap();

    let bool_or = state.instances.get("BoolOr").unwrap();

    // BoolOr has 2 elements (T, F)
    assert_eq!(bool_or.structure.carrier_size(0), 2, "BoolOr should have 2 elements");

    // Check mul function is total
    if let geolog::core::FunctionColumn::ProductLocal { storage, .. } = &bool_or.structure.functions[0] {
        assert!(storage.is_total(&[2, 2]), "mul should be total on 2×2 domain");
    } else {
        panic!("mul should be a ProductLocal function");
    }
}

// ============================================================================
// Preorder example
// ============================================================================

#[test]
fn test_preorder_example_parses() {
    let path = Path::new("examples/geolog/preorder.geolog");
    let state = load_geolog_file(path).expect("preorder.geolog should parse and elaborate");

    // Check theory
    let preorder = state.theories.get("Preorder").expect("Preorder theory should exist");
    assert_eq!(preorder.theory.signature.sorts.len(), 1, "Preorder should have 1 sort (X)");
    assert_eq!(preorder.theory.signature.relations.len(), 1, "Preorder should have 1 relation (leq)");
    assert_eq!(preorder.theory.axioms.len(), 2, "Preorder should have 2 axioms (refl, trans)");

    // Check instances
    assert!(state.instances.contains_key("Discrete3"));
    assert!(state.instances.contains_key("Chain3"));
}

// ============================================================================
// Theories: GeologMeta and RelAlgIR
// ============================================================================

#[test]
fn test_geolog_meta_loads() {
    let path = Path::new("theories/GeologMeta.geolog");
    let state = load_geolog_file(path).expect("GeologMeta.geolog should parse and elaborate");

    let meta = state.theories.get("GeologMeta").expect("GeologMeta theory should exist");

    // GeologMeta is a large theory: 40 sorts, 76 functions, 3 relations
    assert_eq!(meta.theory.signature.sorts.len(), 40, "GeologMeta should have 40 sorts");
    assert_eq!(meta.theory.signature.functions.len(), 76, "GeologMeta should have 76 functions");
    assert_eq!(meta.theory.signature.relations.len(), 3, "GeologMeta should have 3 relations");

    // Check some key sorts exist
    assert!(meta.theory.signature.lookup_sort("Theory").is_some(), "Theory sort should exist");
    assert!(meta.theory.signature.lookup_sort("Srt").is_some(), "Srt sort should exist");
    assert!(meta.theory.signature.lookup_sort("Func").is_some(), "Func sort should exist");
    assert!(meta.theory.signature.lookup_sort("Elem").is_some(), "Elem sort should exist");
}

#[test]
fn test_relalg_ir_loads() {
    // First load GeologMeta (RelAlgIR extends it)
    let meta_content = fs::read_to_string("theories/GeologMeta.geolog")
        .expect("Failed to read GeologMeta.geolog");
    let ir_content = fs::read_to_string("theories/RelAlgIR.geolog")
        .expect("Failed to read RelAlgIR.geolog");

    let mut state = ReplState::new();

    state.execute_geolog(&meta_content)
        .expect("GeologMeta should load");
    state.execute_geolog(&ir_content)
        .expect("RelAlgIR should load");

    let ir = state.theories.get("RelAlgIR").expect("RelAlgIR theory should exist");

    // RelAlgIR has 78 sorts (40 from GeologMeta + 38 own)
    assert_eq!(ir.theory.signature.sorts.len(), 78, "RelAlgIR should have 78 sorts");

    // Check GeologMeta sorts are correctly qualified
    assert!(ir.theory.signature.lookup_sort("GeologMeta/Srt").is_some(),
        "GeologMeta/Srt should exist (inherited sort)");
    assert!(ir.theory.signature.lookup_sort("GeologMeta/Func").is_some(),
        "GeologMeta/Func should exist (inherited sort)");

    // Check RelAlgIR's own sorts exist (no prefix)
    assert!(ir.theory.signature.lookup_sort("Wire").is_some(),
        "Wire sort should exist");
    assert!(ir.theory.signature.lookup_sort("Op").is_some(),
        "Op sort should exist");
    assert!(ir.theory.signature.lookup_sort("ScanOp").is_some(),
        "ScanOp sort should exist");

    // Check functions are correctly qualified
    // GeologMeta's "Func/dom" should become "GeologMeta/Func/dom"
    assert!(ir.theory.signature.lookup_func("GeologMeta/Func/dom").is_some(),
        "GeologMeta/Func/dom should exist (inherited function)");
    assert!(ir.theory.signature.lookup_func("GeologMeta/Func/cod").is_some(),
        "GeologMeta/Func/cod should exist (inherited function)");

    // RelAlgIR's own functions
    assert!(ir.theory.signature.lookup_func("Wire/schema").is_some(),
        "Wire/schema should exist");
    assert!(ir.theory.signature.lookup_func("ScanOp/out").is_some(),
        "ScanOp/out should exist");

    // Check functions referencing inherited sorts have correct domain/codomain
    // ScanOp/srt : ScanOp -> GeologMeta/Srt
    let scan_srt = ir.theory.signature.lookup_func("ScanOp/srt")
        .expect("ScanOp/srt should exist");
    let func_info = &ir.theory.signature.functions[scan_srt];
    match &func_info.codomain {
        geolog::core::DerivedSort::Base(sort_id) => {
            let sort_name = &ir.theory.signature.sorts[*sort_id];
            assert_eq!(sort_name, "GeologMeta/Srt",
                "ScanOp/srt codomain should be GeologMeta/Srt");
        }
        _ => panic!("ScanOp/srt codomain should be a base sort"),
    }
}

// ============================================================================
// RelAlgIR query plan examples
// ============================================================================

/// Test that RelAlgIR instances can be created and represent query plans
#[test]
fn test_relalg_simple_examples() {
    // Load theories first
    let meta_content = fs::read_to_string("theories/GeologMeta.geolog")
        .expect("Failed to read GeologMeta.geolog");
    let ir_content = fs::read_to_string("theories/RelAlgIR.geolog")
        .expect("Failed to read RelAlgIR.geolog");
    let examples_content = fs::read_to_string("examples/geolog/relalg_simple.geolog")
        .expect("Failed to read relalg_simple.geolog");

    let mut state = ReplState::new();

    state.execute_geolog(&meta_content)
        .expect("GeologMeta should load");
    state.execute_geolog(&ir_content)
        .expect("RelAlgIR should load");
    state.execute_geolog(&examples_content)
        .expect("relalg_simple.geolog should load");

    // Check ScanV instance
    let scan_v = state.instances.get("ScanV")
        .expect("ScanV instance should exist");
    assert_eq!(scan_v.structure.len(), 7, "ScanV should have 7 elements");

    // Check FilterScan instance
    let filter_scan = state.instances.get("FilterScan")
        .expect("FilterScan instance should exist");
    assert_eq!(filter_scan.structure.len(), 18, "FilterScan should have 18 elements");

    // Verify FilterScan has the expected sorts populated
    // Get RelAlgIR theory for sort lookups
    let ir = state.theories.get("RelAlgIR").expect("RelAlgIR should exist");

    // Check Wire sort has 2 elements (w1, w2)
    let wire_sort = ir.theory.signature.lookup_sort("Wire").expect("Wire sort");
    assert_eq!(
        filter_scan.structure.carrier_size(wire_sort), 2,
        "FilterScan should have 2 Wire elements"
    );

    // Check FilterOp sort has 1 element
    let filter_sort = ir.theory.signature.lookup_sort("FilterOp").expect("FilterOp sort");
    assert_eq!(
        filter_scan.structure.carrier_size(filter_sort), 1,
        "FilterScan should have 1 FilterOp element"
    );

    // Check ScanOp sort has 1 element
    let scan_sort = ir.theory.signature.lookup_sort("ScanOp").expect("ScanOp sort");
    assert_eq!(
        filter_scan.structure.carrier_size(scan_sort), 1,
        "FilterScan should have 1 ScanOp element"
    );
}

// ============================================================================
// Meta-test: all examples should parse
// ============================================================================

/// Tests that all standalone .geolog example files parse and elaborate.
///
/// Note: Some examples require loading theories first (e.g., relalg_simple.geolog
/// requires GeologMeta and RelAlgIR). These are tested separately.
#[test]
fn test_all_examples_parse() {
    let examples_dir = Path::new("examples/geolog");

    if !examples_dir.exists() {
        panic!("examples/geolog directory does not exist");
    }

    // Examples that require loading theories first (tested separately)
    let requires_theories = ["relalg_simple.geolog"];

    let mut failures = Vec::new();

    for entry in fs::read_dir(examples_dir).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();

        // Skip files that require loading theories first
        if path.file_name()
            .and_then(|f| f.to_str())
            .is_some_and(|file_name| requires_theories.contains(&file_name))
        {
            continue;
        }

        if path.extension().is_some_and(|ext| ext == "geolog")
            && let Err(e) = load_geolog_file(&path) {
                failures.push(format!("{}: {}", path.display(), e));
            }
    }

    if !failures.is_empty() {
        panic!(
            "The following example files failed to parse/elaborate:\n{}",
            failures.join("\n")
        );
    }
}
