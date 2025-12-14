//! Unit tests for GeologMeta theory and structure conversion

use geolog::core::{DerivedSort, ElaboratedTheory, Signature, Theory};
use geolog::meta::{geolog_meta, structure_to_theory, theory_to_structure};
use geolog::naming::NamingIndex;
use geolog::universe::Universe;

#[test]
fn test_theory_to_structure() {
    // Create a simple theory
    let mut sig = Signature::new();
    sig.add_sort("P".to_string());
    sig.add_sort("T".to_string());
    sig.add_function(
        "src".to_string(),
        DerivedSort::Base(1), // T
        DerivedSort::Base(0), // P
    );

    let theory = ElaboratedTheory {
        params: vec![],
        theory: Theory {
            name: "PetriNet".to_string(),
            signature: sig,
            axioms: vec![],
        },
    };

    let mut universe = Universe::new();
    let mut naming = NamingIndex::new();
    let structure = theory_to_structure(&theory, &mut universe, &mut naming);

    // Check basic structure properties
    assert!(!structure.is_empty());

    // Check we have elements in the structure
    // Should have: 1 Theory, 2 Srt, 1 Func, plus DSort/BaseDS elements
    assert!(structure.len() > 5, "Expected more than 5 elements, got {}", structure.len());

    // Verify names were registered in naming index
    assert!(naming.lookup_unique("PetriNet").is_some());
    assert!(naming.lookup_unique("P").is_some());
    assert!(naming.lookup_unique("T").is_some());
    assert!(naming.lookup_unique("src").is_some());
}

#[test]
fn test_geolog_meta_parses() {
    // Just ensure GeologMeta itself can be loaded
    let meta = geolog_meta();
    assert_eq!(meta.theory.name, "GeologMeta");

    // Should have lots of sorts and functions (no Name sort anymore)
    assert!(meta.theory.signature.sorts.len() >= 25, "Expected many sorts, got {}", meta.theory.signature.sorts.len());
    assert!(meta.theory.signature.functions.len() >= 40, "Expected many functions, got {}", meta.theory.signature.functions.len());
    assert!(meta.theory.signature.relations.len() >= 3, "Expected some relations");
}

#[test]
fn test_theory_roundtrip() {
    // Create a theory with sorts, functions, and a relation
    let mut sig = Signature::new();
    let p_id = sig.add_sort("P".to_string());
    let t_id = sig.add_sort("T".to_string());
    sig.add_function(
        "src".to_string(),
        DerivedSort::Base(t_id),
        DerivedSort::Base(p_id),
    );
    sig.add_function(
        "tgt".to_string(),
        DerivedSort::Base(t_id),
        DerivedSort::Base(p_id),
    );
    // Add a relation with record domain
    sig.add_relation(
        "enabled".to_string(),
        DerivedSort::Product(vec![
            ("place".to_string(), DerivedSort::Base(p_id)),
            ("trans".to_string(), DerivedSort::Base(t_id)),
        ]),
    );

    let original = ElaboratedTheory {
        params: vec![],
        theory: Theory {
            name: "PetriNet".to_string(),
            signature: sig,
            axioms: vec![],
        },
    };

    // Convert to structure
    let mut universe = Universe::new();
    let mut naming = NamingIndex::new();
    let structure = theory_to_structure(&original, &mut universe, &mut naming);

    // Convert back
    let reconstructed = structure_to_theory(&structure, &universe, &naming)
        .expect("roundtrip should succeed");

    // Verify basic properties match
    assert_eq!(reconstructed.theory.name, "PetriNet");
    assert_eq!(reconstructed.theory.signature.sorts.len(), 2);
    assert_eq!(reconstructed.theory.signature.functions.len(), 2);
    assert_eq!(reconstructed.theory.signature.relations.len(), 1);

    // Verify sort names
    assert!(reconstructed.theory.signature.lookup_sort("P").is_some());
    assert!(reconstructed.theory.signature.lookup_sort("T").is_some());

    // Verify function names
    assert!(reconstructed.theory.signature.lookup_func("src").is_some());
    assert!(reconstructed.theory.signature.lookup_func("tgt").is_some());

    // Verify relation name
    assert!(reconstructed.theory.signature.lookup_rel("enabled").is_some());
}
