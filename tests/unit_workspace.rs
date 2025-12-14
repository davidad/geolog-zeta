//! Unit tests for workspace save/load

use geolog::core::{ElaboratedTheory, Signature, Structure, Theory};
use geolog::naming::NamingIndex;
use geolog::universe::Universe;
use geolog::workspace::{load_structure, save_structure, Workspace};
use std::fs;
use tempfile::tempdir;

#[test]
fn test_structure_roundtrip() {
    let mut universe = Universe::new();

    let mut structure = Structure::new(2);
    structure.add_element(&mut universe, 0);
    structure.add_element(&mut universe, 0);
    structure.add_element(&mut universe, 1);

    let data = geolog::workspace::StructureData::from_structure(&structure);
    let restored = data.to_structure();

    assert_eq!(restored.len(), 3);
    assert_eq!(restored.num_sorts(), 2);
}

#[test]
fn test_save_load_structure() {
    let mut universe = Universe::new();

    let mut structure = Structure::new(2);
    structure.add_element(&mut universe, 0);
    structure.add_element(&mut universe, 1);

    let dir = tempdir().unwrap();
    let path = dir.path().join("test.structure");
    save_structure(&structure, &path).expect("save should succeed");

    let loaded = load_structure(&path).expect("load should succeed");

    assert_eq!(loaded.len(), 2);
    assert_eq!(loaded.num_sorts(), 2);
}

#[test]
fn test_workspace_roundtrip() {
    let dir = tempdir().unwrap();
    let path = dir.path().join("workspace");
    let mut universe = Universe::new();
    let mut naming = NamingIndex::new();

    // Create workspace and add a theory
    {
        let mut workspace = Workspace::create(&path).expect("create should succeed");

        let mut sig = Signature::new();
        sig.add_sort("P".to_string());
        let theory = ElaboratedTheory {
            params: vec![],
            theory: Theory {
                name: "Simple".to_string(),
                signature: sig,
                axioms: vec![],
            },
        };
        workspace.add_theory(theory);
        workspace.save(&mut universe, &mut naming).expect("save should succeed");
    }

    // Reopen and verify
    {
        let workspace = Workspace::open(&path, &universe, &naming).expect("open should succeed");
        assert!(workspace.theories.contains_key("Simple"));
    }
}
