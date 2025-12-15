//! Unit tests for workspace save/load

use geolog::core::{ElaboratedTheory, Signature, Structure, Theory};
use geolog::id::{NumericId, Slid};
use geolog::universe::Universe;
use geolog::workspace::{InstanceEntry, Workspace, load_structure, save_structure};
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
fn test_workspace_theory_management() {
    // Create workspace
    let mut workspace = Workspace::new();

    // Add a theory
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

    // Verify theory is accessible
    assert!(workspace.theories.contains_key("Simple"));
    let t = workspace.get_theory("Simple").unwrap();
    assert_eq!(t.theory.signature.sorts.len(), 1);
}

#[test]
fn test_workspace_instance_management() {
    let mut workspace = Workspace::new();

    // Create a simple structure
    let mut structure = Structure::new(1);
    structure.add_element(&mut workspace.universe, 0);
    structure.add_element(&mut workspace.universe, 0);

    // Create instance entry
    let mut entry = InstanceEntry::new(structure, "TestTheory".to_string());
    entry.register_element("a".to_string(), Slid::from_usize(0));
    entry.register_element("b".to_string(), Slid::from_usize(1));

    workspace.add_instance("TestInstance".to_string(), entry);

    // Verify instance is accessible
    assert!(workspace.instances.contains_key("TestInstance"));
    let inst = workspace.get_instance("TestInstance").unwrap();
    assert_eq!(inst.structure.len(), 2);
    assert_eq!(inst.get_element("a"), Some(Slid::from_usize(0)));
    assert_eq!(inst.get_element("b"), Some(Slid::from_usize(1)));
}

#[test]
fn test_workspace_with_path() {
    let dir = tempdir().unwrap();
    let path = dir.path().join("workspace");

    let workspace = Workspace::with_path(&path);
    assert_eq!(workspace.path, Some(path));
}
