//! Unit tests for structure serialization
//!
//! Tests for save/load functionality in the serialize module.

use geolog::core::Structure;
use geolog::elaborate::InstanceEntry;
use geolog::id::{NumericId, Slid};
use geolog::serialize::{load_structure, save_structure, StructureData};
use geolog::universe::Universe;
use tempfile::tempdir;

#[test]
fn test_structure_roundtrip() {
    let mut universe = Universe::new();

    let mut structure = Structure::new(2);
    structure.add_element(&mut universe, 0);
    structure.add_element(&mut universe, 0);
    structure.add_element(&mut universe, 1);

    let data = StructureData::from_structure(&structure);
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
fn test_instance_entry_element_management() {
    let mut universe = Universe::new();

    // Create a simple structure
    let mut structure = Structure::new(1);
    structure.add_element(&mut universe, 0);
    structure.add_element(&mut universe, 0);

    // Create instance entry
    let mut entry = InstanceEntry::new(structure, "TestTheory".to_string(), "TestTheory".to_string());
    entry.register_element("a".to_string(), Slid::from_usize(0));
    entry.register_element("b".to_string(), Slid::from_usize(1));

    // Verify element lookup works
    assert_eq!(entry.get_element("a"), Some(Slid::from_usize(0)));
    assert_eq!(entry.get_element("b"), Some(Slid::from_usize(1)));
    assert_eq!(entry.get_element("c"), None);

    // Verify reverse lookup works
    assert_eq!(entry.get_name(Slid::from_usize(0)), Some("a"));
    assert_eq!(entry.get_name(Slid::from_usize(1)), Some("b"));
}
