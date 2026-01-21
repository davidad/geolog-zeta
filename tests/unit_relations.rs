//! Unit tests for relation storage

use geolog::core::{RelationStorage, Structure, VecRelation};
use geolog::id::{NumericId, Slid};
use geolog::universe::Universe;
use geolog::serialize::{load_structure, save_structure};
use tempfile::tempdir;

/// Helper to create Slid from integer
fn slid(n: usize) -> Slid {
    Slid::from_usize(n)
}

#[test]
fn test_vec_relation_basic() {
    let mut rel = VecRelation::new(2);

    // Insert a tuple
    assert!(rel.insert(vec![slid(0), slid(1)]));
    assert_eq!(rel.len(), 1);

    // Check containment
    assert!(rel.contains(&[slid(0), slid(1)]));
    assert!(!rel.contains(&[slid(1), slid(0)]));
    assert!(!rel.contains(&[slid(0), slid(0)]));

    // Insert another tuple
    assert!(rel.insert(vec![slid(1), slid(0)]));
    assert_eq!(rel.len(), 2);

    // Duplicate insert returns false
    assert!(!rel.insert(vec![slid(0), slid(1)]));
    assert_eq!(rel.len(), 2);
}

#[test]
fn test_vec_relation_remove() {
    let mut rel = VecRelation::new(2);

    rel.insert(vec![slid(0), slid(1)]);
    rel.insert(vec![slid(1), slid(2)]);
    assert_eq!(rel.len(), 2);

    // Remove existing tuple
    assert!(rel.remove(&[slid(0), slid(1)]));
    assert_eq!(rel.len(), 1);
    assert!(!rel.contains(&[slid(0), slid(1)]));
    assert!(rel.contains(&[slid(1), slid(2)]));

    // Remove non-existent tuple
    assert!(!rel.remove(&[slid(0), slid(1)]));
    assert_eq!(rel.len(), 1);

    // Re-insert removed tuple (should reuse tuple ID)
    assert!(rel.insert(vec![slid(0), slid(1)]));
    assert_eq!(rel.len(), 2);
    assert!(rel.contains(&[slid(0), slid(1)]));
}

#[test]
fn test_vec_relation_iter() {
    let mut rel = VecRelation::new(2);

    rel.insert(vec![slid(0), slid(1)]);
    rel.insert(vec![slid(1), slid(2)]);
    rel.insert(vec![slid(2), slid(3)]);

    let tuples: Vec<_> = rel.iter().collect();
    assert_eq!(tuples.len(), 3);

    // Remove middle tuple
    rel.remove(&[slid(1), slid(2)]);

    let tuples: Vec<_> = rel.iter().collect();
    assert_eq!(tuples.len(), 2);
}

#[test]
fn test_structure_relations() {
    let mut universe = Universe::new();
    let mut structure = Structure::new(2);

    // Add elements to two sorts
    let (a, _) = structure.add_element(&mut universe, 0);
    let (b, _) = structure.add_element(&mut universe, 0);
    let (x, _) = structure.add_element(&mut universe, 1);
    let (y, _) = structure.add_element(&mut universe, 1);

    // Initialize a binary relation (arity 2)
    structure.init_relations(&[2]);

    // Assert some tuples
    assert!(structure.assert_relation(0, vec![a, x]));
    assert!(structure.assert_relation(0, vec![b, y]));
    assert_eq!(structure.get_relation(0).len(), 2);

    // Query
    assert!(structure.query_relation(0, &[a, x]));
    assert!(!structure.query_relation(0, &[a, y]));

    // Retract
    assert!(structure.retract_relation(0, &[a, x]));
    assert!(!structure.query_relation(0, &[a, x]));
}

#[test]
fn test_relation_serialization_roundtrip() {
    let mut universe = Universe::new();
    let mut structure = Structure::new(2);

    // Add elements
    let (a, _) = structure.add_element(&mut universe, 0);
    let (b, _) = structure.add_element(&mut universe, 0);
    let (x, _) = structure.add_element(&mut universe, 1);

    // Initialize relation and add tuples
    structure.init_relations(&[2]);
    structure.assert_relation(0, vec![a, x]);
    structure.assert_relation(0, vec![b, x]);

    // Serialize and deserialize via StructureData
    let data = geolog::serialize::StructureData::from_structure(&structure);
    let restored = data.to_structure();

    // Check relation was preserved
    assert_eq!(restored.num_relations(), 1);
    assert_eq!(restored.get_relation(0).len(), 2);
    assert!(restored.query_relation(0, &[a, x]));
    assert!(restored.query_relation(0, &[b, x]));
    assert!(!restored.query_relation(0, &[a, b]));
}

#[test]
fn test_relation_file_roundtrip() {
    let mut universe = Universe::new();
    let mut structure = Structure::new(2);

    // Add elements
    let (a, _) = structure.add_element(&mut universe, 0);
    let (b, _) = structure.add_element(&mut universe, 1);

    // Initialize relation and add tuples
    structure.init_relations(&[2]);
    structure.assert_relation(0, vec![a, b]);

    // Save to file
    let dir = tempdir().unwrap();
    let path = dir.path().join("test.structure");
    save_structure(&structure, &path).expect("save should succeed");

    // Load from file
    let loaded = load_structure(&path).expect("load should succeed");

    // Check relation was preserved
    assert_eq!(loaded.num_relations(), 1);
    assert!(loaded.query_relation(0, &[a, b]));
}

#[test]
fn test_unary_relation() {
    let mut rel = VecRelation::new(1);

    rel.insert(vec![slid(42)]);
    rel.insert(vec![slid(100)]);

    assert!(rel.contains(&[slid(42)]));
    assert!(rel.contains(&[slid(100)]));
    assert!(!rel.contains(&[slid(0)]));
    assert_eq!(rel.len(), 2);
}

#[test]
fn test_ternary_relation() {
    let mut rel = VecRelation::new(3);

    rel.insert(vec![slid(1), slid(2), slid(3)]);
    rel.insert(vec![slid(4), slid(5), slid(6)]);

    assert!(rel.contains(&[slid(1), slid(2), slid(3)]));
    assert!(rel.contains(&[slid(4), slid(5), slid(6)]));
    assert!(!rel.contains(&[slid(1), slid(2), slid(4)]));
    assert_eq!(rel.len(), 2);
}
