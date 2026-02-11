//! Property tests for the overlay system.
//!
//! The key invariant: reads through an overlay should match reads against
//! the materialized (committed) structure. This ensures the overlay correctly
//! represents all accumulated changes.

use std::collections::{BTreeSet, HashSet};
use std::sync::Arc;

use geolog::core::{SortId, Structure};
use geolog::id::{Luid, NumericId, Slid, Uuid};
use geolog::overlay::OverlayStructure;
use geolog::universe::Universe;
use geolog::serialize::save_structure;
use geolog::zerocopy::MappedStructure;

use proptest::prelude::*;
use tempfile::tempdir;

// ============================================================================
// STRATEGIES
// ============================================================================

/// Operations that can be applied to an overlay.
#[derive(Clone, Debug)]
enum OverlayOp {
    /// Add a new element with the given sort
    AddElement(SortId),
    /// Assert a relation tuple (rel_id, indices into current elements)
    AssertRelation(usize, Vec<usize>),
    /// Retract a relation tuple (rel_id, indices into current elements)
    RetractRelation(usize, Vec<usize>),
}

/// Strategy for generating overlay operations.
fn overlay_op(
    num_sorts: usize,
    num_relations: usize,
    arities: Vec<usize>,
    max_elements: usize,
) -> impl Strategy<Value = OverlayOp> {
    let arities_assert = arities.clone();
    let arities_retract = arities;

    prop_oneof![
        // Add element (weighted more heavily to build up elements)
        3 => (0..num_sorts).prop_map(OverlayOp::AddElement),
        // Assert relation
        2 => ((0..num_relations), prop::collection::vec(0..max_elements.max(1), 0..5))
            .prop_flat_map(move |(rel, indices)| {
                let arity = arities_assert.get(rel).copied().unwrap_or(1);
                let indices = if indices.len() >= arity {
                    indices[..arity].to_vec()
                } else {
                    // Pad with zeros if not enough indices
                    let mut v = indices;
                    while v.len() < arity {
                        v.push(0);
                    }
                    v
                };
                Just(OverlayOp::AssertRelation(rel, indices))
            }),
        // Retract relation
        1 => ((0..num_relations), prop::collection::vec(0..max_elements.max(1), 0..5))
            .prop_flat_map(move |(rel, indices)| {
                let arity = arities_retract.get(rel).copied().unwrap_or(1);
                let indices = if indices.len() >= arity {
                    indices[..arity].to_vec()
                } else {
                    let mut v = indices;
                    while v.len() < arity {
                        v.push(0);
                    }
                    v
                };
                Just(OverlayOp::RetractRelation(rel, indices))
            }),
    ]
}

/// Strategy for generating a sequence of overlay operations.
fn overlay_ops(
    num_sorts: usize,
    num_relations: usize,
    arities: Vec<usize>,
    num_ops: usize,
) -> impl Strategy<Value = Vec<OverlayOp>> {
    // We generate ops that reference element indices up to some max
    // The actual indices get clamped to valid range during execution
    prop::collection::vec(
        overlay_op(num_sorts, num_relations, arities, 100),
        0..num_ops,
    )
}

// ============================================================================
// TEST HELPERS
// ============================================================================

/// Create a base structure with some initial elements and relations.
fn create_base_structure(
    universe: &mut Universe,
    num_sorts: usize,
    num_elements_per_sort: usize,
    arities: &[usize],
) -> Structure {
    let mut structure = Structure::new(num_sorts);

    // Add initial elements
    for sort in 0..num_sorts {
        for _ in 0..num_elements_per_sort {
            structure.add_element(universe, sort);
        }
    }

    // Initialize relations
    structure.init_relations(arities);

    structure
}

/// Apply an operation to an overlay, tracking current element count.
fn apply_op(
    overlay: &mut OverlayStructure,
    universe: &mut Universe,
    op: &OverlayOp,
    element_count: &mut usize,
) {
    let num_sorts = overlay.num_sorts();
    let num_relations = overlay.num_relations();

    match op {
        OverlayOp::AddElement(sort) => {
            // Clamp sort to valid range
            let sort = *sort % num_sorts;
            let luid = universe.intern(Uuid::now_v7());
            overlay.add_element(luid, sort);
            *element_count += 1;
        }
        OverlayOp::AssertRelation(rel_id, indices) => {
            if *element_count == 0 || num_relations == 0 {
                return; // Can't assert tuples without elements or relations
            }
            // Clamp rel_id and indices to valid range
            let rel_id = *rel_id % num_relations;
            let tuple: Vec<Slid> = indices
                .iter()
                .map(|&i| Slid::from_usize(i % *element_count))
                .collect();
            overlay.assert_relation(rel_id, tuple);
        }
        OverlayOp::RetractRelation(rel_id, indices) => {
            if *element_count == 0 || num_relations == 0 {
                return;
            }
            let rel_id = *rel_id % num_relations;
            let tuple: Vec<Slid> = indices
                .iter()
                .map(|&i| Slid::from_usize(i % *element_count))
                .collect();
            overlay.retract_relation(rel_id, tuple);
        }
    }
}

/// Collect all elements from a MappedStructure into a set.
fn collect_elements_mapped(mapped: &MappedStructure) -> HashSet<(Slid, Luid, SortId)> {
    mapped.elements().collect()
}

/// Collect all elements from an overlay into a set.
fn collect_elements_overlay(overlay: &OverlayStructure) -> HashSet<(Slid, Luid, SortId)> {
    overlay.elements().collect()
}

/// Collect all live tuples from a relation in a MappedStructure.
fn collect_tuples_mapped(mapped: &MappedStructure, rel_id: usize) -> BTreeSet<Vec<Slid>> {
    mapped
        .relation(rel_id)
        .map(|r| r.live_tuples().map(|t| t.collect()).collect())
        .unwrap_or_default()
}

/// Collect all live tuples from a relation in an overlay.
fn collect_tuples_overlay(overlay: &OverlayStructure, rel_id: usize) -> BTreeSet<Vec<Slid>> {
    overlay
        .relation(rel_id)
        .map(|r| r.live_tuples().collect())
        .unwrap_or_default()
}

// ============================================================================
// PROPERTY TESTS
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]

    /// The committed structure should have the same elements as the overlay.
    #[test]
    fn overlay_commit_preserves_elements(
        num_sorts in 1usize..5,
        num_elements_per_sort in 0usize..10,
        ops in overlay_ops(4, 3, vec![1, 2, 3], 50),
    ) {
        let dir = tempdir().unwrap();
        let base_path = dir.path().join("base.structure");
        let commit_path = dir.path().join("commit.structure");

        let mut universe = Universe::new();
        let arities = vec![1, 2, 3];

        // Create and save base
        let base = create_base_structure(&mut universe, num_sorts, num_elements_per_sort, &arities);
        save_structure(&base, &base_path).unwrap();

        // Load and create overlay
        let mapped = MappedStructure::open(&base_path).unwrap();
        let mut overlay = OverlayStructure::new(Arc::new(mapped));

        // Apply operations
        let mut element_count = overlay.len();
        for op in &ops {
            apply_op(&mut overlay, &mut universe, op, &mut element_count);
        }

        // Collect elements from overlay
        let overlay_elements = collect_elements_overlay(&overlay);

        // Commit and collect elements from committed structure
        let committed = overlay.commit(&commit_path).unwrap();
        let committed_elements = collect_elements_mapped(&committed);

        // They should match
        prop_assert_eq!(
            overlay_elements.len(),
            committed_elements.len(),
            "Element count mismatch"
        );

        // Check each element
        for (slid, luid, sort) in &overlay_elements {
            prop_assert!(
                committed_elements.contains(&(*slid, *luid, *sort)),
                "Element {:?} in overlay but not in committed",
                (slid, luid, sort)
            );
        }
    }

    /// The committed structure should have the same relation tuples as the overlay.
    #[test]
    fn overlay_commit_preserves_relations(
        num_sorts in 1usize..4,
        num_elements_per_sort in 1usize..8,
        ops in overlay_ops(3, 3, vec![1, 2, 2], 30),
    ) {
        let dir = tempdir().unwrap();
        let base_path = dir.path().join("base.structure");
        let commit_path = dir.path().join("commit.structure");

        let mut universe = Universe::new();
        let arities = vec![1, 2, 2]; // unary, binary, binary

        // Create and save base
        let base = create_base_structure(&mut universe, num_sorts, num_elements_per_sort, &arities);
        save_structure(&base, &base_path).unwrap();

        // Load and create overlay
        let mapped = MappedStructure::open(&base_path).unwrap();
        let mut overlay = OverlayStructure::new(Arc::new(mapped));

        // Apply operations
        let mut element_count = overlay.len();
        for op in &ops {
            apply_op(&mut overlay, &mut universe, op, &mut element_count);
        }

        // Collect tuples from overlay for each relation
        let overlay_tuples: Vec<BTreeSet<Vec<Slid>>> = (0..arities.len())
            .map(|rel_id| collect_tuples_overlay(&overlay, rel_id))
            .collect();

        // Commit
        let committed = overlay.commit(&commit_path).unwrap();

        // Collect tuples from committed
        let committed_tuples: Vec<BTreeSet<Vec<Slid>>> = (0..arities.len())
            .map(|rel_id| collect_tuples_mapped(&committed, rel_id))
            .collect();

        // They should match for each relation
        for (rel_id, (overlay_set, committed_set)) in
            overlay_tuples.iter().zip(committed_tuples.iter()).enumerate()
        {
            prop_assert_eq!(
                overlay_set,
                committed_set,
                "Relation {} tuples mismatch.\nOverlay: {:?}\nCommitted: {:?}",
                rel_id,
                overlay_set,
                committed_set
            );
        }
    }

    /// Element lookups should be consistent between overlay and committed structure.
    #[test]
    fn overlay_element_lookups_match_committed(
        num_sorts in 1usize..5,
        num_elements_per_sort in 0usize..10,
        ops in overlay_ops(4, 2, vec![1, 2], 40),
    ) {
        let dir = tempdir().unwrap();
        let base_path = dir.path().join("base.structure");
        let commit_path = dir.path().join("commit.structure");

        let mut universe = Universe::new();
        let arities = vec![1, 2];

        // Create and save base
        let base = create_base_structure(&mut universe, num_sorts, num_elements_per_sort, &arities);
        save_structure(&base, &base_path).unwrap();

        // Load and create overlay
        let mapped = MappedStructure::open(&base_path).unwrap();
        let mut overlay = OverlayStructure::new(Arc::new(mapped));

        // Apply operations
        let mut element_count = overlay.len();
        for op in &ops {
            apply_op(&mut overlay, &mut universe, op, &mut element_count);
        }

        // Commit
        let committed = overlay.commit(&commit_path).unwrap();

        // Check that len matches
        prop_assert_eq!(overlay.len(), committed.len(), "len() mismatch");

        // Check each element lookup
        for i in 0..overlay.len() {
            let slid = Slid::from_usize(i);

            let overlay_luid = overlay.get_luid(slid);
            let committed_luid = committed.get_luid(slid);
            prop_assert_eq!(
                overlay_luid,
                committed_luid,
                "get_luid({:?}) mismatch",
                slid
            );

            let overlay_sort = overlay.get_sort(slid);
            let committed_sort = committed.get_sort(slid);
            prop_assert_eq!(
                overlay_sort,
                committed_sort,
                "get_sort({:?}) mismatch",
                slid
            );
        }
    }

    /// Rollback should restore the overlay to match the base.
    #[test]
    fn overlay_rollback_restores_base(
        num_sorts in 1usize..4,
        num_elements_per_sort in 1usize..8,
        ops in overlay_ops(3, 2, vec![1, 2], 20),
    ) {
        let dir = tempdir().unwrap();
        let base_path = dir.path().join("base.structure");

        let mut universe = Universe::new();
        let arities = vec![1, 2];

        // Create base with some initial relation tuples
        let mut base = create_base_structure(&mut universe, num_sorts, num_elements_per_sort, &arities);
        // Add some initial tuples
        if base.len() >= 2 {
            base.assert_relation(0, vec![Slid::from_usize(0)]);
            base.assert_relation(1, vec![Slid::from_usize(0), Slid::from_usize(1)]);
        }
        save_structure(&base, &base_path).unwrap();

        // Load and create overlay
        let mapped = Arc::new(MappedStructure::open(&base_path).unwrap());
        let mut overlay = OverlayStructure::new(mapped.clone());

        // Record base state
        let base_len = overlay.len();
        let base_tuples_0 = collect_tuples_overlay(&overlay, 0);
        let base_tuples_1 = collect_tuples_overlay(&overlay, 1);

        // Apply operations (mutate the overlay)
        let mut element_count = overlay.len();
        for op in &ops {
            apply_op(&mut overlay, &mut universe, op, &mut element_count);
        }

        // Rollback
        overlay.rollback();

        // Should match base again
        prop_assert_eq!(overlay.len(), base_len, "len() should match base after rollback");
        prop_assert!(overlay.is_clean(), "should be clean after rollback");

        let after_tuples_0 = collect_tuples_overlay(&overlay, 0);
        let after_tuples_1 = collect_tuples_overlay(&overlay, 1);

        prop_assert_eq!(base_tuples_0, after_tuples_0, "Relation 0 should match base after rollback");
        prop_assert_eq!(base_tuples_1, after_tuples_1, "Relation 1 should match base after rollback");
    }

    /// Assert then retract should result in no change (for overlay-only tuples).
    #[test]
    fn assert_then_retract_is_noop(
        num_elements in 2usize..10,
        rel_idx_a in 0usize..10,
        rel_idx_b in 0usize..10,
    ) {
        let dir = tempdir().unwrap();
        let base_path = dir.path().join("base.structure");

        let mut universe = Universe::new();

        // Create base with elements but no relation tuples
        let mut base = Structure::new(1);
        for _ in 0..num_elements {
            base.add_element(&mut universe, 0);
        }
        base.init_relations(&[2]); // binary relation
        save_structure(&base, &base_path).unwrap();

        // Load and create overlay
        let mapped = MappedStructure::open(&base_path).unwrap();
        let mut overlay = OverlayStructure::new(Arc::new(mapped));

        // Create a tuple
        let idx_a = rel_idx_a % num_elements;
        let idx_b = rel_idx_b % num_elements;
        let tuple = vec![Slid::from_usize(idx_a), Slid::from_usize(idx_b)];

        // Should start with no tuples
        let initial_tuples = collect_tuples_overlay(&overlay, 0);
        prop_assert!(initial_tuples.is_empty(), "Should start empty");

        // Assert
        overlay.assert_relation(0, tuple.clone());
        let after_assert = collect_tuples_overlay(&overlay, 0);
        prop_assert!(after_assert.contains(&tuple), "Should contain tuple after assert");

        // Retract
        overlay.retract_relation(0, tuple.clone());
        let after_retract = collect_tuples_overlay(&overlay, 0);
        prop_assert!(!after_retract.contains(&tuple), "Should not contain tuple after retract");

        // Should be clean (no net change)
        prop_assert!(overlay.is_clean(), "Should be clean after assert+retract of new tuple");
    }

    /// Retracting a base tuple should hide it from iteration.
    #[test]
    fn retract_hides_base_tuple(
        num_elements in 3usize..10,
    ) {
        let dir = tempdir().unwrap();
        let base_path = dir.path().join("base.structure");

        let mut universe = Universe::new();

        // Create base with elements and a relation tuple
        let mut base = Structure::new(1);
        for _ in 0..num_elements {
            base.add_element(&mut universe, 0);
        }
        base.init_relations(&[2]); // binary relation
        let base_tuple = vec![Slid::from_usize(0), Slid::from_usize(1)];
        base.assert_relation(0, base_tuple.clone());
        save_structure(&base, &base_path).unwrap();

        // Load and create overlay
        let mapped = MappedStructure::open(&base_path).unwrap();
        let mut overlay = OverlayStructure::new(Arc::new(mapped));

        // Should see the base tuple
        let initial = collect_tuples_overlay(&overlay, 0);
        prop_assert!(initial.contains(&base_tuple), "Should see base tuple initially");

        // Retract it
        overlay.retract_relation(0, base_tuple.clone());

        // Should no longer see it
        let after = collect_tuples_overlay(&overlay, 0);
        prop_assert!(!after.contains(&base_tuple), "Should not see base tuple after retract");

        // But overlay should not be clean (we have a retraction)
        prop_assert!(!overlay.is_clean(), "Should not be clean with a retraction");
    }

    /// Multiple commits should produce identical results.
    #[test]
    fn double_commit_is_idempotent(
        num_sorts in 1usize..3,
        num_elements_per_sort in 1usize..5,
        ops in overlay_ops(2, 2, vec![1, 2], 15),
    ) {
        let dir = tempdir().unwrap();
        let base_path = dir.path().join("base.structure");
        let commit1_path = dir.path().join("commit1.structure");
        let commit2_path = dir.path().join("commit2.structure");

        let mut universe = Universe::new();
        let arities = vec![1, 2];

        // Create and save base
        let base = create_base_structure(&mut universe, num_sorts, num_elements_per_sort, &arities);
        save_structure(&base, &base_path).unwrap();

        // Load and create overlay
        let mapped = MappedStructure::open(&base_path).unwrap();
        let mut overlay = OverlayStructure::new(Arc::new(mapped));

        // Apply operations
        let mut element_count = overlay.len();
        for op in &ops {
            apply_op(&mut overlay, &mut universe, op, &mut element_count);
        }

        // Commit twice
        let committed1 = overlay.commit(&commit1_path).unwrap();
        let committed2 = overlay.commit(&commit2_path).unwrap();

        // Both should have the same content
        prop_assert_eq!(committed1.len(), committed2.len(), "len() should match");

        for rel_id in 0..arities.len() {
            let tuples1 = collect_tuples_mapped(&committed1, rel_id);
            let tuples2 = collect_tuples_mapped(&committed2, rel_id);
            prop_assert_eq!(tuples1, tuples2, "Relation {} should match", rel_id);
        }
    }
}

// ============================================================================
// ADDITIONAL TARGETED TESTS
// ============================================================================

#[test]
fn test_empty_overlay_commit() {
    let dir = tempdir().unwrap();
    let base_path = dir.path().join("base.structure");
    let commit_path = dir.path().join("commit.structure");

    let mut universe = Universe::new();

    // Create base with some content
    let mut base = Structure::new(2);
    base.add_element(&mut universe, 0);
    base.add_element(&mut universe, 1);
    base.init_relations(&[1]);
    base.assert_relation(0, vec![Slid::from_usize(0)]);
    save_structure(&base, &base_path).unwrap();

    // Create overlay but don't modify it
    let mapped = MappedStructure::open(&base_path).unwrap();
    let overlay = OverlayStructure::new(Arc::new(mapped));

    assert!(overlay.is_clean());

    // Commit should produce identical structure
    let committed = overlay.commit(&commit_path).unwrap();

    assert_eq!(committed.len(), 2);
    assert_eq!(collect_tuples_mapped(&committed, 0).len(), 1);
}

#[test]
fn test_overlay_with_mixed_element_tuples() {
    // Test tuples that reference both base and overlay elements
    let dir = tempdir().unwrap();
    let base_path = dir.path().join("base.structure");
    let commit_path = dir.path().join("commit.structure");

    let mut universe = Universe::new();

    // Create base with one element
    let mut base = Structure::new(1);
    let (base_elem, _) = base.add_element(&mut universe, 0);
    base.init_relations(&[2]); // binary relation
    save_structure(&base, &base_path).unwrap();

    // Create overlay and add an element
    let mapped = MappedStructure::open(&base_path).unwrap();
    let mut overlay = OverlayStructure::new(Arc::new(mapped));

    let new_luid = universe.intern(Uuid::now_v7());
    let new_elem = overlay.add_element(new_luid, 0);

    // Assert a tuple mixing base and overlay elements
    let mixed_tuple = vec![base_elem, new_elem];
    overlay.assert_relation(0, mixed_tuple.clone());

    // Verify we can see it
    let tuples = collect_tuples_overlay(&overlay, 0);
    assert!(tuples.contains(&mixed_tuple));

    // Commit and verify
    let committed = overlay.commit(&commit_path).unwrap();
    let committed_tuples = collect_tuples_mapped(&committed, 0);
    assert_eq!(committed_tuples.len(), 1);
}
