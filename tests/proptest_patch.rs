//! Property tests for Patch algebra (diff/apply roundtrips)

mod generators;

use generators::{check_structure_invariants, structures_equivalent, StructureParams};
use geolog::core::Structure;
use geolog::naming::NamingIndex;
use geolog::patch::{apply_patch, diff, to_initial_patch, Patch};
use geolog::universe::Universe;
use proptest::prelude::*;
use std::collections::HashSet;

proptest! {
    /// Empty patch is identity: apply_patch(s, empty) == s
    #[test]
    fn empty_patch_is_identity(
        (structure, mut universe) in generators::arb_structure(StructureParams {
            num_sorts: 3,
            max_elements_per_sort: 8,
        })
    ) {
        let empty_patch = Patch::new(None, structure.num_sorts(), structure.num_functions());
        let mut naming = NamingIndex::new();

        let result = apply_patch(&structure, &empty_patch, &mut universe, &mut naming);
        prop_assert!(result.is_ok());

        let result = result.unwrap();
        prop_assert_eq!(result.len(), structure.len());
        prop_assert_eq!(result.num_sorts(), structure.num_sorts());

        // Check same UUIDs
        prop_assert!(structures_equivalent(&result, &structure, &universe, &universe));
    }

    /// diff(s, s) produces empty patch
    #[test]
    fn diff_same_is_empty(
        (structure, universe) in generators::arb_structure(StructureParams {
            num_sorts: 3,
            max_elements_per_sort: 8,
        })
    ) {
        let naming = NamingIndex::new();

        let patch = diff(&structure, &structure, &universe, &naming, &naming);

        prop_assert!(patch.is_empty());
    }

    /// to_initial_patch creates patch that builds structure from empty
    #[test]
    fn initial_patch_builds_from_empty(
        (structure, mut universe) in generators::arb_structure(StructureParams {
            num_sorts: 3,
            max_elements_per_sort: 8,
        })
    ) {
        // Build naming for structure elements
        let mut naming = NamingIndex::new();
        for &luid in &structure.luids {
            if let Some(uuid) = universe.get(luid) {
                naming.insert(uuid, vec![format!("elem_{}", luid)]);
            }
        }

        let patch = to_initial_patch(&structure, &universe, &naming);

        // Apply to empty structure
        let empty = Structure::new(structure.num_sorts());
        let mut result_naming = NamingIndex::new();
        let result = apply_patch(&empty, &patch, &mut universe, &mut result_naming);

        prop_assert!(result.is_ok());
        let result = result.unwrap();

        // Should have same number of elements
        prop_assert_eq!(result.len(), structure.len());

        // Should have same UUIDs
        prop_assert!(structures_equivalent(&result, &structure, &universe, &universe));
    }

    /// Element additions are tracked in patch
    #[test]
    fn additions_tracked(
        num_elements in 1usize..10,
    ) {
        let mut universe = Universe::new();
        let mut naming = NamingIndex::new();

        let old = Structure::new(2);
        let mut new = Structure::new(2);

        for i in 0..num_elements {
            let (_, luid) = new.add_element(&mut universe, i % 2);
            if let Some(uuid) = universe.get(luid) {
                naming.insert(uuid, vec![format!("elem_{}", i)]);
            }
        }

        let old_naming = NamingIndex::new();
        let patch = diff(&old, &new, &universe, &old_naming, &naming);

        prop_assert_eq!(patch.elements.additions.len(), num_elements);
        prop_assert!(patch.elements.deletions.is_empty());
    }

    /// Element deletions are tracked in patch
    #[test]
    fn deletions_tracked(
        num_elements in 1usize..10,
    ) {
        let mut universe = Universe::new();
        let mut old_naming = NamingIndex::new();

        let mut old = Structure::new(2);
        for i in 0..num_elements {
            let (_, luid) = old.add_element(&mut universe, i % 2);
            if let Some(uuid) = universe.get(luid) {
                old_naming.insert(uuid, vec![format!("elem_{}", i)]);
            }
        }

        let new = Structure::new(2);
        let new_naming = NamingIndex::new();

        let patch = diff(&old, &new, &universe, &old_naming, &new_naming);

        prop_assert_eq!(patch.elements.deletions.len(), num_elements);
        prop_assert!(patch.elements.additions.is_empty());
    }

    /// Element patch has disjoint additions and deletions
    #[test]
    fn element_patch_disjoint(
        (old, mut universe) in generators::arb_structure(StructureParams {
            num_sorts: 2,
            max_elements_per_sort: 5,
        }),
        (new, _) in generators::arb_structure(StructureParams {
            num_sorts: 2,
            max_elements_per_sort: 5,
        })
    ) {
        let old_naming = NamingIndex::new();
        let new_naming = NamingIndex::new();

        let patch = diff(&old, &new, &universe, &old_naming, &new_naming);

        // Additions and deletions should be disjoint
        let additions: HashSet<_> = patch.elements.additions.keys().collect();
        let deletions: HashSet<_> = patch.elements.deletions.iter().collect();

        let intersection: Vec<_> = additions.intersection(&deletions).collect();
        prop_assert!(intersection.is_empty());
    }

    /// NamingPatch tracks name additions for new elements
    #[test]
    fn naming_patch_additions(
        num_elements in 1usize..8,
    ) {
        let mut universe = Universe::new();
        let mut naming = NamingIndex::new();

        let old = Structure::new(2);
        let mut new = Structure::new(2);

        for i in 0..num_elements {
            let (_, luid) = new.add_element(&mut universe, 0);
            if let Some(uuid) = universe.get(luid) {
                naming.insert(uuid, vec![format!("elem_{}", i)]);
            }
        }

        let old_naming = NamingIndex::new();
        let patch = diff(&old, &new, &universe, &old_naming, &naming);

        // Naming patch should have names for new elements
        prop_assert_eq!(patch.names.additions.len(), num_elements);
    }

    /// Patch inversion swaps additions/deletions
    #[test]
    fn inversion_swaps_elements(
        (old, mut universe) in generators::arb_structure(StructureParams {
            num_sorts: 2,
            max_elements_per_sort: 4,
        })
    ) {
        // Create a new structure with some different elements
        let mut new = Structure::new(2);
        new.add_element(&mut universe, 0);
        new.add_element(&mut universe, 1);

        let old_naming = NamingIndex::new();
        let new_naming = NamingIndex::new();

        let patch = diff(&old, &new, &universe, &old_naming, &new_naming);
        let inverted = patch.invert();

        // Inverted patch swaps source/target commits
        prop_assert_eq!(inverted.source_commit, Some(patch.target_commit));

        // Additions become deletions (by key count)
        prop_assert_eq!(
            inverted.elements.deletions.len(),
            patch.elements.additions.len()
        );
    }

    /// Double inversion preserves target_commit (but creates new source)
    #[test]
    fn double_inversion_target_preserved(
        (structure, universe) in generators::arb_structure(StructureParams {
            num_sorts: 2,
            max_elements_per_sort: 3,
        })
    ) {
        let naming = NamingIndex::new();
        let patch = to_initial_patch(&structure, &universe, &naming);

        let inverted = patch.invert();
        let double_inverted = inverted.invert();

        // Original target becomes source after double inversion
        // (because each inversion swaps source ↔ target)
        prop_assert_eq!(double_inverted.source_commit, Some(inverted.target_commit));
    }

    /// Result of apply_patch maintains structure invariants
    #[test]
    fn apply_patch_maintains_invariants(
        (old, mut universe) in generators::arb_structure(StructureParams {
            num_sorts: 3,
            max_elements_per_sort: 5,
        }),
        (new, _) in generators::arb_structure(StructureParams {
            num_sorts: 3,
            max_elements_per_sort: 5,
        })
    ) {
        let old_naming = NamingIndex::new();
        let new_naming = NamingIndex::new();

        let patch = diff(&old, &new, &universe, &old_naming, &new_naming);
        let mut result_naming = NamingIndex::new();

        let result = apply_patch(&old, &patch, &mut universe, &mut result_naming);
        prop_assert!(result.is_ok());

        let result = result.unwrap();
        prop_assert!(check_structure_invariants(&result).is_ok());
    }
}

// More focused roundtrip tests

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    /// THE KEY PROPERTY: diff then apply is identity
    /// diff(old, new) |> apply_patch(old, _) ≈ new
    ///
    /// We test this by starting with a structure and modifying it (adding/removing elements)
    /// to create `new`, ensuring both share the same Universe.
    #[test]
    fn diff_apply_roundtrip(
        (base, mut universe) in generators::arb_structure(StructureParams {
            num_sorts: 2,
            max_elements_per_sort: 4,
        }),
        additions in proptest::collection::vec(0usize..2, 0..4),
        deletions_count in 0usize..3,
    ) {
        // Create `old` as a clone of base
        let old = base.clone();

        // Build naming for old structure
        let mut old_naming = NamingIndex::new();
        for &luid in &old.luids {
            if let Some(uuid) = universe.get(luid) {
                old_naming.insert(uuid, vec![format!("old_elem_{}", luid)]);
            }
        }

        // Create `new` by modifying base: add some elements, potentially skip some old ones
        let mut new = Structure::new(base.num_sorts());
        let mut new_naming = NamingIndex::new();

        // Keep some elements from old (skip the first `deletions_count`)
        let keep_count = base.len().saturating_sub(deletions_count);
        for slid in 0..keep_count {
            let luid = base.luids[slid];
            let sort_id = base.sorts[slid];
            new.add_element_with_luid(luid, sort_id);

            if let Some(uuid) = universe.get(luid) {
                new_naming.insert(uuid, vec![format!("kept_elem_{}", luid)]);
            }
        }

        // Add new elements
        for sort_id in additions {
            let (_, luid) = new.add_element(&mut universe, sort_id);
            if let Some(uuid) = universe.get(luid) {
                new_naming.insert(uuid, vec![format!("new_elem_{}", luid)]);
            }
        }

        // Now diff and apply
        let patch = diff(&old, &new, &universe, &old_naming, &new_naming);
        let mut result_naming = NamingIndex::new();

        let result = apply_patch(&old, &patch, &mut universe, &mut result_naming);
        prop_assert!(result.is_ok());

        let result = result.unwrap();

        // Result should have same number of elements as new
        prop_assert_eq!(result.len(), new.len());

        // Result should have same UUIDs as new (both use the same universe)
        let result_uuids: HashSet<_> = result.luids.iter()
            .filter_map(|&luid| universe.get(luid))
            .collect();
        let new_uuids: HashSet<_> = new.luids.iter()
            .filter_map(|&luid| universe.get(luid))
            .collect();

        prop_assert_eq!(result_uuids, new_uuids);
    }
}
