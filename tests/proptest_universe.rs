//! Property tests for Universe (UUID ↔ Luid bijection)

mod generators;

use geolog::id::{Luid, NumericId, Uuid};
use geolog::universe::Universe;
use proptest::prelude::*;
use std::collections::HashSet;
use tempfile::tempdir;

proptest! {
    /// Interning the same UUID twice returns the same Luid
    #[test]
    fn intern_idempotent(uuid in generators::arb_uuid()) {
        let mut universe = Universe::new();

        let luid1 = universe.intern(uuid);
        let luid2 = universe.intern(uuid);

        prop_assert_eq!(luid1, luid2);
    }

    /// Interning then looking up returns the original UUID
    #[test]
    fn intern_lookup_roundtrip(uuid in generators::arb_uuid()) {
        let mut universe = Universe::new();

        let luid = universe.intern(uuid);
        let retrieved = universe.get(luid);

        prop_assert_eq!(retrieved, Some(uuid));
    }

    /// Reverse lookup (UUID → Luid) works correctly
    #[test]
    fn reverse_lookup_roundtrip(uuid in generators::arb_uuid()) {
        let mut universe = Universe::new();

        let luid = universe.intern(uuid);
        let found_luid = universe.lookup(&uuid);

        prop_assert_eq!(found_luid, Some(luid));
    }

    /// After bulk interning, bijection holds for all entries
    #[test]
    fn bijection_after_bulk_intern(uuids in proptest::collection::vec(generators::arb_uuid(), 1..50)) {
        let mut universe = Universe::new();

        // Intern all UUIDs
        let luids: Vec<_> = uuids.iter().map(|&uuid| universe.intern(uuid)).collect();

        // Forward direction: Luid → UUID
        for (&uuid, &luid) in uuids.iter().zip(luids.iter()) {
            prop_assert_eq!(universe.get(luid), Some(uuid));
        }

        // Reverse direction: UUID → Luid
        for &uuid in &uuids {
            prop_assert!(universe.lookup(&uuid).is_some());
        }

        // Uniqueness: unique UUIDs produce unique Luids
        let unique_uuids: HashSet<_> = uuids.iter().collect();
        let unique_luids: HashSet<_> = luids.iter().collect();
        // Note: Luids may have fewer unique values if there are duplicate UUIDs
        prop_assert!(unique_luids.len() <= unique_uuids.len());
    }

    /// Luids are assigned sequentially starting from 0
    #[test]
    fn luids_sequential(count in 1usize..20) {
        let mut universe = Universe::new();

        for i in 0..count {
            let uuid = Uuid::now_v7();
            let luid = universe.intern(uuid);
            prop_assert_eq!(luid, Luid::from_usize(i), "Luid {} should be {}", luid, i);
        }
    }

    /// Save and load preserves all mappings
    #[test]
    fn save_load_roundtrip(uuids in generators::arb_unique_uuids(10)) {
        let dir = tempdir().unwrap();
        let path = dir.path().join("universe.bin");

        // Save
        let original_luids: Vec<_>;
        {
            let mut universe = Universe::with_path(&path);
            original_luids = uuids.iter().map(|&uuid| universe.intern(uuid)).collect();
            universe.save().unwrap();
        }

        // Load
        {
            let loaded = Universe::load(&path).unwrap();

            // Check all mappings preserved
            for (&uuid, &expected_luid) in uuids.iter().zip(original_luids.iter()) {
                let retrieved = loaded.get(expected_luid);
                prop_assert_eq!(retrieved, Some(uuid));

                let found_luid = loaded.lookup(&uuid);
                prop_assert_eq!(found_luid, Some(expected_luid));
            }
        }
    }

    /// Dirty flag is set after intern, cleared after save
    #[test]
    fn dirty_flag_consistency(uuid in generators::arb_uuid()) {
        let dir = tempdir().unwrap();
        let path = dir.path().join("universe.bin");

        let mut universe = Universe::with_path(&path);

        // Initially clean
        prop_assert!(!universe.is_dirty());

        // Dirty after intern
        universe.intern(uuid);
        prop_assert!(universe.is_dirty());

        // Clean after save
        universe.save().unwrap();
        prop_assert!(!universe.is_dirty());
    }

    /// Iterator yields all interned UUIDs in order
    #[test]
    fn iter_yields_all(uuids in generators::arb_unique_uuids(15)) {
        let mut universe = Universe::new();

        for &uuid in &uuids {
            universe.intern(uuid);
        }

        let iter_results: Vec<_> = universe.iter().collect();

        prop_assert_eq!(iter_results.len(), uuids.len());

        for (i, (luid, uuid)) in iter_results.iter().enumerate() {
            prop_assert_eq!(*luid, Luid::from_usize(i));
            prop_assert_eq!(*uuid, uuids[i]);
        }
    }
}

// Non-property unit tests for edge cases

#[test]
fn test_load_nonexistent() {
    let dir = tempdir().unwrap();
    let path = dir.path().join("nonexistent.bin");
    let universe = Universe::load(&path).expect("load should succeed for nonexistent");
    assert!(universe.is_empty());
}
