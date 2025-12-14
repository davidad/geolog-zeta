//! Property tests for NamingIndex (UUID ↔ Name bidirectional consistency)

mod generators;

use geolog::id::Uuid;
use geolog::naming::NamingIndex;
use proptest::prelude::*;
use std::collections::HashSet;
use tempfile::tempdir;

proptest! {
    /// Insert then lookup returns the same name
    #[test]
    fn insert_get_roundtrip(
        uuid in generators::arb_uuid(),
        name in generators::arb_qualified_name()
    ) {
        let mut index = NamingIndex::new();

        index.insert(uuid, name.clone());

        let retrieved = index.get(&uuid);
        prop_assert_eq!(retrieved, Some(&name));
    }

    /// Simple name (last component) is correctly extracted
    #[test]
    fn simple_name_is_last_component(
        uuid in generators::arb_uuid(),
        name in generators::arb_qualified_name()
    ) {
        let mut index = NamingIndex::new();
        index.insert(uuid, name.clone());

        let simple = index.get_simple(&uuid);
        let expected = name.last().map(|s| s.as_str());

        prop_assert_eq!(simple, expected);
    }

    /// lookup(simple_name) contains the UUID
    #[test]
    fn lookup_contains_uuid(
        uuid in generators::arb_uuid(),
        name in generators::arb_qualified_name()
    ) {
        let mut index = NamingIndex::new();
        index.insert(uuid, name.clone());

        if let Some(simple) = name.last() {
            let results = index.lookup(simple);
            prop_assert!(results.is_some());
            prop_assert!(results.unwrap().contains(&uuid));
        }
    }

    /// lookup_unique returns Some iff exactly one UUID has that name
    #[test]
    fn lookup_unique_semantics(
        entries in proptest::collection::vec(
            (generators::arb_uuid(), generators::arb_qualified_name()),
            1..10
        )
    ) {
        // Filter to unique UUIDs
        let mut seen_uuids = HashSet::new();
        let unique_entries: Vec<_> = entries.into_iter()
            .filter(|(uuid, _)| seen_uuids.insert(*uuid))
            .collect();

        let mut index = NamingIndex::new();
        for (uuid, name) in &unique_entries {
            index.insert(*uuid, name.clone());
        }

        // For each simple name, check lookup_unique semantics
        let mut name_counts: std::collections::HashMap<String, Vec<Uuid>> =
            std::collections::HashMap::new();
        for (uuid, name) in &unique_entries {
            if let Some(simple) = name.last() {
                name_counts.entry(simple.clone()).or_default().push(*uuid);
            }
        }

        for (simple_name, uuids) in name_counts {
            let unique_result = index.lookup_unique(&simple_name);
            if uuids.len() == 1 {
                prop_assert_eq!(unique_result, Some(uuids[0]));
            } else {
                prop_assert_eq!(unique_result, None);
            }
        }
    }

    /// Ambiguous names (multiple UUIDs) return None for lookup_unique
    #[test]
    fn ambiguous_names_return_none(
        uuid1 in generators::arb_uuid(),
        uuid2 in generators::arb_uuid(),
        shared_name in generators::arb_identifier()
    ) {
        prop_assume!(uuid1 != uuid2);

        let mut index = NamingIndex::new();
        index.insert(uuid1, vec!["Theory1".to_string(), shared_name.clone()]);
        index.insert(uuid2, vec!["Theory2".to_string(), shared_name.clone()]);

        // lookup returns both
        let results = index.lookup(&shared_name).unwrap();
        prop_assert_eq!(results.len(), 2);
        prop_assert!(results.contains(&uuid1));
        prop_assert!(results.contains(&uuid2));

        // lookup_unique returns None
        prop_assert_eq!(index.lookup_unique(&shared_name), None);
    }

    /// display_name returns the simple name if set, otherwise UUID string
    #[test]
    fn display_name_fallback(uuid in generators::arb_uuid()) {
        let mut index = NamingIndex::new();

        // Without name: should contain UUID
        let display_without = index.display_name(&uuid);
        let uuid_str = format!("{}", uuid);
        prop_assert!(display_without.contains(&uuid_str));

        // With name: should be the simple name
        let name = vec!["Test".to_string(), "Element".to_string()];
        index.insert(uuid, name);
        let display_with = index.display_name(&uuid);
        prop_assert_eq!(display_with, "Element");
    }

    /// Save and load preserves all mappings
    #[test]
    fn save_load_roundtrip(
        entries in proptest::collection::vec(
            (generators::arb_uuid(), generators::arb_qualified_name()),
            1..15
        )
    ) {
        // Filter to unique UUIDs
        let mut seen_uuids = HashSet::new();
        let unique_entries: Vec<_> = entries.into_iter()
            .filter(|(uuid, _)| seen_uuids.insert(*uuid))
            .collect();

        let dir = tempdir().unwrap();
        let path = dir.path().join("names.bin");

        // Save
        {
            let mut index = NamingIndex::with_path(&path);
            for (uuid, name) in &unique_entries {
                index.insert(*uuid, name.clone());
            }
            index.save().unwrap();
        }

        // Load
        {
            let loaded = NamingIndex::load(&path).unwrap();

            for (uuid, name) in &unique_entries {
                prop_assert_eq!(loaded.get(uuid), Some(name));
            }

            prop_assert_eq!(loaded.len(), unique_entries.len());
        }
    }

    /// Dirty flag consistency
    #[test]
    fn dirty_flag_consistency(
        uuid in generators::arb_uuid(),
        name in generators::arb_qualified_name()
    ) {
        let dir = tempdir().unwrap();
        let path = dir.path().join("names.bin");

        let mut index = NamingIndex::with_path(&path);

        // Initially clean
        prop_assert!(!index.is_dirty());

        // Dirty after insert
        index.insert(uuid, name);
        prop_assert!(index.is_dirty());

        // Clean after save
        index.save().unwrap();
        prop_assert!(!index.is_dirty());
    }

    /// Len reflects number of unique UUIDs
    #[test]
    fn len_reflects_entries(
        entries in proptest::collection::vec(
            (generators::arb_uuid(), generators::arb_qualified_name()),
            0..20
        )
    ) {
        // Filter to unique UUIDs
        let mut seen_uuids = HashSet::new();
        let unique_entries: Vec<_> = entries.into_iter()
            .filter(|(uuid, _)| seen_uuids.insert(*uuid))
            .collect();

        let mut index = NamingIndex::new();
        for (uuid, name) in &unique_entries {
            index.insert(*uuid, name.clone());
        }

        prop_assert_eq!(index.len(), unique_entries.len());
        prop_assert_eq!(index.is_empty(), unique_entries.is_empty());
    }
}
