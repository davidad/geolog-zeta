//! Property tests for Structure invariants

mod generators;

use generators::{check_structure_invariants, StructureParams, StructureOp};
use geolog::core::Structure;
use geolog::universe::Universe;
use proptest::prelude::*;

proptest! {
    #![proptest_config(ProptestConfig::with_cases(2048))]
    /// Empty structure maintains invariants
    #[test]
    fn empty_structure_invariants(num_sorts in 1usize..10) {
        let structure = Structure::new(num_sorts);
        prop_assert!(check_structure_invariants(&structure).is_ok());
        prop_assert_eq!(structure.len(), 0);
        prop_assert_eq!(structure.num_sorts(), num_sorts);
    }

    /// Structure maintains invariants after adding elements
    #[test]
    fn structure_invariants_after_adds(
        (structure, _universe) in generators::arb_structure(StructureParams {
            num_sorts: 4,
            max_elements_per_sort: 10,
        })
    ) {
        prop_assert!(check_structure_invariants(&structure).is_ok());
    }

    /// add_element correctly sets up bijection
    #[test]
    fn add_element_bijection(
        num_sorts in 1usize..5,
        sort_id in any::<prop::sample::Index>(),
    ) {
        let sort_id = sort_id.index(num_sorts);

        let mut universe = Universe::new();
        let mut structure = Structure::new(num_sorts);

        let (slid, luid) = structure.add_element(&mut universe, sort_id);

        // Forward: slid → luid
        prop_assert_eq!(structure.luids[slid], luid);

        // Reverse: luid → slid
        prop_assert_eq!(structure.luid_to_slid.get(&luid), Some(&slid));
        prop_assert_eq!(structure.lookup_luid(luid), Some(slid));

        // Sort is correct
        prop_assert_eq!(structure.sorts[slid], sort_id);

        // Carrier contains the element
        prop_assert!(structure.carriers[sort_id].contains(slid as u64));
    }

    /// Carrier membership is exclusive (element in exactly one carrier)
    #[test]
    fn carrier_membership_exclusive(
        ops in generators::arb_structure_ops(5, 20)
    ) {
        let mut universe = Universe::new();
        let mut structure = Structure::new(5);

        for op in ops {
            match op {
                StructureOp::AddElement { sort_id } => {
                    structure.add_element(&mut universe, sort_id);
                }
            }
        }

        // Check each element appears in exactly one carrier
        for slid in 0..structure.len() {
            let sort_id = structure.sorts[slid];
            let mut found_in = Vec::new();

            for (carrier_id, carrier) in structure.carriers.iter().enumerate() {
                if carrier.contains(slid as u64) {
                    found_in.push(carrier_id);
                }
            }

            prop_assert_eq!(
                found_in.len(), 1,
                "slid {} should be in exactly one carrier, found in {:?}",
                slid, found_in
            );
            prop_assert_eq!(found_in[0], sort_id);
        }
    }

    /// sort_local_id is consistent with carrier rank
    #[test]
    fn sort_local_id_consistency(
        (structure, _universe) in generators::arb_structure(StructureParams {
            num_sorts: 3,
            max_elements_per_sort: 8,
        })
    ) {
        for slid in 0..structure.len() {
            let sort_id = structure.sorts[slid];
            let sort_slid = structure.sort_local_id(slid);

            // sort_slid should be in range [0, carrier_size)
            let carrier_size = structure.carrier_size(sort_id);
            prop_assert!(
                sort_slid < carrier_size,
                "sort_slid {} should be < carrier_size {}",
                sort_slid, carrier_size
            );
        }
    }

    /// carrier_size matches number of elements with that sort
    #[test]
    fn carrier_size_matches_count(
        (structure, _universe) in generators::arb_structure(StructureParams {
            num_sorts: 4,
            max_elements_per_sort: 12,
        })
    ) {
        for sort_id in 0..structure.num_sorts() {
            let carrier_size = structure.carrier_size(sort_id);
            let count = structure.sorts.iter().filter(|&&s| s == sort_id).count();
            prop_assert_eq!(carrier_size, count);
        }
    }

    /// add_element_with_luid preserves existing element identity
    #[test]
    fn add_with_existing_luid_identity(num_sorts in 1usize..5) {
        let mut universe = Universe::new();
        let mut structure1 = Structure::new(num_sorts);

        // Create element in first structure
        let (slid1, luid1) = structure1.add_element(&mut universe, 0);

        // Create second structure and add element with same luid
        let mut structure2 = Structure::new(num_sorts);
        let slid2 = structure2.add_element_with_luid(luid1, 0);

        // Should have same luid
        prop_assert_eq!(structure2.luids[slid2], luid1);
        prop_assert_eq!(structure2.lookup_luid(luid1), Some(slid2));

        // Both structures should maintain invariants
        prop_assert!(check_structure_invariants(&structure1).is_ok());
        prop_assert!(check_structure_invariants(&structure2).is_ok());

        let _ = slid1; // silence warning
    }

    /// get_luid returns correct luid for slid
    #[test]
    fn get_luid_correctness(
        (structure, _universe) in generators::arb_structure(StructureParams {
            num_sorts: 3,
            max_elements_per_sort: 10,
        })
    ) {
        for slid in 0..structure.len() {
            let luid = structure.get_luid(slid);
            prop_assert_eq!(structure.luids[slid], luid);
            prop_assert_eq!(structure.lookup_luid(luid), Some(slid));
        }
    }

    /// Total elements equals sum of carrier sizes
    #[test]
    fn total_equals_carrier_sum(
        (structure, _universe) in generators::arb_structure(StructureParams {
            num_sorts: 5,
            max_elements_per_sort: 8,
        })
    ) {
        let carrier_total: usize = (0..structure.num_sorts())
            .map(|s| structure.carrier_size(s))
            .sum();

        prop_assert_eq!(structure.len(), carrier_total);
    }

    /// Sequential add_elements produce sequential slids
    #[test]
    fn sequential_slids(ops in generators::arb_structure_ops(3, 15)) {
        let mut universe = Universe::new();
        let mut structure = Structure::new(3);
        let mut expected_slid = 0;

        for op in ops {
            match op {
                StructureOp::AddElement { sort_id } => {
                    let (slid, _) = structure.add_element(&mut universe, sort_id);
                    prop_assert_eq!(slid, expected_slid);
                    expected_slid += 1;
                }
            }
        }

        prop_assert_eq!(structure.len(), expected_slid);
    }
}

// Additional focused tests

proptest! {
    /// Function initialization creates correct storage
    #[test]
    fn function_init_correct_size(
        (mut structure, _universe) in generators::arb_structure(StructureParams {
            num_sorts: 3,
            max_elements_per_sort: 5,
        })
    ) {
        // Initialize functions with domain sort IDs
        let domain_sort_ids: Vec<Option<usize>> = vec![Some(0), Some(1), None];
        structure.init_functions(&domain_sort_ids);

        prop_assert_eq!(structure.num_functions(), 3);

        // Check sizes match carrier sizes
        prop_assert_eq!(
            structure.functions[0].len(),
            structure.carrier_size(0)
        );
        prop_assert_eq!(
            structure.functions[1].len(),
            structure.carrier_size(1)
        );
        // Function 2 has None domain, so size should be 0
        prop_assert_eq!(structure.functions[2].len(), 0);
    }
}

