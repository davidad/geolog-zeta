//! Proptest generators for geolog data structures
//!
//! Provides `Strategy` implementations for generating valid instances
//! of core data types used in property tests.

use geolog::id::{Luid, Uuid};
use geolog::core::{Structure, SortId};
use geolog::naming::NamingIndex;
use geolog::universe::Universe;
use proptest::prelude::*;
use proptest::collection::vec;
use std::collections::HashSet;

// ============================================================================
// UUID Generation
// ============================================================================

/// Generate arbitrary UUIDs (using v7 format)
pub fn arb_uuid() -> impl Strategy<Value = Uuid> {
    // Generate random bytes for the UUID
    prop::array::uniform16(any::<u8>()).prop_map(|bytes| {
        // Create a valid v7-ish UUID from random bytes
        Uuid::from_bytes(bytes)
    })
}

/// Generate a vector of unique UUIDs
pub fn arb_unique_uuids(count: usize) -> impl Strategy<Value = Vec<Uuid>> {
    vec(arb_uuid(), count..=count).prop_filter_map("unique uuids", |uuids| {
        let set: HashSet<_> = uuids.iter().collect();
        if set.len() == uuids.len() {
            Some(uuids)
        } else {
            None
        }
    })
}

// ============================================================================
// Name Generation
// ============================================================================

/// Generate a valid identifier (alphanumeric, starting with letter)
pub fn arb_identifier() -> impl Strategy<Value = String> {
    "[a-zA-Z][a-zA-Z0-9_]{0,15}".prop_map(String::from)
}

/// Generate a qualified name path (non-empty vector of identifiers)
pub fn arb_qualified_name() -> impl Strategy<Value = Vec<String>> {
    vec(arb_identifier(), 1..=3)
}

// ============================================================================
// Structure Generation
// ============================================================================

/// Parameters for structure generation
#[derive(Debug, Clone)]
pub struct StructureParams {
    pub num_sorts: usize,
    pub max_elements_per_sort: usize,
}

impl Default for StructureParams {
    fn default() -> Self {
        Self {
            num_sorts: 3,
            max_elements_per_sort: 5,
        }
    }
}

/// Generate a valid Structure with elements distributed across sorts
pub fn arb_structure(params: StructureParams) -> impl Strategy<Value = (Structure, Universe)> {
    // Generate element counts for each sort
    vec(0..=params.max_elements_per_sort, params.num_sorts)
        .prop_flat_map(move |element_counts| {
            let num_sorts = params.num_sorts;
            Just((element_counts, num_sorts))
        })
        .prop_map(|(element_counts, num_sorts)| {
            let mut universe = Universe::new();
            let mut structure = Structure::new(num_sorts);

            for (sort_id, &count) in element_counts.iter().enumerate() {
                for _ in 0..count {
                    structure.add_element(&mut universe, sort_id as SortId);
                }
            }

            (structure, universe)
        })
}

/// Generate a structure with specific element count
pub fn arb_structure_with_elements(num_sorts: usize, total_elements: usize)
    -> impl Strategy<Value = (Structure, Universe)>
{
    // Distribute elements randomly across sorts
    vec(0..num_sorts, total_elements)
        .prop_map(move |sort_assignments| {
            let mut universe = Universe::new();
            let mut structure = Structure::new(num_sorts);

            for sort_id in sort_assignments {
                structure.add_element(&mut universe, sort_id as SortId);
            }

            (structure, universe)
        })
}

// ============================================================================
// NamingIndex Generation
// ============================================================================

/// Generate a NamingIndex with random entries
pub fn arb_naming_index(max_entries: usize) -> impl Strategy<Value = NamingIndex> {
    vec((arb_uuid(), arb_qualified_name()), 0..=max_entries)
        .prop_filter_map("unique uuids in naming", |entries| {
            // Ensure UUIDs are unique
            let uuids: HashSet<_> = entries.iter().map(|(u, _)| u).collect();
            if uuids.len() == entries.len() {
                let mut index = NamingIndex::new();
                for (uuid, name) in entries {
                    index.insert(uuid, name);
                }
                Some(index)
            } else {
                None
            }
        })
}

/// Generate a NamingIndex that matches a Universe (same UUIDs)
pub fn arb_naming_for_universe(universe: &Universe) -> impl Strategy<Value = NamingIndex> {
    let uuids: Vec<Uuid> = universe.iter().map(|(_, uuid)| uuid).collect();
    let count = uuids.len();

    vec(arb_qualified_name(), count)
        .prop_map(move |names| {
            let mut index = NamingIndex::new();
            for (uuid, name) in uuids.iter().zip(names.into_iter()) {
                index.insert(*uuid, name);
            }
            index
        })
}

// ============================================================================
// Element Operations (for testing add/remove sequences)
// ============================================================================

/// An operation on a structure
#[derive(Debug, Clone)]
pub enum StructureOp {
    AddElement { sort_id: SortId },
}

/// Generate a sequence of structure operations
pub fn arb_structure_ops(num_sorts: usize, max_ops: usize) -> impl Strategy<Value = Vec<StructureOp>> {
    vec(
        (0..num_sorts).prop_map(|sort_id| StructureOp::AddElement { sort_id }),
        0..=max_ops
    )
}

// ============================================================================
// Test Helpers
// ============================================================================

/// Check that a Structure maintains its internal invariants
pub fn check_structure_invariants(structure: &Structure) -> Result<(), String> {
    // Invariant 1: luids and sorts have same length
    if structure.luids.len() != structure.sorts.len() {
        return Err(format!(
            "luids.len({}) != sorts.len({})",
            structure.luids.len(),
            structure.sorts.len()
        ));
    }

    // Invariant 2: luid_to_slid is inverse of luids
    for (slid, &luid) in structure.luids.iter().enumerate() {
        match structure.luid_to_slid.get(&luid) {
            Some(&mapped_slid) if mapped_slid == slid => {},
            Some(&mapped_slid) => {
                return Err(format!(
                    "luid_to_slid[{}] = {}, but luids[{}] = {}",
                    luid, mapped_slid, slid, luid
                ));
            }
            None => {
                return Err(format!(
                    "luid {} at slid {} not in luid_to_slid",
                    luid, slid
                ));
            }
        }
    }

    // Invariant 3: Each element appears in exactly one carrier, matching its sort
    for (slid, &sort_id) in structure.sorts.iter().enumerate() {
        if sort_id >= structure.carriers.len() {
            return Err(format!(
                "sort_id {} at slid {} >= carriers.len({})",
                sort_id, slid, structure.carriers.len()
            ));
        }

        if !structure.carriers[sort_id].contains(slid as u64) {
            return Err(format!(
                "slid {} with sort {} not in carriers[{}]",
                slid, sort_id, sort_id
            ));
        }

        // Check it's not in any other carrier
        for (other_sort, carrier) in structure.carriers.iter().enumerate() {
            if other_sort != sort_id && carrier.contains(slid as u64) {
                return Err(format!(
                    "slid {} appears in carrier {} but has sort {}",
                    slid, other_sort, sort_id
                ));
            }
        }
    }

    // Invariant 4: Total carrier size equals number of elements
    let total_carrier_size: usize = structure.carriers.iter()
        .map(|c| c.len() as usize)
        .sum();
    if total_carrier_size != structure.luids.len() {
        return Err(format!(
            "total carrier size {} != luids.len({})",
            total_carrier_size, structure.luids.len()
        ));
    }

    Ok(())
}

/// Check that two structures are equivalent (same elements and functions)
pub fn structures_equivalent(
    s1: &Structure,
    s2: &Structure,
    u1: &Universe,
    u2: &Universe,
) -> bool {
    // Same number of sorts
    if s1.num_sorts() != s2.num_sorts() {
        return false;
    }

    // Same number of elements
    if s1.len() != s2.len() {
        return false;
    }

    // Same UUIDs (via Luid lookup)
    let uuids1: HashSet<_> = s1.luids.iter()
        .filter_map(|&luid| u1.get(luid))
        .collect();
    let uuids2: HashSet<_> = s2.luids.iter()
        .filter_map(|&luid| u2.get(luid))
        .collect();

    uuids1 == uuids2
}
