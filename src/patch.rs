//! Patch types for version control of geolog structures
//!
//! A Patch represents the changes between two versions of a Structure.
//! Patches are the fundamental unit of version history - each commit
//! creates a new patch that can be applied to recreate the structure.

use crate::core::SortId;
use crate::id::Uuid;
use rkyv::{Archive, Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};

/// Changes to the element universe (additions and deletions)
#[derive(Default, Clone, Debug, PartialEq, Eq, Archive, Deserialize, Serialize)]
#[archive(check_bytes)]
pub struct ElementPatch {
    /// Elements removed from structure (by UUID)
    pub deletions: BTreeSet<Uuid>,
    /// Elements added: Uuid → (name, sort_id)
    pub additions: BTreeMap<Uuid, (String, SortId)>,
}

impl ElementPatch {
    pub fn is_empty(&self) -> bool {
        self.deletions.is_empty() && self.additions.is_empty()
    }
}

/// Changes to function definitions
///
/// We track both old and new values to support inversion (for undo).
/// The structure uses UUIDs rather than Slids since Slids are unstable
/// across different structure versions.
#[derive(Default, Clone, Debug, PartialEq, Eq, Archive, Deserialize, Serialize)]
#[archive(check_bytes)]
pub struct FunctionPatch {
    /// func_id → (domain_uuid → old_codomain_uuid)
    /// None means was undefined before
    pub old_values: BTreeMap<usize, BTreeMap<Uuid, Option<Uuid>>>,
    /// func_id → (domain_uuid → new_codomain_uuid)
    pub new_values: BTreeMap<usize, BTreeMap<Uuid, Uuid>>,
}

impl FunctionPatch {
    pub fn is_empty(&self) -> bool {
        self.new_values.is_empty()
    }
}

/// A complete patch between two structure versions
///
/// Patches form a linked list via source_commit → target_commit.
/// The initial commit has source_commit = None.
#[derive(Clone, Debug, PartialEq, Eq, Archive, Deserialize, Serialize)]
#[archive(check_bytes)]
pub struct Patch {
    /// The commit this patch is based on (None for initial commit)
    pub source_commit: Option<Uuid>,
    /// The commit this patch creates
    pub target_commit: Uuid,
    /// The theory this structure instantiates
    pub theory_name: String,
    /// Number of sorts in the theory (needed to rebuild structure)
    pub num_sorts: usize,
    /// Number of functions in the theory (needed to rebuild structure)
    pub num_functions: usize,
    /// Element changes
    pub elements: ElementPatch,
    /// Function value changes
    pub functions: FunctionPatch,
}

impl Patch {
    /// Create a new patch
    pub fn new(
        source_commit: Option<Uuid>,
        theory_name: String,
        num_sorts: usize,
        num_functions: usize,
    ) -> Self {
        Self {
            source_commit,
            target_commit: Uuid::now_v7(),
            theory_name,
            num_sorts,
            num_functions,
            elements: ElementPatch::default(),
            functions: FunctionPatch::default(),
        }
    }

    /// Check if this patch makes any changes
    pub fn is_empty(&self) -> bool {
        self.elements.is_empty() && self.functions.is_empty()
    }

    /// Invert this patch (swap old/new, additions/deletions)
    pub fn invert(&self) -> Patch {
        Patch {
            source_commit: Some(self.target_commit),
            target_commit: self
                .source_commit
                .unwrap_or_else(Uuid::now_v7),
            theory_name: self.theory_name.clone(),
            num_sorts: self.num_sorts,
            num_functions: self.num_functions,
            elements: ElementPatch {
                deletions: self.elements.additions.keys().copied().collect(),
                additions: self
                    .elements
                    .deletions
                    .iter()
                    .map(|uuid| (*uuid, (String::new(), 0))) // Note: loses name/sort info
                    .collect(),
            },
            functions: FunctionPatch {
                old_values: self.functions.new_values.iter().map(|(func_id, changes)| {
                    (*func_id, changes.iter().map(|(k, v)| (*k, Some(*v))).collect())
                }).collect(),
                new_values: self.functions.old_values.iter().filter_map(|(func_id, changes)| {
                    let filtered: BTreeMap<_, _> = changes.iter()
                        .filter_map(|(k, v)| v.map(|v| (*k, v)))
                        .collect();
                    if filtered.is_empty() {
                        None
                    } else {
                        Some((*func_id, filtered))
                    }
                }).collect(),
            },
        }
    }
}

// ============ Diff and Apply operations ============

use crate::core::Structure;
use crate::id::{get_slid, some_slid};

/// Create a patch representing the difference from `old` to `new`.
///
/// The resulting patch, when applied to `old`, produces `new`.
pub fn diff(old: &Structure, new: &Structure) -> Patch {
    let mut patch = Patch::new(
        None, // Will be set by caller if needed
        new.theory_name.clone(),
        new.num_sorts(),
        new.num_functions(),
    );

    // Find deletions: elements in old but not in new
    for (_slid, uuid) in old.uuids.iter().enumerate() {
        if !new.uuid_to_slid.contains_key(uuid) {
            patch.elements.deletions.insert(*uuid);
        }
    }

    // Find additions: elements in new but not in old
    for (slid, uuid) in new.uuids.iter().enumerate() {
        if !old.uuid_to_slid.contains_key(uuid) {
            patch.elements.additions.insert(
                *uuid,
                (new.names[slid].clone(), new.sorts[slid]),
            );
        }
    }

    // Find function value changes
    // We need to compare function values for elements that exist in both
    for func_id in 0..new.num_functions() {
        if func_id >= old.num_functions() {
            // New function - all values are additions
            continue; // TODO: handle schema changes
        }

        let mut old_vals: BTreeMap<Uuid, Option<Uuid>> = BTreeMap::new();
        let mut new_vals: BTreeMap<Uuid, Uuid> = BTreeMap::new();

        // Iterate over elements in the new structure's function domain
        for (sort_slid, opt_codomain) in new.functions[func_id].iter().enumerate() {
            // Find the UUID for this domain element
            // We need to find the slid from sort_slid
            if let Some(new_codomain_slid) = get_slid(*opt_codomain) {
                let domain_uuid = find_uuid_by_sort_slid(new, func_id, sort_slid);
                if let Some(domain_uuid) = domain_uuid {
                    let new_codomain_uuid = new.uuids[new_codomain_slid];

                    // Check if this element existed in old
                    if let Some(&old_domain_slid) = old.uuid_to_slid.get(&domain_uuid) {
                        let old_sort_slid = old.sort_local_id(old_domain_slid);
                        let old_codomain = get_slid(old.functions[func_id][old_sort_slid]);

                        match old_codomain {
                            Some(old_codomain_slid) => {
                                let old_codomain_uuid = old.uuids[old_codomain_slid];
                                if old_codomain_uuid != new_codomain_uuid {
                                    // Value changed
                                    old_vals.insert(domain_uuid, Some(old_codomain_uuid));
                                    new_vals.insert(domain_uuid, new_codomain_uuid);
                                }
                            }
                            None => {
                                // Was undefined, now defined
                                old_vals.insert(domain_uuid, None);
                                new_vals.insert(domain_uuid, new_codomain_uuid);
                            }
                        }
                    } else {
                        // Domain element is new - function value is part of the addition
                        // We still record it in the patch for completeness
                        new_vals.insert(domain_uuid, new_codomain_uuid);
                    }
                }
            }
        }

        if !new_vals.is_empty() {
            patch.functions.old_values.insert(func_id, old_vals);
            patch.functions.new_values.insert(func_id, new_vals);
        }
    }

    patch
}

/// Helper to find the UUID of an element given its func_id and sort_slid in a structure
fn find_uuid_by_sort_slid(structure: &Structure, func_id: usize, sort_slid: usize) -> Option<Uuid> {
    // We need to find which sort this function's domain is
    // For now, assume functions have base sort domains
    // This is a simplification - product domains would need more work

    // Iterate through all elements to find one with matching sort_slid
    for (slid, &_sort_id) in structure.sorts.iter().enumerate() {
        let elem_sort_slid = structure.sort_local_id(slid);
        if elem_sort_slid == sort_slid {
            // Check if this element is in the domain of this function
            // by checking if the carrier matches
            if structure.functions[func_id].len() > sort_slid {
                return Some(structure.uuids[slid]);
            }
        }
    }
    None
}

/// Apply a patch to create a new structure.
///
/// Returns Ok(new_structure) on success, or Err with a description of what went wrong.
pub fn apply_patch(base: &Structure, patch: &Patch) -> Result<Structure, String> {
    // Create a new structure with the same theory
    let mut result = Structure::new(patch.theory_name.clone(), patch.num_sorts);

    // Copy elements from base that weren't deleted
    for (slid, uuid) in base.uuids.iter().enumerate() {
        if !patch.elements.deletions.contains(uuid) {
            result.add_element_with_uuid(*uuid, base.names[slid].clone(), base.sorts[slid]);
        }
    }

    // Add new elements from the patch
    for (uuid, (name, sort_id)) in &patch.elements.additions {
        result.add_element_with_uuid(*uuid, name.clone(), *sort_id);
    }

    // Initialize function storage
    // We need domain sort ids for each function
    // For now, assume same structure as base (no schema changes)
    let domain_sort_ids: Vec<Option<SortId>> = (0..patch.num_functions)
        .map(|func_id| {
            if func_id < base.functions.len() && !base.functions[func_id].is_empty() {
                // Find the sort that matches this function's domain size
                // This is a heuristic - proper solution needs signature info
                for (sort_id, carrier) in base.carriers.iter().enumerate() {
                    if carrier.len() as usize == base.functions[func_id].len() {
                        return Some(sort_id);
                    }
                }
            }
            None
        })
        .collect();

    result.init_functions(&domain_sort_ids);

    // Copy function values from base (for non-deleted elements)
    for func_id in 0..base.num_functions().min(result.num_functions()) {
        for (old_sort_slid, opt_codomain) in base.functions[func_id].iter().enumerate() {
            if let Some(old_codomain_slid) = get_slid(*opt_codomain) {
                // Find the domain element's UUID
                let domain_uuid = find_uuid_by_sort_slid(base, func_id, old_sort_slid);
                if let Some(domain_uuid) = domain_uuid {
                    // Check if domain element still exists
                    if let Some(&new_domain_slid) = result.uuid_to_slid.get(&domain_uuid) {
                        // Check if codomain element still exists
                        let codomain_uuid = base.uuids[old_codomain_slid];
                        if let Some(&new_codomain_slid) = result.uuid_to_slid.get(&codomain_uuid) {
                            let new_sort_slid = result.sort_local_id(new_domain_slid);
                            if new_sort_slid < result.functions[func_id].len() {
                                result.functions[func_id][new_sort_slid] = some_slid(new_codomain_slid);
                            }
                        }
                    }
                }
            }
        }
    }

    // Apply function value changes from patch
    for (func_id, changes) in &patch.functions.new_values {
        if *func_id < result.num_functions() {
            for (domain_uuid, codomain_uuid) in changes {
                if let (Some(&domain_slid), Some(&codomain_slid)) = (
                    result.uuid_to_slid.get(domain_uuid),
                    result.uuid_to_slid.get(codomain_uuid),
                ) {
                    let sort_slid = result.sort_local_id(domain_slid);
                    if sort_slid < result.functions[*func_id].len() {
                        result.functions[*func_id][sort_slid] = some_slid(codomain_slid);
                    }
                }
            }
        }
    }

    Ok(result)
}

/// Create a patch representing a structure from empty (initial commit)
pub fn to_initial_patch(structure: &Structure) -> Patch {
    let empty = Structure::new(structure.theory_name.clone(), structure.num_sorts());
    diff(&empty, structure)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_patch() {
        let patch = Patch::new(None, "Test".to_string(), 2, 1);
        assert!(patch.is_empty());
        assert!(patch.source_commit.is_none());
    }

    #[test]
    fn test_patch_with_elements() {
        let mut patch = Patch::new(None, "Test".to_string(), 2, 1);
        let uuid = Uuid::now_v7();
        patch.elements.additions.insert(uuid, ("foo".to_string(), 0));
        assert!(!patch.is_empty());
    }

    #[test]
    fn test_diff_empty_structures() {
        let s1 = Structure::new("Test".to_string(), 2);
        let s2 = Structure::new("Test".to_string(), 2);
        let patch = diff(&s1, &s2);
        assert!(patch.is_empty());
    }

    #[test]
    fn test_diff_with_additions() {
        let s1 = Structure::new("Test".to_string(), 2);
        let mut s2 = Structure::new("Test".to_string(), 2);
        s2.add_element("foo".to_string(), 0);
        s2.add_element("bar".to_string(), 1);

        let patch = diff(&s1, &s2);
        assert_eq!(patch.elements.additions.len(), 2);
        assert!(patch.elements.deletions.is_empty());
    }

    #[test]
    fn test_apply_patch_additions() {
        let s1 = Structure::new("Test".to_string(), 2);
        let mut s2 = Structure::new("Test".to_string(), 2);
        let uuid1 = s2.add_element("foo".to_string(), 0);
        let uuid2 = s2.add_element("bar".to_string(), 1);

        let patch = diff(&s1, &s2);
        let s3 = apply_patch(&s1, &patch).unwrap();

        assert_eq!(s3.len(), 2);
        assert!(s3.uuid_to_slid.contains_key(&s2.uuids[uuid1]));
        assert!(s3.uuid_to_slid.contains_key(&s2.uuids[uuid2]));
    }
}
