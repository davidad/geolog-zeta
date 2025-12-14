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
///
/// Note: Element names are tracked separately in NamingPatch.
#[derive(Default, Clone, Debug, PartialEq, Eq, Archive, Deserialize, Serialize)]
#[archive(check_bytes)]
pub struct ElementPatch {
    /// Elements removed from structure (by UUID)
    pub deletions: BTreeSet<Uuid>,
    /// Elements added: Uuid → sort_id
    pub additions: BTreeMap<Uuid, SortId>,
}

impl ElementPatch {
    pub fn is_empty(&self) -> bool {
        self.deletions.is_empty() && self.additions.is_empty()
    }
}

/// Changes to element names (separate from structural changes)
///
/// Names can change independently of structure (renames), and new elements
/// need names. This keeps patches self-contained for version control.
#[derive(Default, Clone, Debug, PartialEq, Eq, Archive, Deserialize, Serialize)]
#[archive(check_bytes)]
pub struct NamingPatch {
    /// Names removed (by UUID) - typically when element is deleted
    pub deletions: BTreeSet<Uuid>,
    /// Names added or changed: UUID → qualified_name path
    pub additions: BTreeMap<Uuid, Vec<String>>,
}

impl NamingPatch {
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
///
/// Note: Theory reference is stored as a Luid in the Structure, not here.
#[derive(Clone, Debug, PartialEq, Eq, Archive, Deserialize, Serialize)]
#[archive(check_bytes)]
pub struct Patch {
    /// The commit this patch is based on (None for initial commit)
    pub source_commit: Option<Uuid>,
    /// The commit this patch creates
    pub target_commit: Uuid,
    /// Number of sorts in the theory (needed to rebuild structure)
    pub num_sorts: usize,
    /// Number of functions in the theory (needed to rebuild structure)
    pub num_functions: usize,
    /// Element changes (additions/deletions)
    pub elements: ElementPatch,
    /// Function value changes
    pub functions: FunctionPatch,
    /// Name changes (for self-contained patches)
    pub names: NamingPatch,
}

impl Patch {
    /// Create a new patch
    pub fn new(
        source_commit: Option<Uuid>,
        num_sorts: usize,
        num_functions: usize,
    ) -> Self {
        Self {
            source_commit,
            target_commit: Uuid::now_v7(),
            num_sorts,
            num_functions,
            elements: ElementPatch::default(),
            functions: FunctionPatch::default(),
            names: NamingPatch::default(),
        }
    }

    /// Check if this patch makes any changes
    pub fn is_empty(&self) -> bool {
        self.elements.is_empty() && self.functions.is_empty() && self.names.is_empty()
    }

    /// Invert this patch (swap old/new, additions/deletions)
    ///
    /// Note: Inversion of element additions requires knowing the sort_id of deleted elements,
    /// which we don't track in deletions. This is a known limitation - sort info is lost on invert.
    /// Names are fully invertible since we track the full qualified name.
    pub fn invert(&self) -> Patch {
        Patch {
            source_commit: Some(self.target_commit),
            target_commit: self
                .source_commit
                .unwrap_or_else(Uuid::now_v7),
            num_sorts: self.num_sorts,
            num_functions: self.num_functions,
            elements: ElementPatch {
                deletions: self.elements.additions.keys().copied().collect(),
                additions: self
                    .elements
                    .deletions
                    .iter()
                    .map(|uuid| (*uuid, 0)) // Note: loses sort info on invert
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
            names: NamingPatch {
                deletions: self.names.additions.keys().copied().collect(),
                additions: self
                    .names
                    .deletions
                    .iter()
                    .map(|uuid| (*uuid, vec![])) // Note: loses name on invert (would need old_names tracking)
                    .collect(),
            },
        }
    }
}

// ============ Diff and Apply operations ============

use crate::core::Structure;
use crate::id::{get_slid, some_slid, Luid};
use crate::naming::NamingIndex;
use crate::universe::Universe;

/// Create a patch representing the difference from `old` to `new`.
///
/// The resulting patch, when applied to `old`, produces `new`.
/// Requires Universe for UUID lookup and NamingIndex for name changes.
pub fn diff(
    old: &Structure,
    new: &Structure,
    universe: &Universe,
    old_naming: &NamingIndex,
    new_naming: &NamingIndex,
) -> Patch {
    let mut patch = Patch::new(
        None, // Will be set by caller if needed
        new.num_sorts(),
        new.num_functions(),
    );

    // Find element deletions: elements in old but not in new
    for (_slid, &luid) in old.luids.iter().enumerate() {
        if !new.luid_to_slid.contains_key(&luid) {
            if let Some(uuid) = universe.get(luid) {
                patch.elements.deletions.insert(uuid);
                // Also mark name as deleted
                patch.names.deletions.insert(uuid);
            }
        }
    }

    // Find element additions: elements in new but not in old
    for (slid, &luid) in new.luids.iter().enumerate() {
        if !old.luid_to_slid.contains_key(&luid) {
            if let Some(uuid) = universe.get(luid) {
                patch.elements.additions.insert(uuid, new.sorts[slid]);
                // Also add name from new_naming
                if let Some(name) = new_naming.get(&uuid) {
                    patch.names.additions.insert(uuid, name.clone());
                }
            }
        }
    }

    // Find name changes for elements that exist in both
    for &luid in new.luids.iter() {
        if old.luid_to_slid.contains_key(&luid) {
            // Element exists in both - check for name change
            if let Some(uuid) = universe.get(luid) {
                let old_name = old_naming.get(&uuid);
                let new_name = new_naming.get(&uuid);
                if old_name != new_name {
                    if let Some(name) = new_name {
                        patch.names.additions.insert(uuid, name.clone());
                    }
                }
            }
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
            if let Some(new_codomain_slid) = get_slid(*opt_codomain) {
                let domain_uuid = find_uuid_by_sort_slid(new, universe, func_id, sort_slid);
                if let Some(domain_uuid) = domain_uuid {
                    let new_codomain_luid = new.luids[new_codomain_slid];
                    let new_codomain_uuid = universe.get(new_codomain_luid);

                    if let Some(new_codomain_uuid) = new_codomain_uuid {
                        // Check if this element existed in old (by looking up its luid)
                        let domain_luid = find_luid_by_sort_slid(new, func_id, sort_slid);
                        if let Some(domain_luid) = domain_luid {
                            if let Some(&old_domain_slid) = old.luid_to_slid.get(&domain_luid) {
                                let old_sort_slid = old.sort_local_id(old_domain_slid);
                                let old_codomain = get_slid(old.functions[func_id][old_sort_slid]);

                                match old_codomain {
                                    Some(old_codomain_slid) => {
                                        let old_codomain_luid = old.luids[old_codomain_slid];
                                        if let Some(old_codomain_uuid) = universe.get(old_codomain_luid) {
                                            if old_codomain_uuid != new_codomain_uuid {
                                                // Value changed
                                                old_vals.insert(domain_uuid, Some(old_codomain_uuid));
                                                new_vals.insert(domain_uuid, new_codomain_uuid);
                                            }
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
                                new_vals.insert(domain_uuid, new_codomain_uuid);
                            }
                        }
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

/// Helper to find the Luid of an element given its func_id and sort_slid in a structure
fn find_luid_by_sort_slid(structure: &Structure, func_id: usize, sort_slid: usize) -> Option<Luid> {
    for (slid, &_sort_id) in structure.sorts.iter().enumerate() {
        let elem_sort_slid = structure.sort_local_id(slid);
        if elem_sort_slid == sort_slid {
            if structure.functions[func_id].len() > sort_slid {
                return Some(structure.luids[slid]);
            }
        }
    }
    None
}

/// Helper to find the UUID of an element given its func_id and sort_slid in a structure
fn find_uuid_by_sort_slid(structure: &Structure, universe: &Universe, func_id: usize, sort_slid: usize) -> Option<Uuid> {
    find_luid_by_sort_slid(structure, func_id, sort_slid)
        .and_then(|luid| universe.get(luid))
}

/// Apply a patch to create a new structure and update naming index.
///
/// Returns Ok(new_structure) on success, or Err with a description of what went wrong.
/// Requires a Universe to convert UUIDs from the patch to Luids.
/// The naming parameter is updated with name changes from the patch.
pub fn apply_patch(
    base: &Structure,
    patch: &Patch,
    universe: &mut Universe,
    naming: &mut NamingIndex,
) -> Result<Structure, String> {
    // Create a new structure
    let mut result = Structure::new(patch.num_sorts);

    // Build a set of deleted UUIDs for quick lookup
    let deleted_uuids: std::collections::HashSet<Uuid> = patch.elements.deletions.iter().copied().collect();

    // Copy elements from base that weren't deleted
    for (slid, &luid) in base.luids.iter().enumerate() {
        let uuid = universe.get(luid).ok_or("Unknown luid in base structure")?;
        if !deleted_uuids.contains(&uuid) {
            result.add_element_with_luid(luid, base.sorts[slid]);
        }
    }

    // Add new elements from the patch (register UUIDs in universe)
    for (uuid, sort_id) in &patch.elements.additions {
        result.add_element_with_uuid(universe, *uuid, *sort_id);
    }

    // Apply naming changes
    for uuid in &patch.names.deletions {
        // Note: NamingIndex doesn't have a remove method yet, skip for now
        let _ = uuid;
    }
    for (uuid, name) in &patch.names.additions {
        naming.insert(*uuid, name.clone());
    }

    // Initialize function storage
    let domain_sort_ids: Vec<Option<SortId>> = (0..patch.num_functions)
        .map(|func_id| {
            if func_id < base.functions.len() && !base.functions[func_id].is_empty() {
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
                // Find the domain element's Luid
                let domain_luid = find_luid_by_sort_slid(base, func_id, old_sort_slid);
                if let Some(domain_luid) = domain_luid {
                    // Check if domain element still exists in result
                    if let Some(&new_domain_slid) = result.luid_to_slid.get(&domain_luid) {
                        // Check if codomain element still exists
                        let codomain_luid = base.luids[old_codomain_slid];
                        if let Some(&new_codomain_slid) = result.luid_to_slid.get(&codomain_luid) {
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

    // Apply function value changes from patch (using UUIDs → Luids)
    for (func_id, changes) in &patch.functions.new_values {
        if *func_id < result.num_functions() {
            for (domain_uuid, codomain_uuid) in changes {
                let domain_luid = universe.lookup(domain_uuid);
                let codomain_luid = universe.lookup(codomain_uuid);
                if let (Some(domain_luid), Some(codomain_luid)) = (domain_luid, codomain_luid) {
                    if let (Some(&domain_slid), Some(&codomain_slid)) = (
                        result.luid_to_slid.get(&domain_luid),
                        result.luid_to_slid.get(&codomain_luid),
                    ) {
                        let sort_slid = result.sort_local_id(domain_slid);
                        if sort_slid < result.functions[*func_id].len() {
                            result.functions[*func_id][sort_slid] = some_slid(codomain_slid);
                        }
                    }
                }
            }
        }
    }

    Ok(result)
}

/// Create a patch representing a structure from empty (initial commit)
pub fn to_initial_patch(structure: &Structure, universe: &Universe, naming: &NamingIndex) -> Patch {
    let empty = Structure::new(structure.num_sorts());
    let empty_naming = NamingIndex::new();
    diff(&empty, structure, universe, &empty_naming, naming)
}

// Unit tests moved to tests/proptest_patch.rs
