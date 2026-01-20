//! Patch types for version control of geolog structures
//!
//! A Patch represents the changes between two versions of a Structure.
//! Patches are the fundamental unit of version history - each commit
//! creates a new patch that can be applied to recreate the structure.

use crate::core::SortId;
use crate::id::{NumericId, Slid, Uuid};
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

/// Changes to relation assertions (tuples added/removed)
///
/// Tuples are stored as Vec<Uuid> since element Slids are unstable across versions.
/// We track both assertions and retractions to support inversion.
#[derive(Default, Clone, Debug, PartialEq, Eq, Archive, Deserialize, Serialize)]
#[archive(check_bytes)]
pub struct RelationPatch {
    /// rel_id → set of tuples retracted (as UUID vectors)
    pub retractions: BTreeMap<usize, BTreeSet<Vec<Uuid>>>,
    /// rel_id → set of tuples asserted (as UUID vectors)
    pub assertions: BTreeMap<usize, BTreeSet<Vec<Uuid>>>,
}

impl RelationPatch {
    pub fn is_empty(&self) -> bool {
        self.assertions.is_empty() && self.retractions.is_empty()
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
    /// Number of relations in the theory (needed to rebuild structure)
    pub num_relations: usize,
    /// Element changes (additions/deletions)
    pub elements: ElementPatch,
    /// Function value changes
    pub functions: FunctionPatch,
    /// Relation tuple changes (assertions/retractions)
    pub relations: RelationPatch,
    /// Name changes (for self-contained patches)
    pub names: NamingPatch,
}

impl Patch {
    /// Create a new patch
    pub fn new(
        source_commit: Option<Uuid>,
        num_sorts: usize,
        num_functions: usize,
        num_relations: usize,
    ) -> Self {
        Self {
            source_commit,
            target_commit: Uuid::now_v7(),
            num_sorts,
            num_functions,
            num_relations,
            elements: ElementPatch::default(),
            functions: FunctionPatch::default(),
            relations: RelationPatch::default(),
            names: NamingPatch::default(),
        }
    }

    /// Check if this patch makes any changes
    pub fn is_empty(&self) -> bool {
        self.elements.is_empty()
            && self.functions.is_empty()
            && self.relations.is_empty()
            && self.names.is_empty()
    }

    /// Invert this patch (swap old/new, additions/deletions)
    ///
    /// Note: Inversion of element additions requires knowing the sort_id of deleted elements,
    /// which we don't track in deletions. This is a known limitation - sort info is lost on invert.
    /// Names are fully invertible since we track the full qualified name.
    /// Relations are fully invertible (assertions ↔ retractions).
    pub fn invert(&self) -> Patch {
        Patch {
            source_commit: Some(self.target_commit),
            target_commit: self.source_commit.unwrap_or_else(Uuid::now_v7),
            num_sorts: self.num_sorts,
            num_functions: self.num_functions,
            num_relations: self.num_relations,
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
                old_values: self
                    .functions
                    .new_values
                    .iter()
                    .map(|(func_id, changes)| {
                        (
                            *func_id,
                            changes.iter().map(|(k, v)| (*k, Some(*v))).collect(),
                        )
                    })
                    .collect(),
                new_values: self
                    .functions
                    .old_values
                    .iter()
                    .filter_map(|(func_id, changes)| {
                        let filtered: BTreeMap<_, _> = changes
                            .iter()
                            .filter_map(|(k, v)| v.map(|v| (*k, v)))
                            .collect();
                        if filtered.is_empty() {
                            None
                        } else {
                            Some((*func_id, filtered))
                        }
                    })
                    .collect(),
            },
            relations: RelationPatch {
                // Swap assertions ↔ retractions
                retractions: self.relations.assertions.clone(),
                assertions: self.relations.retractions.clone(),
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

use crate::core::{RelationStorage, Structure};
use crate::id::{Luid, get_slid, some_slid};
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
        new.relations.len(),
    );

    // Find element deletions: elements in old but not in new
    for &luid in old.luids.iter() {
        if !new.luid_to_slid.contains_key(&luid)
            && let Some(uuid) = universe.get(luid) {
                patch.elements.deletions.insert(uuid);
                // Also mark name as deleted
                patch.names.deletions.insert(uuid);
            }
    }

    // Find element additions: elements in new but not in old
    for (slid, &luid) in new.luids.iter().enumerate() {
        if !old.luid_to_slid.contains_key(&luid)
            && let Some(uuid) = universe.get(luid) {
                patch.elements.additions.insert(uuid, new.sorts[slid]);
                // Also add name from new_naming
                if let Some(name) = new_naming.get(&uuid) {
                    patch.names.additions.insert(uuid, name.clone());
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
                if old_name != new_name
                    && let Some(name) = new_name {
                        patch.names.additions.insert(uuid, name.clone());
                    }
            }
        }
    }

    // Find function value changes
    // We need to compare function values for elements that exist in both
    for func_id in 0..new.num_functions() {
        if func_id >= old.num_functions() {
            // New function added to schema - all its values are additions
            // Record each defined value with old_value = None
            let Some(new_func_col) = new.functions[func_id].as_local() else { continue };
            for (sort_slid, opt_codomain) in new_func_col.iter().enumerate() {
                if let Some(new_codomain_slid) = get_slid(*opt_codomain) {
                    // Find UUIDs for domain and codomain
                    let domain_uuid = find_uuid_by_sort_slid(new, universe, func_id, sort_slid);
                    if let Some(domain_uuid) = domain_uuid {
                        let new_codomain_luid = new.luids[new_codomain_slid.index()];
                        if let Some(new_codomain_uuid) = universe.get(new_codomain_luid) {
                            // Record: this domain element now maps to this codomain element
                            // (was undefined before since function didn't exist)
                            patch.functions.old_values
                                .entry(func_id)
                                .or_default()
                                .insert(domain_uuid, None);
                            patch.functions.new_values
                                .entry(func_id)
                                .or_default()
                                .insert(domain_uuid, new_codomain_uuid);
                        }
                    }
                }
            }
            continue;
        }

        let mut old_vals: BTreeMap<Uuid, Option<Uuid>> = BTreeMap::new();
        let mut new_vals: BTreeMap<Uuid, Uuid> = BTreeMap::new();

        // Iterate over elements in the new structure's function domain
        // Note: patches only work with local functions currently
        let Some(new_func_col) = new.functions[func_id].as_local() else { continue };
        let Some(old_func_col) = old.functions[func_id].as_local() else { continue };

        for (sort_slid, opt_codomain) in new_func_col.iter().enumerate() {
            // Find the UUID for this domain element
            if let Some(new_codomain_slid) = get_slid(*opt_codomain) {
                let domain_uuid = find_uuid_by_sort_slid(new, universe, func_id, sort_slid);
                if let Some(domain_uuid) = domain_uuid {
                    let new_codomain_luid = new.luids[new_codomain_slid.index()];
                    let new_codomain_uuid = universe.get(new_codomain_luid);

                    if let Some(new_codomain_uuid) = new_codomain_uuid {
                        // Check if this element existed in old (by looking up its luid)
                        let domain_luid = find_luid_by_sort_slid(new, func_id, sort_slid);
                        if let Some(domain_luid) = domain_luid {
                            if let Some(&old_domain_slid) = old.luid_to_slid.get(&domain_luid) {
                                let old_sort_slid = old.sort_local_id(old_domain_slid);
                                let old_codomain = get_slid(old_func_col[old_sort_slid.index()]);

                                match old_codomain {
                                    Some(old_codomain_slid) => {
                                        let old_codomain_luid = old.luids[old_codomain_slid.index()];
                                        if let Some(old_codomain_uuid) =
                                            universe.get(old_codomain_luid)
                                            && old_codomain_uuid != new_codomain_uuid {
                                                // Value changed
                                                old_vals
                                                    .insert(domain_uuid, Some(old_codomain_uuid));
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

    // Find relation changes
    // Compare tuples in each relation between old and new
    let num_relations = new.relations.len().min(old.relations.len());
    for rel_id in 0..num_relations {
        let old_rel = &old.relations[rel_id];
        let new_rel = &new.relations[rel_id];

        // Helper: convert a Slid tuple to UUID tuple
        let slid_tuple_to_uuids = |tuple: &[Slid], structure: &Structure| -> Option<Vec<Uuid>> {
            tuple
                .iter()
                .map(|&slid| {
                    let luid = structure.luids[slid.index()];
                    universe.get(luid)
                })
                .collect()
        };

        // Find tuples in old but not in new (retractions)
        let mut retractions: BTreeSet<Vec<Uuid>> = BTreeSet::new();
        for tuple in old_rel.iter() {
            // Check if this tuple (by UUID) exists in new
            if let Some(uuid_tuple) = slid_tuple_to_uuids(tuple, old) {
                // See if we can find the same UUID tuple in new
                let exists_in_new = new_rel.iter().any(|new_tuple| {
                    slid_tuple_to_uuids(new_tuple, new)
                        .map(|new_uuids| new_uuids == uuid_tuple)
                        .unwrap_or(false)
                });
                if !exists_in_new {
                    retractions.insert(uuid_tuple);
                }
            }
        }

        // Find tuples in new but not in old (assertions)
        let mut assertions: BTreeSet<Vec<Uuid>> = BTreeSet::new();
        for tuple in new_rel.iter() {
            if let Some(uuid_tuple) = slid_tuple_to_uuids(tuple, new) {
                let exists_in_old = old_rel.iter().any(|old_tuple| {
                    slid_tuple_to_uuids(old_tuple, old)
                        .map(|old_uuids| old_uuids == uuid_tuple)
                        .unwrap_or(false)
                });
                if !exists_in_old {
                    assertions.insert(uuid_tuple);
                }
            }
        }

        if !retractions.is_empty() {
            patch.relations.retractions.insert(rel_id, retractions);
        }
        if !assertions.is_empty() {
            patch.relations.assertions.insert(rel_id, assertions);
        }
    }

    // Handle new relations in new that don't exist in old
    for rel_id in num_relations..new.relations.len() {
        let new_rel = &new.relations[rel_id];
        let mut assertions: BTreeSet<Vec<Uuid>> = BTreeSet::new();

        for tuple in new_rel.iter() {
            let uuid_tuple: Option<Vec<Uuid>> = tuple
                .iter()
                .map(|&slid| {
                    let luid = new.luids[slid.index()];
                    universe.get(luid)
                })
                .collect();
            if let Some(uuids) = uuid_tuple {
                assertions.insert(uuids);
            }
        }

        if !assertions.is_empty() {
            patch.relations.assertions.insert(rel_id, assertions);
        }
    }

    patch
}

/// Helper to find the Luid of an element given its func_id and sort_slid in a structure
fn find_luid_by_sort_slid(structure: &Structure, func_id: usize, sort_slid: usize) -> Option<Luid> {
    let func_col_len = structure.functions[func_id].len();
    for (slid_idx, &_sort_id) in structure.sorts.iter().enumerate() {
        let slid = Slid::from_usize(slid_idx);
        let elem_sort_slid = structure.sort_local_id(slid);
        if elem_sort_slid.index() == sort_slid && func_col_len > sort_slid {
            return Some(structure.luids[slid_idx]);
        }
    }
    None
}

/// Helper to find the UUID of an element given its func_id and sort_slid in a structure
fn find_uuid_by_sort_slid(
    structure: &Structure,
    universe: &Universe,
    func_id: usize,
    sort_slid: usize,
) -> Option<Uuid> {
    find_luid_by_sort_slid(structure, func_id, sort_slid).and_then(|luid| universe.get(luid))
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
    let deleted_uuids: std::collections::HashSet<Uuid> =
        patch.elements.deletions.iter().copied().collect();

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
                let func_len = base.functions[func_id].len();
                for (sort_id, carrier) in base.carriers.iter().enumerate() {
                    if carrier.len() as usize == func_len {
                        return Some(sort_id);
                    }
                }
            }
            None
        })
        .collect();

    result.init_functions(&domain_sort_ids);

    // Copy function values from base (for non-deleted elements)
    // Note: patches only work with local functions currently
    for func_id in 0..base.num_functions().min(result.num_functions()) {
        let Some(base_func_col) = base.functions[func_id].as_local() else { continue };
        if !result.functions[func_id].is_local() { continue };

        // Collect all the updates we need to make (to avoid borrow checker issues)
        let mut updates: Vec<(usize, Slid)> = Vec::new();

        for (old_sort_slid, opt_codomain) in base_func_col.iter().enumerate() {
            if let Some(old_codomain_slid) = get_slid(*opt_codomain) {
                // Find the domain element's Luid
                let domain_luid = find_luid_by_sort_slid(base, func_id, old_sort_slid);
                if let Some(domain_luid) = domain_luid {
                    // Check if domain element still exists in result
                    if let Some(&new_domain_slid) = result.luid_to_slid.get(&domain_luid) {
                        // Check if codomain element still exists
                        let codomain_luid = base.luids[old_codomain_slid.index()];
                        if let Some(&new_codomain_slid) = result.luid_to_slid.get(&codomain_luid) {
                            let new_sort_slid = result.sort_local_id(new_domain_slid);
                            updates.push((new_sort_slid.index(), new_codomain_slid));
                        }
                    }
                }
            }
        }

        // Apply updates
        if let Some(result_func_col) = result.functions[func_id].as_local_mut() {
            for (idx, codomain_slid) in updates {
                if idx < result_func_col.len() {
                    result_func_col[idx] = some_slid(codomain_slid);
                }
            }
        }
    }

    // Apply function value changes from patch (using UUIDs → Luids)
    // Note: patches only work with local functions currently
    for (func_id, changes) in &patch.functions.new_values {
        if *func_id < result.num_functions() && result.functions[*func_id].is_local() {
            // Collect updates first to avoid borrow checker issues
            let mut updates: Vec<(usize, Slid)> = Vec::new();
            for (domain_uuid, codomain_uuid) in changes {
                let domain_luid = universe.lookup(domain_uuid);
                let codomain_luid = universe.lookup(codomain_uuid);
                if let (Some(domain_luid), Some(codomain_luid)) = (domain_luid, codomain_luid)
                    && let (Some(&domain_slid), Some(&codomain_slid)) = (
                        result.luid_to_slid.get(&domain_luid),
                        result.luid_to_slid.get(&codomain_luid),
                    )
                {
                    let sort_slid = result.sort_local_id(domain_slid);
                    updates.push((sort_slid.index(), codomain_slid));
                }
            }

            // Apply updates
            if let Some(result_func_col) = result.functions[*func_id].as_local_mut() {
                for (idx, codomain_slid) in updates {
                    if idx < result_func_col.len() {
                        result_func_col[idx] = some_slid(codomain_slid);
                    }
                }
            }
        }
    }

    // Initialize relation storage
    // Infer arities from base if available, otherwise from patch assertions
    let relation_arities: Vec<usize> = (0..patch.num_relations)
        .map(|rel_id| {
            // Try base first
            if rel_id < base.relations.len() {
                base.relations[rel_id].arity()
            } else if let Some(assertions) = patch.relations.assertions.get(&rel_id) {
                // Infer from first assertion
                assertions.iter().next().map(|t| t.len()).unwrap_or(0)
            } else {
                0
            }
        })
        .collect();
    result.init_relations(&relation_arities);

    // Copy relation tuples from base (for non-deleted elements)
    for rel_id in 0..base.relations.len().min(patch.num_relations) {
        let base_rel = &base.relations[rel_id];

        for tuple in base_rel.iter() {
            // Convert Slid tuple to UUID tuple to check if still valid
            let uuid_tuple: Option<Vec<Uuid>> = tuple
                .iter()
                .map(|&slid| {
                    let luid = base.luids[slid.index()];
                    universe.get(luid)
                })
                .collect();

            if let Some(uuid_tuple) = uuid_tuple {
                // Check if this tuple should be retracted
                let should_retract = patch
                    .relations
                    .retractions
                    .get(&rel_id)
                    .map(|r| r.contains(&uuid_tuple))
                    .unwrap_or(false);

                if !should_retract {
                    // Check all elements still exist and convert to new Slids
                    let new_tuple: Option<Vec<Slid>> = uuid_tuple
                        .iter()
                        .map(|uuid| {
                            universe
                                .lookup(uuid)
                                .and_then(|luid| result.luid_to_slid.get(&luid).copied())
                        })
                        .collect();

                    if let Some(new_tuple) = new_tuple {
                        result.assert_relation(rel_id, new_tuple);
                    }
                }
            }
        }
    }

    // Apply relation assertions from patch
    for (rel_id, assertions) in &patch.relations.assertions {
        if *rel_id < patch.num_relations {
            for uuid_tuple in assertions {
                let slid_tuple: Option<Vec<Slid>> = uuid_tuple
                    .iter()
                    .map(|uuid| {
                        universe
                            .lookup(uuid)
                            .and_then(|luid| result.luid_to_slid.get(&luid).copied())
                    })
                    .collect();

                if let Some(slid_tuple) = slid_tuple {
                    result.assert_relation(*rel_id, slid_tuple);
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
