//! Overlay structures: patch-on-write semantics for efficient mutations.
//!
//! Instead of copying a structure to mutate it, we layer changes on top of an
//! immutable base. The base is memory-mapped (zero-copy), and mutations accumulate
//! in a thin delta layer. Cost of mutation is O(Δ), never O(base).
//!
//! # Architecture
//!
//! ```text
//! ┌────────────────────────────────────────────────────────┐
//! │  MappedStructure (immutable, mmap'd, potentially huge) │
//! └────────────────────────────────────────────────────────┘
//!                          ↑ read fallthrough
//! ┌────────────────────────────────────────────────────────┐
//! │  StructureDelta (tiny: just the changes)               │
//! └────────────────────────────────────────────────────────┘
//! ```
//!
//! # Slid Addressing
//!
//! Base elements have Slids `0..base_len`. New overlay elements get Slids
//! `base_len..base_len+delta_len`, so the address space is contiguous.
//!
//! # Usage
//!
//! ```ignore
//! // Load base (fast, zero-copy)
//! let base = MappedStructure::open(path)?;
//!
//! // Create overlay for mutations
//! let mut overlay = OverlayStructure::new(Arc::new(base));
//!
//! // Mutate (changes go to delta)
//! let elem = overlay.add_element(luid, sort_id);
//! overlay.assert_relation(rel_id, vec![elem, other]);
//!
//! // Read (checks delta first, falls back to base)
//! let sort = overlay.get_sort(elem);
//!
//! // Commit (materialize to new immutable structure)
//! let new_base = overlay.commit(new_path)?;
//!
//! // Or rollback (instant - just clears delta)
//! overlay.rollback();
//! ```

use std::collections::{BTreeSet, HashMap};
use std::path::Path;
use std::sync::Arc;

use crate::core::{SortId, Structure};
use crate::id::{Luid, NumericId, Slid};
use crate::serialize::save_structure;
use crate::zerocopy::{MappedRelation, MappedStructure};

// ============================================================================
// DELTA TYPES
// ============================================================================

/// A delta/patch representing changes to a structure.
///
/// This is the runtime-efficient analog of `Patch` (which uses UUIDs for
/// persistence). `StructureDelta` uses Slids for fast in-memory operations.
#[derive(Clone, Debug, Default)]
pub struct StructureDelta {
    /// New elements: (Luid, SortId). Slids start at base.len().
    pub new_elements: Vec<(Luid, SortId)>,

    /// Per-relation deltas (indexed by rel_id)
    pub relations: Vec<RelationDelta>,

    /// Per-function deltas (indexed by func_id)
    pub functions: Vec<FunctionDelta>,
}

impl StructureDelta {
    /// Create a new empty delta with the given number of relations and functions.
    pub fn new(num_relations: usize, num_functions: usize) -> Self {
        Self {
            new_elements: Vec::new(),
            relations: vec![RelationDelta::default(); num_relations],
            functions: vec![FunctionDelta::default(); num_functions],
        }
    }

    /// Check if the delta is empty (no changes).
    pub fn is_empty(&self) -> bool {
        self.new_elements.is_empty()
            && self.relations.iter().all(|r| r.is_empty())
            && self.functions.iter().all(|f| f.is_empty())
    }
}

/// Delta for a single relation: assertions and retractions.
#[derive(Clone, Debug, Default)]
pub struct RelationDelta {
    /// New tuples to assert (by content)
    pub assertions: BTreeSet<Vec<Slid>>,

    /// Tuples to retract (by content, not by ID)
    pub retractions: BTreeSet<Vec<Slid>>,
}

impl RelationDelta {
    /// Check if empty.
    pub fn is_empty(&self) -> bool {
        self.assertions.is_empty() && self.retractions.is_empty()
    }
}

/// Delta for a single function: updated mappings.
#[derive(Clone, Debug, Default)]
pub struct FunctionDelta {
    /// Updated mappings: domain Slid -> codomain Slid.
    /// Only supports local functions in this version.
    pub updates: HashMap<Slid, Slid>,
}

impl FunctionDelta {
    /// Check if empty.
    pub fn is_empty(&self) -> bool {
        self.updates.is_empty()
    }
}

// ============================================================================
// OVERLAY STRUCTURE
// ============================================================================

/// A mutable overlay on top of an immutable base structure.
///
/// All reads check the delta first, then fall back to the base.
/// All writes go to the delta. The base is never modified.
pub struct OverlayStructure {
    /// The immutable base (memory-mapped, zero-copy)
    base: Arc<MappedStructure>,

    /// Accumulated changes
    delta: StructureDelta,
}

impl OverlayStructure {
    /// Create a new overlay on top of a base structure.
    pub fn new(base: Arc<MappedStructure>) -> Self {
        let num_relations = base.num_relations();
        let num_functions = base.num_functions();
        Self {
            base,
            delta: StructureDelta::new(num_relations, num_functions),
        }
    }

    /// Get the immutable base.
    pub fn base(&self) -> &MappedStructure {
        &self.base
    }

    /// Get the accumulated delta.
    pub fn delta(&self) -> &StructureDelta {
        &self.delta
    }

    /// Check if clean (no changes from base).
    pub fn is_clean(&self) -> bool {
        self.delta.is_empty()
    }

    /// Discard all changes, returning to base state.
    pub fn rollback(&mut self) {
        self.delta = StructureDelta::new(
            self.base.num_relations(),
            self.base.num_functions(),
        );
    }

    // ========================================================================
    // ELEMENT OPERATIONS
    // ========================================================================

    /// Total number of elements (base + overlay).
    pub fn len(&self) -> usize {
        self.base.len() + self.delta.new_elements.len()
    }

    /// Check if empty.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Number of sorts.
    pub fn num_sorts(&self) -> usize {
        self.base.num_sorts()
    }

    /// Number of relations.
    pub fn num_relations(&self) -> usize {
        self.base.num_relations()
    }

    /// Number of functions.
    pub fn num_functions(&self) -> usize {
        self.base.num_functions()
    }

    /// Add a new element. Returns its Slid (starts at base.len()).
    pub fn add_element(&mut self, luid: Luid, sort_id: SortId) -> Slid {
        let slid = Slid::from_usize(self.base.len() + self.delta.new_elements.len());
        self.delta.new_elements.push((luid, sort_id));
        slid
    }

    /// Get the Luid for an element.
    pub fn get_luid(&self, slid: Slid) -> Option<Luid> {
        let idx = slid.index();
        let base_len = self.base.len();
        if idx < base_len {
            self.base.get_luid(slid)
        } else {
            self.delta
                .new_elements
                .get(idx - base_len)
                .map(|(luid, _)| *luid)
        }
    }

    /// Get the sort for an element.
    pub fn get_sort(&self, slid: Slid) -> Option<SortId> {
        let idx = slid.index();
        let base_len = self.base.len();
        if idx < base_len {
            self.base.get_sort(slid)
        } else {
            self.delta
                .new_elements
                .get(idx - base_len)
                .map(|(_, sort)| *sort)
        }
    }

    /// Iterate over all elements (base + overlay).
    pub fn elements(&self) -> impl Iterator<Item = (Slid, Luid, SortId)> + '_ {
        let base_iter = self.base.elements();
        let base_len = self.base.len();
        let overlay_iter = self
            .delta
            .new_elements
            .iter()
            .enumerate()
            .map(move |(i, (luid, sort))| {
                (Slid::from_usize(base_len + i), *luid, *sort)
            });
        base_iter.chain(overlay_iter)
    }

    /// Iterate over elements of a specific sort.
    pub fn elements_of_sort(&self, sort_id: SortId) -> impl Iterator<Item = Slid> + '_ {
        let base_iter = self.base.elements_of_sort(sort_id);
        let base_len = self.base.len();
        let overlay_iter = self
            .delta
            .new_elements
            .iter()
            .enumerate()
            .filter(move |(_, (_, s))| *s == sort_id)
            .map(move |(i, _)| Slid::from_usize(base_len + i));
        base_iter.chain(overlay_iter)
    }

    // ========================================================================
    // RELATION OPERATIONS
    // ========================================================================

    /// Assert a relation tuple.
    pub fn assert_relation(&mut self, rel_id: usize, tuple: Vec<Slid>) {
        // If this tuple was previously retracted, un-retract it
        self.delta.relations[rel_id].retractions.remove(&tuple);
        // Add to assertions
        self.delta.relations[rel_id].assertions.insert(tuple);
    }

    /// Retract a relation tuple (by content).
    pub fn retract_relation(&mut self, rel_id: usize, tuple: Vec<Slid>) {
        // If this tuple was asserted in the overlay, just remove it
        if self.delta.relations[rel_id].assertions.remove(&tuple) {
            return;
        }
        // Otherwise, mark it as retracted from base
        self.delta.relations[rel_id].retractions.insert(tuple);
    }

    /// Get an overlay view of a relation.
    pub fn relation(&self, rel_id: usize) -> Option<OverlayRelation<'_>> {
        let base_rel = self.base.relation(rel_id)?;
        let delta = self.delta.relations.get(rel_id)?;
        Some(OverlayRelation {
            base: base_rel,
            delta,
        })
    }

    // ========================================================================
    // FUNCTION OPERATIONS
    // ========================================================================

    /// Set a function value.
    pub fn set_function(&mut self, func_id: usize, domain: Slid, value: Slid) {
        self.delta.functions[func_id].updates.insert(domain, value);
    }

    /// Get a function value.
    pub fn get_function(&self, func_id: usize, domain: Slid) -> Option<Slid> {
        // Check delta first
        if let Some(&value) = self.delta.functions[func_id].updates.get(&domain) {
            return Some(value);
        }
        // Fall back to base (only for base elements)
        if domain.index() < self.base.len() {
            // Need to convert Slid to sort-local index for base lookup
            // This requires knowing the sort of the domain element
            if let Some(sort_id) = self.base.get_sort(domain) {
                // Count how many elements of this sort come before this one
                let sort_local_idx = self
                    .base
                    .elements_of_sort(sort_id)
                    .take_while(|&s| s.index() < domain.index())
                    .count();
                return self.base.function(func_id)?.get_local(sort_local_idx);
            }
        }
        None
    }

    // ========================================================================
    // COMMIT / MATERIALIZE
    // ========================================================================

    /// Materialize the overlay into an owned Structure.
    ///
    /// This combines the base and delta into a single Structure that can be
    /// saved to disk.
    pub fn materialize(&self) -> Structure {
        // Start with a fresh structure
        let mut structure = Structure::new(self.num_sorts());

        // Copy base elements (we need to create them fresh since Structure wants to own them)
        // For now, we'll iterate and add. In production, we'd want a more efficient bulk copy.
        let mut slid_map: HashMap<Slid, Slid> = HashMap::new();

        // We need a universe to add elements, but we're materializing so we'll
        // reuse the Luids from the overlay. Create elements with existing Luids.
        for (old_slid, luid, sort_id) in self.elements() {
            let new_slid = structure.add_element_with_luid(luid, sort_id);
            slid_map.insert(old_slid, new_slid);
        }

        // Initialize relations with correct arities
        let arities: Vec<usize> = (0..self.num_relations())
            .map(|rel_id| {
                self.base
                    .relation(rel_id)
                    .map(|r| r.arity())
                    .unwrap_or(0)
            })
            .collect();
        structure.init_relations(&arities);

        // Copy relation tuples (applying the slid remapping)
        for rel_id in 0..self.num_relations() {
            if let Some(rel) = self.relation(rel_id) {
                for tuple in rel.live_tuples() {
                    let remapped: Vec<Slid> = tuple
                        .iter()
                        .map(|&old_slid| slid_map.get(&old_slid).copied().unwrap_or(old_slid))
                        .collect();
                    structure.assert_relation(rel_id, remapped);
                }
            }
        }

        // TODO: Copy functions (more complex, skip for now)

        structure
    }

    /// Commit the overlay: materialize and save to a new file, returning the new MappedStructure.
    pub fn commit(&self, path: &Path) -> Result<MappedStructure, String> {
        let structure = self.materialize();
        save_structure(&structure, path)?;
        MappedStructure::open(path)
    }
}

// ============================================================================
// OVERLAY RELATION VIEW
// ============================================================================

/// A read-only view of a relation through an overlay.
pub struct OverlayRelation<'a> {
    base: MappedRelation<'a>,
    delta: &'a RelationDelta,
}

impl<'a> OverlayRelation<'a> {
    /// Relation arity.
    pub fn arity(&self) -> usize {
        self.base.arity()
    }

    /// Approximate count of live tuples.
    ///
    /// This is approximate because checking retractions against base tuples
    /// would require iterating. For exact count, iterate `live_tuples()`.
    pub fn live_count_approx(&self) -> usize {
        // Base count + assertions - retractions (approximate)
        self.base.live_count() + self.delta.assertions.len()
            - self.delta.retractions.len().min(self.base.live_count())
    }

    /// Check if a tuple is live (in base or assertions, not retracted).
    pub fn contains(&self, tuple: &[Slid]) -> bool {
        // Check if retracted
        if self.delta.retractions.contains(tuple) {
            return false;
        }
        // Check assertions
        if self.delta.assertions.contains(tuple) {
            return true;
        }
        // Check base - need to iterate base tuples to check
        // This is O(n) which is unfortunate, but we don't have a hash index
        for base_tuple in self.base.live_tuples() {
            let base_vec: Vec<Slid> = base_tuple.collect();
            if base_vec.as_slice() == tuple {
                return true;
            }
        }
        false
    }

    /// Iterate over live tuples (base filtered by retractions, plus assertions).
    ///
    /// Returns tuples as `Vec<Slid>` for simplicity. Each vec is one tuple.
    pub fn live_tuples(&self) -> impl Iterator<Item = Vec<Slid>> + '_ {
        // Collect base tuples, filtering out retracted ones
        let base_filtered = self
            .base
            .live_tuples()
            .map(|t| t.collect::<Vec<_>>())
            .filter(|tuple| !self.delta.retractions.contains(tuple));

        // Chain with assertions
        let assertions = self.delta.assertions.iter().cloned();

        base_filtered.chain(assertions)
    }
}

// ============================================================================
// TESTS
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::universe::Universe;
    use crate::serialize::save_structure;
    use tempfile::tempdir;

    #[test]
    fn test_overlay_add_elements() {
        let dir = tempdir().unwrap();
        let path = dir.path().join("base.structure");

        // Create and save a base structure
        let mut universe = Universe::new();
        let mut base_structure = Structure::new(2);
        let (a, _) = base_structure.add_element(&mut universe, 0);
        let (b, _) = base_structure.add_element(&mut universe, 1);
        save_structure(&base_structure, &path).unwrap();

        // Load as mapped and create overlay
        let mapped = MappedStructure::open(&path).unwrap();
        let mut overlay = OverlayStructure::new(Arc::new(mapped));

        assert_eq!(overlay.len(), 2);
        assert!(overlay.is_clean());

        // Add elements through overlay
        let luid_c = universe.intern(crate::id::Uuid::now_v7());
        let c = overlay.add_element(luid_c, 0);

        assert_eq!(overlay.len(), 3);
        assert!(!overlay.is_clean());
        assert_eq!(c.index(), 2); // New element gets Slid after base

        // Check element lookups
        assert_eq!(overlay.get_sort(a), Some(0));
        assert_eq!(overlay.get_sort(b), Some(1));
        assert_eq!(overlay.get_sort(c), Some(0));

        // Rollback
        overlay.rollback();
        assert_eq!(overlay.len(), 2);
        assert!(overlay.is_clean());
    }

    #[test]
    fn test_overlay_relations() {
        let dir = tempdir().unwrap();
        let path = dir.path().join("base.structure");

        // Create base with a relation
        let mut universe = Universe::new();
        let mut base_structure = Structure::new(1);
        let (a, _) = base_structure.add_element(&mut universe, 0);
        let (b, _) = base_structure.add_element(&mut universe, 0);
        base_structure.init_relations(&[2]); // binary relation
        base_structure.assert_relation(0, vec![a, b]);
        save_structure(&base_structure, &path).unwrap();

        // Load and overlay
        let mapped = MappedStructure::open(&path).unwrap();
        let mut overlay = OverlayStructure::new(Arc::new(mapped));

        // Check base relation
        let rel = overlay.relation(0).unwrap();
        assert_eq!(rel.arity(), 2);
        assert!(rel.contains(&[a, b]));
        assert!(!rel.contains(&[b, a]));

        // Assert new tuple
        overlay.assert_relation(0, vec![b, a]);
        let rel = overlay.relation(0).unwrap();
        assert!(rel.contains(&[a, b]));
        assert!(rel.contains(&[b, a]));

        // Retract original tuple
        overlay.retract_relation(0, vec![a, b]);
        let rel = overlay.relation(0).unwrap();
        assert!(!rel.contains(&[a, b]));
        assert!(rel.contains(&[b, a]));
    }

    #[test]
    fn test_overlay_materialize() {
        let dir = tempdir().unwrap();
        let base_path = dir.path().join("base.structure");
        let new_path = dir.path().join("new.structure");

        // Create base
        let mut universe = Universe::new();
        let mut base_structure = Structure::new(1);
        let (a, _) = base_structure.add_element(&mut universe, 0);
        base_structure.init_relations(&[1]); // unary relation
        base_structure.assert_relation(0, vec![a]);
        save_structure(&base_structure, &base_path).unwrap();

        // Load, modify, commit
        let mapped = MappedStructure::open(&base_path).unwrap();
        let mut overlay = OverlayStructure::new(Arc::new(mapped));

        let luid_b = universe.intern(crate::id::Uuid::now_v7());
        let b = overlay.add_element(luid_b, 0);
        overlay.assert_relation(0, vec![b]);

        let new_mapped = overlay.commit(&new_path).unwrap();

        // Verify new structure
        assert_eq!(new_mapped.len(), 2);
        assert_eq!(new_mapped.num_relations(), 1);
        let rel = new_mapped.relation(0).unwrap();
        assert_eq!(rel.live_count(), 2);
    }
}
