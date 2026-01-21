//! Bridge between Patch (version control) and tensor deltas (incremental computation).
//!
//! This module connects the UUID-based `Patch` types from version control
//! to the index-based tensor delta representation used for incremental axiom checking.
//!
//! Key concepts:
//! - **MonotoneSubmodel**: Under this discipline, structure only grows (no deletions).
//!   Element additions create new indices; relation assertions create new tensor entries.
//! - **Dimension growth**: Adding elements to sort S increases that dimension's size.
//!   The "border" consists of tuples involving at least one new index.
//! - **Delta tensors**: For incremental computation, we track (value, delta) pairs
//!   where delta contains only the new/changed entries.
//!
//! # Pipeline
//!
//! ```text
//! Patch (UUIDs, version control)
//!    │
//!    ▼ extract_dimension_changes()
//! DimensionDelta (per-sort old_size → new_size)
//!    │
//!    ▼ patch_to_relation_delta()
//! SparseTensorData (index-based delta tensor)
//!    │
//!    ▼ IncrementalTensor::with_delta()
//! IncrementalTensor (for TensorSym incremental interpreter)
//! ```

use std::collections::{BTreeMap, BTreeSet};

use crate::core::{Signature, SortId, Structure};
use crate::id::{NumericId, Uuid};
use crate::patch::{ElementPatch, Patch};
use crate::universe::Universe;

use super::algebra::{from_dimension_growth, IncrementalTensor, SparseTensorData};
use super::compile::relation_column_sorts;
use super::pattern::{BTreeSetPattern, SparsityPattern};

// ============================================================================
// Dimension Changes
// ============================================================================

/// Per-sort dimension changes extracted from a Patch.
///
/// For each sort, tracks how the carrier size changed.
/// Under MonotoneSubmodel: old_size <= new_size always.
#[derive(Clone, Debug, Default)]
pub struct DimensionDelta {
    /// sort_id → (old_cardinality, new_cardinality)
    pub changes: BTreeMap<SortId, (usize, usize)>,
}

impl DimensionDelta {
    /// Create from explicit old and new cardinalities per sort.
    pub fn from_cardinalities(old: &[usize], new: &[usize]) -> Self {
        assert_eq!(old.len(), new.len());
        let changes = old
            .iter()
            .zip(new.iter())
            .enumerate()
            .filter(|&(_, (o, n))| o != n)
            .map(|(sort_id, (old_card, new_card))| (sort_id, (*old_card, *new_card)))
            .collect();
        Self { changes }
    }

    /// Get the old dimension for a sort (returns 0 if sort is new).
    pub fn old_dim(&self, sort_id: SortId) -> usize {
        self.changes.get(&sort_id).map(|(old, _)| *old).unwrap_or(0)
    }

    /// Get the new dimension for a sort.
    pub fn new_dim(&self, sort_id: SortId) -> Option<usize> {
        self.changes.get(&sort_id).map(|(_, new)| *new)
    }

    /// Check if any dimensions changed.
    pub fn is_empty(&self) -> bool {
        self.changes.is_empty()
    }

    /// Get old dimensions for a list of sorts (for tensor creation).
    pub fn old_dims(&self, sort_ids: &[SortId]) -> Vec<usize> {
        sort_ids.iter().map(|&s| self.old_dim(s)).collect()
    }

    /// Get new dimensions for a list of sorts.
    /// Uses the provided defaults for sorts not in the delta.
    pub fn new_dims(&self, sort_ids: &[SortId], defaults: &[usize]) -> Vec<usize> {
        sort_ids
            .iter()
            .zip(defaults.iter())
            .map(|(&s, &default)| self.new_dim(s).unwrap_or(default))
            .collect()
    }
}

/// Extract dimension changes from an ElementPatch.
///
/// Counts how many elements were added per sort. Combined with the old
/// structure's cardinalities, this gives the dimension growth.
pub fn extract_dimension_changes(
    patch: &ElementPatch,
    old_structure: &Structure,
    num_sorts: usize,
) -> DimensionDelta {
    // Count additions per sort
    let mut additions_per_sort: BTreeMap<SortId, usize> = BTreeMap::new();
    for &sort_id in patch.additions.values() {
        *additions_per_sort.entry(sort_id).or_default() += 1;
    }

    // Build dimension changes
    let mut changes = BTreeMap::new();
    for sort_id in 0..num_sorts {
        let old_card = old_structure.carriers.get(sort_id).map(|c| c.len()).unwrap_or(0) as usize;
        let additions = additions_per_sort.get(&sort_id).copied().unwrap_or(0);
        let new_card = old_card + additions;
        if old_card != new_card {
            changes.insert(sort_id, (old_card, new_card));
        }
    }

    DimensionDelta { changes }
}

// ============================================================================
// Relation Deltas
// ============================================================================

/// Configuration for converting relation deltas to tensors.
pub struct RelationDeltaConfig<'a> {
    /// Theory signature (for getting relation domain sorts)
    pub signature: &'a Signature,
    /// The old structure (before patch application)
    pub old_structure: &'a Structure,
    /// The new structure (after patch application)
    pub new_structure: &'a Structure,
    /// Universe for UUID → Luid resolution
    pub universe: &'a Universe,
    /// Dimension changes extracted from the element patch
    pub dim_delta: &'a DimensionDelta,
}

/// Convert relation assertions from a Patch to a sparse tensor pattern.
///
/// Takes UUID-based tuple assertions and converts them to index-based
/// tensor entries using the new structure's element ordering.
///
/// Returns None if:
/// - The relation doesn't exist in the signature
/// - Any UUID in the assertion can't be resolved
pub fn relation_assertions_to_pattern(
    rel_id: usize,
    assertions: &BTreeSet<Vec<Uuid>>,
    config: &RelationDeltaConfig,
) -> Option<BTreeSetPattern> {
    let sig = config.signature;
    let new_structure = config.new_structure;
    let universe = config.universe;

    // Get column sorts from signature
    if rel_id >= sig.relations.len() {
        return None;
    }
    let column_sorts = relation_column_sorts(sig, rel_id);
    let arity = column_sorts.len();

    // Build dimensions from actual per-column sorts
    let dims: Vec<usize> = column_sorts
        .iter()
        .map(|&sort_id| {
            new_structure
                .carriers
                .get(sort_id)
                .map(|c| c.len())
                .unwrap_or(0) as usize
        })
        .collect();

    let mut pattern = BTreeSetPattern::empty(dims.clone());

    for uuid_tuple in assertions {
        if uuid_tuple.len() != arity {
            continue;
        }

        // Convert each UUID to its index in the new structure
        let index_tuple: Option<Vec<usize>> = uuid_tuple
            .iter()
            .map(|uuid| {
                // UUID → Luid → Slid → sort-local index
                universe.lookup(uuid).and_then(|luid| {
                    new_structure.luid_to_slid.get(&luid).map(|&slid| {
                        new_structure.sort_local_id(slid).index()
                    })
                })
            })
            .collect();

        if let Some(indices) = index_tuple {
            // Verify indices are within bounds
            if indices.iter().zip(&dims).all(|(idx, dim)| *idx < *dim) {
                pattern.insert(indices);
            }
        }
    }

    Some(pattern)
}

/// Convert a full relation to a tensor pattern, then extract the delta.
///
/// This is useful when you have the full new state but need to compute
/// what changed relative to old dimensions.
pub fn relation_to_incremental_tensor(
    rel_id: usize,
    config: &RelationDeltaConfig,
) -> Option<IncrementalTensor<bool, BTreeSetPattern>> {
    let sig = config.signature;
    let new_structure = config.new_structure;
    let old_structure = config.old_structure;

    // Get column sorts from signature
    if rel_id >= sig.relations.len() {
        return None;
    }
    let column_sorts = relation_column_sorts(sig, rel_id);
    let arity = column_sorts.len();

    // Compute dimensions from actual per-column sorts
    let new_dims: Vec<usize> = column_sorts
        .iter()
        .map(|&sort_id| {
            new_structure
                .carriers
                .get(sort_id)
                .map(|c| c.len())
                .unwrap_or(0) as usize
        })
        .collect();

    let old_dims: Vec<usize> = column_sorts
        .iter()
        .map(|&sort_id| {
            old_structure
                .carriers
                .get(sort_id)
                .map(|c| c.len())
                .unwrap_or(0) as usize
        })
        .collect();

    // Build full pattern from new relation
    let mut pattern = BTreeSetPattern::empty(new_dims.clone());

    // Only proceed if the relation exists in the new structure
    if rel_id < new_structure.relations.len() {
        let new_rel = &new_structure.relations[rel_id];
        for tuple in new_rel.iter() {
            let indices: Vec<usize> = tuple
                .iter()
                .map(|&slid| new_structure.sort_local_id(slid).index())
                .collect();
            if indices.len() == arity {
                pattern.insert(indices);
            }
        }
    }

    let full_tensor: SparseTensorData<bool, BTreeSetPattern> = SparseTensorData {
        pattern,
        values: vec![],
    };

    // Create incremental tensor with border as delta
    Some(from_dimension_growth(full_tensor, &old_dims))
}

// ============================================================================
// Full Patch to Tensor Delta
// ============================================================================

/// Result of converting a Patch to tensor deltas.
#[derive(Clone, Debug)]
pub struct PatchTensorDelta {
    /// Dimension changes per sort
    pub dim_delta: DimensionDelta,
    /// Delta patterns for each changed relation (rel_id → delta pattern)
    pub relation_deltas: BTreeMap<usize, BTreeSetPattern>,
}

/// Convert a full Patch to tensor deltas for all changed relations.
///
/// This is the main entry point for the Patch → tensor delta pipeline.
pub fn patch_to_tensor_deltas(
    patch: &Patch,
    sig: &Signature,
    old_structure: &Structure,
    new_structure: &Structure,
    universe: &Universe,
) -> PatchTensorDelta {
    // Extract dimension changes
    let dim_delta = extract_dimension_changes(
        &patch.elements,
        old_structure,
        patch.num_sorts,
    );

    let config = RelationDeltaConfig {
        signature: sig,
        old_structure,
        new_structure,
        universe,
        dim_delta: &dim_delta,
    };

    // Convert relation assertions to delta patterns
    let mut relation_deltas = BTreeMap::new();
    for (rel_id, assertions) in &patch.relations.assertions {
        if let Some(pattern) = relation_assertions_to_pattern(*rel_id, assertions, &config)
            && !pattern.is_empty() {
                relation_deltas.insert(*rel_id, pattern);
            }
    }

    PatchTensorDelta {
        dim_delta,
        relation_deltas,
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_dimension_delta_from_cardinalities() {
        let old = vec![3, 5, 2];
        let new = vec![4, 5, 3]; // sort 0: +1, sort 1: no change, sort 2: +1

        let delta = DimensionDelta::from_cardinalities(&old, &new);

        assert_eq!(delta.old_dim(0), 3);
        assert_eq!(delta.new_dim(0), Some(4));
        assert_eq!(delta.old_dim(1), 0); // not in changes
        assert_eq!(delta.new_dim(1), None);
        assert_eq!(delta.old_dim(2), 2);
        assert_eq!(delta.new_dim(2), Some(3));

        assert!(!delta.is_empty());
    }

    #[test]
    fn test_dimension_delta_old_dims() {
        let old = vec![3, 5, 2];
        let new = vec![4, 5, 3];
        let delta = DimensionDelta::from_cardinalities(&old, &new);

        // For a relation over [sort0, sort2]
        let sort_ids = vec![0, 2];
        let old_dims = delta.old_dims(&sort_ids);
        assert_eq!(old_dims, vec![3, 2]);
    }

    #[test]
    fn test_dimension_delta_empty() {
        let old = vec![3, 5, 2];
        let new = vec![3, 5, 2]; // no changes

        let delta = DimensionDelta::from_cardinalities(&old, &new);
        assert!(delta.is_empty());
    }

    #[test]
    fn test_btreeset_pattern_basics() {
        // Test that our BTreeSetPattern interface works as expected
        let mut pattern = BTreeSetPattern::empty(vec![4, 4]);
        pattern.insert(vec![0, 1]);
        pattern.insert(vec![3, 3]); // new element

        assert_eq!(pattern.len(), 2);
        assert!(pattern.contains(&[0, 1]));
        assert!(pattern.contains(&[3, 3]));
        assert!(!pattern.contains(&[0, 0]));
    }

    #[test]
    fn test_relation_column_sorts_multi_sort() {
        use crate::core::{DerivedSort, Signature};

        // Create signature with two sorts: Person, City
        let mut sig = Signature::new();
        let person = sig.add_sort("Person".to_string());
        let city = sig.add_sort("City".to_string());

        // Add a relation: lives_in(Person, City)
        let domain = DerivedSort::Product(vec![
            ("person".to_string(), DerivedSort::Base(person)),
            ("city".to_string(), DerivedSort::Base(city)),
        ]);
        sig.add_relation("lives_in".to_string(), domain);

        // Verify relation_column_sorts returns correct sorts
        let column_sorts = relation_column_sorts(&sig, 0);
        assert_eq!(column_sorts, vec![person, city]);
        assert_eq!(column_sorts, vec![0, 1]); // Person is sort 0, City is sort 1
    }

    #[test]
    fn test_multi_sort_relation_dimensions() {
        use crate::core::{DerivedSort, Signature, Structure};
        use crate::universe::Universe;

        // Create signature with two sorts
        let mut sig = Signature::new();
        let person = sig.add_sort("Person".to_string());
        let city = sig.add_sort("City".to_string());

        // Add lives_in(Person, City) relation
        let domain = DerivedSort::Product(vec![
            ("person".to_string(), DerivedSort::Base(person)),
            ("city".to_string(), DerivedSort::Base(city)),
        ]);
        sig.add_relation("lives_in".to_string(), domain);

        // Create structure with 3 persons and 2 cities
        let mut old_structure = Structure::new(2);
        let mut universe = Universe::new();

        // Add persons (sort 0)
        for _ in 0..3 {
            old_structure.add_element(&mut universe, person);
        }
        // Add cities (sort 1)
        for _ in 0..2 {
            old_structure.add_element(&mut universe, city);
        }

        old_structure.init_relations(&[2]); // binary relation

        // Create new structure with one more person
        let mut new_structure = Structure::new(2);
        for _ in 0..4 {
            new_structure.add_element(&mut universe, person);
        }
        for _ in 0..2 {
            new_structure.add_element(&mut universe, city);
        }
        new_structure.init_relations(&[2]);

        // Create delta config
        let dim_delta = DimensionDelta::from_cardinalities(
            &[3, 2], // old: 3 persons, 2 cities
            &[4, 2], // new: 4 persons, 2 cities
        );

        let config = RelationDeltaConfig {
            signature: &sig,
            old_structure: &old_structure,
            new_structure: &new_structure,
            universe: &universe,
            dim_delta: &dim_delta,
        };

        // Build incremental tensor for relation
        let result = relation_to_incremental_tensor(0, &config);
        assert!(result.is_some());

        let incr_tensor = result.unwrap();
        // The tensor should have shape [4, 2] (4 persons × 2 cities)
        // Old dims were [3, 2], so border includes person index 3
        assert_eq!(incr_tensor.value.pattern.dims(), &[4, 2]);
    }
}
