//! Zero-copy access to serialized structures via memory mapping.
//!
//! This module provides `MappedStructure` which memory-maps a serialized structure
//! file and provides direct access to the archived data without deserialization.
//!
//! # Benefits
//! - **No deserialization cost**: Data is accessed directly from the mmap
//! - **Minimal memory overhead**: Only the mmap exists, no heap copies
//! - **Fast startup**: Opening a structure is O(1), not O(n) elements
//!
//! # Trade-offs
//! - Read-only access (archived types are immutable)
//! - Slightly different API (ArchivedVec vs Vec, etc.)
//! - Requires file to remain valid for lifetime of MappedStructure

use std::fs::File;
use std::path::Path;
use std::sync::Arc;

use memmap2::Mmap;
use rkyv::check_archived_root;
use rkyv::Archived;

use crate::core::{SortId, TupleId};
use crate::id::{Luid, Slid, NumericId};
use crate::serialize::{
    StructureData, RelationData, FunctionColumnData, ArchivedFunctionColumnData,
};

/// A memory-mapped structure providing zero-copy access to archived data.
///
/// The structure data is accessed directly from the memory map without
/// deserialization. This is ideal for read-heavy workloads on large structures.
pub struct MappedStructure {
    /// The memory map - must outlive all references to archived data
    _mmap: Arc<Mmap>,
    /// Pointer to the archived structure data (valid for lifetime of mmap)
    archived: &'static Archived<StructureData>,
}

// Safety: The archived data is read-only and the mmap is reference-counted
unsafe impl Send for MappedStructure {}
unsafe impl Sync for MappedStructure {}

impl MappedStructure {
    /// Open a structure file with zero-copy access.
    ///
    /// The file is memory-mapped and validated. Returns an error if the file
    /// cannot be opened or contains invalid data.
    pub fn open(path: &Path) -> Result<Self, String> {
        let file = File::open(path)
            .map_err(|e| format!("Failed to open {}: {}", path.display(), e))?;

        let mmap = unsafe { Mmap::map(&file) }
            .map_err(|e| format!("Failed to mmap {}: {}", path.display(), e))?;

        // Validate and get reference to archived data
        let archived = check_archived_root::<StructureData>(&mmap)
            .map_err(|e| format!("Invalid archive in {}: {:?}", path.display(), e))?;

        // Extend lifetime to 'static - safe because mmap is Arc'd and outlives the reference
        let archived: &'static Archived<StructureData> = unsafe {
            std::mem::transmute(archived)
        };

        Ok(Self {
            _mmap: Arc::new(mmap),
            archived,
        })
    }

    /// Number of sorts in the structure
    #[inline]
    pub fn num_sorts(&self) -> usize {
        self.archived.num_sorts as usize
    }

    /// Number of elements in the structure
    #[inline]
    pub fn len(&self) -> usize {
        self.archived.luids.len()
    }

    /// Check if empty
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.archived.luids.is_empty()
    }

    /// Number of functions
    #[inline]
    pub fn num_functions(&self) -> usize {
        self.archived.functions.len()
    }

    /// Number of relations
    #[inline]
    pub fn num_relations(&self) -> usize {
        self.archived.relations.len()
    }

    /// Get the Luid for an element by Slid
    #[inline]
    pub fn get_luid(&self, slid: Slid) -> Option<Luid> {
        self.archived.luids.get(slid.index()).map(|l| Luid::from_usize(l.rep as usize))
    }

    /// Get the sort for an element by Slid
    #[inline]
    pub fn get_sort(&self, slid: Slid) -> Option<SortId> {
        self.archived.sorts.get(slid.index()).map(|&s| s as SortId)
    }

    /// Iterate over all (slid, luid, sort) triples
    pub fn elements(&self) -> impl Iterator<Item = (Slid, Luid, SortId)> + '_ {
        self.archived.luids.iter().enumerate().map(|(i, luid)| {
            let slid = Slid::from_usize(i);
            let luid = Luid::from_usize(luid.rep as usize);
            let sort = self.archived.sorts[i] as SortId;
            (slid, luid, sort)
        })
    }

    /// Get a zero-copy view of a relation
    pub fn relation(&self, rel_id: usize) -> Option<MappedRelation<'_>> {
        self.archived.relations.get(rel_id).map(|r| MappedRelation { archived: r })
    }

    /// Iterate over all relations
    pub fn relations(&self) -> impl Iterator<Item = MappedRelation<'_>> + '_ {
        self.archived.relations.iter().map(|r| MappedRelation { archived: r })
    }

    /// Get a zero-copy view of a function column
    pub fn function(&self, func_id: usize) -> Option<MappedFunction<'_>> {
        self.archived.functions.get(func_id).map(|f| MappedFunction { archived: f })
    }

    /// Get elements of a particular sort (zero-copy iteration)
    pub fn elements_of_sort(&self, sort_id: SortId) -> impl Iterator<Item = Slid> + '_ {
        self.archived.sorts.iter().enumerate()
            .filter(move |&(_, s)| *s as SortId == sort_id)
            .map(|(i, _)| Slid::from_usize(i))
    }
}

/// A zero-copy view of an archived relation.
pub struct MappedRelation<'a> {
    archived: &'a Archived<RelationData>,
}

impl<'a> MappedRelation<'a> {
    /// Relation arity
    #[inline]
    pub fn arity(&self) -> usize {
        self.archived.arity as usize
    }

    /// Number of tuples in the relation (including non-live ones)
    #[inline]
    pub fn tuple_count(&self) -> usize {
        self.archived.tuples.len()
    }

    /// Number of live tuples (in the extent)
    #[inline]
    pub fn live_count(&self) -> usize {
        self.archived.extent.len()
    }

    /// Get a tuple by ID (zero-copy - returns slice into mmap)
    pub fn get_tuple(&self, id: TupleId) -> Option<impl Iterator<Item = Slid> + '_> {
        self.archived.tuples.get(id).map(|tuple| {
            tuple.iter().map(|s| Slid::from_usize(s.rep as usize))
        })
    }

    /// Iterate over live tuple IDs
    pub fn live_tuple_ids(&self) -> impl Iterator<Item = TupleId> + '_ {
        self.archived.extent.iter().map(|&id| id as TupleId)
    }

    /// Iterate over live tuples (zero-copy)
    pub fn live_tuples(&self) -> impl Iterator<Item = impl Iterator<Item = Slid> + '_> + '_ {
        self.live_tuple_ids().filter_map(|id| self.get_tuple(id))
    }
}

/// A zero-copy view of an archived function column.
pub struct MappedFunction<'a> {
    archived: &'a Archived<FunctionColumnData>,
}

impl<'a> MappedFunction<'a> {
    /// Check if this is a local function
    pub fn is_local(&self) -> bool {
        matches!(self.archived, ArchivedFunctionColumnData::Local(_))
    }

    /// Get function value for a domain element (local functions only)
    pub fn get_local(&self, domain_sort_local_id: usize) -> Option<Slid> {
        match self.archived {
            ArchivedFunctionColumnData::Local(col) => {
                col.get(domain_sort_local_id).and_then(|opt| {
                    // ArchivedOption<u32> - check if Some
                    match opt {
                        rkyv::option::ArchivedOption::Some(idx) => {
                            Some(Slid::from_usize(*idx as usize))
                        }
                        rkyv::option::ArchivedOption::None => None,
                    }
                })
            }
            _ => None,
        }
    }

    /// Iterate over defined local function values: (domain_sort_local_id, codomain_slid)
    pub fn iter_local(&self) -> impl Iterator<Item = (usize, Slid)> + '_ {
        match self.archived {
            ArchivedFunctionColumnData::Local(col) => {
                itertools::Either::Left(col.iter().enumerate().filter_map(|(i, opt)| {
                    match opt {
                        rkyv::option::ArchivedOption::Some(idx) => {
                            Some((i, Slid::from_usize(*idx as usize)))
                        }
                        rkyv::option::ArchivedOption::None => None,
                    }
                }))
            }
            _ => itertools::Either::Right(std::iter::empty()),
        }
    }

    /// Iterate over product domain function values: (tuple, result_slid)
    pub fn iter_product(&self) -> impl Iterator<Item = (Vec<usize>, Slid)> + '_ {
        match self.archived {
            ArchivedFunctionColumnData::ProductLocal { entries, .. } => {
                itertools::Either::Left(entries.iter().map(|(tuple, result)| {
                    let tuple: Vec<usize> = tuple.iter().map(|&x| x as usize).collect();
                    let result = Slid::from_usize(*result as usize);
                    (tuple, result)
                }))
            }
            _ => itertools::Either::Right(std::iter::empty()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::Structure;
    use crate::universe::Universe;
    use crate::serialize::save_structure;
    use tempfile::tempdir;

    #[test]
    fn test_mapped_structure_basic() {
        let dir = tempdir().unwrap();
        let path = dir.path().join("test.structure");

        // Create and save a structure
        let mut universe = Universe::new();
        let mut structure = Structure::new(2); // 2 sorts
        structure.init_relations(&[1, 2]); // unary and binary relations

        // Add some elements
        let (a, _) = structure.add_element(&mut universe, 0);
        let (b, _) = structure.add_element(&mut universe, 0);
        let (c, _) = structure.add_element(&mut universe, 1);

        // Assert some relation tuples
        structure.assert_relation(0, vec![a]);
        structure.assert_relation(0, vec![b]);
        structure.assert_relation(1, vec![a, c]);

        save_structure(&structure, &path).unwrap();

        // Open with zero-copy
        let mapped = MappedStructure::open(&path).unwrap();

        assert_eq!(mapped.num_sorts(), 2);
        assert_eq!(mapped.len(), 3);
        assert_eq!(mapped.num_relations(), 2);

        // Check relation 0 (unary)
        let rel0 = mapped.relation(0).unwrap();
        assert_eq!(rel0.arity(), 1);
        assert_eq!(rel0.live_count(), 2);

        // Check relation 1 (binary)
        let rel1 = mapped.relation(1).unwrap();
        assert_eq!(rel1.arity(), 2);
        assert_eq!(rel1.live_count(), 1);

        // Iterate over live tuples
        let tuples: Vec<Vec<Slid>> = rel0.live_tuples()
            .map(|t| t.collect())
            .collect();
        assert_eq!(tuples.len(), 2);
    }

    #[test]
    fn test_zero_copy_elements() {
        let dir = tempdir().unwrap();
        let path = dir.path().join("test.structure");

        let mut universe = Universe::new();
        let mut structure = Structure::new(3);

        // Add elements to different sorts
        structure.add_element(&mut universe, 0);
        structure.add_element(&mut universe, 0);
        structure.add_element(&mut universe, 1);
        structure.add_element(&mut universe, 2);
        structure.add_element(&mut universe, 2);
        structure.add_element(&mut universe, 2);

        save_structure(&structure, &path).unwrap();

        let mapped = MappedStructure::open(&path).unwrap();

        // Count elements per sort
        assert_eq!(mapped.elements_of_sort(0).count(), 2);
        assert_eq!(mapped.elements_of_sort(1).count(), 1);
        assert_eq!(mapped.elements_of_sort(2).count(), 3);
    }

    /// Benchmark test comparing zero-copy vs deserialize access patterns.
    /// Run with: `cargo test --release benchmark_zerocopy -- --ignored --nocapture`
    #[test]
    #[ignore]
    fn benchmark_zerocopy_vs_deserialize() {
        use crate::serialize::load_structure;
        use std::time::Instant;

        let dir = tempdir().unwrap();
        let path = dir.path().join("large.structure");

        // Create a moderately large structure
        let num_elements = 100_000;
        let num_sorts = 10;
        let num_relations = 5;

        eprintln!("Creating structure with {} elements, {} sorts, {} relations...",
                  num_elements, num_sorts, num_relations);

        let mut universe = Universe::new();
        let mut structure = Structure::new(num_sorts);

        // Initialize relations with varying arities
        let arities: Vec<usize> = (0..num_relations).map(|i| (i % 3) + 1).collect();
        structure.init_relations(&arities);

        // Add elements distributed across sorts
        let elements: Vec<Slid> = (0..num_elements)
            .map(|i| {
                let sort = i % num_sorts;
                let (slid, _) = structure.add_element(&mut universe, sort);
                slid
            })
            .collect();

        // Add some relation tuples
        for (rel_id, &arity) in arities.iter().enumerate().take(num_relations) {
            for i in (0..1000).step_by(arity) {
                let tuple: Vec<Slid> = (0..arity)
                    .map(|j| elements[(i + j) % num_elements])
                    .collect();
                structure.assert_relation(rel_id, tuple);
            }
        }

        save_structure(&structure, &path).unwrap();

        let file_size = std::fs::metadata(&path).unwrap().len();
        eprintln!("Structure file size: {} bytes ({:.2} KB)", file_size, file_size as f64 / 1024.0);

        // Benchmark: deserialize approach (current)
        const ITERATIONS: usize = 100;

        eprintln!("\n--- Deserialize approach ({} iterations) ---", ITERATIONS);
        let start = Instant::now();
        for _ in 0..ITERATIONS {
            let loaded = load_structure(&path).unwrap();
            // Access pattern: count elements per sort using carrier_size
            let _counts: Vec<usize> = (0..num_sorts)
                .map(|sort| loaded.carrier_size(sort))
                .collect();
            // Also access all elements to exercise deserialization
            let _total: usize = loaded.luids.len();
        }
        let deserialize_time = start.elapsed();
        eprintln!("Total: {:?}, Per iteration: {:?}",
                  deserialize_time, deserialize_time / ITERATIONS as u32);

        // Benchmark: zero-copy approach (new)
        eprintln!("\n--- Zero-copy approach ({} iterations) ---", ITERATIONS);
        let start = Instant::now();
        for _ in 0..ITERATIONS {
            let mapped = MappedStructure::open(&path).unwrap();
            // Same access pattern: count elements of each sort
            let _counts: Vec<usize> = (0..num_sorts)
                .map(|sort| mapped.elements_of_sort(sort).count())
                .collect();
            // Also access len
            let _total: usize = mapped.len();
        }
        let zerocopy_time = start.elapsed();
        eprintln!("Total: {:?}, Per iteration: {:?}",
                  zerocopy_time, zerocopy_time / ITERATIONS as u32);

        // Compare
        let speedup = deserialize_time.as_nanos() as f64 / zerocopy_time.as_nanos() as f64;
        eprintln!("\n--- Results ---");
        eprintln!("Zero-copy is {:.2}x faster than deserialize", speedup);

        // The zero-copy approach should be faster for large structures
        // (we don't assert this since performance varies by system)
    }
}
