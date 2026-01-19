//! Structure serialization and deserialization.
//!
//! Provides rkyv-based serialization for `Structure` with both:
//! - `save_structure` / `load_structure`: heap-allocated deserialization
//! - `load_structure_mapped`: zero-copy memory-mapped access

use std::fs::{self, File};
use std::io::Write;
use std::path::Path;

use memmap2::Mmap;
use rkyv::ser::serializers::AllocSerializer;
use rkyv::ser::Serializer;
use rkyv::{check_archived_root, Archive, Deserialize, Serialize};

use crate::core::{FunctionColumn, ProductStorage, RelationStorage, SortId, Structure, TupleId, VecRelation};
use crate::id::{get_luid, get_slid, some_luid, some_slid, Luid, NumericId, Slid};

// ============================================================================
// SERIALIZABLE DATA TYPES
// ============================================================================

/// Serializable form of a relation
#[derive(Archive, Deserialize, Serialize)]
#[archive(check_bytes)]
pub struct RelationData {
    pub arity: usize,
    pub tuples: Vec<Vec<Slid>>,
    pub extent: Vec<TupleId>,
}

/// Serializable form of a function column
#[derive(Archive, Deserialize, Serialize)]
#[archive(check_bytes)]
pub enum FunctionColumnData {
    Local(Vec<Option<usize>>),
    External(Vec<Option<usize>>),
    /// Product domain: maps tuples of sort-local indices to result Slid index,
    /// along with the field sort IDs for reconstruction
    ProductLocal {
        entries: Vec<(Vec<usize>, usize)>,
        field_sorts: Vec<usize>,
    },
}

/// Serializable form of a Structure
#[derive(Archive, Deserialize, Serialize)]
#[archive(check_bytes)]
pub struct StructureData {
    pub num_sorts: usize,
    pub luids: Vec<Luid>,
    pub sorts: Vec<SortId>,
    pub functions: Vec<FunctionColumnData>,
    pub relations: Vec<RelationData>,
}

impl StructureData {
    pub fn from_structure(structure: &Structure) -> Self {
        let functions = structure
            .functions
            .iter()
            .map(|func_col| match func_col {
                FunctionColumn::Local(col) => FunctionColumnData::Local(
                    col.iter()
                        .map(|&opt| get_slid(opt).map(|s| s.index()))
                        .collect(),
                ),
                FunctionColumn::External(col) => FunctionColumnData::External(
                    col.iter()
                        .map(|&opt| get_luid(opt).map(|l| l.index()))
                        .collect(),
                ),
                FunctionColumn::ProductLocal {
                    storage,
                    field_sorts,
                } => {
                    let entries: Vec<(Vec<usize>, usize)> = storage
                        .iter_defined()
                        .map(|(tuple, result)| (tuple, result.index()))
                        .collect();
                    FunctionColumnData::ProductLocal {
                        entries,
                        field_sorts: field_sorts.clone(),
                    }
                }
            })
            .collect();

        let relations = structure
            .relations
            .iter()
            .map(|rel| RelationData {
                arity: rel.arity(),
                tuples: rel.tuples.clone(),
                extent: rel.iter_ids().collect(),
            })
            .collect();

        Self {
            num_sorts: structure.num_sorts(),
            luids: structure.luids.clone(),
            sorts: structure.sorts.clone(),
            functions,
            relations,
        }
    }

    pub fn to_structure(&self) -> Structure {
        use crate::id::NumericId;

        let mut structure = Structure::new(self.num_sorts);

        for (slid_idx, (&luid, &sort_id)) in self.luids.iter().zip(self.sorts.iter()).enumerate() {
            let added_slid = structure.add_element_with_luid(luid, sort_id);
            debug_assert_eq!(added_slid, Slid::from_usize(slid_idx));
        }

        structure.functions = self
            .functions
            .iter()
            .map(|func_data| match func_data {
                FunctionColumnData::Local(col) => FunctionColumn::Local(
                    col.iter()
                        .map(|&opt| opt.map(Slid::from_usize).and_then(some_slid))
                        .collect(),
                ),
                FunctionColumnData::External(col) => FunctionColumn::External(
                    col.iter()
                        .map(|&opt| opt.map(Luid::from_usize).and_then(some_luid))
                        .collect(),
                ),
                FunctionColumnData::ProductLocal {
                    entries,
                    field_sorts,
                } => {
                    let mut storage = ProductStorage::new_general();
                    for (tuple, result) in entries {
                        storage
                            .set(tuple, Slid::from_usize(*result))
                            .expect("no conflicts in serialized data");
                    }
                    FunctionColumn::ProductLocal {
                        storage,
                        field_sorts: field_sorts.clone(),
                    }
                }
            })
            .collect();

        structure.relations = self
            .relations
            .iter()
            .map(|rel_data| {
                let mut rel = VecRelation::new(rel_data.arity);
                for tuple in &rel_data.tuples {
                    rel.tuple_to_id.insert(tuple.clone(), rel.tuples.len());
                    rel.tuples.push(tuple.clone());
                }
                for &tuple_id in &rel_data.extent {
                    rel.extent.insert(tuple_id as u64);
                }
                rel
            })
            .collect();

        structure
    }
}

// ============================================================================
// SAVE / LOAD FUNCTIONS
// ============================================================================

/// Save a Structure to a file
pub fn save_structure(structure: &Structure, path: &Path) -> Result<(), String> {
    let data = StructureData::from_structure(structure);

    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).map_err(|e| format!("Failed to create directory: {}", e))?;
    }

    let mut serializer = AllocSerializer::<4096>::default();
    serializer
        .serialize_value(&data)
        .map_err(|e| format!("Failed to serialize structure: {}", e))?;
    let bytes = serializer.into_serializer().into_inner();

    let temp_path = path.with_extension("tmp");
    {
        let mut file =
            File::create(&temp_path).map_err(|e| format!("Failed to create temp file: {}", e))?;
        file.write_all(&bytes)
            .map_err(|e| format!("Failed to write file: {}", e))?;
        file.sync_all()
            .map_err(|e| format!("Failed to sync file: {}", e))?;
    }

    fs::rename(&temp_path, path).map_err(|e| format!("Failed to rename file: {}", e))?;

    Ok(())
}

/// Load a Structure from a file (deserializes into heap-allocated Structure)
///
/// Use this when you need a mutable Structure or when access patterns involve
/// heavy computation on the data. For read-only access to large structures,
/// prefer `load_structure_mapped` which is ~100-400x faster.
pub fn load_structure(path: &Path) -> Result<Structure, String> {
    let file = File::open(path).map_err(|e| format!("Failed to open file: {}", e))?;

    let mmap = unsafe { Mmap::map(&file) }.map_err(|e| format!("Failed to mmap file: {}", e))?;

    if mmap.is_empty() {
        return Err("Empty structure file".to_string());
    }

    let archived = check_archived_root::<StructureData>(&mmap)
        .map_err(|e| format!("Failed to validate archive: {}", e))?;

    let data: StructureData = archived
        .deserialize(&mut rkyv::Infallible)
        .map_err(|_| "Failed to deserialize structure")?;

    Ok(data.to_structure())
}

/// Load a Structure from a file with zero-copy access (memory-mapped)
///
/// This is ~100-400x faster than `load_structure` for large structures because
/// it doesn't deserialize the data - it accesses the archived format directly
/// from the memory map.
///
/// Use this for:
/// - Read-only access to large structures
/// - Fast startup when you just need to query existing data
/// - Reducing memory footprint (only the mmap exists, no heap copies)
///
/// Trade-offs:
/// - Read-only (cannot modify the structure)
/// - Slightly different API (returns `MappedStructure` instead of `Structure`)
/// - File must remain valid for lifetime of `MappedStructure`
pub fn load_structure_mapped(path: &Path) -> Result<crate::zerocopy::MappedStructure, String> {
    crate::zerocopy::MappedStructure::open(path)
}
