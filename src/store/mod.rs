//! Append-only store for GeologMeta elements.
//!
//! This module provides the foundation for geolog's persistent, versioned data model.
//! All data (theories, instances, elements, function values, relation tuples) is stored
//! as elements in a single GeologMeta Structure that is append-only.
//!
//! # Key design principles
//!
//! - **Append-only**: Elements are never deleted, only tombstoned
//! - **Patch-based versioning**: Each theory/instance version is a delta from its parent
//! - **Incremental materialization**: Views are updated efficiently as patches arrive
//! - **Eternal format**: Once GeologMeta schema is v1.0, it never changes
//!
//! # Module structure
//!
//! - [`schema`]: Cached sort and function IDs from GeologMeta
//! - [`append`]: Low-level element append operations
//! - [`theory`]: Theory CRUD (create, extend, add sorts/functions/relations)
//! - [`instance`]: Instance CRUD (create, extend, add elements, retractions)
//! - [`commit`]: Version control (commits, name bindings, history)
//! - [`query`]: Query operations (walking version chains)
//! - [`materialize`]: Materialized views for fast indexed access

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use crate::core::{DerivedSort, ElaboratedTheory, Structure};
use crate::id::{NumericId, Slid};
use crate::meta::geolog_meta;
use crate::naming::NamingIndex;
use crate::universe::Universe;

pub mod append;
pub mod batch;
pub mod bootstrap_queries;
pub mod columnar;
pub mod commit;
pub mod instance;
pub mod materialize;
pub mod query;
pub mod schema;
pub mod theory;

pub use batch::{ElementBatch, ElementBuilder, ElementCreationContext};
pub use materialize::MaterializedView;
pub use schema::{FuncIds, SortIds};

// ============================================================================
// STORE
// ============================================================================

/// The append-only store: a single GeologMeta Structure plus indexing.
///
/// This is the "source of truth" for all geolog data. Theories and instances
/// are represented as elements within this structure, along with their
/// components (sorts, functions, relations, elements, values, etc.).
pub struct Store {
    /// The GeologMeta instance containing all data
    pub meta: Structure,

    /// The GeologMeta theory (for signature lookups)
    pub meta_theory: Arc<ElaboratedTheory>,

    /// Universe for UUID <-> Luid mapping
    pub universe: Universe,

    /// Human-readable names for UUIDs
    pub naming: NamingIndex,

    /// Current HEAD commit (None if no commits yet)
    pub head: Option<Slid>,

    /// Uncommitted changes (name -> target slid)
    /// These become NameBindings on commit
    pub uncommitted: HashMap<String, UncommittedBinding>,

    /// Cached sort IDs for quick lookup
    pub(crate) sort_ids: SortIds,

    /// Cached function IDs for quick lookup
    pub(crate) func_ids: FuncIds,

    /// Path for persistence (None = in-memory only)
    pub path: Option<PathBuf>,

    /// Whether there are unsaved changes
    dirty: bool,
}

/// An uncommitted name binding
#[derive(Debug, Clone)]
pub struct UncommittedBinding {
    /// The target (Theory or Instance slid in meta)
    pub target: Slid,
    /// Whether this binds to a theory or instance
    pub kind: BindingKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BindingKind {
    Theory,
    Instance,
}

// ============================================================================
// APPEND TRAIT IMPLEMENTATION
// ============================================================================

impl append::AppendOps for Store {
    fn add_element(&mut self, sort_id: usize, name: &str) -> Slid {
        let (slid, luid) = self.meta.add_element(&mut self.universe, sort_id);
        let uuid = self.universe.get(luid).expect("freshly created luid should have uuid");
        self.naming.insert(uuid, vec![name.to_string()]);
        self.dirty = true;
        slid
    }

    fn add_element_qualified(&mut self, sort_id: usize, path: Vec<String>) -> Slid {
        let (slid, luid) = self.meta.add_element(&mut self.universe, sort_id);
        let uuid = self.universe.get(luid).expect("freshly created luid should have uuid");
        self.naming.insert(uuid, path);
        self.dirty = true;
        slid
    }

    fn define_func(&mut self, func_id: usize, domain: Slid, codomain: Slid) -> Result<(), String> {
        self.meta.define_function(func_id, domain, codomain)?;
        self.dirty = true;
        Ok(())
    }

    fn get_func(&self, func_id: usize, domain: Slid) -> Option<Slid> {
        let sort_slid = self.meta.sort_local_id(domain);
        self.meta.get_function(func_id, sort_slid)
    }

    fn elements_of_sort(&self, sort_id: usize) -> Vec<Slid> {
        if sort_id >= self.meta.carriers.len() {
            return vec![];
        }
        self.meta.carriers[sort_id]
            .iter()
            .map(|x| Slid::from_usize(x as usize))
            .collect()
    }

    fn get_element_name(&self, slid: Slid) -> String {
        let luid = self.meta.get_luid(slid);
        if let Some(uuid) = self.universe.get(luid) {
            self.naming.display_name(&uuid)
        } else {
            format!("#{}", slid.index())
        }
    }
}

// ============================================================================
// STORE IMPL
// ============================================================================

impl Store {
    /// Create a new empty store
    pub fn new() -> Self {
        let meta_theory = geolog_meta();
        let num_sorts = meta_theory.theory.signature.sorts.len();
        let mut meta = Structure::new(num_sorts);

        // Initialize function storage for all functions in GeologMeta
        let domain_sort_ids: Vec<Option<usize>> = meta_theory
            .theory
            .signature
            .functions
            .iter()
            .map(|f| match &f.domain {
                DerivedSort::Base(sort_id) => Some(*sort_id),
                DerivedSort::Product(_) => None,
            })
            .collect();
        meta.init_functions(&domain_sort_ids);

        // Initialize relation storage
        let arities: Vec<usize> = meta_theory
            .theory
            .signature
            .relations
            .iter()
            .map(|r| match &r.domain {
                DerivedSort::Base(_) => 1,
                DerivedSort::Product(fields) => fields.len(),
            })
            .collect();
        meta.init_relations(&arities);

        let sort_ids = SortIds::from_theory(&meta_theory);
        let func_ids = FuncIds::from_theory(&meta_theory);

        Self {
            meta,
            meta_theory,
            universe: Universe::new(),
            naming: NamingIndex::new(),
            head: None,
            uncommitted: HashMap::new(),
            sort_ids,
            func_ids,
            path: None,
            dirty: false,
        }
    }

    /// Create a store with a persistence path
    pub fn with_path(path: impl Into<PathBuf>) -> Self {
        let path = path.into();

        // Create directory if needed
        let _ = std::fs::create_dir_all(&path);

        // Create store with paths for all components
        let mut store = Self::new();
        store.path = Some(path.clone());
        store.universe = Universe::with_path(path.join("universe"));
        store.naming = NamingIndex::with_path(path.join("naming"));
        store
    }

    /// Load a store from disk, or create new if doesn't exist
    pub fn load_or_create(path: impl Into<PathBuf>) -> Self {
        let path = path.into();
        if path.exists() {
            Self::load(&path).unwrap_or_else(|_| Self::with_path(path))
        } else {
            Self::with_path(path)
        }
    }

    /// Load a store from disk
    pub fn load(path: &Path) -> Result<Self, String> {
        // Load meta structure
        let meta_path = path.join("meta.bin");
        let meta = crate::serialize::load_structure(&meta_path)?;

        // Load universe
        let universe_path = path.join("universe");
        let universe = Universe::load(&universe_path)?;

        // Load naming
        let naming_path = path.join("naming");
        let naming = NamingIndex::load(&naming_path)?;

        // Load HEAD commit reference
        let head_path = path.join("HEAD");
        let head = if head_path.exists() {
            let content = std::fs::read_to_string(&head_path)
                .map_err(|e| format!("Failed to read HEAD: {}", e))?;
            let index: usize = content
                .trim()
                .parse()
                .map_err(|e| format!("Invalid HEAD format: {}", e))?;
            Some(Slid::from_usize(index))
        } else {
            None
        };

        // Get meta theory and build IDs (same as new())
        let meta_theory = geolog_meta();
        let sort_ids = SortIds::from_theory(&meta_theory);
        let func_ids = FuncIds::from_theory(&meta_theory);

        Ok(Self {
            meta,
            meta_theory,
            universe,
            naming,
            head,
            uncommitted: HashMap::new(),
            sort_ids,
            func_ids,
            path: Some(path.to_path_buf()),
            dirty: false,
        })
    }

    /// Save the store to disk
    pub fn save(&mut self) -> Result<(), String> {
        if !self.dirty {
            return Ok(());
        }

        let Some(path) = &self.path else {
            return Ok(()); // In-memory store, nothing to save
        };

        // Ensure parent directory exists
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent)
                .map_err(|e| format!("Failed to create directory: {}", e))?;
        }

        // Save universe
        self.universe.save()?;

        // Save naming
        self.naming.save()?;

        // Save meta structure
        let meta_path = path.join("meta.bin");
        crate::serialize::save_structure(&self.meta, &meta_path)?;

        // Save head commit reference
        if let Some(head) = self.head {
            let head_path = path.join("HEAD");
            std::fs::write(&head_path, format!("{}", head.index()))
                .map_err(|e| format!("Failed to write HEAD: {}", e))?;
        }

        self.dirty = false;
        Ok(())
    }

    /// Check if the store has uncommitted changes
    pub fn is_dirty(&self) -> bool {
        self.dirty || !self.uncommitted.is_empty()
    }

    /// Get the number of elements in the meta structure
    pub fn len(&self) -> usize {
        self.meta.len()
    }

    /// Check if the store is empty
    pub fn is_empty(&self) -> bool {
        self.meta.is_empty()
    }

    // ========================================================================
    // COLUMNAR BATCH STORAGE
    // ========================================================================

    /// Get the directory for instance data (columnar batches)
    fn instance_data_dir(&self) -> Option<PathBuf> {
        self.path.as_ref().map(|p| p.join("instance_data"))
    }

    /// Save instance data batch for a specific patch version.
    ///
    /// Each patch can have up to 2 batches per instance:
    /// - One EDB batch (user-declared facts)
    /// - One IDB batch (chase-derived facts)
    ///
    /// The batch kind is encoded in the filename to allow both to coexist.
    pub fn save_instance_data_batch(
        &self,
        instance_uuid: crate::id::Uuid,
        patch_version: u64,
        batch: &columnar::InstanceDataBatch,
    ) -> Result<(), String> {
        use rkyv::ser::serializers::AllocSerializer;
        use rkyv::ser::Serializer;

        let Some(dir) = self.instance_data_dir() else {
            return Ok(()); // In-memory store, nothing to save
        };

        // Ensure directory exists
        std::fs::create_dir_all(&dir)
            .map_err(|e| format!("Failed to create instance_data dir: {}", e))?;

        // Serialize batch with rkyv
        let mut serializer = AllocSerializer::<4096>::default();
        serializer.serialize_value(batch)
            .map_err(|e| format!("Failed to serialize instance data batch: {}", e))?;
        let bytes = serializer.into_serializer().into_inner();

        // Write to file named by instance UUID, patch version, and batch kind
        // EDB batches: {uuid}_v{version}_edb.batch.bin
        // IDB batches: {uuid}_v{version}_idb.batch.bin
        let kind_suffix = match batch.kind {
            columnar::BatchKind::Edb => "edb",
            columnar::BatchKind::Idb => "idb",
        };
        let filename = format!("{}_v{}_{}.batch.bin", instance_uuid, patch_version, kind_suffix);
        let file_path = dir.join(filename);
        std::fs::write(&file_path, &bytes)
            .map_err(|e| format!("Failed to write instance data batch: {}", e))?;

        Ok(())
    }

    /// Load all instance data batches for an instance (across all patch versions).
    ///
    /// Returns batches in version order so they can be applied sequentially.
    /// Both EDB and IDB batches are loaded; use `batch.kind` to filter if needed.
    pub fn load_instance_data_batches(
        &self,
        instance_uuid: crate::id::Uuid,
    ) -> Result<Vec<columnar::InstanceDataBatch>, String> {
        use rkyv::Deserialize;

        let Some(dir) = self.instance_data_dir() else {
            return Ok(vec![]); // In-memory store, no data
        };

        if !dir.exists() {
            return Ok(vec![]);
        }

        // (version, is_idb, batch) - sort so EDB comes before IDB at same version
        let mut version_batches: Vec<(u64, bool, columnar::InstanceDataBatch)> = Vec::new();
        let prefix = format!("{}_v", instance_uuid);

        // Read all matching batch files
        let entries = std::fs::read_dir(&dir)
            .map_err(|e| format!("Failed to read instance_data dir: {}", e))?;

        for entry in entries {
            let entry = entry.map_err(|e| format!("Failed to read dir entry: {}", e))?;
            let path = entry.path();

            if let Some(name) = path.file_name().and_then(|n| n.to_str())
                && name.starts_with(&prefix) && name.ends_with(".batch.bin") {
                    // Parse filename: {uuid}_v{version}_{edb|idb}.batch.bin
                    // or legacy format: {uuid}_v{version}.batch.bin
                    let suffix = name
                        .strip_prefix(&prefix)
                        .and_then(|s| s.strip_suffix(".batch.bin"))
                        .ok_or_else(|| format!("Invalid batch filename: {}", name))?;

                    // Check for new format with _edb or _idb suffix
                    let (version_str, is_idb) = if let Some(v) = suffix.strip_suffix("_edb") {
                        (v, false)
                    } else if let Some(v) = suffix.strip_suffix("_idb") {
                        (v, true)
                    } else {
                        // Legacy format without kind suffix - assume EDB
                        (suffix, false)
                    };

                    let version: u64 = version_str.parse()
                        .map_err(|_| format!("Invalid version in filename: {}", name))?;

                    let bytes = std::fs::read(&path)
                        .map_err(|e| format!("Failed to read batch {}: {}", name, e))?;

                    let archived = rkyv::check_archived_root::<columnar::InstanceDataBatch>(&bytes)
                        .map_err(|e| format!("Failed to validate batch {}: {}", name, e))?;

                    let batch: columnar::InstanceDataBatch = archived.deserialize(&mut rkyv::Infallible)
                        .map_err(|_| format!("Failed to deserialize batch {}", name))?;

                    version_batches.push((version, is_idb, batch));
                }
        }

        // Sort by version, then EDB before IDB at same version
        version_batches.sort_by_key(|(v, is_idb, _)| (*v, *is_idb));
        Ok(version_batches.into_iter().map(|(_, _, b)| b).collect())
    }

    /// Load only EDB (wire-transmittable) batches for an instance.
    ///
    /// This is what would be sent over the network during sync.
    pub fn load_edb_batches(
        &self,
        instance_uuid: crate::id::Uuid,
    ) -> Result<Vec<columnar::InstanceDataBatch>, String> {
        let all = self.load_instance_data_batches(instance_uuid)?;
        Ok(all.into_iter().filter(|b| b.is_wire_transmittable()).collect())
    }
}

impl Default for Store {
    fn default() -> Self {
        Self::new()
    }
}

// ============================================================================
// TESTS
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_create_store() {
        let store = Store::new();
        assert!(store.head.is_none());
        assert!(store.uncommitted.is_empty());
    }

    #[test]
    fn test_create_theory() {
        let mut store = Store::new();
        let _theory = store.create_theory("TestTheory").unwrap();
        assert!(store.uncommitted.contains_key("TestTheory"));
    }

    #[test]
    fn test_create_instance() {
        let mut store = Store::new();
        let theory = store.create_theory("TestTheory").unwrap();
        let _instance = store.create_instance("TestInstance", theory).unwrap();
        assert!(store.uncommitted.contains_key("TestInstance"));
    }

    #[test]
    fn test_commit() {
        let mut store = Store::new();
        let _theory = store.create_theory("TestTheory").unwrap();
        let commit = store.commit(Some("Initial commit")).unwrap();
        assert_eq!(store.head, Some(commit));
        assert!(store.uncommitted.is_empty());
    }

    #[test]
    fn test_materialize_empty_instance() {
        let mut store = Store::new();
        let theory = store.create_theory("TestTheory").unwrap();
        let instance = store.create_instance("TestInstance", theory).unwrap();

        let view = store.materialize(instance);
        assert_eq!(view.instance, instance);
        assert!(view.elements.is_empty());
        assert!(view.rel_tuples.is_empty());
        assert!(view.func_vals.is_empty());
    }

    #[test]
    fn test_materialize_with_elements() {
        let mut store = Store::new();
        let theory = store.create_theory("TestTheory").unwrap();
        let instance = store.create_instance("TestInstance", theory).unwrap();

        // We'd need a sort in the theory to add elements, so this test is limited
        let view = store.materialize(instance);
        assert_eq!(view.instance, instance);
    }

    #[test]
    fn test_incremental_view_update() {
        let mut store = Store::new();
        let theory = store.create_theory("TestTheory").unwrap();
        let v1 = store.create_instance("TestInstance", theory).unwrap();

        let mut view = store.materialize(v1);
        assert_eq!(view.instance, v1);

        // Extend the instance
        let v2 = store.extend_instance(v1, "TestInstance_v2").unwrap();

        // Update view incrementally
        let result = store.update_view(&mut view, v2);
        assert!(result.is_ok());
        assert_eq!(view.instance, v2);
    }

    #[test]
    fn test_incremental_update_invalid_parent() {
        let mut store = Store::new();
        let theory = store.create_theory("TestTheory").unwrap();
        let v1 = store.create_instance("Instance1", theory).unwrap();
        let v2 = store.create_instance("Instance2", theory).unwrap();

        let mut view = store.materialize(v1);

        // v2 is not a child of v1, so this should fail
        let result = store.update_view(&mut view, v2);
        assert!(result.is_err());
    }

    #[test]
    fn test_commit_history() {
        let mut store = Store::new();
        let _theory = store.create_theory("TestTheory").unwrap();
        let c1 = store.commit(Some("First")).unwrap();

        store.create_theory("Theory2").unwrap();
        let c2 = store.commit(Some("Second")).unwrap();

        let history = store.commit_history();
        assert_eq!(history, vec![c1, c2]);
    }
}
