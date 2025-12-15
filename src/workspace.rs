//! Unified Workspace: the single source of truth for all geolog state.
//!
//! A Workspace owns:
//! - `universe`: UUID <-> Luid mapping
//! - `naming`: UUID -> human-readable qualified names
//! - `meta`: Structure containing all theories (as GeologMeta instances)
//! - `instances`: user-defined instances
//!
//! After bootstrap, theories are data in `meta`, not separate `ElaboratedTheory` objects.
//! Cross-instance references resolve through `naming` - no special cases needed.

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::sync::Arc;

use crate::core::{ElaboratedTheory, SortId, Structure};
use crate::id::{Luid, NumericId, Slid, Uuid};
use crate::meta::geolog_meta;
use crate::naming::NamingIndex;
use crate::universe::Universe;

// ============================================================================
// INSTANCE ENTRY
// ============================================================================

/// An instance stored in the workspace
pub struct InstanceEntry {
    /// The structure itself
    pub structure: Structure,

    /// The theory this is an instance of (name, for now - later: Slid into meta)
    pub theory_name: String,

    /// Local element names: name -> Slid (for elaboration-time lookup)
    pub element_names: HashMap<String, Slid>,

    /// Reverse mapping: Slid -> name (for display)
    pub slid_to_name: HashMap<Slid, String>,
}

impl InstanceEntry {
    /// Create a new instance entry
    pub fn new(structure: Structure, theory_name: String) -> Self {
        Self {
            structure,
            theory_name,
            element_names: HashMap::new(),
            slid_to_name: HashMap::new(),
        }
    }

    /// Register an element with a name
    pub fn register_element(&mut self, name: String, slid: Slid) {
        self.element_names.insert(name.clone(), slid);
        self.slid_to_name.insert(slid, name);
    }

    /// Look up element by local name
    pub fn get_element(&self, name: &str) -> Option<Slid> {
        self.element_names.get(name).copied()
    }

    /// Get name for Slid
    pub fn get_name(&self, slid: Slid) -> Option<&str> {
        self.slid_to_name.get(&slid).map(|s| s.as_str())
    }
}

// ============================================================================
// WORKSPACE
// ============================================================================

/// The unified workspace: single source of truth for all geolog state.
///
/// This replaces the scattered state across Env, ReplState, and old Workspace.
pub struct Workspace {
    /// The global UUID universe
    pub universe: Universe,

    /// Human-readable names for all UUIDs
    pub naming: NamingIndex,

    /// The primordial GeologMeta instance (contains all theory definitions)
    /// Initially empty; populated via bootstrap or loading.
    pub meta: Structure,

    /// The GeologMeta theory (cached for signature lookups during elaboration)
    /// This is the ONE place we keep an ElaboratedTheory at runtime.
    pub meta_theory: Arc<ElaboratedTheory>,

    /// Named user instances
    pub instances: HashMap<String, InstanceEntry>,

    /// Theories cache: name -> ElaboratedTheory
    /// TRANSITIONAL: This will be removed once elaborate_theory writes to meta directly.
    /// For now, we keep this to maintain compatibility with existing code.
    pub theories: HashMap<String, Rc<ElaboratedTheory>>,

    /// Optional workspace directory path (for persistence)
    pub path: Option<PathBuf>,
}

impl Default for Workspace {
    fn default() -> Self {
        Self::new()
    }
}

impl Workspace {
    /// Create a new empty workspace
    pub fn new() -> Self {
        let meta_theory = geolog_meta();
        let num_sorts = meta_theory.theory.signature.sorts.len();

        Self {
            universe: Universe::new(),
            naming: NamingIndex::new(),
            meta: Structure::new(num_sorts),
            meta_theory,
            instances: HashMap::new(),
            theories: HashMap::new(),
            path: None,
        }
    }

    /// Create a workspace with persistence path
    pub fn with_path(path: impl Into<PathBuf>) -> Self {
        let mut ws = Self::new();
        ws.path = Some(path.into());
        ws
    }

    /// Load workspace from disk (universe and naming from global paths)
    pub fn load() -> Self {
        let universe = global_universe();
        let naming = crate::naming::global_naming_index();
        let meta_theory = geolog_meta();
        let num_sorts = meta_theory.theory.signature.sorts.len();

        Self {
            universe,
            naming,
            meta: Structure::new(num_sorts),
            meta_theory,
            instances: HashMap::new(),
            theories: HashMap::new(),
            path: None,
        }
    }

    // ========================================================================
    // NAME RESOLUTION
    // ========================================================================

    /// Resolve a qualified path to an element Slid.
    ///
    /// Resolution order:
    /// 1. Check `local_names` (current instance being elaborated)
    /// 2. Check `naming` index for global qualified names
    /// 3. Search instances for the UUID
    ///
    /// This is the core of cross-instance reference resolution.
    pub fn resolve_element(
        &self,
        path: &[String],
        local_names: &HashMap<String, Slid>,
    ) -> Result<ResolvedElement, ResolveError> {
        // 1. Single-segment? Try local first
        if path.len() == 1 {
            if let Some(&slid) = local_names.get(&path[0]) {
                return Ok(ResolvedElement::Local(slid));
            }
        }

        // 2. Try global naming resolution
        match self.naming.resolve(path) {
            Ok(uuid) => {
                // Found unique UUID, now find which instance contains it
                let luid = self
                    .universe
                    .lookup(&uuid)
                    .ok_or(ResolveError::UuidNotInUniverse(uuid))?;

                // Search instances for this Luid
                for (instance_name, entry) in &self.instances {
                    if let Some(slid) = entry.structure.luid_to_slid.get(&luid) {
                        return Ok(ResolvedElement::External {
                            instance_name: instance_name.clone(),
                            slid: *slid,
                            luid,
                        });
                    }
                }

                // Check meta structure too
                if let Some(slid) = self.meta.luid_to_slid.get(&luid) {
                    return Ok(ResolvedElement::Meta { slid: *slid, luid });
                }

                Err(ResolveError::UuidNotInAnyInstance(uuid))
            }
            Err(candidates) if candidates.is_empty() => {
                Err(ResolveError::NotFound(path.join("/")))
            }
            Err(candidates) => Err(ResolveError::Ambiguous(path.join("/"), candidates.len())),
        }
    }

    /// Resolve a path that should be in a specific instance.
    ///
    /// For parameterized instances: resolve `N/A` where N is bound to `ExampleNet`.
    pub fn resolve_in_instance(
        &self,
        instance_name: &str,
        element_name: &str,
    ) -> Result<Slid, ResolveError> {
        let entry = self
            .instances
            .get(instance_name)
            .ok_or_else(|| ResolveError::NotFound(instance_name.to_string()))?;

        entry
            .get_element(element_name)
            .ok_or_else(|| ResolveError::NotFound(format!("{}/{}", instance_name, element_name)))
    }

    // ========================================================================
    // INSTANCE MANAGEMENT
    // ========================================================================

    /// Add a new instance to the workspace
    pub fn add_instance(&mut self, name: String, entry: InstanceEntry) {
        self.instances.insert(name, entry);
    }

    /// Get an instance by name
    pub fn get_instance(&self, name: &str) -> Option<&InstanceEntry> {
        self.instances.get(name)
    }

    /// Get mutable instance by name
    pub fn get_instance_mut(&mut self, name: &str) -> Option<&mut InstanceEntry> {
        self.instances.get_mut(name)
    }

    /// Get a structure by instance name
    pub fn get_structure(&self, name: &str) -> Option<&Structure> {
        self.instances.get(name).map(|e| &e.structure)
    }

    /// List instance names
    pub fn instance_names(&self) -> impl Iterator<Item = &String> {
        self.instances.keys()
    }

    // ========================================================================
    // THEORY MANAGEMENT (TRANSITIONAL)
    // ========================================================================

    /// Add a theory (TRANSITIONAL: will write to meta instead)
    pub fn add_theory(&mut self, theory: ElaboratedTheory) {
        let name = theory.theory.name.clone();
        self.theories.insert(name, Rc::new(theory));
    }

    /// Get a theory by name (TRANSITIONAL)
    pub fn get_theory(&self, name: &str) -> Option<&Rc<ElaboratedTheory>> {
        self.theories.get(name)
    }

    /// List theory names
    pub fn theory_names(&self) -> impl Iterator<Item = &String> {
        self.theories.keys()
    }

    // ========================================================================
    // ELEMENT REGISTRATION
    // ========================================================================

    /// Register an element's name in the global naming index.
    ///
    /// Called when creating elements during instance elaboration.
    /// The qualified path is [instance_name, element_name].
    pub fn register_element_name(
        &mut self,
        instance_name: &str,
        element_name: &str,
        luid: Luid,
    ) -> Result<(), String> {
        let uuid = self
            .universe
            .get(luid)
            .ok_or_else(|| format!("Luid {} not in universe", luid))?;

        self.naming
            .insert(uuid, vec![instance_name.to_string(), element_name.to_string()]);
        Ok(())
    }

    // ========================================================================
    // PERSISTENCE
    // ========================================================================

    /// Save workspace state (universe and naming to global paths)
    pub fn save(&mut self) -> Result<(), String> {
        self.universe.save()?;
        self.naming.save()?;
        Ok(())
    }
}

// ============================================================================
// RESOLUTION TYPES
// ============================================================================

/// Result of resolving an element path
#[derive(Debug, Clone)]
pub enum ResolvedElement {
    /// Element is local to the instance being elaborated
    Local(Slid),

    /// Element is in another instance
    External {
        instance_name: String,
        slid: Slid,
        luid: Luid,
    },

    /// Element is in the meta structure (a theory component)
    Meta { slid: Slid, luid: Luid },
}

/// Errors during name resolution
#[derive(Debug, Clone)]
pub enum ResolveError {
    /// Name not found anywhere
    NotFound(String),

    /// Name is ambiguous (multiple matches)
    Ambiguous(String, usize),

    /// UUID found but not in universe
    UuidNotInUniverse(Uuid),

    /// UUID found in naming but not in any instance
    UuidNotInAnyInstance(Uuid),
}

impl std::fmt::Display for ResolveError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ResolveError::NotFound(name) => write!(f, "not found: {}", name),
            ResolveError::Ambiguous(name, count) => {
                write!(f, "ambiguous: {} matches {} entries", name, count)
            }
            ResolveError::UuidNotInUniverse(uuid) => {
                write!(f, "UUID {} not in universe", uuid)
            }
            ResolveError::UuidNotInAnyInstance(uuid) => {
                write!(f, "UUID {} not in any instance", uuid)
            }
        }
    }
}

// ============================================================================
// GLOBAL PATHS
// ============================================================================

/// Get the global universe path (~/.config/geolog/universe.bin)
pub fn global_universe_path() -> Option<PathBuf> {
    #[cfg(unix)]
    {
        std::env::var("HOME").ok().map(|h| {
            let mut p = PathBuf::from(h);
            p.push(".config");
            p.push("geolog");
            p.push("universe.bin");
            p
        })
    }
    #[cfg(windows)]
    {
        std::env::var("APPDATA").ok().map(|mut p| {
            p.push("geolog");
            p.push("universe.bin");
            p
        })
    }
    #[cfg(not(any(unix, windows)))]
    {
        None
    }
}

/// Load or create the global universe
pub fn global_universe() -> Universe {
    match global_universe_path() {
        Some(path) => Universe::load(&path).unwrap_or_else(|_| Universe::with_path(path)),
        None => Universe::new(),
    }
}

// ============================================================================
// STRUCTURE SERIALIZATION (kept for compatibility)
// ============================================================================

// TODO: Move serialization to a separate module or keep minimal here
// For now, keeping the essentials for save/load

use crate::core::{RelationStorage, TupleId, VecRelation};
use crate::id::{get_slid, some_slid};
use memmap2::Mmap;
use rkyv::ser::Serializer;
use rkyv::ser::serializers::AllocSerializer;
use rkyv::{Archive, Deserialize, Serialize, check_archived_root};
use std::fs::{self, File};
use std::io::Write;

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
        use crate::core::FunctionColumn;
        use crate::id::get_luid;

        let functions = structure
            .functions
            .iter()
            .map(|func_col| match func_col {
                FunctionColumn::Local(col) => FunctionColumnData::Local(
                    col.iter().map(|&opt| get_slid(opt).map(|s| s.index())).collect(),
                ),
                FunctionColumn::External(col) => FunctionColumnData::External(
                    col.iter().map(|&opt| get_luid(opt).map(|l| l.index())).collect(),
                ),
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
        use crate::core::FunctionColumn;

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
                        .map(|&opt| opt.map(Luid::from_usize).and_then(crate::id::some_luid))
                        .collect(),
                ),
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

/// Load a Structure from a file
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
