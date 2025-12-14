//! Workspace persistence for Geolog
//!
//! A workspace is simply a directory containing serialized structures:
//! - *.theory: Serialized theories (as GeologMeta structures)
//! - *.instance: Serialized user instances
//!
//! The UUID universe and naming index are global (installation-wide), not per-workspace.

use crate::core::{ElaboratedTheory, SortId, Structure};
use crate::elaborate::Env;
use crate::id::{get_slid, some_slid, Luid};
use crate::meta::{structure_to_theory, theory_to_structure};
use crate::naming::NamingIndex;
use crate::universe::Universe;
use memmap2::Mmap;
use rkyv::ser::serializers::AllocSerializer;
use rkyv::ser::Serializer;
use rkyv::{check_archived_root, Archive, Deserialize, Serialize};
use std::collections::HashMap;
use std::fs::{self, File};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::rc::Rc;

// ============================================================================
// GLOBAL UNIVERSE PATH
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
// STRUCTURE SERIALIZATION
// ============================================================================

/// Serializable form of a Structure
///
/// Strips out RoaringTreemap carriers and luid_to_slid HashMap (rebuilt on load).
/// Functions use Option<usize> instead of OptSlid for rkyv compatibility.
/// Note: Human-readable names are stored separately in the global NamingIndex.
#[derive(Archive, Deserialize, Serialize)]
#[archive(check_bytes)]
pub struct StructureData {
    pub num_sorts: usize,
    pub luids: Vec<Luid>,
    pub sorts: Vec<SortId>,
    pub functions: Vec<Vec<Option<usize>>>,
}

impl StructureData {
    /// Create serializable data from a Structure
    pub fn from_structure(structure: &Structure) -> Self {
        let functions = structure
            .functions
            .iter()
            .map(|func_vec| func_vec.iter().map(|&opt| get_slid(opt)).collect())
            .collect();

        Self {
            num_sorts: structure.num_sorts(),
            luids: structure.luids.clone(),
            sorts: structure.sorts.clone(),
            functions,
        }
    }

    /// Rebuild a Structure from serialized data
    pub fn to_structure(&self) -> Structure {
        let mut structure = Structure::new(self.num_sorts);

        // Rebuild elements (also rebuilds carriers and luid_to_slid)
        for (slid, (&luid, &sort_id)) in self
            .luids
            .iter()
            .zip(self.sorts.iter())
            .enumerate()
        {
            let added_slid = structure.add_element_with_luid(luid, sort_id);
            debug_assert_eq!(added_slid, slid);
        }

        // Convert Option<usize> -> OptSlid
        structure.functions = self
            .functions
            .iter()
            .map(|func_vec| {
                func_vec
                    .iter()
                    .map(|&opt| opt.and_then(some_slid))
                    .collect()
            })
            .collect();

        structure
    }
}

/// Save a Structure to a file
pub fn save_structure(structure: &Structure, path: &Path) -> Result<(), String> {
    let data = StructureData::from_structure(structure);

    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent)
            .map_err(|e| format!("Failed to create directory: {}", e))?;
    }

    let mut serializer = AllocSerializer::<4096>::default();
    serializer
        .serialize_value(&data)
        .map_err(|e| format!("Failed to serialize structure: {}", e))?;
    let bytes = serializer.into_serializer().into_inner();

    // Write atomically
    let temp_path = path.with_extension("tmp");
    {
        let mut file = File::create(&temp_path)
            .map_err(|e| format!("Failed to create temp file: {}", e))?;
        file.write_all(&bytes)
            .map_err(|e| format!("Failed to write file: {}", e))?;
        file.sync_all()
            .map_err(|e| format!("Failed to sync file: {}", e))?;
    }

    fs::rename(&temp_path, path)
        .map_err(|e| format!("Failed to rename file: {}", e))?;

    Ok(())
}

/// Load a Structure from a file
pub fn load_structure(path: &Path) -> Result<Structure, String> {
    let file = File::open(path)
        .map_err(|e| format!("Failed to open file: {}", e))?;

    let mmap = unsafe { Mmap::map(&file) }
        .map_err(|e| format!("Failed to mmap file: {}", e))?;

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

// ============================================================================
// WORKSPACE (directory of structures)
// ============================================================================

/// A workspace: a directory containing .theory and .instance files
pub struct Workspace {
    path: PathBuf,
    pub env: Env,
    pub theories: HashMap<String, Rc<ElaboratedTheory>>,
    pub instances: HashMap<String, Structure>,
}

impl Workspace {
    /// Create a new empty workspace at the given path
    pub fn create(path: impl Into<PathBuf>) -> Result<Self, String> {
        let path = path.into();

        if path.exists() {
            return Err(format!("Path already exists: {}", path.display()));
        }

        fs::create_dir_all(&path)
            .map_err(|e| format!("Failed to create workspace directory: {}", e))?;

        Ok(Self {
            path,
            env: Env::new(),
            theories: HashMap::new(),
            instances: HashMap::new(),
        })
    }

    /// Open an existing workspace (or create if it doesn't exist)
    /// Requires Universe and NamingIndex to reconstruct theories from structures.
    pub fn open(
        path: impl Into<PathBuf>,
        universe: &Universe,
        naming: &NamingIndex,
    ) -> Result<Self, String> {
        let path = path.into();

        if !path.exists() {
            fs::create_dir_all(&path)
                .map_err(|e| format!("Failed to create workspace directory: {}", e))?;
        }

        let mut workspace = Self {
            path,
            env: Env::new(),
            theories: HashMap::new(),
            instances: HashMap::new(),
        };

        workspace.load_all(universe, naming)?;

        Ok(workspace)
    }

    /// Load all theories and instances from disk
    fn load_all(&mut self, universe: &Universe, naming: &NamingIndex) -> Result<(), String> {
        // Load theories (*.theory files)
        if let Ok(entries) = fs::read_dir(&self.path) {
            for entry in entries.flatten() {
                let path = entry.path();
                if path.extension().map(|e| e == "theory").unwrap_or(false) {
                    if let Some(name) = path.file_stem().and_then(|s| s.to_str()) {
                        match self.load_theory_file(&path, universe, naming) {
                            Ok(theory) => {
                                self.env.theories.insert(name.to_string(), Rc::new(theory.clone()));
                                self.theories.insert(name.to_string(), Rc::new(theory));
                            }
                            Err(e) => eprintln!("Warning: failed to load {}: {}", path.display(), e),
                        }
                    }
                }
            }
        }

        // Load instances (*.instance files)
        if let Ok(entries) = fs::read_dir(&self.path) {
            for entry in entries.flatten() {
                let path = entry.path();
                if path.extension().map(|e| e == "instance").unwrap_or(false) {
                    if let Some(name) = path.file_stem().and_then(|s| s.to_str()) {
                        match load_structure(&path) {
                            Ok(structure) => {
                                self.instances.insert(name.to_string(), structure);
                            }
                            Err(e) => eprintln!("Warning: failed to load {}: {}", path.display(), e),
                        }
                    }
                }
            }
        }

        Ok(())
    }

    /// Load a theory from a .theory file (GeologMeta structure)
    fn load_theory_file(
        &self,
        path: &Path,
        universe: &Universe,
        naming: &NamingIndex,
    ) -> Result<ElaboratedTheory, String> {
        let structure = load_structure(path)?;
        structure_to_theory(&structure, universe, naming)
    }

    /// Save all theories and instances to disk
    pub fn save(&self, universe: &mut Universe, naming: &mut NamingIndex) -> Result<(), String> {
        // Save theories as GeologMeta structures
        for (_name, theory) in &self.theories {
            let structure = theory_to_structure(theory, universe, naming);
            let path = self.path.join(format!("{}.theory", theory.theory.name));
            save_structure(&structure, &path)?;
        }

        // Save instances
        for (name, structure) in &self.instances {
            let path = self.path.join(format!("{}.instance", name));
            save_structure(structure, &path)?;
        }

        Ok(())
    }

    /// Add a theory to the workspace
    pub fn add_theory(&mut self, theory: ElaboratedTheory) {
        let name = theory.theory.name.clone();
        let rc_theory = Rc::new(theory);
        self.env.theories.insert(name.clone(), rc_theory.clone());
        self.theories.insert(name, rc_theory);
    }

    /// Add an instance to the workspace
    pub fn add_instance(&mut self, name: String, structure: Structure) {
        self.instances.insert(name, structure);
    }

    /// Get workspace path
    pub fn path(&self) -> &Path {
        &self.path
    }

    /// List theory names
    pub fn theory_names(&self) -> Vec<&String> {
        self.theories.keys().collect()
    }

    /// List instance names
    pub fn instance_names(&self) -> Vec<&String> {
        self.instances.keys().collect()
    }
}


// Unit tests moved to tests/unit_workspace.rs
