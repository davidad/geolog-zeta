//! Global UUID universe with Luid (Locally Universal ID) mapping
//!
//! This provides a single, persistent index of all UUIDs known to this
//! installation. UUIDs are mapped to compact integer Luids for efficient
//! in-memory operations.
//!
//! Following chit's multi-level ID design:
//! - Uuid: 128-bit globally unique identifier (for persistence, cross-system)
//! - Luid: Local index into this installation's universe (for computation)

use crate::id::{Luid, NumericId, Uuid};
use indexmap::IndexSet;
use memmap2::Mmap;
use rkyv::ser::Serializer;
use rkyv::ser::serializers::AllocSerializer;
use rkyv::{Archive, Deserialize, Serialize, check_archived_root};
use std::fs::{self, File};
use std::io::Write;
use std::path::{Path, PathBuf};

/// The global universe of all UUIDs known to this installation.
///
/// Provides bidirectional mapping between UUIDs and Luids:
/// - `intern(uuid)` → Luid (get or create)
/// - `get(luid)` → Uuid
/// - `lookup(uuid)` → Option<Luid>
///
/// The universe is persisted to disk and can be memory-mapped for
/// efficient access without loading everything into memory.
#[derive(Debug)]
pub struct Universe {
    /// The index mapping Luid → Uuid (and via IndexSet, Uuid → Luid)
    index: IndexSet<Uuid>,
    /// Path to the universe file (if persistent)
    path: Option<PathBuf>,
    /// Whether there are unsaved changes
    dirty: bool,
}

/// Serializable form of the universe for persistence
#[derive(Archive, Deserialize, Serialize)]
#[archive(check_bytes)]
struct UniverseData {
    uuids: Vec<Uuid>,
}

impl Universe {
    /// Create a new empty universe (in-memory only)
    pub fn new() -> Self {
        Self {
            index: IndexSet::new(),
            path: None,
            dirty: false,
        }
    }

    /// Create a new universe with a persistence path
    pub fn with_path(path: impl Into<PathBuf>) -> Self {
        Self {
            index: IndexSet::new(),
            path: Some(path.into()),
            dirty: false,
        }
    }

    /// Load a universe from disk, or create empty if file doesn't exist
    pub fn load(path: impl Into<PathBuf>) -> Result<Self, String> {
        let path = path.into();

        if !path.exists() {
            return Ok(Self::with_path(path));
        }

        let file = File::open(&path).map_err(|e| format!("Failed to open universe file: {}", e))?;

        // Memory-map the file for zero-copy access
        let mmap = unsafe { Mmap::map(&file) }
            .map_err(|e| format!("Failed to mmap universe file: {}", e))?;

        if mmap.is_empty() {
            return Ok(Self::with_path(path));
        }

        // Validate and access the archived data
        let archived = check_archived_root::<UniverseData>(&mmap)
            .map_err(|e| format!("Failed to validate universe archive: {}", e))?;

        // Deserialize to build the IndexSet
        let data: UniverseData = archived
            .deserialize(&mut rkyv::Infallible)
            .map_err(|_| "Failed to deserialize universe")?;

        let index: IndexSet<Uuid> = data.uuids.into_iter().collect();

        Ok(Self {
            index,
            path: Some(path),
            dirty: false,
        })
    }

    /// Save the universe to disk
    pub fn save(&mut self) -> Result<(), String> {
        let path = self
            .path
            .as_ref()
            .ok_or("Universe has no persistence path")?;

        // Create parent directories if needed
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent)
                .map_err(|e| format!("Failed to create universe directory: {}", e))?;
        }

        // Serialize the universe
        let data = UniverseData {
            uuids: self.index.iter().copied().collect(),
        };

        let mut serializer = AllocSerializer::<1024>::default();
        serializer
            .serialize_value(&data)
            .map_err(|e| format!("Failed to serialize universe: {}", e))?;
        let bytes = serializer.into_serializer().into_inner();

        // Write atomically by writing to temp file then renaming
        let temp_path = path.with_extension("universe.tmp");
        {
            let mut file = File::create(&temp_path)
                .map_err(|e| format!("Failed to create temp universe file: {}", e))?;
            file.write_all(&bytes)
                .map_err(|e| format!("Failed to write universe file: {}", e))?;
            file.sync_all()
                .map_err(|e| format!("Failed to sync universe file: {}", e))?;
        }

        fs::rename(&temp_path, path)
            .map_err(|e| format!("Failed to rename universe file: {}", e))?;

        self.dirty = false;
        Ok(())
    }

    /// Intern a UUID, returning its Luid (creating if new)
    pub fn intern(&mut self, uuid: Uuid) -> Luid {
        let (idx, inserted) = self.index.insert_full(uuid);
        if inserted {
            self.dirty = true;
        }
        Luid::from_usize(idx)
    }

    /// Get the UUID for a Luid
    pub fn get(&self, luid: Luid) -> Option<Uuid> {
        self.index.get_index(luid.index()).copied()
    }

    /// Look up the Luid for a UUID (if known)
    pub fn lookup(&self, uuid: &Uuid) -> Option<Luid> {
        self.index.get_index_of(uuid).map(Luid::from_usize)
    }

    /// Get the number of UUIDs in the universe
    pub fn len(&self) -> usize {
        self.index.len()
    }

    /// Check if the universe is empty
    pub fn is_empty(&self) -> bool {
        self.index.is_empty()
    }

    /// Check if there are unsaved changes
    pub fn is_dirty(&self) -> bool {
        self.dirty
    }

    /// Iterate over all (Luid, Uuid) pairs
    pub fn iter(&self) -> impl Iterator<Item = (Luid, Uuid)> + '_ {
        self.index
            .iter()
            .enumerate()
            .map(|(idx, &uuid)| (Luid::from_usize(idx), uuid))
    }

    /// Get the persistence path (if any)
    pub fn path(&self) -> Option<&Path> {
        self.path.as_deref()
    }
}

impl Default for Universe {
    fn default() -> Self {
        Self::new()
    }
}

impl Drop for Universe {
    fn drop(&mut self) {
        // Auto-save on drop if dirty and has a path
        if self.dirty && self.path.is_some() {
            let _ = self.save(); // Ignore errors on drop
        }
    }
}

// Unit tests moved to tests/proptest_universe.rs
