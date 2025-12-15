//! Global naming index for human-readable names
//!
//! Names are purely a UI concern - all data in structures is identified by UUID.
//! This index maps UUIDs to human-readable names for display and provides
//! reverse lookup for parsing.
//!
//! Following chit's design: "namings are purely a user interface (input/output
//! for humans and large language models)"
//!
//! ## Suffix-based lookup via ReversedPath
//!
//! To efficiently look up names by suffix (e.g., find all `*/A` when given just `A`),
//! we store paths reversed in a BTreeMap. For example:
//! - `["PetriNet", "P"]` is stored as `ReversedPath(["P", "PetriNet"])`
//! - A prefix scan for `["A"]` finds all paths ending in `A`
//!
//! This enables O(log n + k) suffix lookups where k is the number of matches.

use crate::id::Uuid;
use indexmap::IndexMap;
use memmap2::Mmap;
use rkyv::ser::Serializer;
use rkyv::ser::serializers::AllocSerializer;
use rkyv::{Archive, Deserialize, Serialize, check_archived_root};
use std::collections::BTreeMap;
use std::fs::{self, File};
use std::io::Write;
use std::path::PathBuf;

/// A qualified name path (e.g., ["PetriNet", "P"] for sort P in theory PetriNet)
pub type QualifiedName = Vec<String>;

/// A path stored with segments reversed for efficient suffix-based lookup.
///
/// `["PetriNet", "P"]` becomes `ReversedPath(["P", "PetriNet"])`.
/// This allows BTreeMap range queries to find all paths with a given suffix.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ReversedPath(Vec<String>);

impl ReversedPath {
    /// Create a reversed path from a qualified name.
    pub fn from_qualified(segments: &[String]) -> Self {
        Self(segments.iter().rev().cloned().collect())
    }

    /// Convert back to a qualified name (forward order).
    pub fn to_qualified(&self) -> QualifiedName {
        self.0.iter().rev().cloned().collect()
    }

    /// Create a prefix for range queries (just the suffix segments, reversed).
    /// For looking up all paths ending in `["A"]`, create `ReversedPath(["A"])`.
    pub fn from_suffix(suffix: &[String]) -> Self {
        // Suffix is already in forward order, just reverse it
        Self(suffix.iter().rev().cloned().collect())
    }

    /// Check if this path starts with the given prefix (for range iteration).
    pub fn starts_with(&self, prefix: &ReversedPath) -> bool {
        self.0.len() >= prefix.0.len() && self.0[..prefix.0.len()] == prefix.0[..]
    }

    /// Get the inner segments (reversed order).
    pub fn segments(&self) -> &[String] {
        &self.0
    }
}

/// Serializable form of the naming index
#[derive(Archive, Deserialize, Serialize, Default)]
#[archive(check_bytes)]
struct NamingData {
    /// UUID → qualified name mapping
    entries: Vec<(Uuid, QualifiedName)>,
}

/// Global naming index
///
/// Provides bidirectional mapping between UUIDs and human-readable names.
/// Names are qualified paths like ["PetriNet", "P"] for sort P in theory PetriNet.
///
/// ## Lookup modes
/// - **By UUID**: O(1) via `uuid_to_name`
/// - **By exact path**: O(log n) via `path_to_uuid`
/// - **By suffix**: O(log n + k) via BTreeMap range query on reversed paths
#[derive(Debug, Default)]
pub struct NamingIndex {
    /// UUID → qualified name (for display)
    uuid_to_name: IndexMap<Uuid, QualifiedName>,
    /// Reversed path → UUIDs (for suffix-based lookup)
    /// Paths are stored reversed so that suffix queries become prefix scans.
    /// Multiple UUIDs can share the same path (ambiguous names).
    path_to_uuid: BTreeMap<ReversedPath, Vec<Uuid>>,
    /// Persistence path
    path: Option<PathBuf>,
    /// Dirty flag
    dirty: bool,
}

impl NamingIndex {
    /// Create a new empty naming index
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a naming index with a persistence path
    pub fn with_path(path: impl Into<PathBuf>) -> Self {
        Self {
            uuid_to_name: IndexMap::new(),
            path_to_uuid: BTreeMap::new(),
            path: Some(path.into()),
            dirty: false,
        }
    }

    /// Load a naming index from disk
    pub fn load(path: impl Into<PathBuf>) -> Result<Self, String> {
        let path = path.into();

        if !path.exists() {
            return Ok(Self::with_path(path));
        }

        let file = File::open(&path).map_err(|e| format!("Failed to open naming index: {}", e))?;

        let mmap = unsafe { Mmap::map(&file) }
            .map_err(|e| format!("Failed to mmap naming index: {}", e))?;

        if mmap.is_empty() {
            return Ok(Self::with_path(path));
        }

        let archived = check_archived_root::<NamingData>(&mmap)
            .map_err(|e| format!("Failed to validate naming index: {}", e))?;

        let data: NamingData = archived
            .deserialize(&mut rkyv::Infallible)
            .map_err(|_| "Failed to deserialize naming index")?;

        let mut index = Self::with_path(path);
        for (uuid, name) in data.entries {
            index.insert_internal(uuid, name);
        }

        Ok(index)
    }

    /// Save the naming index to disk
    pub fn save(&mut self) -> Result<(), String> {
        let path = self
            .path
            .as_ref()
            .ok_or("Naming index has no persistence path")?;

        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent)
                .map_err(|e| format!("Failed to create naming directory: {}", e))?;
        }

        let data = NamingData {
            entries: self
                .uuid_to_name
                .iter()
                .map(|(k, v)| (*k, v.clone()))
                .collect(),
        };

        let mut serializer = AllocSerializer::<4096>::default();
        serializer
            .serialize_value(&data)
            .map_err(|e| format!("Failed to serialize naming index: {}", e))?;
        let bytes = serializer.into_serializer().into_inner();

        let temp_path = path.with_extension("tmp");
        {
            let mut file = File::create(&temp_path)
                .map_err(|e| format!("Failed to create temp file: {}", e))?;
            file.write_all(&bytes)
                .map_err(|e| format!("Failed to write naming index: {}", e))?;
            file.sync_all()
                .map_err(|e| format!("Failed to sync naming index: {}", e))?;
        }

        fs::rename(&temp_path, path)
            .map_err(|e| format!("Failed to rename naming index: {}", e))?;

        self.dirty = false;
        Ok(())
    }

    /// Internal insert without setting dirty flag
    fn insert_internal(&mut self, uuid: Uuid, name: QualifiedName) {
        // Add to reverse index (reversed path → UUIDs)
        let reversed = ReversedPath::from_qualified(&name);
        self.path_to_uuid
            .entry(reversed)
            .or_default()
            .push(uuid);
        self.uuid_to_name.insert(uuid, name);
    }

    /// Register a name for a UUID
    pub fn insert(&mut self, uuid: Uuid, name: QualifiedName) {
        self.insert_internal(uuid, name);
        self.dirty = true;
    }

    /// Register a simple (unqualified) name for a UUID
    pub fn insert_simple(&mut self, uuid: Uuid, name: String) {
        self.insert(uuid, vec![name]);
    }

    /// Get the qualified name for a UUID
    pub fn get(&self, uuid: &Uuid) -> Option<&QualifiedName> {
        self.uuid_to_name.get(uuid)
    }

    /// Get the simple (last component) name for a UUID
    pub fn get_simple(&self, uuid: &Uuid) -> Option<&str> {
        self.uuid_to_name
            .get(uuid)
            .and_then(|name| name.last())
            .map(|s| s.as_str())
    }

    /// Get the display name for a UUID (simple name, or UUID if unnamed)
    pub fn display_name(&self, uuid: &Uuid) -> String {
        self.get_simple(uuid)
            .map(|s| s.to_string())
            .unwrap_or_else(|| format!("{}", uuid))
    }

    /// Look up all UUIDs whose qualified name ends with the given suffix.
    ///
    /// Examples:
    /// - `lookup_suffix(&["A"])` returns UUIDs for "ExampleNet/A", "OtherNet/A", etc.
    /// - `lookup_suffix(&["ExampleNet", "A"])` returns just "ExampleNet/A"
    ///
    /// Returns an iterator over matching UUIDs.
    pub fn lookup_suffix<'a>(&'a self, suffix: &[String]) -> impl Iterator<Item = Uuid> + 'a {
        let prefix = ReversedPath::from_suffix(suffix);
        self.path_to_uuid
            .range(prefix.clone()..)
            .take_while(move |(k, _)| k.starts_with(&prefix))
            .flat_map(|(_, uuids)| uuids.iter().copied())
    }

    /// Look up UUID by exact qualified path.
    /// Returns None if ambiguous (multiple UUIDs share the exact path).
    pub fn lookup_exact(&self, path: &[String]) -> Option<Uuid> {
        let reversed = ReversedPath::from_qualified(path);
        match self.path_to_uuid.get(&reversed) {
            Some(uuids) if uuids.len() == 1 => Some(uuids[0]),
            _ => None,
        }
    }

    /// Resolve a path to a UUID.
    /// - If exact match exists, return it.
    /// - If suffix matches exactly one UUID, return it.
    /// - Otherwise return Err with all candidates (empty if not found, multiple if ambiguous).
    pub fn resolve(&self, path: &[String]) -> Result<Uuid, Vec<Uuid>> {
        // First try exact match
        if let Some(uuid) = self.lookup_exact(path) {
            return Ok(uuid);
        }

        // Fall back to suffix match
        let candidates: Vec<Uuid> = self.lookup_suffix(path).collect();
        match candidates.len() {
            1 => Ok(candidates[0]),
            _ => Err(candidates),
        }
    }

    /// Look up UUIDs by simple (single-segment) name.
    /// This is a convenience wrapper around `lookup_suffix` for single names.
    pub fn lookup(&self, name: &str) -> Vec<Uuid> {
        self.lookup_suffix(&[name.to_string()]).collect()
    }

    /// Look up a unique UUID by simple name (returns None if ambiguous or not found)
    pub fn lookup_unique(&self, name: &str) -> Option<Uuid> {
        let results: Vec<Uuid> = self.lookup_suffix(&[name.to_string()]).collect();
        if results.len() == 1 {
            Some(results[0])
        } else {
            None
        }
    }

    /// Check if dirty
    pub fn is_dirty(&self) -> bool {
        self.dirty
    }

    /// Number of entries
    pub fn len(&self) -> usize {
        self.uuid_to_name.len()
    }

    /// Check if empty
    pub fn is_empty(&self) -> bool {
        self.uuid_to_name.is_empty()
    }

    /// Iterate over all (UUID, name) pairs
    pub fn iter(&self) -> impl Iterator<Item = (&Uuid, &QualifiedName)> {
        self.uuid_to_name.iter()
    }
}

impl Drop for NamingIndex {
    fn drop(&mut self) {
        if self.dirty && self.path.is_some() {
            let _ = self.save();
        }
    }
}

/// Get the global naming index path
pub fn global_naming_path() -> Option<PathBuf> {
    #[cfg(unix)]
    {
        std::env::var("HOME").ok().map(|h| {
            let mut p = PathBuf::from(h);
            p.push(".config");
            p.push("geolog");
            p.push("names.bin");
            p
        })
    }
    #[cfg(windows)]
    {
        std::env::var("APPDATA").ok().map(|mut p| {
            p.push("geolog");
            p.push("names.bin");
            p
        })
    }
    #[cfg(not(any(unix, windows)))]
    {
        None
    }
}

/// Load or create the global naming index
pub fn global_naming_index() -> NamingIndex {
    match global_naming_path() {
        Some(path) => NamingIndex::load(&path).unwrap_or_else(|_| NamingIndex::with_path(path)),
        None => NamingIndex::new(),
    }
}

// Unit tests moved to tests/proptest_naming.rs
