//! Global naming index for human-readable names
//!
//! Names are purely a UI concern - all data in structures is identified by UUID.
//! This index maps UUIDs to human-readable names for display and provides
//! reverse lookup for parsing.
//!
//! Following chit's design: "namings are purely a user interface (input/output
//! for humans and large language models)"

use crate::id::Uuid;
use indexmap::IndexMap;
use memmap2::Mmap;
use rkyv::ser::serializers::AllocSerializer;
use rkyv::ser::Serializer;
use rkyv::{check_archived_root, Archive, Deserialize, Serialize};
use std::collections::HashMap;
use std::fs::{self, File};
use std::io::Write;
use std::path::PathBuf;

/// A qualified name path (e.g., ["PetriNet", "P"] for sort P in theory PetriNet)
pub type QualifiedName = Vec<String>;

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
#[derive(Debug, Default)]
pub struct NamingIndex {
    /// UUID → qualified name (for display)
    uuid_to_name: IndexMap<Uuid, QualifiedName>,
    /// Simple name → UUIDs (for lookup; multiple UUIDs may share a simple name)
    name_to_uuids: HashMap<String, Vec<Uuid>>,
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
            name_to_uuids: HashMap::new(),
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

        let file = File::open(&path)
            .map_err(|e| format!("Failed to open naming index: {}", e))?;

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
        let path = self.path.as_ref()
            .ok_or("Naming index has no persistence path")?;

        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent)
                .map_err(|e| format!("Failed to create naming directory: {}", e))?;
        }

        let data = NamingData {
            entries: self.uuid_to_name
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
        // Add to reverse index (simple name → UUIDs)
        if let Some(simple) = name.last() {
            self.name_to_uuids
                .entry(simple.clone())
                .or_default()
                .push(uuid);
        }
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
        self.uuid_to_name.get(uuid)
            .and_then(|name| name.last())
            .map(|s| s.as_str())
    }

    /// Get the display name for a UUID (simple name, or UUID if unnamed)
    pub fn display_name(&self, uuid: &Uuid) -> String {
        self.get_simple(uuid)
            .map(|s| s.to_string())
            .unwrap_or_else(|| format!("{}", uuid))
    }

    /// Look up UUIDs by simple name
    pub fn lookup(&self, name: &str) -> Option<&[Uuid]> {
        self.name_to_uuids.get(name).map(|v| v.as_slice())
    }

    /// Look up a unique UUID by simple name (returns None if ambiguous or not found)
    pub fn lookup_unique(&self, name: &str) -> Option<Uuid> {
        self.name_to_uuids.get(name).and_then(|uuids| {
            if uuids.len() == 1 {
                Some(uuids[0])
            } else {
                None
            }
        })
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

#[cfg(test)]
mod tests {
    use super::*;
    use std::env;

    fn temp_path() -> PathBuf {
        let mut path = env::temp_dir();
        path.push(format!("geolog_naming_test_{}", Uuid::now_v7()));
        path.push("names.bin");
        path
    }

    #[test]
    fn test_insert_and_lookup() {
        let mut index = NamingIndex::new();

        let uuid1 = Uuid::now_v7();
        let uuid2 = Uuid::now_v7();

        index.insert(uuid1, vec!["PetriNet".to_string(), "P".to_string()]);
        index.insert(uuid2, vec!["PetriNet".to_string(), "T".to_string()]);

        assert_eq!(index.get_simple(&uuid1), Some("P"));
        assert_eq!(index.get_simple(&uuid2), Some("T"));
        assert_eq!(index.lookup_unique("P"), Some(uuid1));
        assert_eq!(index.lookup_unique("T"), Some(uuid2));
    }

    #[test]
    fn test_ambiguous_lookup() {
        let mut index = NamingIndex::new();

        let uuid1 = Uuid::now_v7();
        let uuid2 = Uuid::now_v7();

        // Both named "P" in different contexts
        index.insert(uuid1, vec!["Theory1".to_string(), "P".to_string()]);
        index.insert(uuid2, vec!["Theory2".to_string(), "P".to_string()]);

        // Ambiguous - returns None
        assert_eq!(index.lookup_unique("P"), None);

        // But lookup returns both
        let ps = index.lookup("P").unwrap();
        assert_eq!(ps.len(), 2);
    }

    #[test]
    fn test_save_and_load() {
        let path = temp_path();

        let uuid1 = Uuid::now_v7();
        let uuid2 = Uuid::now_v7();

        {
            let mut index = NamingIndex::with_path(&path);
            index.insert(uuid1, vec!["Foo".to_string()]);
            index.insert(uuid2, vec!["Bar".to_string()]);
            index.save().expect("save should succeed");
        }

        {
            let index = NamingIndex::load(&path).expect("load should succeed");
            assert_eq!(index.len(), 2);
            assert_eq!(index.get_simple(&uuid1), Some("Foo"));
            assert_eq!(index.get_simple(&uuid2), Some("Bar"));
        }

        // Clean up
        if let Some(parent) = path.parent() {
            let _ = fs::remove_dir_all(parent);
        }
    }
}
