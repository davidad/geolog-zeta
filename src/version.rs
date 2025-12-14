//! Version control for geolog structures
//!
//! This module provides a simple linear version control system for structures.
//! Patches are serialized to disk and can be loaded to reconstruct any version.

use crate::core::Structure;
use crate::id::Uuid;
use crate::patch::{apply_patch, diff, to_initial_patch, Patch};
use crate::universe::Universe;

use rkyv::ser::serializers::AllocSerializer;
use rkyv::ser::Serializer;
use rkyv::{check_archived_root, Deserialize};
use std::collections::BTreeMap;
use std::fs::{self, File};
use std::io::{Read, Write};
use std::path::{Path, PathBuf};

/// A version-controlled state for managing structure history.
///
/// This provides a simple linear history (no branches/merges yet).
/// Patches are stored on disk and loaded on demand.
///
/// Contains a Universe for mapping UUIDs to Luids. The Universe is
/// persisted alongside the patches.
#[derive(Debug)]
pub struct VersionedState {
    /// All patches, indexed by target_commit UUID
    pub patches: BTreeMap<Uuid, Patch>,
    /// Map from target_commit to source_commit (for walking history)
    pub commit_parents: BTreeMap<Uuid, Option<Uuid>>,
    /// Current HEAD commit (None = empty)
    pub head: Option<Uuid>,
    /// Directory where patches are stored
    pub patches_dir: PathBuf,
    /// The universe for UUID↔Luid mapping
    pub universe: Universe,
}

impl VersionedState {
    /// Create a new versioned state with the given patches directory
    pub fn new(patches_dir: impl Into<PathBuf>) -> Self {
        let patches_dir = patches_dir.into();
        let universe_path = patches_dir.join("universe.bin");
        Self {
            patches: BTreeMap::new(),
            commit_parents: BTreeMap::new(),
            head: None,
            patches_dir,
            universe: Universe::with_path(universe_path),
        }
    }

    /// Load all patches from the patches directory
    pub fn load_patches(&mut self) -> Result<(), String> {
        fs::create_dir_all(&self.patches_dir)
            .map_err(|e| format!("Failed to create patches directory: {}", e))?;

        // Load the universe
        let universe_path = self.patches_dir.join("universe.bin");
        self.universe = Universe::load(&universe_path)?;

        let entries = fs::read_dir(&self.patches_dir)
            .map_err(|e| format!("Failed to read patches directory: {}", e))?;

        for entry in entries {
            let entry = entry.map_err(|e| format!("Failed to read directory entry: {}", e))?;
            let path = entry.path();

            if path.extension().map_or(false, |ext| ext == "patch") {
                self.load_patch(&path)?;
            }
        }

        // Find the head (the commit that is not a source of any other commit)
        self.find_head();

        Ok(())
    }

    /// Load a single patch file
    fn load_patch(&mut self, path: &Path) -> Result<(), String> {
        let mut file =
            File::open(path).map_err(|e| format!("Failed to open patch file: {}", e))?;

        let mut bytes = Vec::new();
        file.read_to_end(&mut bytes)
            .map_err(|e| format!("Failed to read patch file: {}", e))?;

        // Use check_archived_root for validation
        let archived = check_archived_root::<Patch>(&bytes)
            .map_err(|e| format!("Failed to validate patch archive: {}", e))?;

        // Deserialize to owned Patch
        let patch: Patch = archived
            .deserialize(&mut rkyv::Infallible)
            .map_err(|_| "Failed to deserialize patch")?;

        let target = patch.target_commit;
        let source = patch.source_commit;

        self.commit_parents.insert(target, source);
        self.patches.insert(target, patch);

        Ok(())
    }

    /// Find the head commit (most recent commit not superseded by another)
    fn find_head(&mut self) {
        // Collect all source commits (commits that have children)
        let sources: std::collections::HashSet<Uuid> = self
            .commit_parents
            .values()
            .filter_map(|s| *s)
            .collect();

        // Head is a commit that is not a source of any other commit
        for &commit in self.commit_parents.keys() {
            if !sources.contains(&commit) {
                self.head = Some(commit);
                return;
            }
        }
    }

    /// Save a patch to disk (also saves the universe if dirty)
    pub fn save_patch(&mut self, patch: &Patch) -> Result<(), String> {
        fs::create_dir_all(&self.patches_dir)
            .map_err(|e| format!("Failed to create patches directory: {}", e))?;

        let filename = format!("{}.patch", patch.target_commit);
        let path = self.patches_dir.join(filename);

        // Serialize with rkyv
        let mut serializer = AllocSerializer::<256>::default();
        serializer
            .serialize_value(patch)
            .map_err(|e| format!("Failed to serialize patch: {}", e))?;
        let bytes = serializer.into_serializer().into_inner();

        let mut file =
            File::create(&path).map_err(|e| format!("Failed to create patch file: {}", e))?;

        file.write_all(&bytes)
            .map_err(|e| format!("Failed to write patch file: {}", e))?;

        // Save the universe if dirty
        if self.universe.is_dirty() {
            self.universe.save()?;
        }

        Ok(())
    }

    /// Checkout a specific commit, returning the reconstructed structure
    pub fn checkout(&mut self, commit: Uuid) -> Result<Structure, String> {
        // Build the chain of patches from root to target
        let mut chain = Vec::new();
        let mut current = Some(commit);

        while let Some(c) = current {
            let patch = self
                .patches
                .get(&c)
                .ok_or_else(|| format!("Commit {} not found", c))?;
            chain.push(patch.clone());
            current = patch.source_commit;
        }

        // Reverse to apply from root to target
        chain.reverse();

        // Apply patches in order
        let mut structure = if let Some(first_patch) = chain.first() {
            Structure::new(first_patch.theory_name.clone(), first_patch.num_sorts)
        } else {
            return Err("No patches to apply".to_string());
        };

        for patch in &chain {
            structure = apply_patch(&structure, patch, &mut self.universe)?;
        }

        Ok(structure)
    }

    /// Commit a structure, creating a new patch from the current HEAD
    ///
    /// Returns the new commit's UUID
    pub fn commit(&mut self, structure: &Structure) -> Result<Uuid, String> {
        let patch = if let Some(head) = self.head {
            // Diff from current HEAD
            let base = self.checkout(head)?;
            let mut patch = diff(&base, structure, &self.universe);
            patch.source_commit = Some(head);
            patch
        } else {
            // Initial commit
            to_initial_patch(structure, &self.universe)
        };

        // Skip empty patches
        if patch.is_empty() {
            return Err("No changes to commit".to_string());
        }

        let commit_uuid = patch.target_commit;

        // Save to disk
        self.save_patch(&patch)?;

        // Update in-memory state
        self.commit_parents
            .insert(commit_uuid, patch.source_commit);
        self.patches.insert(commit_uuid, patch);
        self.head = Some(commit_uuid);

        Ok(commit_uuid)
    }

    /// Get the current HEAD structure, or None if no commits
    pub fn get_head_structure(&mut self) -> Result<Option<Structure>, String> {
        match self.head {
            Some(head) => Ok(Some(self.checkout(head)?)),
            None => Ok(None),
        }
    }

    /// List all commits in order from oldest to newest
    pub fn list_commits(&self) -> Vec<Uuid> {
        // Build list by following parents
        let mut commits = Vec::new();
        let mut current = self.head;

        while let Some(c) = current {
            commits.push(c);
            current = self.commit_parents.get(&c).and_then(|p| *p);
        }

        commits.reverse();
        commits
    }

    /// Get the number of commits
    pub fn num_commits(&self) -> usize {
        self.patches.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::env;

    fn temp_dir() -> PathBuf {
        let mut path = env::temp_dir();
        path.push(format!("geolog_test_{}", Uuid::now_v7()));
        path
    }

    #[test]
    fn test_new_versioned_state() {
        let dir = temp_dir();
        let state = VersionedState::new(&dir);
        assert!(state.head.is_none());
        assert_eq!(state.num_commits(), 0);
    }

    #[test]
    fn test_commit_and_checkout() {
        let dir = temp_dir();
        let mut state = VersionedState::new(&dir);

        // Create a structure using the state's universe
        let mut s1 = Structure::new("Test".to_string(), 2);
        s1.add_element(&mut state.universe, "foo".to_string(), 0);
        s1.add_element(&mut state.universe, "bar".to_string(), 1);

        // Commit it
        let commit1 = state.commit(&s1).expect("commit should succeed");
        assert_eq!(state.num_commits(), 1);
        assert_eq!(state.head, Some(commit1));

        // Checkout and verify
        let s1_checkout = state.checkout(commit1).expect("checkout should succeed");
        assert_eq!(s1_checkout.len(), 2);

        // Clean up
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_multiple_commits() {
        let dir = temp_dir();
        let mut state = VersionedState::new(&dir);

        // First commit
        let mut s1 = Structure::new("Test".to_string(), 2);
        let foo_slid = s1.add_element(&mut state.universe, "foo".to_string(), 0);
        let foo_luid = s1.get_luid(foo_slid);
        let commit1 = state.commit(&s1).expect("commit 1");

        // Second commit with more elements (preserving "foo" via its Luid)
        let mut s2 = Structure::new("Test".to_string(), 2);
        s2.add_element_with_luid(foo_luid, "foo".to_string(), 0);
        s2.add_element(&mut state.universe, "bar".to_string(), 1);
        s2.add_element(&mut state.universe, "baz".to_string(), 0);
        let commit2 = state.commit(&s2).expect("commit 2");

        assert_eq!(state.num_commits(), 2);

        // Checkout first commit
        let s1_checkout = state.checkout(commit1).expect("checkout commit1");
        assert_eq!(s1_checkout.len(), 1);

        // Checkout second commit
        let s2_checkout = state.checkout(commit2).expect("checkout commit2");
        assert_eq!(s2_checkout.len(), 3);

        // List commits
        let commits = state.list_commits();
        assert_eq!(commits.len(), 2);
        assert_eq!(commits[0], commit1);
        assert_eq!(commits[1], commit2);

        // Clean up
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_save_and_load_patches() {
        let dir = temp_dir();

        // Create state and commit
        let commit_uuid;
        {
            let mut state = VersionedState::new(&dir);
            let mut s = Structure::new("Test".to_string(), 2);
            s.add_element(&mut state.universe, "foo".to_string(), 0);
            commit_uuid = state.commit(&s).expect("commit");
        }

        // Create new state and load
        {
            let mut state = VersionedState::new(&dir);
            state.load_patches().expect("load patches");

            assert_eq!(state.num_commits(), 1);
            assert_eq!(state.head, Some(commit_uuid));

            let s = state.checkout(commit_uuid).expect("checkout");
            assert_eq!(s.len(), 1);
        }

        // Clean up
        let _ = fs::remove_dir_all(&dir);
    }
}
