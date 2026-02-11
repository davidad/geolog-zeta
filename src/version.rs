//! Version control for geolog structures
//!
//! This module provides a simple linear version control system for structures.
//! Patches are serialized to disk and can be loaded to reconstruct any version.

use crate::core::Structure;
use crate::id::Uuid;
use crate::naming::NamingIndex;
use crate::core::{Sequent, Signature};
use crate::patch::{apply_patch_checked, ApplyPatchError, Patch, apply_patch, diff, to_initial_patch};
use crate::universe::Universe;

use rkyv::ser::Serializer;
use rkyv::ser::serializers::AllocSerializer;
use rkyv::{Deserialize, check_archived_root};
use std::collections::BTreeMap;
use std::fs::{self, File};
use std::io::{Read, Write};
use std::path::{Path, PathBuf};

/// Error type for checked checkout operations.
#[derive(Clone, Debug)]
pub enum CheckoutError {
    /// The commit was not found in the repository
    CommitNotFound(Uuid),
    /// No patches to apply (empty history)
    NoPatches,
    /// A patch failed to apply or violated axioms
    PatchFailed {
        patch_index: usize,
        commit: Uuid,
        error: ApplyPatchError,
    },
}

impl std::fmt::Display for CheckoutError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CheckoutError::CommitNotFound(uuid) => write!(f, "Commit {} not found", uuid),
            CheckoutError::NoPatches => write!(f, "No patches to apply"),
            CheckoutError::PatchFailed {
                patch_index,
                commit,
                error,
            } => write!(
                f,
                "Patch {} (commit {}) failed: {}",
                patch_index, commit, error
            ),
        }
    }
}

impl std::error::Error for CheckoutError {}

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
    /// The naming index for element names
    pub naming: NamingIndex,
}

impl VersionedState {
    /// Create a new versioned state with the given patches directory
    pub fn new(patches_dir: impl Into<PathBuf>) -> Self {
        let patches_dir = patches_dir.into();
        let universe_path = patches_dir.join("universe.bin");
        let naming_path = patches_dir.join("names.bin");
        Self {
            patches: BTreeMap::new(),
            commit_parents: BTreeMap::new(),
            head: None,
            patches_dir,
            universe: Universe::with_path(universe_path),
            naming: NamingIndex::with_path(naming_path),
        }
    }

    /// Load all patches from the patches directory
    pub fn load_patches(&mut self) -> Result<(), String> {
        fs::create_dir_all(&self.patches_dir)
            .map_err(|e| format!("Failed to create patches directory: {}", e))?;

        // Load the universe
        let universe_path = self.patches_dir.join("universe.bin");
        self.universe = Universe::load(&universe_path)?;

        // Load the naming index
        let naming_path = self.patches_dir.join("names.bin");
        self.naming = NamingIndex::load(&naming_path)?;

        let entries = fs::read_dir(&self.patches_dir)
            .map_err(|e| format!("Failed to read patches directory: {}", e))?;

        for entry in entries {
            let entry = entry.map_err(|e| format!("Failed to read directory entry: {}", e))?;
            let path = entry.path();

            if path.extension().is_some_and(|ext| ext == "patch") {
                self.load_patch(&path)?;
            }
        }

        // Find the head (the commit that is not a source of any other commit)
        self.find_head();

        Ok(())
    }

    /// Load a single patch file
    fn load_patch(&mut self, path: &Path) -> Result<(), String> {
        let mut file = File::open(path).map_err(|e| format!("Failed to open patch file: {}", e))?;

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
        let sources: std::collections::HashSet<Uuid> =
            self.commit_parents.values().filter_map(|s| *s).collect();

        // Head is a commit that is not a source of any other commit
        for &commit in self.commit_parents.keys() {
            if !sources.contains(&commit) {
                self.head = Some(commit);
                return;
            }
        }
    }

    /// Save a patch to disk (also saves the universe and naming if dirty)
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

        // Save the naming index if dirty
        if self.naming.is_dirty() {
            self.naming.save()?;
        }

        Ok(())
    }

    /// Checkout a specific commit, returning the reconstructed structure
    ///
    /// Also updates the naming index with names from applied patches.
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
            Structure::new(first_patch.num_sorts)
        } else {
            return Err("No patches to apply".to_string());
        };

        // Create a temporary naming index for checkout (don't modify the main one)
        let mut checkout_naming = NamingIndex::new();

        for patch in &chain {
            structure = apply_patch(&structure, patch, &mut self.universe, &mut checkout_naming)?;
        }

        Ok(structure)
    }

    /// Checkout a commit with incremental axiom checking.
    ///
    /// Like `checkout`, but validates each patch against the theory's axioms.
    /// Only checks tuples involving new elements (incremental checking).
    ///
    /// This is the main entry point for loading commits from other workspaces
    /// where you want to verify the commit doesn't violate axioms.
    ///
    /// # Arguments
    /// - `commit`: The commit UUID to checkout
    /// - `axioms`: The theory's axioms to check
    /// - `sig`: The theory's signature
    ///
    /// # Returns
    /// - `Ok(Structure)` if checkout succeeds and all axioms are satisfied
    /// - `Err` if checkout fails or any patch violates axioms
    pub fn checkout_checked(
        &mut self,
        commit: Uuid,
        axioms: &[Sequent],
        sig: &Signature,
    ) -> Result<Structure, CheckoutError> {
        // Build the chain of patches from root to target
        let mut chain = Vec::new();
        let mut current = Some(commit);

        while let Some(c) = current {
            let patch = self
                .patches
                .get(&c)
                .ok_or(CheckoutError::CommitNotFound(c))?;
            chain.push(patch.clone());
            current = patch.source_commit;
        }

        // Reverse to apply from root to target
        chain.reverse();

        // Apply patches in order with checking
        let mut structure = if let Some(first_patch) = chain.first() {
            Structure::new(first_patch.num_sorts)
        } else {
            return Err(CheckoutError::NoPatches);
        };

        let mut checkout_naming = NamingIndex::new();

        for (patch_idx, patch) in chain.iter().enumerate() {
            structure = apply_patch_checked(
                &structure,
                patch,
                &mut self.universe,
                &mut checkout_naming,
                axioms,
                sig,
            )
            .map_err(|e| CheckoutError::PatchFailed {
                patch_index: patch_idx,
                commit: patch.target_commit,
                error: e,
            })?;
        }

        Ok(structure)
    }

    /// Commit a structure, creating a new patch from the current HEAD
    ///
    /// Returns the new commit's UUID.
    /// The naming parameter provides names for elements in the structure.
    pub fn commit(&mut self, structure: &Structure, naming: &NamingIndex) -> Result<Uuid, String> {
        let patch = if let Some(head) = self.head {
            // Diff from current HEAD
            let base = self.checkout(head)?;
            // Use empty naming for base (names are reconstructed from patches)
            let base_naming = NamingIndex::new();
            let mut patch = diff(&base, structure, &self.universe, &base_naming, naming);
            patch.source_commit = Some(head);
            patch
        } else {
            // Initial commit
            to_initial_patch(structure, &self.universe, naming)
        };

        // Skip empty patches
        if patch.is_empty() {
            return Err("No changes to commit".to_string());
        }

        let commit_uuid = patch.target_commit;

        // Apply names from patch to our naming index
        for (uuid, name) in &patch.names.additions {
            self.naming.insert(*uuid, name.clone());
        }

        // Save to disk
        self.save_patch(&patch)?;

        // Update in-memory state
        self.commit_parents.insert(commit_uuid, patch.source_commit);
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

// ============================================================================
// Standalone Functions for Cross-Host Commit Loading
// ============================================================================

/// Load a patch file and apply it to a structure with incremental axiom checking.
///
/// This is the main entry point for loading commits from other workspaces.
/// It loads the patch from disk, applies it to the base structure, and
/// validates that all axioms are satisfied (only checking new tuples).
///
/// # Arguments
/// - `patch_path`: Path to the .patch file
/// - `base`: The structure before the patch
/// - `universe`: For UUID resolution (will be modified)
/// - `naming`: For name resolution (will be modified)
/// - `axioms`: The theory's axioms to check
/// - `sig`: The theory's signature
///
/// # Returns
/// - `Ok((Patch, Structure))` if patch loads, applies, and validates
/// - `Err` if loading fails or axioms are violated
pub fn load_and_apply_patch_checked(
    patch_path: &Path,
    base: &Structure,
    universe: &mut Universe,
    naming: &mut NamingIndex,
    axioms: &[Sequent],
    sig: &Signature,
) -> Result<(Patch, Structure), LoadPatchError> {
    // Load the patch file
    let mut file = File::open(patch_path)
        .map_err(|e| LoadPatchError::IoError(e.to_string()))?;

    let mut bytes = Vec::new();
    file.read_to_end(&mut bytes)
        .map_err(|e| LoadPatchError::IoError(e.to_string()))?;

    // Validate and deserialize
    let archived = check_archived_root::<Patch>(&bytes)
        .map_err(|e| LoadPatchError::DeserializeError(e.to_string()))?;

    let patch: Patch = archived
        .deserialize(&mut rkyv::Infallible)
        .map_err(|_| LoadPatchError::DeserializeError("rkyv deserialize failed".to_string()))?;

    // Apply with checking
    let new_structure = apply_patch_checked(base, &patch, universe, naming, axioms, sig)
        .map_err(LoadPatchError::ApplyError)?;

    Ok((patch, new_structure))
}

/// Error type for loading patches from files.
#[derive(Clone, Debug)]
pub enum LoadPatchError {
    /// I/O error reading the file
    IoError(String),
    /// Failed to deserialize the patch
    DeserializeError(String),
    /// Patch application or validation failed
    ApplyError(ApplyPatchError),
}

impl std::fmt::Display for LoadPatchError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LoadPatchError::IoError(msg) => write!(f, "I/O error: {}", msg),
            LoadPatchError::DeserializeError(msg) => write!(f, "Deserialize error: {}", msg),
            LoadPatchError::ApplyError(e) => write!(f, "Apply error: {}", e),
        }
    }
}

impl std::error::Error for LoadPatchError {}

// Unit tests moved to tests/unit_version.rs
