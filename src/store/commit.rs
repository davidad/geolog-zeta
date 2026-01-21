//! Commit operations for the Store.
//!
//! Version control through commits and name bindings.

use crate::id::{NumericId, Slid};

use super::append::AppendOps;
use super::{BindingKind, Store};

impl Store {
    /// Create a new commit
    pub fn commit(&mut self, message: Option<&str>) -> Result<Slid, String> {
        let sort_id = self.sort_ids.commit.ok_or("Commit sort not found")?;
        let commit_slid = self.add_element(sort_id, message.unwrap_or("commit"));

        // Set parent if there's a head
        if let Some(head) = self.head {
            let parent_func = self.func_ids.commit_parent.ok_or("Commit/parent not found")?;
            self.define_func(parent_func, commit_slid, head)?;
        }

        // Create NameBindings for all uncommitted changes
        let nb_sort = self.sort_ids.name_binding.ok_or("NameBinding sort not found")?;
        let commit_func = self.func_ids.name_binding_commit.ok_or("NameBinding/commit not found")?;
        let theory_func = self.func_ids.name_binding_theory.ok_or("NameBinding/theory not found")?;
        let instance_func = self.func_ids.name_binding_instance.ok_or("NameBinding/instance not found")?;

        // Collect uncommitted to avoid borrow issues
        let uncommitted: Vec<_> = self.uncommitted.drain().collect();
        for (name, binding) in uncommitted {
            let nb_slid = self.add_element(nb_sort, &format!("nb_{}_{}", name, commit_slid.index()));
            self.define_func(commit_func, nb_slid, commit_slid)?;

            match binding.kind {
                BindingKind::Theory => {
                    self.define_func(theory_func, nb_slid, binding.target)?;
                }
                BindingKind::Instance => {
                    self.define_func(instance_func, nb_slid, binding.target)?;
                }
            }
        }

        // Update head
        self.head = Some(commit_slid);

        // Auto-save
        self.save()?;

        Ok(commit_slid)
    }

    /// Get the current binding for a name (from HEAD commit or uncommitted)
    pub fn resolve_name(&self, name: &str) -> Option<(Slid, BindingKind)> {
        // Check uncommitted first
        if let Some(binding) = self.uncommitted.get(name) {
            return Some((binding.target, binding.kind));
        }

        // Otherwise, search through name bindings from HEAD backwards
        let head = self.head?;

        let nb_sort = self.sort_ids.name_binding?;
        let commit_func = self.func_ids.name_binding_commit?;
        let theory_func = self.func_ids.name_binding_theory?;
        let instance_func = self.func_ids.name_binding_instance?;

        // Walk commits from head backwards
        let mut current = Some(head);
        while let Some(commit) = current {
            // Find all NameBindings for this commit
            for nb_slid in self.elements_of_sort(nb_sort) {
                if self.get_func(commit_func, nb_slid) == Some(commit) {
                    // Check if this binding is for our name
                    let nb_name = self.get_element_name(nb_slid);
                    if nb_name.starts_with(&format!("nb_{}_", name)) {
                        // Found it! Return the target
                        if let Some(theory) = self.get_func(theory_func, nb_slid) {
                            return Some((theory, BindingKind::Theory));
                        }
                        if let Some(instance) = self.get_func(instance_func, nb_slid) {
                            return Some((instance, BindingKind::Instance));
                        }
                    }
                }
            }

            // Move to parent commit
            let parent_func = self.func_ids.commit_parent?;
            current = self.get_func(parent_func, commit);
        }

        None
    }

    /// Get all commits in order (oldest to newest)
    pub fn commit_history(&self) -> Vec<Slid> {
        let Some(head) = self.head else {
            return vec![];
        };

        let mut chain = Vec::new();
        let mut current = Some(head);

        while let Some(commit) = current {
            chain.push(commit);
            current = self
                .func_ids
                .commit_parent
                .and_then(|f| self.get_func(f, commit));
        }

        chain.reverse();
        chain
    }

    /// List all committed bindings (theories and instances)
    ///
    /// Returns (name, kind, target_slid) for each binding visible from HEAD.
    /// Names may appear multiple times if rebound in different commits.
    pub fn list_bindings(&self) -> Vec<(String, BindingKind, Slid)> {
        let Some(head) = self.head else {
            return vec![];
        };

        let Some(nb_sort) = self.sort_ids.name_binding else {
            return vec![];
        };
        let Some(commit_func) = self.func_ids.name_binding_commit else {
            return vec![];
        };
        let Some(theory_func) = self.func_ids.name_binding_theory else {
            return vec![];
        };
        let Some(instance_func) = self.func_ids.name_binding_instance else {
            return vec![];
        };

        let mut bindings = Vec::new();
        let mut seen_names = std::collections::HashSet::new();

        // Walk commits from head backwards
        let mut current = Some(head);
        while let Some(commit) = current {
            // Find all NameBindings for this commit
            for nb_slid in self.elements_of_sort(nb_sort) {
                if self.get_func(commit_func, nb_slid) == Some(commit) {
                    // Extract name from "nb_{name}_{commit_id}"
                    let nb_name = self.get_element_name(nb_slid);
                    if let Some(name) = extract_binding_name(&nb_name) {
                        // Only include first (most recent) binding for each name
                        if seen_names.insert(name.clone()) {
                            if let Some(theory) = self.get_func(theory_func, nb_slid) {
                                bindings.push((name, BindingKind::Theory, theory));
                            } else if let Some(instance) = self.get_func(instance_func, nb_slid) {
                                bindings.push((name, BindingKind::Instance, instance));
                            }
                        }
                    }
                }
            }

            // Move to parent commit
            current = self
                .func_ids
                .commit_parent
                .and_then(|f| self.get_func(f, commit));
        }

        bindings
    }
}

/// Extract the name from a binding element name like "nb_Graph_2"
fn extract_binding_name(nb_name: &str) -> Option<String> {
    // Format: "nb_{name}_{commit_id}"
    if !nb_name.starts_with("nb_") {
        return None;
    }
    let rest = &nb_name[3..]; // Skip "nb_"
    // Find the last underscore (before commit_id)
    if let Some(last_underscore) = rest.rfind('_') {
        // Verify the part after underscore is a number
        if rest[last_underscore + 1..].parse::<usize>().is_ok() {
            return Some(rest[..last_underscore].to_string());
        }
    }
    None
}
