//! Materialized views for the Store.
//!
//! A MaterializedView is an indexed snapshot of an instance at a specific version,
//! computed by walking the version chain and applying all additions/retractions.

use std::collections::{HashMap, HashSet};

use crate::id::{NumericId, Slid};

use super::append::AppendOps;
use super::Store;

/// A materialized view of an instance at a specific version.
///
/// This is the "rendered" state of an instance after applying all patches
/// from the root to a particular version. It can be incrementally updated
/// when a new child version is created.
#[derive(Clone, Debug)]
pub struct MaterializedView {
    /// The instance version this view is materialized at
    pub instance: Slid,

    /// Live elements (not tombstoned)
    pub elements: HashSet<Slid>,

    /// Live relation tuples: tuple_slid -> (rel, arg)
    pub rel_tuples: HashMap<Slid, (Slid, Slid)>,

    /// Live function values: fv_slid -> (func, arg, result)
    pub func_vals: HashMap<Slid, (Slid, Slid, Slid)>,

    /// Element tombstones (for delta computation)
    /// NOTE: Only elements can be tombstoned; FuncVals and RelTuples are immutable
    pub elem_tombstones: HashSet<Slid>,
}

impl MaterializedView {
    /// Create an empty materialized view
    pub fn empty(instance: Slid) -> Self {
        Self {
            instance,
            elements: HashSet::new(),
            rel_tuples: HashMap::new(),
            func_vals: HashMap::new(),
            elem_tombstones: HashSet::new(),
        }
    }

    /// Get the number of live elements
    pub fn element_count(&self) -> usize {
        self.elements.len()
    }

    /// Check if an element is live
    pub fn has_element(&self, elem: Slid) -> bool {
        self.elements.contains(&elem)
    }

    /// Check if a relation tuple is live
    pub fn has_rel_tuple(&self, tuple: Slid) -> bool {
        self.rel_tuples.contains_key(&tuple)
    }

    /// Get all elements of a particular sort (requires Store for lookup)
    pub fn elements_of_sort<'a>(
        &'a self,
        store: &'a Store,
        sort: Slid,
    ) -> impl Iterator<Item = Slid> + 'a {
        self.elements.iter().copied().filter(move |&elem| {
            store
                .func_ids
                .elem_sort
                .and_then(|f| store.get_func(f, elem))
                .map(|s| s == sort)
                .unwrap_or(false)
        })
    }

    /// Get all relation tuples for a particular relation
    pub fn tuples_of_relation(&self, rel: Slid) -> impl Iterator<Item = (Slid, Slid)> + '_ {
        self.rel_tuples
            .iter()
            .filter(move |(_, (r, _))| *r == rel)
            .map(|(&tuple_slid, (_, arg))| (tuple_slid, *arg))
    }

    /// Get all function values for a particular function
    pub fn values_of_function(&self, func: Slid) -> impl Iterator<Item = (Slid, Slid)> + '_ {
        self.func_vals
            .iter()
            .filter(move |(_, (f, _, _))| *f == func)
            .map(|(_, (_, arg, result))| (*arg, *result))
    }
}

impl Store {
    /// Materialize an instance from scratch by walking the parent chain.
    ///
    /// This collects all additions and retractions from root to the specified
    /// version, producing a complete view of the instance state.
    pub fn materialize(&self, instance: Slid) -> MaterializedView {
        let mut view = MaterializedView::empty(instance);

        // Collect version chain (from instance back to root)
        let mut chain = Vec::new();
        let mut version = Some(instance);
        while let Some(v) = version {
            chain.push(v);
            version = self.func_ids.instance_parent.and_then(|f| self.get_func(f, v));
        }

        // Process from oldest to newest (reverse the chain)
        for v in chain.into_iter().rev() {
            self.apply_version_delta(&mut view, v);
        }

        view.instance = instance;
        view
    }

    /// Apply the delta from a single instance version to a materialized view.
    ///
    /// This is the core of incremental materialization: given a view at version N,
    /// we can efficiently update it to version N+1 by applying only the changes
    /// introduced in N+1.
    pub fn apply_version_delta(&self, view: &mut MaterializedView, version: Slid) {
        // 1. Process element additions
        if let Some(elem_sort) = self.sort_ids.elem {
            if let Some(instance_func) = self.func_ids.elem_instance {
                for elem in self.elements_of_sort(elem_sort) {
                    if self.get_func(instance_func, elem) == Some(version) {
                        // Don't add if already tombstoned
                        if !view.elem_tombstones.contains(&elem) {
                            view.elements.insert(elem);
                        }
                    }
                }
            }
        }

        // 2. Process element retractions
        if let Some(retract_sort) = self.sort_ids.elem_retract {
            if let Some(instance_func) = self.func_ids.elem_retract_instance {
                if let Some(elem_func) = self.func_ids.elem_retract_elem {
                    for retract in self.elements_of_sort(retract_sort) {
                        if self.get_func(instance_func, retract) == Some(version) {
                            if let Some(elem) = self.get_func(elem_func, retract) {
                                view.elements.remove(&elem);
                                view.elem_tombstones.insert(elem);
                            }
                        }
                    }
                }
            }
        }

        // 3. Process relation tuple additions (IMMUTABLE - no retractions)
        if let Some(tuple_sort) = self.sort_ids.rel_tuple {
            if let (Some(instance_func), Some(rel_func), Some(arg_func)) = (
                self.func_ids.rel_tuple_instance,
                self.func_ids.rel_tuple_rel,
                self.func_ids.rel_tuple_arg,
            ) {
                for tuple in self.elements_of_sort(tuple_sort) {
                    if self.get_func(instance_func, tuple) == Some(version) {
                        if let (Some(rel), Some(arg)) =
                            (self.get_func(rel_func, tuple), self.get_func(arg_func, tuple))
                        {
                            view.rel_tuples.insert(tuple, (rel, arg));
                        }
                    }
                }
            }
        }

        // 4. Process function value additions (IMMUTABLE - no retractions)
        if let Some(fv_sort) = self.sort_ids.func_val {
            if let (Some(instance_func), Some(func_func), Some(arg_func), Some(result_func)) = (
                self.func_ids.func_val_instance,
                self.func_ids.func_val_func,
                self.func_ids.func_val_arg,
                self.func_ids.func_val_result,
            ) {
                for fv in self.elements_of_sort(fv_sort) {
                    if self.get_func(instance_func, fv) == Some(version) {
                        if let (Some(func), Some(arg), Some(result)) = (
                            self.get_func(func_func, fv),
                            self.get_func(arg_func, fv),
                            self.get_func(result_func, fv),
                        ) {
                            view.func_vals.insert(fv, (func, arg, result));
                        }
                    }
                }
            }
        }
    }

    /// Incrementally update a materialized view to a new version.
    ///
    /// The new version must be a direct child of the view's current version,
    /// or this will return an error.
    pub fn update_view(
        &self,
        view: &mut MaterializedView,
        new_version: Slid,
    ) -> Result<(), String> {
        // Verify that new_version is a direct child of view.instance
        let parent = self
            .func_ids
            .instance_parent
            .and_then(|f| self.get_func(f, new_version));

        if parent != Some(view.instance) {
            return Err(format!(
                "Cannot incrementally update: {} is not a direct child of {}",
                new_version.index(),
                view.instance.index()
            ));
        }

        // Apply the delta
        self.apply_version_delta(view, new_version);
        view.instance = new_version;

        Ok(())
    }

    /// Create a new instance version extending an existing view, and update the view.
    ///
    /// This is the preferred way to modify instances: create the extension,
    /// add elements/tuples/values to it, then update the view.
    pub fn extend_instance_with_view(
        &mut self,
        view: &mut MaterializedView,
        name: &str,
    ) -> Result<Slid, String> {
        let new_version = self.extend_instance(view.instance, name)?;

        // The view can be updated after mutations are done
        // For now, just update the instance reference
        view.instance = new_version;

        Ok(new_version)
    }

    /// Materialize and cache a view for an instance.
    ///
    /// This stores the view in a view cache for efficient reuse.
    /// The cache is invalidated when the instance is extended.
    pub fn get_or_create_view(&mut self, instance: Slid) -> MaterializedView {
        // For now, just materialize (cache can be added later)
        self.materialize(instance)
    }
}
