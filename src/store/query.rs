//! Query operations for the Store.
//!
//! Walking instance version chains to collect elements, function values, and relation tuples.
//!
//! NOTE: FuncVals and RelTuples are IMMUTABLE (Monotonic Submodel Property).
//! Only elements can be retracted.

use std::collections::HashSet;

use crate::id::Slid;

use super::append::AppendOps;
use super::Store;

impl Store {
    /// Get all elements of an instance (including from parent chain)
    pub fn get_instance_elements(&self, instance: Slid) -> Vec<Slid> {
        let mut elements = Vec::new();
        let mut retractions = HashSet::new();

        // Collect retractions first (from all versions in chain)
        let mut version = Some(instance);
        while let Some(v) = version {
            if let Some(retract_sort) = self.sort_ids.elem_retract {
                if let Some(instance_func) = self.func_ids.elem_retract_instance {
                    if let Some(elem_func) = self.func_ids.elem_retract_elem {
                        for retract in self.elements_of_sort(retract_sort) {
                            if self.get_func(instance_func, retract) == Some(v) {
                                if let Some(elem) = self.get_func(elem_func, retract) {
                                    retractions.insert(elem);
                                }
                            }
                        }
                    }
                }
            }
            version = self.func_ids.instance_parent.and_then(|f| self.get_func(f, v));
        }

        // Now collect elements (filtering out retracted ones)
        let mut version = Some(instance);
        while let Some(v) = version {
            if let Some(elem_sort) = self.sort_ids.elem {
                if let Some(instance_func) = self.func_ids.elem_instance {
                    for elem in self.elements_of_sort(elem_sort) {
                        if self.get_func(instance_func, elem) == Some(v) {
                            if !retractions.contains(&elem) {
                                elements.push(elem);
                            }
                        }
                    }
                }
            }
            version = self.func_ids.instance_parent.and_then(|f| self.get_func(f, v));
        }

        elements
    }

    /// Get all relation tuples of an instance (including from parent chain)
    ///
    /// Returns (tuple_slid, rel_slid, arg_slid) triples.
    /// NOTE: RelTuples are IMMUTABLE - no retractions (Monotonic Submodel Property)
    pub fn get_instance_rel_tuples(&self, instance: Slid) -> Vec<(Slid, Slid, Slid)> {
        let mut tuples = Vec::new();

        // Collect tuples from all versions in the chain
        let mut version = Some(instance);
        while let Some(v) = version {
            if let Some(tuple_sort) = self.sort_ids.rel_tuple {
                if let (Some(instance_func), Some(rel_func), Some(arg_func)) = (
                    self.func_ids.rel_tuple_instance,
                    self.func_ids.rel_tuple_rel,
                    self.func_ids.rel_tuple_arg,
                ) {
                    for tuple in self.elements_of_sort(tuple_sort) {
                        if self.get_func(instance_func, tuple) == Some(v) {
                            if let (Some(rel), Some(arg)) =
                                (self.get_func(rel_func, tuple), self.get_func(arg_func, tuple))
                            {
                                tuples.push((tuple, rel, arg));
                            }
                        }
                    }
                }
            }
            version = self.func_ids.instance_parent.and_then(|f| self.get_func(f, v));
        }

        tuples
    }

    /// Get all function values of an instance (including from parent chain)
    ///
    /// Returns (fv_slid, func_slid, arg_slid, result_slid) tuples.
    /// NOTE: FuncVals are IMMUTABLE - no retractions (Monotonic Submodel Property)
    pub fn get_instance_func_vals(&self, instance: Slid) -> Vec<(Slid, Slid, Slid, Slid)> {
        let mut vals = Vec::new();

        // Collect function values from all versions in the chain
        let mut version = Some(instance);
        while let Some(v) = version {
            if let Some(fv_sort) = self.sort_ids.func_val {
                if let (
                    Some(instance_func),
                    Some(func_func),
                    Some(arg_func),
                    Some(result_func),
                ) = (
                    self.func_ids.func_val_instance,
                    self.func_ids.func_val_func,
                    self.func_ids.func_val_arg,
                    self.func_ids.func_val_result,
                ) {
                    for fv in self.elements_of_sort(fv_sort) {
                        if self.get_func(instance_func, fv) == Some(v) {
                            if let (Some(func), Some(arg), Some(result)) = (
                                self.get_func(func_func, fv),
                                self.get_func(arg_func, fv),
                                self.get_func(result_func, fv),
                            ) {
                                vals.push((fv, func, arg, result));
                            }
                        }
                    }
                }
            }
            version = self.func_ids.instance_parent.and_then(|f| self.get_func(f, v));
        }

        vals
    }

    /// Get the theory for an instance
    pub fn get_instance_theory(&self, instance: Slid) -> Option<Slid> {
        self.func_ids
            .instance_theory
            .and_then(|f| self.get_func(f, instance))
    }

    /// Get the parent of an instance (for versioning)
    pub fn get_instance_parent(&self, instance: Slid) -> Option<Slid> {
        self.func_ids
            .instance_parent
            .and_then(|f| self.get_func(f, instance))
    }

    /// Get an element's sort
    pub fn get_elem_sort(&self, elem: Slid) -> Option<Slid> {
        self.func_ids
            .elem_sort
            .and_then(|f| self.get_func(f, elem))
    }
}
