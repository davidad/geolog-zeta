//! Instance operations for the Store.
//!
//! Creating, extending, and modifying instances in the GeologMeta structure.

use std::collections::HashMap;

use crate::core::Structure;
use crate::id::{NumericId, Slid};

use super::append::AppendOps;
use super::{BindingKind, Store, UncommittedBinding};

impl Store {
    /// Create a new instance (version 0, no parent)
    pub fn create_instance(&mut self, name: &str, theory: Slid) -> Result<Slid, String> {
        let sort_id = self.sort_ids.instance.ok_or("Instance sort not found")?;
        let instance_slid = self.add_element(sort_id, name);

        // Set theory
        let func_id = self.func_ids.instance_theory.ok_or("Instance/theory not found")?;
        self.define_func(func_id, instance_slid, theory)?;

        // Register uncommitted binding
        self.uncommitted.insert(
            name.to_string(),
            UncommittedBinding {
                target: instance_slid,
                kind: BindingKind::Instance,
            },
        );

        Ok(instance_slid)
    }

    /// Create a new version of an existing instance
    pub fn extend_instance(&mut self, parent: Slid, name: &str) -> Result<Slid, String> {
        let sort_id = self.sort_ids.instance.ok_or("Instance sort not found")?;

        // Get the theory from the parent
        let theory_func = self.func_ids.instance_theory.ok_or("Instance/theory not found")?;
        let theory = self.get_func(theory_func, parent).ok_or("Parent has no theory")?;

        let instance_slid = self.add_element(
            sort_id,
            &format!("{}@v{}", name, self.meta.carriers[sort_id].len()),
        );

        // Set parent and theory
        let parent_func = self.func_ids.instance_parent.ok_or("Instance/parent not found")?;
        self.define_func(parent_func, instance_slid, parent)?;
        self.define_func(theory_func, instance_slid, theory)?;

        // Update uncommitted binding
        self.uncommitted.insert(
            name.to_string(),
            UncommittedBinding {
                target: instance_slid,
                kind: BindingKind::Instance,
            },
        );

        Ok(instance_slid)
    }

    /// Add an element to an instance
    pub fn add_elem(&mut self, instance: Slid, srt: Slid, name: &str) -> Result<Slid, String> {
        let sort_id = self.sort_ids.elem.ok_or("Elem sort not found")?;
        let elem_slid = self.add_element_qualified(
            sort_id,
            vec![self.get_element_name(instance), name.to_string()],
        );

        let instance_func = self.func_ids.elem_instance.ok_or("Elem/instance not found")?;
        let sort_func = self.func_ids.elem_sort.ok_or("Elem/sort not found")?;

        self.define_func(instance_func, elem_slid, instance)?;
        self.define_func(sort_func, elem_slid, srt)?;

        Ok(elem_slid)
    }

    /// Retract an element from an instance
    pub fn retract_elem(&mut self, instance: Slid, elem: Slid) -> Result<Slid, String> {
        let sort_id = self.sort_ids.elem_retract.ok_or("ElemRetract sort not found")?;
        let retract_slid = self.add_element(sort_id, &format!("retract_{}", self.get_element_name(elem)));

        let instance_func = self.func_ids.elem_retract_instance.ok_or("ElemRetract/instance not found")?;
        let elem_func = self.func_ids.elem_retract_elem.ok_or("ElemRetract/elem not found")?;

        self.define_func(instance_func, retract_slid, instance)?;
        self.define_func(elem_func, retract_slid, elem)?;

        Ok(retract_slid)
    }

    /// Define a function value in an instance
    pub fn add_func_val(
        &mut self,
        instance: Slid,
        func: Slid,
        arg: Slid,
        result: Slid,
    ) -> Result<Slid, String> {
        let sort_id = self.sort_ids.func_val.ok_or("FuncVal sort not found")?;
        let fv_slid = self.add_element(
            sort_id,
            &format!("fv_{}_{}", self.get_element_name(func), self.get_element_name(arg)),
        );

        let instance_func = self.func_ids.func_val_instance.ok_or("FuncVal/instance not found")?;
        let func_func = self.func_ids.func_val_func.ok_or("FuncVal/func not found")?;
        let arg_func = self.func_ids.func_val_arg.ok_or("FuncVal/arg not found")?;
        let result_func = self.func_ids.func_val_result.ok_or("FuncVal/result not found")?;

        self.define_func(instance_func, fv_slid, instance)?;
        self.define_func(func_func, fv_slid, func)?;
        self.define_func(arg_func, fv_slid, arg)?;
        self.define_func(result_func, fv_slid, result)?;

        Ok(fv_slid)
    }

    // NOTE: No retract_func_val - function values are IMMUTABLE (Monotonic Submodel Property)

    /// Assert a relation tuple in an instance
    pub fn add_rel_tuple(&mut self, instance: Slid, rel: Slid, arg: Slid) -> Result<Slid, String> {
        let sort_id = self.sort_ids.rel_tuple.ok_or("RelTuple sort not found")?;
        let rt_slid = self.add_element(
            sort_id,
            &format!("rt_{}_{}", self.get_element_name(rel), self.get_element_name(arg)),
        );

        let instance_func = self.func_ids.rel_tuple_instance.ok_or("RelTuple/instance not found")?;
        let rel_func = self.func_ids.rel_tuple_rel.ok_or("RelTuple/rel not found")?;
        let arg_func = self.func_ids.rel_tuple_arg.ok_or("RelTuple/arg not found")?;

        self.define_func(instance_func, rt_slid, instance)?;
        self.define_func(rel_func, rt_slid, rel)?;
        self.define_func(arg_func, rt_slid, arg)?;

        Ok(rt_slid)
    }

    // NOTE: No retract_rel_tuple - relation tuples are IMMUTABLE (Monotonic Submodel Property)

    /// Persist all instance data (elements, function values, relation tuples) to GeologMeta.
    ///
    /// This takes a Structure and persists its contents to the Store, creating Elem,
    /// FuncVal, and RelTuple elements in GeologMeta.
    ///
    /// Returns a mapping from Structure Slids to GeologMeta Elem Slids.
    pub fn persist_instance_data(
        &mut self,
        instance_slid: Slid,
        theory_slid: Slid,
        structure: &Structure,
        element_names: &HashMap<Slid, String>,
    ) -> Result<InstancePersistResult, String> {
        // Get theory's sorts to map sort indices to Srt Slids
        let sort_infos = self.query_theory_sorts(theory_slid);
        let func_infos = self.query_theory_funcs(theory_slid);
        let rel_infos = self.query_theory_rels(theory_slid);

        // Build sort index -> Srt Slid mapping
        let sort_idx_to_srt: HashMap<usize, Slid> = sort_infos
            .iter()
            .enumerate()
            .map(|(idx, info)| (idx, info.slid))
            .collect();

        // Build func index -> Func Slid mapping
        let func_idx_to_func: HashMap<usize, Slid> = func_infos
            .iter()
            .enumerate()
            .map(|(idx, info)| (idx, info.slid))
            .collect();

        // Build rel index -> Rel Slid mapping
        let rel_idx_to_rel: HashMap<usize, Slid> = rel_infos
            .iter()
            .enumerate()
            .map(|(idx, info)| (idx, info.slid))
            .collect();

        // Mapping from Structure Slid to GeologMeta Elem Slid
        let mut elem_slid_map: HashMap<Slid, Slid> = HashMap::new();

        // 1. Persist all elements
        for (sort_idx, carrier) in structure.carriers.iter().enumerate() {
            let srt_slid = sort_idx_to_srt
                .get(&sort_idx)
                .copied()
                .ok_or_else(|| format!("Unknown sort index: {}", sort_idx))?;

            for structure_slid_u64 in carrier.iter() {
                let structure_slid = Slid::from_usize(structure_slid_u64 as usize);
                let elem_name = element_names
                    .get(&structure_slid)
                    .map(|s| s.as_str())
                    .unwrap_or_else(|| "elem");

                let elem_slid = self.add_elem(instance_slid, srt_slid, elem_name)?;
                elem_slid_map.insert(structure_slid, elem_slid);
            }
        }

        // 2. Persist function values
        // For now, only handle base domain functions (not product domains)
        for (func_idx, func_col) in structure.functions.iter().enumerate() {
            let func_slid = match func_idx_to_func.get(&func_idx) {
                Some(s) => *s,
                None => continue, // Skip if no corresponding Func in theory
            };

            match func_col {
                crate::core::FunctionColumn::Local(values) => {
                    for (local_idx, opt_result) in values.iter().enumerate() {
                        if let Some(result_slid) = crate::id::get_slid(*opt_result) {
                            // Find the structure Slid for this local index
                            // The local index corresponds to position in the domain sort's carrier
                            if let Some(domain_sort_idx) = self.get_func_domain_sort(func_slid)
                                && let Some(carrier) = structure.carriers.get(domain_sort_idx)
                                    && let Some(arg_u64) = carrier.iter().nth(local_idx) {
                                        let arg_slid = Slid::from_usize(arg_u64 as usize);
                                        if let (Some(&arg_elem), Some(&result_elem)) =
                                            (elem_slid_map.get(&arg_slid), elem_slid_map.get(&result_slid))
                                        {
                                            self.add_func_val(instance_slid, func_slid, arg_elem, result_elem)?;
                                        }
                                    }
                        }
                    }
                }
                crate::core::FunctionColumn::External(_) => {
                    // External functions reference elements from other instances
                    // TODO: Handle external references
                }
                crate::core::FunctionColumn::ProductLocal { .. } => {
                    // Product domain functions need special handling
                    // TODO: Handle product domains
                }
                crate::core::FunctionColumn::ProductCodomain { .. } => {
                    // Product codomain functions need special handling
                    // TODO: Handle product codomains (store each field value)
                }
            }
        }

        // 3. Persist relation tuples
        // NOTE: Currently only handles unary relations (single element domain).
        // Product domain relations (e.g., Edge : [src: Node, tgt: Node] -> Prop)
        // require schema changes to properly persist all tuple components.
        for (rel_idx, relation) in structure.relations.iter().enumerate() {
            let rel_slid = match rel_idx_to_rel.get(&rel_idx) {
                Some(s) => *s,
                None => continue,
            };

            // Check if this is a product domain relation by checking arity
            let rel_info = rel_infos.get(rel_idx);
            let is_product = rel_info.map(|r| r.domain.arity() > 1).unwrap_or(false);

            if is_product {
                // Skip product-domain relations for now
                // TODO: Add RelTupleArg sort to GeologMeta for proper tuple component storage
                continue;
            }

            for tuple in relation.iter() {
                // Unary relation: single element
                if let Some(&elem) = tuple.first()
                    && let Some(&elem_slid) = elem_slid_map.get(&elem) {
                        self.add_rel_tuple(instance_slid, rel_slid, elem_slid)?;
                    }
            }
        }

        Ok(InstancePersistResult { elem_slid_map })
    }

    /// Helper to get the domain sort index for a function.
    fn get_func_domain_sort(&self, func_slid: Slid) -> Option<usize> {
        let dom_func = self.func_ids.func_dom?;
        let dsort_slid = self.get_func(dom_func, func_slid)?;

        // Check if it's a base dsort
        let base_ds_sort = self.sort_ids.base_ds?;
        let srt_func = self.func_ids.base_ds_srt?;
        let dsort_func = self.func_ids.base_ds_dsort?;

        for base_slid in self.elements_of_sort(base_ds_sort) {
            if self.get_func(dsort_func, base_slid) == Some(dsort_slid)
                && let Some(srt_slid) = self.get_func(srt_func, base_slid) {
                    // Find this Srt's index in the theory
                    let srt_theory_func = self.func_ids.srt_theory?;
                    if let Some(theory_slid) = self.get_func(srt_theory_func, srt_slid) {
                        let sorts = self.query_theory_sorts(theory_slid);
                        for (idx, info) in sorts.iter().enumerate() {
                            if info.slid == srt_slid {
                                return Some(idx);
                            }
                        }
                    }
                }
        }
        None
    }
}

/// Result of persisting instance data to GeologMeta.
#[derive(Debug)]
pub struct InstancePersistResult {
    /// Mapping from Structure Slids to GeologMeta Elem Slids
    pub elem_slid_map: HashMap<Slid, Slid>,
}
