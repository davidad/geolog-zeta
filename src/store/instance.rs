//! Instance operations for the Store.
//!
//! Creating, extending, and modifying instances in the GeologMeta structure.

use crate::id::Slid;

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
}
