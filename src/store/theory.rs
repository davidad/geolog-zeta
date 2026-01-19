//! Theory operations for the Store.
//!
//! Creating, extending, and modifying theories in the GeologMeta structure.

use crate::id::Slid;

use super::append::AppendOps;
use super::{BindingKind, Store, UncommittedBinding};

impl Store {
    /// Create a new theory (version 0, no parent)
    pub fn create_theory(&mut self, name: &str) -> Result<Slid, String> {
        let sort_id = self.sort_ids.theory.ok_or("Theory sort not found")?;
        let theory_slid = self.add_element(sort_id, name);

        // Register uncommitted binding
        self.uncommitted.insert(
            name.to_string(),
            UncommittedBinding {
                target: theory_slid,
                kind: BindingKind::Theory,
            },
        );

        Ok(theory_slid)
    }

    /// Create a new version of an existing theory
    pub fn extend_theory(&mut self, parent: Slid, name: &str) -> Result<Slid, String> {
        let sort_id = self.sort_ids.theory.ok_or("Theory sort not found")?;
        let theory_slid = self.add_element(
            sort_id,
            &format!("{}@v{}", name, self.meta.carriers[sort_id].len()),
        );

        // Set parent
        let func_id = self.func_ids.theory_parent.ok_or("Theory/parent not found")?;
        self.define_func(func_id, theory_slid, parent)?;

        // Update uncommitted binding
        self.uncommitted.insert(
            name.to_string(),
            UncommittedBinding {
                target: theory_slid,
                kind: BindingKind::Theory,
            },
        );

        Ok(theory_slid)
    }

    /// Add a sort to a theory
    pub fn add_sort(&mut self, theory: Slid, name: &str) -> Result<Slid, String> {
        let sort_id = self.sort_ids.srt.ok_or("Srt sort not found")?;
        let srt_slid = self.add_element_qualified(
            sort_id,
            vec![self.get_element_name(theory), name.to_string()],
        );

        let func_id = self.func_ids.srt_theory.ok_or("Srt/theory not found")?;
        self.define_func(func_id, srt_slid, theory)?;

        Ok(srt_slid)
    }

    /// Add a function to a theory
    pub fn add_function(
        &mut self,
        theory: Slid,
        name: &str,
        domain: Slid,
        codomain: Slid,
    ) -> Result<Slid, String> {
        let sort_id = self.sort_ids.func.ok_or("Func sort not found")?;
        let func_slid = self.add_element_qualified(
            sort_id,
            vec![self.get_element_name(theory), name.to_string()],
        );

        let theory_func = self.func_ids.func_theory.ok_or("Func/theory not found")?;
        let dom_func = self.func_ids.func_dom.ok_or("Func/dom not found")?;
        let cod_func = self.func_ids.func_cod.ok_or("Func/cod not found")?;

        self.define_func(theory_func, func_slid, theory)?;
        self.define_func(dom_func, func_slid, domain)?;
        self.define_func(cod_func, func_slid, codomain)?;

        Ok(func_slid)
    }

    /// Add a relation to a theory
    pub fn add_relation(&mut self, theory: Slid, name: &str, domain: Slid) -> Result<Slid, String> {
        let sort_id = self.sort_ids.rel.ok_or("Rel sort not found")?;
        let rel_slid = self.add_element_qualified(
            sort_id,
            vec![self.get_element_name(theory), name.to_string()],
        );

        let theory_func = self.func_ids.rel_theory.ok_or("Rel/theory not found")?;
        let dom_func = self.func_ids.rel_dom.ok_or("Rel/dom not found")?;

        self.define_func(theory_func, rel_slid, theory)?;
        self.define_func(dom_func, rel_slid, domain)?;

        Ok(rel_slid)
    }

    /// Create a base DSort from a Srt
    pub fn make_base_dsort(&mut self, srt: Slid) -> Result<Slid, String> {
        let base_ds_sort = self.sort_ids.base_ds.ok_or("BaseDS sort not found")?;
        let dsort_sort = self.sort_ids.dsort.ok_or("DSort sort not found")?;

        let base_ds_slid = self.add_element(base_ds_sort, &format!("base_{}", self.get_element_name(srt)));
        let dsort_slid = self.add_element(dsort_sort, &format!("dsort_{}", self.get_element_name(srt)));

        let dsort_func = self.func_ids.base_ds_dsort.ok_or("BaseDS/dsort not found")?;
        let srt_func = self.func_ids.base_ds_srt.ok_or("BaseDS/srt not found")?;

        self.define_func(dsort_func, base_ds_slid, dsort_slid)?;
        self.define_func(srt_func, base_ds_slid, srt)?;

        Ok(dsort_slid)
    }
}
