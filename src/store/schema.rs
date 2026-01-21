//! Schema ID caching for GeologMeta.
//!
//! Caches sort and function IDs from the GeologMeta signature for fast lookup.

use crate::core::ElaboratedTheory;

/// Cached sort IDs from GeologMeta
#[derive(Default)]
pub struct SortIds {
    pub theory: Option<usize>,
    pub instance: Option<usize>,
    pub commit: Option<usize>,
    pub name_binding: Option<usize>,
    pub srt: Option<usize>,
    pub func: Option<usize>,
    pub rel: Option<usize>,
    pub elem: Option<usize>,
    pub elem_retract: Option<usize>,
    pub func_val: Option<usize>,
    pub rel_tuple: Option<usize>,
    // NOTE: No func_val_retract or rel_tuple_retract - these are immutable (Monotonic Submodel Property)
    pub sequent: Option<usize>,
    pub param: Option<usize>,
    pub dsort: Option<usize>,
    pub base_ds: Option<usize>,
    pub prod_ds: Option<usize>,
    pub field: Option<usize>,
    pub binder: Option<usize>,
    pub term: Option<usize>,
    pub formula: Option<usize>,
}

/// Cached function IDs from GeologMeta
#[derive(Default)]
pub struct FuncIds {
    // Theory functions
    pub theory_parent: Option<usize>,

    // Instance functions
    pub instance_parent: Option<usize>,
    pub instance_theory: Option<usize>,

    // Commit functions
    pub commit_parent: Option<usize>,

    // NameBinding functions
    pub name_binding_commit: Option<usize>,
    pub name_binding_theory: Option<usize>,
    pub name_binding_instance: Option<usize>,

    // Elem functions
    pub elem_instance: Option<usize>,
    pub elem_sort: Option<usize>,

    // ElemRetract functions
    pub elem_retract_instance: Option<usize>,
    pub elem_retract_elem: Option<usize>,

    // FuncVal functions (IMMUTABLE - no retract)
    pub func_val_instance: Option<usize>,
    pub func_val_func: Option<usize>,
    pub func_val_arg: Option<usize>,
    pub func_val_result: Option<usize>,

    // RelTuple functions (IMMUTABLE - no retract)
    pub rel_tuple_instance: Option<usize>,
    pub rel_tuple_rel: Option<usize>,
    pub rel_tuple_arg: Option<usize>,

    // Srt functions
    pub srt_theory: Option<usize>,

    // Func functions
    pub func_theory: Option<usize>,
    pub func_dom: Option<usize>,
    pub func_cod: Option<usize>,

    // Rel functions
    pub rel_theory: Option<usize>,
    pub rel_dom: Option<usize>,

    // DSort functions
    pub base_ds_dsort: Option<usize>,
    pub base_ds_srt: Option<usize>,
    pub prod_ds_dsort: Option<usize>,
    pub field_prod: Option<usize>,
    pub field_type: Option<usize>,
}

impl SortIds {
    /// Populate sort IDs from a GeologMeta theory
    pub fn from_theory(theory: &ElaboratedTheory) -> Self {
        let sig = &theory.theory.signature;
        Self {
            theory: sig.lookup_sort("Theory"),
            instance: sig.lookup_sort("Instance"),
            commit: sig.lookup_sort("Commit"),
            name_binding: sig.lookup_sort("NameBinding"),
            srt: sig.lookup_sort("Srt"),
            func: sig.lookup_sort("Func"),
            rel: sig.lookup_sort("Rel"),
            elem: sig.lookup_sort("Elem"),
            elem_retract: sig.lookup_sort("ElemRetract"),
            func_val: sig.lookup_sort("FuncVal"),
            rel_tuple: sig.lookup_sort("RelTuple"),
            sequent: sig.lookup_sort("Sequent"),
            param: sig.lookup_sort("Param"),
            dsort: sig.lookup_sort("DSort"),
            base_ds: sig.lookup_sort("BaseDS"),
            prod_ds: sig.lookup_sort("ProdDS"),
            field: sig.lookup_sort("Field"),
            binder: sig.lookup_sort("Binder"),
            term: sig.lookup_sort("Term"),
            formula: sig.lookup_sort("Formula"),
        }
    }
}

impl FuncIds {
    /// Populate function IDs from a GeologMeta theory
    pub fn from_theory(theory: &ElaboratedTheory) -> Self {
        let sig = &theory.theory.signature;
        Self {
            theory_parent: sig.lookup_func("Theory/parent"),
            instance_parent: sig.lookup_func("Instance/parent"),
            instance_theory: sig.lookup_func("Instance/theory"),
            commit_parent: sig.lookup_func("Commit/parent"),
            name_binding_commit: sig.lookup_func("NameBinding/commit"),
            name_binding_theory: sig.lookup_func("NameBinding/theory"),
            name_binding_instance: sig.lookup_func("NameBinding/instance"),
            elem_instance: sig.lookup_func("Elem/instance"),
            elem_sort: sig.lookup_func("Elem/sort"),
            elem_retract_instance: sig.lookup_func("ElemRetract/instance"),
            elem_retract_elem: sig.lookup_func("ElemRetract/elem"),
            func_val_instance: sig.lookup_func("FuncVal/instance"),
            func_val_func: sig.lookup_func("FuncVal/func"),
            func_val_arg: sig.lookup_func("FuncVal/arg"),
            func_val_result: sig.lookup_func("FuncVal/result"),
            rel_tuple_instance: sig.lookup_func("RelTuple/instance"),
            rel_tuple_rel: sig.lookup_func("RelTuple/rel"),
            rel_tuple_arg: sig.lookup_func("RelTuple/arg"),
            srt_theory: sig.lookup_func("Srt/theory"),
            func_theory: sig.lookup_func("Func/theory"),
            func_dom: sig.lookup_func("Func/dom"),
            func_cod: sig.lookup_func("Func/cod"),
            rel_theory: sig.lookup_func("Rel/theory"),
            rel_dom: sig.lookup_func("Rel/dom"),
            base_ds_dsort: sig.lookup_func("BaseDS/dsort"),
            base_ds_srt: sig.lookup_func("BaseDS/srt"),
            prod_ds_dsort: sig.lookup_func("ProdDS/dsort"),
            field_prod: sig.lookup_func("Field/prod"),
            field_type: sig.lookup_func("Field/type"),
        }
    }
}
