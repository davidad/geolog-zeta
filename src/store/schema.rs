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
    pub rel_tuple_arg: Option<usize>,
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

    // Context variables (for sequent universal quantification)
    pub ctx_var: Option<usize>,

    // Term subtypes
    pub var_t: Option<usize>,
    pub app_t: Option<usize>,
    pub record_t: Option<usize>,
    pub rec_entry: Option<usize>,
    pub proj_t: Option<usize>,

    // Formula subtypes
    pub true_f: Option<usize>,
    pub false_f: Option<usize>,
    pub eq_f: Option<usize>,
    pub rel_f: Option<usize>,
    pub conj_f: Option<usize>,
    pub conj_arm: Option<usize>,
    pub disj_f: Option<usize>,
    pub disj_arm: Option<usize>,
    pub exists_f: Option<usize>,

    // Node (for ancestry/scoping - may not be needed for persistence)
    pub node: Option<usize>,
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

    // RelTupleArg functions (uniform for all relations, even unary)
    pub rel_tuple_arg_tuple: Option<usize>,
    pub rel_tuple_arg_elem: Option<usize>,
    pub rel_tuple_arg_position: Option<usize>,

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

    // Sequent functions
    pub sequent_theory: Option<usize>,
    pub sequent_premise: Option<usize>,
    pub sequent_conclusion: Option<usize>,

    // CtxVar functions (sequent-level universal quantification)
    pub ctx_var_sequent: Option<usize>,
    pub ctx_var_binder: Option<usize>,

    // Binder functions
    pub binder_type: Option<usize>,

    // Term/Formula to Node embeddings
    pub term_node: Option<usize>,
    pub formula_node: Option<usize>,

    // VarT functions
    pub var_t_term: Option<usize>,
    pub var_t_binder: Option<usize>,

    // AppT functions
    pub app_t_term: Option<usize>,
    pub app_t_func: Option<usize>,
    pub app_t_arg: Option<usize>,

    // RecordT functions
    pub record_t_term: Option<usize>,

    // RecEntry functions
    pub rec_entry_record: Option<usize>,
    pub rec_entry_val: Option<usize>,
    pub rec_entry_field: Option<usize>,

    // ProjT functions
    pub proj_t_term: Option<usize>,
    pub proj_t_base: Option<usize>,
    pub proj_t_field: Option<usize>,

    // TrueF/FalseF functions
    pub true_f_formula: Option<usize>,
    pub false_f_formula: Option<usize>,

    // EqF functions
    pub eq_f_formula: Option<usize>,
    pub eq_f_lhs: Option<usize>,
    pub eq_f_rhs: Option<usize>,

    // RelF functions
    pub rel_f_formula: Option<usize>,
    pub rel_f_arg: Option<usize>,
    pub rel_f_rel: Option<usize>,

    // ConjF functions
    pub conj_f_formula: Option<usize>,

    // ConjArm functions
    pub conj_arm_conj: Option<usize>,
    pub conj_arm_child: Option<usize>,

    // DisjF functions
    pub disj_f_formula: Option<usize>,

    // DisjArm functions
    pub disj_arm_disj: Option<usize>,
    pub disj_arm_child: Option<usize>,

    // ExistsF functions
    pub exists_f_formula: Option<usize>,
    pub exists_f_binder: Option<usize>,
    pub exists_f_body: Option<usize>,
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
            rel_tuple_arg: sig.lookup_sort("RelTupleArg"),
            sequent: sig.lookup_sort("Sequent"),
            param: sig.lookup_sort("Param"),
            dsort: sig.lookup_sort("DSort"),
            base_ds: sig.lookup_sort("BaseDS"),
            prod_ds: sig.lookup_sort("ProdDS"),
            field: sig.lookup_sort("Field"),
            binder: sig.lookup_sort("Binder"),
            term: sig.lookup_sort("Term"),
            formula: sig.lookup_sort("Formula"),
            ctx_var: sig.lookup_sort("CtxVar"),
            var_t: sig.lookup_sort("VarT"),
            app_t: sig.lookup_sort("AppT"),
            record_t: sig.lookup_sort("RecordT"),
            rec_entry: sig.lookup_sort("RecEntry"),
            proj_t: sig.lookup_sort("ProjT"),
            true_f: sig.lookup_sort("TrueF"),
            false_f: sig.lookup_sort("FalseF"),
            eq_f: sig.lookup_sort("EqF"),
            rel_f: sig.lookup_sort("RelF"),
            conj_f: sig.lookup_sort("ConjF"),
            conj_arm: sig.lookup_sort("ConjArm"),
            disj_f: sig.lookup_sort("DisjF"),
            disj_arm: sig.lookup_sort("DisjArm"),
            exists_f: sig.lookup_sort("ExistsF"),
            node: sig.lookup_sort("Node"),
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
            rel_tuple_arg_tuple: sig.lookup_func("RelTupleArg/tuple"),
            rel_tuple_arg_elem: sig.lookup_func("RelTupleArg/elem"),
            rel_tuple_arg_position: sig.lookup_func("RelTupleArg/position"),
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

            // Sequent functions
            sequent_theory: sig.lookup_func("Sequent/theory"),
            sequent_premise: sig.lookup_func("Sequent/premise"),
            sequent_conclusion: sig.lookup_func("Sequent/conclusion"),

            // CtxVar functions
            ctx_var_sequent: sig.lookup_func("CtxVar/sequent"),
            ctx_var_binder: sig.lookup_func("CtxVar/binder"),

            // Binder functions
            binder_type: sig.lookup_func("Binder/type"),

            // Term/Formula to Node embeddings
            term_node: sig.lookup_func("Term/node"),
            formula_node: sig.lookup_func("Formula/node"),

            // VarT functions
            var_t_term: sig.lookup_func("VarT/term"),
            var_t_binder: sig.lookup_func("VarT/binder"),

            // AppT functions
            app_t_term: sig.lookup_func("AppT/term"),
            app_t_func: sig.lookup_func("AppT/func"),
            app_t_arg: sig.lookup_func("AppT/arg"),

            // RecordT functions
            record_t_term: sig.lookup_func("RecordT/term"),

            // RecEntry functions
            rec_entry_record: sig.lookup_func("RecEntry/record"),
            rec_entry_val: sig.lookup_func("RecEntry/val"),
            rec_entry_field: sig.lookup_func("RecEntry/field"),

            // ProjT functions
            proj_t_term: sig.lookup_func("ProjT/term"),
            proj_t_base: sig.lookup_func("ProjT/base"),
            proj_t_field: sig.lookup_func("ProjT/field"),

            // TrueF/FalseF functions
            true_f_formula: sig.lookup_func("TrueF/formula"),
            false_f_formula: sig.lookup_func("FalseF/formula"),

            // EqF functions
            eq_f_formula: sig.lookup_func("EqF/formula"),
            eq_f_lhs: sig.lookup_func("EqF/lhs"),
            eq_f_rhs: sig.lookup_func("EqF/rhs"),

            // RelF functions
            rel_f_formula: sig.lookup_func("RelF/formula"),
            rel_f_arg: sig.lookup_func("RelF/arg"),
            rel_f_rel: sig.lookup_func("RelF/rel"),

            // ConjF functions
            conj_f_formula: sig.lookup_func("ConjF/formula"),

            // ConjArm functions
            conj_arm_conj: sig.lookup_func("ConjArm/conj"),
            conj_arm_child: sig.lookup_func("ConjArm/child"),

            // DisjF functions
            disj_f_formula: sig.lookup_func("DisjF/formula"),

            // DisjArm functions
            disj_arm_disj: sig.lookup_func("DisjArm/disj"),
            disj_arm_child: sig.lookup_func("DisjArm/child"),

            // ExistsF functions
            exists_f_formula: sig.lookup_func("ExistsF/formula"),
            exists_f_binder: sig.lookup_func("ExistsF/binder"),
            exists_f_body: sig.lookup_func("ExistsF/body"),
        }
    }
}
