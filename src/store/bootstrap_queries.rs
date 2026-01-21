//! Bootstrap query methods for GeologMeta.
//!
//! These methods provide typed query APIs for GeologMeta. They now delegate
//! to the compiled query engine (see query/store_queries.rs) for the core
//! scan+filter operations, with additional lookups for complex fields.
//!
//! TODO(geolog-ubi): Further integrate with the full query engine.

use std::collections::HashMap;

use crate::core::{Context, DerivedSort, ElaboratedTheory, Formula, Sequent, Signature, Term, Theory};
use crate::id::{NumericId, Slid};

use super::append::AppendOps;
use super::Store;

/// Remap a DerivedSort from Slid indices to sort indices.
///
/// During reconstruction, DerivedSort::Base contains Slid.index() values
/// (from resolve_dsort). This function maps them to proper sort indices
/// using the provided mapping.
fn remap_derived_sort(
    ds: &DerivedSort,
    srt_slid_to_idx: &HashMap<usize, usize>,
) -> DerivedSort {
    match ds {
        DerivedSort::Base(slid_idx) => {
            // The slid_idx is a Slid.index() from resolve_dsort
            // Map it to a sort index
            if let Some(&sort_idx) = srt_slid_to_idx.get(slid_idx) {
                DerivedSort::Base(sort_idx)
            } else {
                // Fallback: assume it's already a sort index
                DerivedSort::Base(*slid_idx)
            }
        }
        DerivedSort::Product(fields) => {
            let remapped: Vec<_> = fields
                .iter()
                .map(|(name, field_ds)| {
                    (name.clone(), remap_derived_sort(field_ds, srt_slid_to_idx))
                })
                .collect();
            DerivedSort::Product(remapped)
        }
    }
}

/// Information about a sort in a theory
#[derive(Debug, Clone)]
pub struct SortInfo {
    pub name: String,
    pub slid: Slid,
}

/// Information about a function in a theory
#[derive(Debug, Clone)]
pub struct FuncInfo {
    pub name: String,
    pub slid: Slid,
    pub domain: DerivedSort,
    pub codomain: DerivedSort,
}

/// Information about a relation in a theory
#[derive(Debug, Clone)]
pub struct RelInfo {
    pub name: String,
    pub slid: Slid,
    pub domain: DerivedSort,
}

/// Information about a sequent (axiom) in a theory
#[derive(Debug, Clone)]
pub struct SequentInfo {
    pub name: String,
    pub slid: Slid,
    pub premise_slid: Option<Slid>,
    pub conclusion_slid: Option<Slid>,
}

/// Information about a context variable in a sequent
#[derive(Debug, Clone)]
pub struct CtxVarInfo {
    pub slid: Slid,
    pub binder_slid: Option<Slid>,
}

impl Store {
    /// Query all sorts belonging to a theory.
    ///
    /// Returns (name, slid) for each Srt where Srt/theory == theory_slid.
    /// Delegates to the compiled query engine.
    pub fn query_theory_sorts(&self, theory_slid: Slid) -> Vec<SortInfo> {
        // Delegate to compiled query engine
        self.query_theory_sorts_compiled(theory_slid)
    }

    /// Query all functions belonging to a theory.
    ///
    /// Returns FuncInfo for each Func where Func/theory == theory_slid.
    /// Delegates to the compiled query engine.
    pub fn query_theory_funcs(&self, theory_slid: Slid) -> Vec<FuncInfo> {
        // Delegate to compiled query engine
        self.query_theory_funcs_compiled(theory_slid)
    }

    /// Query all relations belonging to a theory.
    ///
    /// Returns RelInfo for each Rel where Rel/theory == theory_slid.
    /// Delegates to the compiled query engine.
    pub fn query_theory_rels(&self, theory_slid: Slid) -> Vec<RelInfo> {
        // Delegate to compiled query engine
        self.query_theory_rels_compiled(theory_slid)
    }

    /// Look up a sort by name within a theory.
    pub fn lookup_sort_by_name(&self, theory_slid: Slid, name: &str) -> Option<Slid> {
        self.query_theory_sorts(theory_slid)
            .into_iter()
            .find(|s| s.name == name)
            .map(|s| s.slid)
    }

    /// Look up a function by name within a theory.
    pub fn lookup_func_by_name(&self, theory_slid: Slid, name: &str) -> Option<Slid> {
        self.query_theory_funcs(theory_slid)
            .into_iter()
            .find(|f| f.name == name)
            .map(|f| f.slid)
    }

    /// Look up a relation by name within a theory.
    pub fn lookup_rel_by_name(&self, theory_slid: Slid, name: &str) -> Option<Slid> {
        self.query_theory_rels(theory_slid)
            .into_iter()
            .find(|r| r.name == name)
            .map(|r| r.slid)
    }

    /// Query all sequents (axioms) belonging to a theory.
    pub fn query_theory_sequents(&self, theory_slid: Slid) -> Vec<SequentInfo> {
        let Some(sequent_sort) = self.sort_ids.sequent else {
            return vec![];
        };
        let Some(theory_func) = self.func_ids.sequent_theory else {
            return vec![];
        };

        let mut results = Vec::new();
        for sequent_slid in self.elements_of_sort(sequent_sort) {
            if self.get_func(theory_func, sequent_slid) == Some(theory_slid) {
                let name = self.get_element_name(sequent_slid);
                let short_name = name.rsplit('/').next().unwrap_or(&name).to_string();

                let premise_slid = self
                    .func_ids
                    .sequent_premise
                    .and_then(|f| self.get_func(f, sequent_slid));
                let conclusion_slid = self
                    .func_ids
                    .sequent_conclusion
                    .and_then(|f| self.get_func(f, sequent_slid));

                results.push(SequentInfo {
                    name: short_name,
                    slid: sequent_slid,
                    premise_slid,
                    conclusion_slid,
                });
            }
        }
        results
    }

    /// Query context variables for a sequent.
    fn query_sequent_ctx_vars(&self, sequent_slid: Slid) -> Vec<CtxVarInfo> {
        let Some(ctx_var_sort) = self.sort_ids.ctx_var else {
            return vec![];
        };
        let Some(sequent_func) = self.func_ids.ctx_var_sequent else {
            return vec![];
        };

        let mut results = Vec::new();
        for ctx_var_slid in self.elements_of_sort(ctx_var_sort) {
            if self.get_func(sequent_func, ctx_var_slid) == Some(sequent_slid) {
                let binder_slid = self
                    .func_ids
                    .ctx_var_binder
                    .and_then(|f| self.get_func(f, ctx_var_slid));

                results.push(CtxVarInfo {
                    slid: ctx_var_slid,
                    binder_slid,
                });
            }
        }
        results
    }

    /// Get the binder's type (DSort slid).
    fn get_binder_type(&self, binder_slid: Slid) -> Option<Slid> {
        self.func_ids
            .binder_type
            .and_then(|f| self.get_func(f, binder_slid))
    }

    /// Reconstruct a Term from its Term slid.
    fn reconstruct_term(
        &self,
        term_slid: Slid,
        binder_to_var: &HashMap<Slid, (String, DerivedSort)>,
        func_to_idx: &HashMap<Slid, usize>,
        srt_slid_to_idx: &HashMap<usize, usize>,
    ) -> Option<Term> {
        // Check VarT
        if let Some(var_t_sort) = self.sort_ids.var_t {
            for var_t_slid in self.elements_of_sort(var_t_sort) {
                if let Some(term_func) = self.func_ids.var_t_term {
                    if self.get_func(term_func, var_t_slid) == Some(term_slid) {
                        // Found a VarT for this term
                        if let Some(binder_func) = self.func_ids.var_t_binder {
                            if let Some(binder_slid) = self.get_func(binder_func, var_t_slid) {
                                if let Some((var_name, var_sort)) = binder_to_var.get(&binder_slid) {
                                    return Some(Term::Var(var_name.clone(), var_sort.clone()));
                                }
                            }
                        }
                    }
                }
            }
        }

        // Check AppT
        if let Some(app_t_sort) = self.sort_ids.app_t {
            for app_t_slid in self.elements_of_sort(app_t_sort) {
                if let Some(term_func) = self.func_ids.app_t_term {
                    if self.get_func(term_func, app_t_slid) == Some(term_slid) {
                        // Found an AppT for this term
                        let func_slid = self
                            .func_ids
                            .app_t_func
                            .and_then(|f| self.get_func(f, app_t_slid))?;
                        let func_idx = *func_to_idx.get(&func_slid)?;

                        let arg_term_slid = self
                            .func_ids
                            .app_t_arg
                            .and_then(|f| self.get_func(f, app_t_slid))?;
                        let arg = self.reconstruct_term(
                            arg_term_slid,
                            binder_to_var,
                            func_to_idx,
                            srt_slid_to_idx,
                        )?;

                        return Some(Term::App(func_idx, Box::new(arg)));
                    }
                }
            }
        }

        // Check RecordT
        if let Some(record_t_sort) = self.sort_ids.record_t {
            for record_t_slid in self.elements_of_sort(record_t_sort) {
                if let Some(term_func) = self.func_ids.record_t_term {
                    if self.get_func(term_func, record_t_slid) == Some(term_slid) {
                        // Found a RecordT for this term - collect entries
                        let mut fields = Vec::new();
                        if let Some(rec_entry_sort) = self.sort_ids.rec_entry {
                            for rec_entry_slid in self.elements_of_sort(rec_entry_sort) {
                                if let Some(record_func) = self.func_ids.rec_entry_record {
                                    if self.get_func(record_func, rec_entry_slid)
                                        == Some(record_t_slid)
                                    {
                                        // Get field name (from Field)
                                        let field_name = self
                                            .func_ids
                                            .rec_entry_field
                                            .and_then(|f| self.get_func(f, rec_entry_slid))
                                            .map(|field_slid| {
                                                let name = self.get_element_name(field_slid);
                                                name.rsplit('/').next().unwrap_or(&name).to_string()
                                            })
                                            .unwrap_or_default();

                                        // Get value term
                                        if let Some(val_slid) = self
                                            .func_ids
                                            .rec_entry_val
                                            .and_then(|f| self.get_func(f, rec_entry_slid))
                                        {
                                            if let Some(val_term) = self.reconstruct_term(
                                                val_slid,
                                                binder_to_var,
                                                func_to_idx,
                                                srt_slid_to_idx,
                                            ) {
                                                fields.push((field_name, val_term));
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        return Some(Term::Record(fields));
                    }
                }
            }
        }

        // Check ProjT
        if let Some(proj_t_sort) = self.sort_ids.proj_t {
            for proj_t_slid in self.elements_of_sort(proj_t_sort) {
                if let Some(term_func) = self.func_ids.proj_t_term {
                    if self.get_func(term_func, proj_t_slid) == Some(term_slid) {
                        // Get base term
                        let base_slid = self
                            .func_ids
                            .proj_t_base
                            .and_then(|f| self.get_func(f, proj_t_slid))?;
                        let base =
                            self.reconstruct_term(base_slid, binder_to_var, func_to_idx, srt_slid_to_idx)?;

                        // Get field name
                        let field_name = self
                            .func_ids
                            .proj_t_field
                            .and_then(|f| self.get_func(f, proj_t_slid))
                            .map(|field_slid| {
                                let name = self.get_element_name(field_slid);
                                name.rsplit('/').next().unwrap_or(&name).to_string()
                            })
                            .unwrap_or_default();

                        return Some(Term::Project(Box::new(base), field_name));
                    }
                }
            }
        }

        None
    }

    /// Reconstruct a Formula from its Formula slid.
    fn reconstruct_formula(
        &self,
        formula_slid: Slid,
        binder_to_var: &mut HashMap<Slid, (String, DerivedSort)>,
        func_to_idx: &HashMap<Slid, usize>,
        rel_to_idx: &HashMap<Slid, usize>,
        srt_slid_to_idx: &HashMap<usize, usize>,
    ) -> Option<Formula> {
        // Check TrueF
        if let Some(true_f_sort) = self.sort_ids.true_f {
            for true_f_slid in self.elements_of_sort(true_f_sort) {
                if let Some(formula_func) = self.func_ids.true_f_formula {
                    if self.get_func(formula_func, true_f_slid) == Some(formula_slid) {
                        return Some(Formula::True);
                    }
                }
            }
        }

        // Check FalseF
        if let Some(false_f_sort) = self.sort_ids.false_f {
            for false_f_slid in self.elements_of_sort(false_f_sort) {
                if let Some(formula_func) = self.func_ids.false_f_formula {
                    if self.get_func(formula_func, false_f_slid) == Some(formula_slid) {
                        return Some(Formula::False);
                    }
                }
            }
        }

        // Check EqF
        if let Some(eq_f_sort) = self.sort_ids.eq_f {
            for eq_f_slid in self.elements_of_sort(eq_f_sort) {
                if let Some(formula_func) = self.func_ids.eq_f_formula {
                    if self.get_func(formula_func, eq_f_slid) == Some(formula_slid) {
                        let lhs_slid = self
                            .func_ids
                            .eq_f_lhs
                            .and_then(|f| self.get_func(f, eq_f_slid))?;
                        let rhs_slid = self
                            .func_ids
                            .eq_f_rhs
                            .and_then(|f| self.get_func(f, eq_f_slid))?;

                        let lhs =
                            self.reconstruct_term(lhs_slid, binder_to_var, func_to_idx, srt_slid_to_idx)?;
                        let rhs =
                            self.reconstruct_term(rhs_slid, binder_to_var, func_to_idx, srt_slid_to_idx)?;

                        return Some(Formula::Eq(lhs, rhs));
                    }
                }
            }
        }

        // Check RelF
        if let Some(rel_f_sort) = self.sort_ids.rel_f {
            for rel_f_slid in self.elements_of_sort(rel_f_sort) {
                if let Some(formula_func) = self.func_ids.rel_f_formula {
                    if self.get_func(formula_func, rel_f_slid) == Some(formula_slid) {
                        let rel_slid = self
                            .func_ids
                            .rel_f_rel
                            .and_then(|f| self.get_func(f, rel_f_slid))?;
                        let rel_idx = *rel_to_idx.get(&rel_slid)?;

                        let arg_slid = self
                            .func_ids
                            .rel_f_arg
                            .and_then(|f| self.get_func(f, rel_f_slid))?;
                        let arg =
                            self.reconstruct_term(arg_slid, binder_to_var, func_to_idx, srt_slid_to_idx)?;

                        return Some(Formula::Rel(rel_idx, arg));
                    }
                }
            }
        }

        // Check ConjF
        if let Some(conj_f_sort) = self.sort_ids.conj_f {
            for conj_f_slid in self.elements_of_sort(conj_f_sort) {
                if let Some(formula_func) = self.func_ids.conj_f_formula {
                    if self.get_func(formula_func, conj_f_slid) == Some(formula_slid) {
                        // Collect conjuncts from ConjArm
                        let mut conjuncts = Vec::new();
                        if let Some(conj_arm_sort) = self.sort_ids.conj_arm {
                            for arm_slid in self.elements_of_sort(conj_arm_sort) {
                                if let Some(conj_func) = self.func_ids.conj_arm_conj {
                                    if self.get_func(conj_func, arm_slid) == Some(conj_f_slid) {
                                        if let Some(child_slid) = self
                                            .func_ids
                                            .conj_arm_child
                                            .and_then(|f| self.get_func(f, arm_slid))
                                        {
                                            if let Some(child) = self.reconstruct_formula(
                                                child_slid,
                                                binder_to_var,
                                                func_to_idx,
                                                rel_to_idx,
                                                srt_slid_to_idx,
                                            ) {
                                                conjuncts.push(child);
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        return Some(Formula::Conj(conjuncts));
                    }
                }
            }
        }

        // Check DisjF
        if let Some(disj_f_sort) = self.sort_ids.disj_f {
            for disj_f_slid in self.elements_of_sort(disj_f_sort) {
                if let Some(formula_func) = self.func_ids.disj_f_formula {
                    if self.get_func(formula_func, disj_f_slid) == Some(formula_slid) {
                        // Collect disjuncts from DisjArm
                        let mut disjuncts = Vec::new();
                        if let Some(disj_arm_sort) = self.sort_ids.disj_arm {
                            for arm_slid in self.elements_of_sort(disj_arm_sort) {
                                if let Some(disj_func) = self.func_ids.disj_arm_disj {
                                    if self.get_func(disj_func, arm_slid) == Some(disj_f_slid) {
                                        if let Some(child_slid) = self
                                            .func_ids
                                            .disj_arm_child
                                            .and_then(|f| self.get_func(f, arm_slid))
                                        {
                                            if let Some(child) = self.reconstruct_formula(
                                                child_slid,
                                                binder_to_var,
                                                func_to_idx,
                                                rel_to_idx,
                                                srt_slid_to_idx,
                                            ) {
                                                disjuncts.push(child);
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        return Some(Formula::Disj(disjuncts));
                    }
                }
            }
        }

        // Check ExistsF
        if let Some(exists_f_sort) = self.sort_ids.exists_f {
            for exists_f_slid in self.elements_of_sort(exists_f_sort) {
                if let Some(formula_func) = self.func_ids.exists_f_formula {
                    if self.get_func(formula_func, exists_f_slid) == Some(formula_slid) {
                        // Get the binder
                        let binder_slid = self
                            .func_ids
                            .exists_f_binder
                            .and_then(|f| self.get_func(f, exists_f_slid))?;

                        // Get binder type
                        let dsort_slid = self.get_binder_type(binder_slid)?;
                        let dsort_raw = self.resolve_dsort(dsort_slid);
                        let dsort = remap_derived_sort(&dsort_raw, srt_slid_to_idx);

                        // Get var name from binder element name
                        let binder_name = self.get_element_name(binder_slid);
                        let var_name = binder_name
                            .strip_prefix("binder_")
                            .unwrap_or(&binder_name)
                            .to_string();

                        // Add to binder mapping for body reconstruction
                        binder_to_var.insert(binder_slid, (var_name.clone(), dsort.clone()));

                        // Reconstruct body
                        let body_slid = self
                            .func_ids
                            .exists_f_body
                            .and_then(|f| self.get_func(f, exists_f_slid))?;
                        let body = self.reconstruct_formula(
                            body_slid,
                            binder_to_var,
                            func_to_idx,
                            rel_to_idx,
                            srt_slid_to_idx,
                        )?;

                        return Some(Formula::Exists(var_name, dsort, Box::new(body)));
                    }
                }
            }
        }

        None
    }

    /// Reconstruct an axiom (Sequent) from its SequentInfo.
    fn reconstruct_axiom(
        &self,
        info: &SequentInfo,
        func_to_idx: &HashMap<Slid, usize>,
        rel_to_idx: &HashMap<Slid, usize>,
        srt_slid_to_idx: &HashMap<usize, usize>,
    ) -> Option<Sequent> {
        // Build binder mapping from context variables
        let mut binder_to_var: HashMap<Slid, (String, DerivedSort)> = HashMap::new();
        let mut context = Context::new();

        let ctx_vars = self.query_sequent_ctx_vars(info.slid);
        for cv in ctx_vars {
            if let Some(binder_slid) = cv.binder_slid {
                // Get binder type
                if let Some(dsort_slid) = self.get_binder_type(binder_slid) {
                    let dsort_raw = self.resolve_dsort(dsort_slid);
                    let dsort = remap_derived_sort(&dsort_raw, srt_slid_to_idx);

                    // Get var name from binder element name
                    let binder_name = self.get_element_name(binder_slid);
                    let var_name = binder_name
                        .strip_prefix("binder_")
                        .unwrap_or(&binder_name)
                        .to_string();

                    binder_to_var.insert(binder_slid, (var_name.clone(), dsort.clone()));
                    context = context.extend(var_name, dsort);
                }
            }
        }

        // Reconstruct premise
        let premise = info.premise_slid.and_then(|slid| {
            self.reconstruct_formula(slid, &mut binder_to_var, func_to_idx, rel_to_idx, srt_slid_to_idx)
        })?;

        // Reconstruct conclusion
        let conclusion = info.conclusion_slid.and_then(|slid| {
            self.reconstruct_formula(slid, &mut binder_to_var, func_to_idx, rel_to_idx, srt_slid_to_idx)
        })?;

        Some(Sequent {
            context,
            premise,
            conclusion,
        })
    }

    /// Resolve a DSort slid to a DerivedSort.
    ///
    /// DSorts in GeologMeta are represented as either BaseDS or ProdDS elements.
    /// This traverses the structure to build the corresponding DerivedSort.
    pub fn resolve_dsort(&self, dsort_slid: Slid) -> DerivedSort {
        // Check if it's a BaseDS
        if let Some(base_ds_sort) = self.sort_ids.base_ds
            && let Some(srt_func) = self.func_ids.base_ds_srt {
                // Check all BaseDS elements to find one whose dsort matches
                for base_slid in self.elements_of_sort(base_ds_sort) {
                    if let Some(dsort_func) = self.func_ids.base_ds_dsort
                        && self.get_func(dsort_func, base_slid) == Some(dsort_slid) {
                            // Found the BaseDS, get its Srt
                            if let Some(srt_slid) = self.get_func(srt_func, base_slid) {
                                // We need to map srt_slid to a sort index...
                                // This is tricky without knowing the theory context.
                                // For bootstrap, we store the slid index and resolve later.
                                return DerivedSort::Base(srt_slid.index());
                            }
                        }
                }
            }

        // Check if it's a ProdDS
        if let Some(prod_ds_sort) = self.sort_ids.prod_ds {
            for prod_slid in self.elements_of_sort(prod_ds_sort) {
                if let Some(dsort_func) = self.func_ids.prod_ds_dsort
                    && self.get_func(dsort_func, prod_slid) == Some(dsort_slid) {
                        // Found the ProdDS, get its fields
                        let fields = self.query_prod_fields(prod_slid);
                        return DerivedSort::Product(fields);
                    }
            }
        }

        // Fallback: empty product (unit type)
        DerivedSort::Product(vec![])
    }

    /// Query the fields of a product DSort.
    fn query_prod_fields(&self, prod_slid: Slid) -> Vec<(String, DerivedSort)> {
        let Some(field_sort) = self.sort_ids.field else {
            return vec![];
        };
        let Some(prod_func) = self.func_ids.field_prod else {
            return vec![];
        };
        let Some(type_func) = self.func_ids.field_type else {
            return vec![];
        };

        let mut fields = Vec::new();
        for field_slid in self.elements_of_sort(field_sort) {
            if self.get_func(prod_func, field_slid) == Some(prod_slid) {
                let name = self.get_element_name(field_slid);
                let short_name = name.rsplit('/').next().unwrap_or(&name).to_string();

                let field_type = self
                    .get_func(type_func, field_slid)
                    .map(|ds| self.resolve_dsort(ds))
                    .unwrap_or(DerivedSort::Product(vec![]));

                fields.push((short_name, field_type));
            }
        }
        fields
    }

    /// Get all theory names that are committed (visible from HEAD).
    pub fn query_committed_theories(&self) -> Vec<(String, Slid)> {
        use super::BindingKind;
        self.list_bindings()
            .into_iter()
            .filter_map(|(name, kind, slid)| {
                if kind == BindingKind::Theory {
                    Some((name, slid))
                } else {
                    None
                }
            })
            .collect()
    }

    /// Get all instance names that are committed (visible from HEAD).
    pub fn query_committed_instances(&self) -> Vec<(String, Slid)> {
        use super::BindingKind;
        self.list_bindings()
            .into_iter()
            .filter_map(|(name, kind, slid)| {
                if kind == BindingKind::Instance {
                    Some((name, slid))
                } else {
                    None
                }
            })
            .collect()
    }

    /// Get all theories in GeologMeta (regardless of commit status).
    ///
    /// This is useful for reconstruction when loading from disk,
    /// where we want to restore all data, not just committed data.
    pub fn query_all_theories(&self) -> Vec<(String, Slid)> {
        let Some(theory_sort) = self.sort_ids.theory else {
            return vec![];
        };

        self.elements_of_sort(theory_sort)
            .into_iter()
            .map(|slid| {
                let name = self.get_element_name(slid);
                (name, slid)
            })
            .collect()
    }

    /// Get all instances in GeologMeta (regardless of commit status).
    ///
    /// This is useful for reconstruction when loading from disk,
    /// where we want to restore all data, not just committed data.
    pub fn query_all_instances(&self) -> Vec<(String, Slid)> {
        let Some(instance_sort) = self.sort_ids.instance else {
            return vec![];
        };

        self.elements_of_sort(instance_sort)
            .into_iter()
            .map(|slid| {
                let name = self.get_element_name(slid);
                (name, slid)
            })
            .collect()
    }

    /// Reconstruct an ElaboratedTheory from persisted GeologMeta data.
    ///
    /// This is a bootstrap method that will be replaced by proper query engine.
    /// It rebuilds the in-memory ElaboratedTheory representation from the
    /// persisted sorts, functions, and relations.
    pub fn reconstruct_theory(&self, theory_slid: Slid) -> Option<ElaboratedTheory> {
        let theory_name = self.get_element_name(theory_slid);

        // Query sorts, functions, relations
        let sort_infos = self.query_theory_sorts(theory_slid);
        let func_infos = self.query_theory_funcs(theory_slid);
        let rel_infos = self.query_theory_rels(theory_slid);

        // Build Srt Slid -> sort index mapping for resolving DerivedSorts
        let mut srt_slid_to_idx: std::collections::HashMap<usize, usize> =
            std::collections::HashMap::new();
        for (idx, info) in sort_infos.iter().enumerate() {
            srt_slid_to_idx.insert(info.slid.index(), idx);
        }

        // Build signature using its constructor methods
        let mut signature = Signature::new();

        // Add sorts
        for info in &sort_infos {
            signature.add_sort(info.name.clone());
        }

        // Add functions with remapped DerivedSorts
        for info in &func_infos {
            let domain = remap_derived_sort(&info.domain, &srt_slid_to_idx);
            let codomain = remap_derived_sort(&info.codomain, &srt_slid_to_idx);
            signature.add_function(info.name.clone(), domain, codomain);
        }

        // Add relations with remapped DerivedSorts
        for info in &rel_infos {
            let domain = remap_derived_sort(&info.domain, &srt_slid_to_idx);
            signature.add_relation(info.name.clone(), domain);
        }

        // Build Func Slid -> func index mapping
        let func_to_idx: HashMap<Slid, usize> = func_infos
            .iter()
            .enumerate()
            .map(|(idx, info)| (info.slid, idx))
            .collect();

        // Build Rel Slid -> rel index mapping
        let rel_to_idx: HashMap<Slid, usize> = rel_infos
            .iter()
            .enumerate()
            .map(|(idx, info)| (info.slid, idx))
            .collect();

        // Query and reconstruct axioms
        let sequent_infos = self.query_theory_sequents(theory_slid);
        let mut axioms = Vec::new();
        let mut axiom_names = Vec::new();

        for info in &sequent_infos {
            if let Some(axiom) = self.reconstruct_axiom(info, &func_to_idx, &rel_to_idx, &srt_slid_to_idx) {
                axiom_names.push(info.name.clone());
                axioms.push(axiom);
            }
        }

        let theory = Theory {
            name: theory_name,
            signature,
            axioms,
            axiom_names,
        };

        Some(ElaboratedTheory {
            params: vec![], // TODO: persist and reconstruct params
            theory,
        })
    }

    /// Reconstruct all persisted theories.
    ///
    /// Returns a map from theory name to ElaboratedTheory.
    pub fn reconstruct_all_theories(
        &self,
    ) -> std::collections::HashMap<String, std::rc::Rc<ElaboratedTheory>> {
        let mut result = std::collections::HashMap::new();
        // Use query_all_theories to restore ALL theories from disk,
        // not just committed ones
        for (name, slid) in self.query_all_theories() {
            if let Some(theory) = self.reconstruct_theory(slid) {
                result.insert(name, std::rc::Rc::new(theory));
            }
        }
        result
    }

    // ========================================================================
    // Instance queries and reconstruction
    // ========================================================================

    /// Query all elements belonging to an instance.
    /// Delegates to the compiled query engine.
    pub fn query_instance_elems(&self, instance_slid: Slid) -> Vec<ElemInfo> {
        // Delegate to compiled query engine
        self.query_instance_elems_compiled(instance_slid)
    }

    /// Query all function values in an instance.
    /// Delegates to the compiled query engine.
    pub fn query_instance_func_vals(&self, instance_slid: Slid) -> Vec<FuncValInfo> {
        // Delegate to compiled query engine
        self.query_instance_func_vals_compiled(instance_slid)
    }

    /// Query all relation tuples in an instance.
    /// Delegates to the compiled query engine.
    pub fn query_instance_rel_tuples(&self, instance_slid: Slid) -> Vec<RelTupleInfo> {
        // Delegate to compiled query engine
        self.query_instance_rel_tuples_compiled(instance_slid)
    }

    /// Reconstruct an instance (Structure + metadata) from persisted GeologMeta data.
    pub fn reconstruct_instance(
        &self,
        instance_slid: Slid,
    ) -> Option<ReconstructedInstance> {
        let theory_slid = self.get_instance_theory(instance_slid)?;
        let theory = self.reconstruct_theory(theory_slid)?;

        let instance_name = self.get_element_name(instance_slid);
        let num_sorts = theory.theory.signature.sorts.len();

        // Query elements
        let elem_infos = self.query_instance_elems(instance_slid);
        let sort_infos = self.query_theory_sorts(theory_slid);

        // Build Srt Slid -> sort index mapping
        let srt_to_idx: HashMap<Slid, usize> = sort_infos
            .iter()
            .enumerate()
            .map(|(idx, info)| (info.slid, idx))
            .collect();

        // Build Elem Slid -> Structure Slid mapping
        // Structure Slids are assigned sequentially as we add elements
        let mut elem_to_structure_slid: HashMap<Slid, Slid> = HashMap::new();
        let mut structure = crate::core::Structure::new(num_sorts);
        let mut element_names: HashMap<Slid, String> = HashMap::new();

        // Group elements by sort and add to structure
        for elem_info in &elem_infos {
            if let Some(srt_slid) = elem_info.srt_slid
                && let Some(&sort_idx) = srt_to_idx.get(&srt_slid) {
                    // Add element to structure
                    let (structure_slid, _luid) =
                        structure.add_element(&mut crate::universe::Universe::new(), sort_idx);
                    elem_to_structure_slid.insert(elem_info.slid, structure_slid);
                    element_names.insert(structure_slid, elem_info.name.clone());
                }
        }

        // Build srt_slid -> sort index mapping for remapping DerivedSorts
        let srt_slid_to_idx: HashMap<usize, usize> = sort_infos
            .iter()
            .enumerate()
            .map(|(idx, info)| (info.slid.index(), idx))
            .collect();

        // Initialize functions
        let func_infos = self.query_theory_funcs(theory_slid);
        let domain_sort_ids: Vec<Option<usize>> = func_infos
            .iter()
            .map(|f| {
                // Remap the domain from Slid indices to sort indices
                let remapped = remap_derived_sort(&f.domain, &srt_slid_to_idx);
                match remapped {
                    DerivedSort::Base(idx) => Some(idx),
                    DerivedSort::Product(_) => None,
                }
            })
            .collect();
        structure.init_functions(&domain_sort_ids);

        // Initialize relations
        let rel_infos = self.query_theory_rels(theory_slid);
        let arities: Vec<usize> = rel_infos
            .iter()
            .map(|r| {
                // Remap to get correct arity
                let remapped = remap_derived_sort(&r.domain, &srt_slid_to_idx);
                remapped.arity()
            })
            .collect();
        structure.init_relations(&arities);

        // Build Func Slid -> func index mapping
        let func_to_idx: HashMap<Slid, usize> = func_infos
            .iter()
            .enumerate()
            .map(|(idx, info)| (info.slid, idx))
            .collect();

        // Build Rel Slid -> rel index mapping
        let rel_to_idx: HashMap<Slid, usize> = rel_infos
            .iter()
            .enumerate()
            .map(|(idx, info)| (info.slid, idx))
            .collect();

        // Populate function values
        let func_vals = self.query_instance_func_vals(instance_slid);
        for fv in func_vals {
            if let (Some(func_slid), Some(arg_slid), Some(result_slid)) =
                (fv.func_slid, fv.arg_slid, fv.result_slid)
                && let Some(&func_idx) = func_to_idx.get(&func_slid)
                    && let (Some(&arg_struct), Some(&result_struct)) = (
                        elem_to_structure_slid.get(&arg_slid),
                        elem_to_structure_slid.get(&result_slid),
                    ) {
                        let _ = structure.define_function(func_idx, arg_struct, result_struct);
                    }
        }

        // Populate relation tuples
        // NOTE: Currently only reconstructs unary relations.
        // Product domain relations are skipped during persistence.
        let rel_tuples = self.query_instance_rel_tuples(instance_slid);
        for rt in rel_tuples {
            if let (Some(rel_slid), Some(arg_slid)) = (rt.rel_slid, rt.arg_slid)
                && let Some(&rel_idx) = rel_to_idx.get(&rel_slid) {
                    // Check if this is a product-domain relation
                    let is_product = rel_infos
                        .get(rel_idx)
                        .map(|r| r.domain.arity() > 1)
                        .unwrap_or(false);

                    if is_product {
                        // Skip - product domain relations not yet supported
                        continue;
                    }

                    if let Some(&arg_struct) = elem_to_structure_slid.get(&arg_slid) {
                        structure.assert_relation(rel_idx, vec![arg_struct]);
                    }
                }
        }

        Some(ReconstructedInstance {
            name: instance_name,
            theory_name: theory.theory.name.clone(),
            structure,
            element_names,
        })
    }

    /// Reconstruct all persisted instances.
    pub fn reconstruct_all_instances(&self) -> HashMap<String, ReconstructedInstance> {
        let mut result = HashMap::new();
        // Use query_all_instances to restore ALL instances from disk,
        // not just committed ones
        for (name, slid) in self.query_all_instances() {
            if let Some(instance) = self.reconstruct_instance(slid) {
                result.insert(name, instance);
            }
        }
        result
    }
}

/// Information about an element in an instance
#[derive(Debug, Clone)]
pub struct ElemInfo {
    pub name: String,
    pub slid: Slid,
    pub srt_slid: Option<Slid>,
}

/// Information about a function value
#[derive(Debug, Clone)]
pub struct FuncValInfo {
    pub slid: Slid,
    pub func_slid: Option<Slid>,
    pub arg_slid: Option<Slid>,
    pub result_slid: Option<Slid>,
}

/// Information about a relation tuple
#[derive(Debug, Clone)]
pub struct RelTupleInfo {
    pub slid: Slid,
    pub rel_slid: Option<Slid>,
    pub arg_slid: Option<Slid>,
}

/// A reconstructed instance with its structure and metadata
#[derive(Debug)]
pub struct ReconstructedInstance {
    pub name: String,
    pub theory_name: String,
    pub structure: crate::core::Structure,
    pub element_names: HashMap<Slid, String>,
}
