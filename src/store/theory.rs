//! Theory operations for the Store.
//!
//! Creating, extending, and modifying theories in the GeologMeta structure.

use std::collections::HashMap;

use crate::core::{DerivedSort, Formula, Sequent, Signature, Term};
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

    /// Create a product DSort with fields
    pub fn make_product_dsort(
        &mut self,
        theory: Slid,
        fields: &[(String, Slid)], // (field_name, field_dsort)
    ) -> Result<Slid, String> {
        let (dsort, _) = self.make_product_dsort_with_fields(theory, fields)?;
        Ok(dsort)
    }

    /// Create a product DSort with fields, returning both the DSort and field Slids
    fn make_product_dsort_with_fields(
        &mut self,
        theory: Slid,
        fields: &[(String, Slid)], // (field_name, field_dsort)
    ) -> Result<(Slid, HashMap<String, Slid>), String> {
        let prod_ds_sort = self.sort_ids.prod_ds.ok_or("ProdDS sort not found")?;
        let dsort_sort = self.sort_ids.dsort.ok_or("DSort sort not found")?;
        let field_sort = self.sort_ids.field.ok_or("Field sort not found")?;

        // Create the DSort element
        let field_names: Vec<_> = fields.iter().map(|(n, _)| n.as_str()).collect();
        let dsort_name = format!("dsort_[{}]", field_names.join(","));
        let dsort_slid = self.add_element(dsort_sort, &dsort_name);

        // Create the ProdDS element
        let prod_ds_slid = self.add_element(prod_ds_sort, &format!("prod_{}", dsort_name));

        let dsort_func = self.func_ids.prod_ds_dsort.ok_or("ProdDS/dsort not found")?;
        self.define_func(dsort_func, prod_ds_slid, dsort_slid)?;

        // Create Field elements
        let prod_func = self.func_ids.field_prod.ok_or("Field/prod not found")?;
        let type_func = self.func_ids.field_type.ok_or("Field/type not found")?;

        let mut field_slids = HashMap::new();
        for (field_name, field_dsort) in fields {
            let field_slid = self.add_element_qualified(
                field_sort,
                vec![self.get_element_name(theory), field_name.clone()],
            );
            self.define_func(prod_func, field_slid, prod_ds_slid)?;
            self.define_func(type_func, field_slid, *field_dsort)?;

            field_slids.insert(field_name.clone(), field_slid);
        }

        Ok((dsort_slid, field_slids))
    }

    /// Persist a full signature to the Store.
    ///
    /// Creates all sorts, functions, and relations in GeologMeta.
    /// Returns a mapping from sort indices to Srt Slids.
    pub fn persist_signature(
        &mut self,
        theory: Slid,
        signature: &Signature,
    ) -> Result<SignaturePersistResult, String> {
        let mut sort_slids: HashMap<usize, Slid> = HashMap::new();
        let mut dsort_slids: HashMap<usize, Slid> = HashMap::new(); // Base DSort for each sort
        let mut func_slids: HashMap<usize, Slid> = HashMap::new();
        let mut rel_slids: HashMap<usize, Slid> = HashMap::new();
        let mut field_slids: HashMap<String, Slid> = HashMap::new();

        // 1. Create all Srt elements and their base DSorts
        for (sort_id, sort_name) in signature.sorts.iter().enumerate() {
            let srt_slid = self.add_sort(theory, sort_name)?;
            sort_slids.insert(sort_id, srt_slid);

            // Create base DSort for this sort
            let dsort_slid = self.make_base_dsort(srt_slid)?;
            dsort_slids.insert(sort_id, dsort_slid);
        }

        // 2. Create all Func elements
        for (func_id, func_sym) in signature.functions.iter().enumerate() {
            let (domain_dsort, dom_fields) =
                self.persist_derived_sort_with_fields(theory, &func_sym.domain, &dsort_slids)?;
            let (codomain_dsort, cod_fields) =
                self.persist_derived_sort_with_fields(theory, &func_sym.codomain, &dsort_slids)?;

            // Collect field slids
            field_slids.extend(dom_fields);
            field_slids.extend(cod_fields);

            let func_slid = self.add_function(theory, &func_sym.name, domain_dsort, codomain_dsort)?;
            func_slids.insert(func_id, func_slid);
        }

        // 3. Create all Rel elements
        for (rel_id, rel_sym) in signature.relations.iter().enumerate() {
            let (domain_dsort, dom_fields) =
                self.persist_derived_sort_with_fields(theory, &rel_sym.domain, &dsort_slids)?;
            field_slids.extend(dom_fields);

            let rel_slid = self.add_relation(theory, &rel_sym.name, domain_dsort)?;
            rel_slids.insert(rel_id, rel_slid);
        }

        Ok(SignaturePersistResult {
            sort_slids,
            dsort_slids,
            func_slids,
            rel_slids,
            field_slids,
        })
    }

    /// Convert a DerivedSort to a DSort Slid, creating necessary elements.
    fn persist_derived_sort(
        &mut self,
        theory: Slid,
        ds: &DerivedSort,
        dsort_slids: &HashMap<usize, Slid>,
    ) -> Result<Slid, String> {
        let (dsort, _) = self.persist_derived_sort_with_fields(theory, ds, dsort_slids)?;
        Ok(dsort)
    }

    /// Convert a DerivedSort to a DSort Slid, also returning field Slids.
    fn persist_derived_sort_with_fields(
        &mut self,
        theory: Slid,
        ds: &DerivedSort,
        dsort_slids: &HashMap<usize, Slid>,
    ) -> Result<(Slid, HashMap<String, Slid>), String> {
        match ds {
            DerivedSort::Base(sort_id) => {
                let dsort = dsort_slids
                    .get(sort_id)
                    .copied()
                    .ok_or_else(|| format!("Unknown sort id: {}", sort_id))?;
                Ok((dsort, HashMap::new()))
            }
            DerivedSort::Product(fields) => {
                if fields.is_empty() {
                    // Unit type - create empty product
                    let dsort = self.make_product_dsort(theory, &[])?;
                    Ok((dsort, HashMap::new()))
                } else {
                    // Recursively persist field types
                    let mut field_dsorts = Vec::new();
                    let mut all_field_slids = HashMap::new();

                    for (field_name, field_type) in fields {
                        let (field_dsort, nested_fields) =
                            self.persist_derived_sort_with_fields(theory, field_type, dsort_slids)?;
                        field_dsorts.push((field_name.clone(), field_dsort));
                        all_field_slids.extend(nested_fields);
                    }

                    let (dsort, new_field_slids) =
                        self.make_product_dsort_with_fields(theory, &field_dsorts)?;
                    all_field_slids.extend(new_field_slids);

                    Ok((dsort, all_field_slids))
                }
            }
        }
    }

    // ================================================================
    // AXIOM PERSISTENCE
    // ================================================================

    /// Create a Binder element with the given type.
    fn persist_binder(
        &mut self,
        name: &str,
        dsort: Slid,
    ) -> Result<Slid, String> {
        let binder_sort = self.sort_ids.binder.ok_or("Binder sort not found")?;
        let binder_slid = self.add_element(binder_sort, &format!("binder_{}", name));

        let type_func = self.func_ids.binder_type.ok_or("Binder/type not found")?;
        self.define_func(type_func, binder_slid, dsort)?;

        Ok(binder_slid)
    }

    /// Persist a Term, returning its Term Slid.
    ///
    /// # Arguments
    /// - `theory`: The theory this term belongs to
    /// - `term`: The term to persist
    /// - `sig_result`: Mapping from signature indices to Slids
    /// - `binders`: Mapping from variable names to their Binder Slids
    pub fn persist_term(
        &mut self,
        theory: Slid,
        term: &Term,
        sig_result: &SignaturePersistResult,
        binders: &HashMap<String, Slid>,
    ) -> Result<Slid, String> {
        let term_sort = self.sort_ids.term.ok_or("Term sort not found")?;
        let node_sort = self.sort_ids.node.ok_or("Node sort not found")?;

        match term {
            Term::Var(name, _sort) => {
                // Create VarT element
                let var_t_sort = self.sort_ids.var_t.ok_or("VarT sort not found")?;
                let term_slid = self.add_element(term_sort, &format!("term_var_{}", name));
                let var_t_slid = self.add_element(var_t_sort, &format!("var_t_{}", name));

                // Link VarT to Term
                let term_func = self.func_ids.var_t_term.ok_or("VarT/term not found")?;
                self.define_func(term_func, var_t_slid, term_slid)?;

                // Link VarT to Binder
                let binder_slid = binders
                    .get(name)
                    .copied()
                    .ok_or_else(|| format!("Unknown variable: {}", name))?;
                let binder_func = self.func_ids.var_t_binder.ok_or("VarT/binder not found")?;
                self.define_func(binder_func, var_t_slid, binder_slid)?;

                // Create Node for scoping
                let node_slid = self.add_element(node_sort, &format!("node_term_var_{}", name));
                let term_node_func = self.func_ids.term_node.ok_or("Term/node not found")?;
                self.define_func(term_node_func, term_slid, node_slid)?;

                Ok(term_slid)
            }

            Term::App(func_id, arg) => {
                // Recursively persist argument
                let arg_slid = self.persist_term(theory, arg, sig_result, binders)?;

                // Create AppT element
                let app_t_sort = self.sort_ids.app_t.ok_or("AppT sort not found")?;
                let term_slid = self.add_element(term_sort, "term_app");
                let app_t_slid = self.add_element(app_t_sort, "app_t");

                // Link AppT to Term
                let term_func = self.func_ids.app_t_term.ok_or("AppT/term not found")?;
                self.define_func(term_func, app_t_slid, term_slid)?;

                // Link AppT to Func
                let func_slid = sig_result
                    .func_slids
                    .get(func_id)
                    .copied()
                    .ok_or_else(|| format!("Unknown function id: {}", func_id))?;
                let func_func = self.func_ids.app_t_func.ok_or("AppT/func not found")?;
                self.define_func(func_func, app_t_slid, func_slid)?;

                // Link AppT to argument Term
                let arg_func = self.func_ids.app_t_arg.ok_or("AppT/arg not found")?;
                self.define_func(arg_func, app_t_slid, arg_slid)?;

                // Create Node for scoping
                let node_slid = self.add_element(node_sort, "node_term_app");
                let term_node_func = self.func_ids.term_node.ok_or("Term/node not found")?;
                self.define_func(term_node_func, term_slid, node_slid)?;

                Ok(term_slid)
            }

            Term::Record(fields) => {
                // Create RecordT element
                let record_t_sort = self.sort_ids.record_t.ok_or("RecordT sort not found")?;
                let rec_entry_sort = self.sort_ids.rec_entry.ok_or("RecEntry sort not found")?;

                let term_slid = self.add_element(term_sort, "term_record");
                let record_t_slid = self.add_element(record_t_sort, "record_t");

                // Link RecordT to Term
                let term_func = self.func_ids.record_t_term.ok_or("RecordT/term not found")?;
                self.define_func(term_func, record_t_slid, term_slid)?;

                // Create RecEntry for each field
                for (field_name, field_term) in fields {
                    let val_slid = self.persist_term(theory, field_term, sig_result, binders)?;

                    let rec_entry_slid =
                        self.add_element(rec_entry_sort, &format!("rec_entry_{}", field_name));

                    // Link to record
                    let record_func = self.func_ids.rec_entry_record.ok_or("RecEntry/record not found")?;
                    self.define_func(record_func, rec_entry_slid, record_t_slid)?;

                    // Link to value
                    let val_func = self.func_ids.rec_entry_val.ok_or("RecEntry/val not found")?;
                    self.define_func(val_func, rec_entry_slid, val_slid)?;

                    // Link to field (need to look up Field Slid by name)
                    if let Some(&field_slid) = sig_result.field_slids.get(field_name) {
                        let field_func = self.func_ids.rec_entry_field.ok_or("RecEntry/field not found")?;
                        self.define_func(field_func, rec_entry_slid, field_slid)?;
                    }
                    // Note: field_slids may not contain all fields if they weren't persisted
                    // (e.g., for inline record types). This is a known limitation.
                }

                // Create Node for scoping
                let node_slid = self.add_element(node_sort, "node_term_record");
                let term_node_func = self.func_ids.term_node.ok_or("Term/node not found")?;
                self.define_func(term_node_func, term_slid, node_slid)?;

                Ok(term_slid)
            }

            Term::Project(base, field_name) => {
                // Recursively persist base term
                let base_slid = self.persist_term(theory, base, sig_result, binders)?;

                // Create ProjT element
                let proj_t_sort = self.sort_ids.proj_t.ok_or("ProjT sort not found")?;
                let term_slid = self.add_element(term_sort, &format!("term_proj_{}", field_name));
                let proj_t_slid = self.add_element(proj_t_sort, &format!("proj_t_{}", field_name));

                // Link ProjT to Term
                let term_func = self.func_ids.proj_t_term.ok_or("ProjT/term not found")?;
                self.define_func(term_func, proj_t_slid, term_slid)?;

                // Link ProjT to base Term
                let base_func = self.func_ids.proj_t_base.ok_or("ProjT/base not found")?;
                self.define_func(base_func, proj_t_slid, base_slid)?;

                // Link ProjT to Field (if we can find it)
                if let Some(&field_slid) = sig_result.field_slids.get(field_name) {
                    let field_func = self.func_ids.proj_t_field.ok_or("ProjT/field not found")?;
                    self.define_func(field_func, proj_t_slid, field_slid)?;
                }

                // Create Node for scoping
                let node_slid = self.add_element(node_sort, &format!("node_term_proj_{}", field_name));
                let term_node_func = self.func_ids.term_node.ok_or("Term/node not found")?;
                self.define_func(term_node_func, term_slid, node_slid)?;

                Ok(term_slid)
            }
        }
    }

    /// Persist a Formula, returning its Formula Slid.
    ///
    /// # Arguments
    /// - `theory`: The theory this formula belongs to
    /// - `formula`: The formula to persist
    /// - `sig_result`: Mapping from signature indices to Slids
    /// - `binders`: Mapping from variable names to their Binder Slids (mutable for Exists)
    pub fn persist_formula(
        &mut self,
        theory: Slid,
        formula: &Formula,
        sig_result: &SignaturePersistResult,
        binders: &mut HashMap<String, Slid>,
    ) -> Result<Slid, String> {
        let formula_sort = self.sort_ids.formula.ok_or("Formula sort not found")?;
        let node_sort = self.sort_ids.node.ok_or("Node sort not found")?;

        match formula {
            Formula::True => {
                let true_f_sort = self.sort_ids.true_f.ok_or("TrueF sort not found")?;
                let formula_slid = self.add_element(formula_sort, "formula_true");
                let true_f_slid = self.add_element(true_f_sort, "true_f");

                let formula_func = self.func_ids.true_f_formula.ok_or("TrueF/formula not found")?;
                self.define_func(formula_func, true_f_slid, formula_slid)?;

                let node_slid = self.add_element(node_sort, "node_formula_true");
                let formula_node_func = self.func_ids.formula_node.ok_or("Formula/node not found")?;
                self.define_func(formula_node_func, formula_slid, node_slid)?;

                Ok(formula_slid)
            }

            Formula::False => {
                let false_f_sort = self.sort_ids.false_f.ok_or("FalseF sort not found")?;
                let formula_slid = self.add_element(formula_sort, "formula_false");
                let false_f_slid = self.add_element(false_f_sort, "false_f");

                let formula_func = self.func_ids.false_f_formula.ok_or("FalseF/formula not found")?;
                self.define_func(formula_func, false_f_slid, formula_slid)?;

                let node_slid = self.add_element(node_sort, "node_formula_false");
                let formula_node_func = self.func_ids.formula_node.ok_or("Formula/node not found")?;
                self.define_func(formula_node_func, formula_slid, node_slid)?;

                Ok(formula_slid)
            }

            Formula::Eq(lhs, rhs) => {
                let lhs_slid = self.persist_term(theory, lhs, sig_result, binders)?;
                let rhs_slid = self.persist_term(theory, rhs, sig_result, binders)?;

                let eq_f_sort = self.sort_ids.eq_f.ok_or("EqF sort not found")?;
                let formula_slid = self.add_element(formula_sort, "formula_eq");
                let eq_f_slid = self.add_element(eq_f_sort, "eq_f");

                let formula_func = self.func_ids.eq_f_formula.ok_or("EqF/formula not found")?;
                self.define_func(formula_func, eq_f_slid, formula_slid)?;

                let lhs_func = self.func_ids.eq_f_lhs.ok_or("EqF/lhs not found")?;
                self.define_func(lhs_func, eq_f_slid, lhs_slid)?;

                let rhs_func = self.func_ids.eq_f_rhs.ok_or("EqF/rhs not found")?;
                self.define_func(rhs_func, eq_f_slid, rhs_slid)?;

                let node_slid = self.add_element(node_sort, "node_formula_eq");
                let formula_node_func = self.func_ids.formula_node.ok_or("Formula/node not found")?;
                self.define_func(formula_node_func, formula_slid, node_slid)?;

                Ok(formula_slid)
            }

            Formula::Rel(rel_id, arg) => {
                let arg_slid = self.persist_term(theory, arg, sig_result, binders)?;

                let rel_f_sort = self.sort_ids.rel_f.ok_or("RelF sort not found")?;
                let formula_slid = self.add_element(formula_sort, "formula_rel");
                let rel_f_slid = self.add_element(rel_f_sort, "rel_f");

                let formula_func = self.func_ids.rel_f_formula.ok_or("RelF/formula not found")?;
                self.define_func(formula_func, rel_f_slid, formula_slid)?;

                let arg_func = self.func_ids.rel_f_arg.ok_or("RelF/arg not found")?;
                self.define_func(arg_func, rel_f_slid, arg_slid)?;

                let rel_slid = sig_result
                    .rel_slids
                    .get(rel_id)
                    .copied()
                    .ok_or_else(|| format!("Unknown relation id: {}", rel_id))?;
                let rel_func = self.func_ids.rel_f_rel.ok_or("RelF/rel not found")?;
                self.define_func(rel_func, rel_f_slid, rel_slid)?;

                let node_slid = self.add_element(node_sort, "node_formula_rel");
                let formula_node_func = self.func_ids.formula_node.ok_or("Formula/node not found")?;
                self.define_func(formula_node_func, formula_slid, node_slid)?;

                Ok(formula_slid)
            }

            Formula::Conj(conjuncts) => {
                let conj_f_sort = self.sort_ids.conj_f.ok_or("ConjF sort not found")?;
                let conj_arm_sort = self.sort_ids.conj_arm.ok_or("ConjArm sort not found")?;

                let formula_slid = self.add_element(formula_sort, "formula_conj");
                let conj_f_slid = self.add_element(conj_f_sort, "conj_f");

                let formula_func = self.func_ids.conj_f_formula.ok_or("ConjF/formula not found")?;
                self.define_func(formula_func, conj_f_slid, formula_slid)?;

                // Persist each conjunct as a ConjArm
                for (i, child_formula) in conjuncts.iter().enumerate() {
                    let child_slid = self.persist_formula(theory, child_formula, sig_result, binders)?;

                    let arm_slid = self.add_element(conj_arm_sort, &format!("conj_arm_{}", i));

                    let conj_func = self.func_ids.conj_arm_conj.ok_or("ConjArm/conj not found")?;
                    self.define_func(conj_func, arm_slid, conj_f_slid)?;

                    let child_func = self.func_ids.conj_arm_child.ok_or("ConjArm/child not found")?;
                    self.define_func(child_func, arm_slid, child_slid)?;
                }

                let node_slid = self.add_element(node_sort, "node_formula_conj");
                let formula_node_func = self.func_ids.formula_node.ok_or("Formula/node not found")?;
                self.define_func(formula_node_func, formula_slid, node_slid)?;

                Ok(formula_slid)
            }

            Formula::Disj(disjuncts) => {
                let disj_f_sort = self.sort_ids.disj_f.ok_or("DisjF sort not found")?;
                let disj_arm_sort = self.sort_ids.disj_arm.ok_or("DisjArm sort not found")?;

                let formula_slid = self.add_element(formula_sort, "formula_disj");
                let disj_f_slid = self.add_element(disj_f_sort, "disj_f");

                let formula_func = self.func_ids.disj_f_formula.ok_or("DisjF/formula not found")?;
                self.define_func(formula_func, disj_f_slid, formula_slid)?;

                // Persist each disjunct as a DisjArm
                for (i, child_formula) in disjuncts.iter().enumerate() {
                    let child_slid = self.persist_formula(theory, child_formula, sig_result, binders)?;

                    let arm_slid = self.add_element(disj_arm_sort, &format!("disj_arm_{}", i));

                    let disj_func = self.func_ids.disj_arm_disj.ok_or("DisjArm/disj not found")?;
                    self.define_func(disj_func, arm_slid, disj_f_slid)?;

                    let child_func = self.func_ids.disj_arm_child.ok_or("DisjArm/child not found")?;
                    self.define_func(child_func, arm_slid, child_slid)?;
                }

                let node_slid = self.add_element(node_sort, "node_formula_disj");
                let formula_node_func = self.func_ids.formula_node.ok_or("Formula/node not found")?;
                self.define_func(formula_node_func, formula_slid, node_slid)?;

                Ok(formula_slid)
            }

            Formula::Exists(var_name, var_sort, body) => {
                let exists_f_sort = self.sort_ids.exists_f.ok_or("ExistsF sort not found")?;

                let formula_slid = self.add_element(formula_sort, &format!("formula_exists_{}", var_name));
                let exists_f_slid = self.add_element(exists_f_sort, &format!("exists_f_{}", var_name));

                let formula_func = self.func_ids.exists_f_formula.ok_or("ExistsF/formula not found")?;
                self.define_func(formula_func, exists_f_slid, formula_slid)?;

                // Create binder for this existential
                let dsort = self.persist_derived_sort(theory, var_sort, &sig_result.dsort_slids)?;
                let binder_slid = self.persist_binder(var_name, dsort)?;

                let binder_func = self.func_ids.exists_f_binder.ok_or("ExistsF/binder not found")?;
                self.define_func(binder_func, exists_f_slid, binder_slid)?;

                // Extend binders for the body
                let old_binder = binders.insert(var_name.clone(), binder_slid);

                // Persist body with extended binders
                let body_slid = self.persist_formula(theory, body, sig_result, binders)?;

                // Restore old binder (if any) for proper scoping
                if let Some(old) = old_binder {
                    binders.insert(var_name.clone(), old);
                } else {
                    binders.remove(var_name);
                }

                let body_func = self.func_ids.exists_f_body.ok_or("ExistsF/body not found")?;
                self.define_func(body_func, exists_f_slid, body_slid)?;

                let node_slid = self.add_element(node_sort, &format!("node_formula_exists_{}", var_name));
                let formula_node_func = self.func_ids.formula_node.ok_or("Formula/node not found")?;
                self.define_func(formula_node_func, formula_slid, node_slid)?;

                Ok(formula_slid)
            }
        }
    }

    /// Persist an axiom (Sequent) to GeologMeta.
    ///
    /// Creates the Sequent element, context variables, premise, and conclusion.
    pub fn persist_axiom(
        &mut self,
        theory: Slid,
        axiom: &Sequent,
        axiom_name: &str,
        sig_result: &SignaturePersistResult,
    ) -> Result<Slid, String> {
        let sequent_sort = self.sort_ids.sequent.ok_or("Sequent sort not found")?;
        let ctx_var_sort = self.sort_ids.ctx_var.ok_or("CtxVar sort not found")?;

        // Create Sequent element
        let sequent_slid = self.add_element_qualified(
            sequent_sort,
            vec![self.get_element_name(theory), axiom_name.to_string()],
        );

        // Link to theory
        let theory_func = self.func_ids.sequent_theory.ok_or("Sequent/theory not found")?;
        self.define_func(theory_func, sequent_slid, theory)?;

        // Create binders for context variables
        let mut binders = HashMap::new();
        for (var_name, var_sort) in &axiom.context.vars {
            let dsort = self.persist_derived_sort(theory, var_sort, &sig_result.dsort_slids)?;
            let binder_slid = self.persist_binder(var_name, dsort)?;
            binders.insert(var_name.clone(), binder_slid);

            // Create CtxVar linking sequent to binder
            let ctx_var_slid = self.add_element(ctx_var_sort, &format!("ctx_var_{}", var_name));

            let sequent_func = self.func_ids.ctx_var_sequent.ok_or("CtxVar/sequent not found")?;
            self.define_func(sequent_func, ctx_var_slid, sequent_slid)?;

            let binder_func = self.func_ids.ctx_var_binder.ok_or("CtxVar/binder not found")?;
            self.define_func(binder_func, ctx_var_slid, binder_slid)?;
        }

        // Persist premise formula
        let premise_slid = self.persist_formula(theory, &axiom.premise, sig_result, &mut binders)?;
        let premise_func = self.func_ids.sequent_premise.ok_or("Sequent/premise not found")?;
        self.define_func(premise_func, sequent_slid, premise_slid)?;

        // Persist conclusion formula
        let conclusion_slid = self.persist_formula(theory, &axiom.conclusion, sig_result, &mut binders)?;
        let conclusion_func = self.func_ids.sequent_conclusion.ok_or("Sequent/conclusion not found")?;
        self.define_func(conclusion_func, sequent_slid, conclusion_slid)?;

        Ok(sequent_slid)
    }

    /// Persist all axioms from a Theory to GeologMeta.
    pub fn persist_axioms(
        &mut self,
        theory: Slid,
        axioms: &[Sequent],
        axiom_names: &[String],
        sig_result: &SignaturePersistResult,
    ) -> Result<Vec<Slid>, String> {
        let mut axiom_slids = Vec::new();
        for (axiom, name) in axioms.iter().zip(axiom_names.iter()) {
            let slid = self.persist_axiom(theory, axiom, name, sig_result)?;
            axiom_slids.push(slid);
        }
        Ok(axiom_slids)
    }
}

/// Result of persisting a signature to GeologMeta.
///
/// Maps from local indices (as used in Signature) to Slids in GeologMeta.
#[derive(Debug)]
pub struct SignaturePersistResult {
    /// Sort index -> Srt Slid
    pub sort_slids: HashMap<usize, Slid>,
    /// Sort index -> base DSort Slid for that sort
    pub dsort_slids: HashMap<usize, Slid>,
    /// Function index -> Func Slid
    pub func_slids: HashMap<usize, Slid>,
    /// Relation index -> Rel Slid
    pub rel_slids: HashMap<usize, Slid>,
    /// Field name -> Field Slid (for record types in domains)
    pub field_slids: HashMap<String, Slid>,
}
