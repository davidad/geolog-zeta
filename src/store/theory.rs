//! Theory operations for the Store.
//!
//! Creating, extending, and modifying theories in the GeologMeta structure.

use std::collections::HashMap;

use crate::core::{DerivedSort, Signature};
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

        for (field_name, field_dsort) in fields {
            let field_slid = self.add_element_qualified(
                field_sort,
                vec![self.get_element_name(theory), field_name.clone()],
            );
            self.define_func(prod_func, field_slid, prod_ds_slid)?;
            self.define_func(type_func, field_slid, *field_dsort)?;
        }

        Ok(dsort_slid)
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
            let domain_dsort = self.persist_derived_sort(theory, &func_sym.domain, &dsort_slids)?;
            let codomain_dsort = self.persist_derived_sort(theory, &func_sym.codomain, &dsort_slids)?;
            let func_slid = self.add_function(theory, &func_sym.name, domain_dsort, codomain_dsort)?;
            func_slids.insert(func_id, func_slid);
        }

        // 3. Create all Rel elements
        for (rel_id, rel_sym) in signature.relations.iter().enumerate() {
            let domain_dsort = self.persist_derived_sort(theory, &rel_sym.domain, &dsort_slids)?;
            let rel_slid = self.add_relation(theory, &rel_sym.name, domain_dsort)?;
            rel_slids.insert(rel_id, rel_slid);
        }

        Ok(SignaturePersistResult {
            sort_slids,
            dsort_slids,
            func_slids,
            rel_slids,
        })
    }

    /// Convert a DerivedSort to a DSort Slid, creating necessary elements.
    fn persist_derived_sort(
        &mut self,
        theory: Slid,
        ds: &DerivedSort,
        dsort_slids: &HashMap<usize, Slid>,
    ) -> Result<Slid, String> {
        match ds {
            DerivedSort::Base(sort_id) => dsort_slids
                .get(sort_id)
                .copied()
                .ok_or_else(|| format!("Unknown sort id: {}", sort_id)),
            DerivedSort::Product(fields) => {
                if fields.is_empty() {
                    // Unit type - create empty product
                    self.make_product_dsort(theory, &[])
                } else {
                    // Recursively persist field types
                    let mut field_dsorts = Vec::new();
                    for (field_name, field_type) in fields {
                        let field_dsort = self.persist_derived_sort(theory, field_type, dsort_slids)?;
                        field_dsorts.push((field_name.clone(), field_dsort));
                    }
                    self.make_product_dsort(theory, &field_dsorts)
                }
            }
        }
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
}
