//! Bootstrap query methods for GeologMeta.
//!
//! These are temporary hardcoded query implementations that will be replaced
//! by the proper query engine (geolog-7tt). They exist to allow eliminating
//! ElaboratedTheory from the codebase before the query engine is ready.
//!
//! TODO(geolog-ubi): Replace these with proper query engine calls.

use std::collections::HashMap;

use crate::core::{DerivedSort, ElaboratedTheory, Signature, Theory};
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

impl Store {
    /// Query all sorts belonging to a theory.
    ///
    /// Returns (name, slid) for each Srt where Srt/theory == theory_slid.
    pub fn query_theory_sorts(&self, theory_slid: Slid) -> Vec<SortInfo> {
        let Some(srt_sort) = self.sort_ids.srt else {
            return vec![];
        };
        let Some(theory_func) = self.func_ids.srt_theory else {
            return vec![];
        };

        let mut result = Vec::new();
        for srt_slid in self.elements_of_sort(srt_sort) {
            if self.get_func(theory_func, srt_slid) == Some(theory_slid) {
                let name = self.get_element_name(srt_slid);
                // Extract just the sort name (last component of qualified name)
                let short_name = name.rsplit('/').next().unwrap_or(&name).to_string();
                result.push(SortInfo {
                    name: short_name,
                    slid: srt_slid,
                });
            }
        }
        result
    }

    /// Query all functions belonging to a theory.
    ///
    /// Returns FuncInfo for each Func where Func/theory == theory_slid.
    pub fn query_theory_funcs(&self, theory_slid: Slid) -> Vec<FuncInfo> {
        let Some(func_sort) = self.sort_ids.func else {
            return vec![];
        };
        let Some(theory_func) = self.func_ids.func_theory else {
            return vec![];
        };
        let Some(dom_func) = self.func_ids.func_dom else {
            return vec![];
        };
        let Some(cod_func) = self.func_ids.func_cod else {
            return vec![];
        };

        let mut result = Vec::new();
        for func_slid in self.elements_of_sort(func_sort) {
            if self.get_func(theory_func, func_slid) == Some(theory_slid) {
                let name = self.get_element_name(func_slid);
                let short_name = name.rsplit('/').next().unwrap_or(&name).to_string();

                // Get domain and codomain DSorts
                let domain = self
                    .get_func(dom_func, func_slid)
                    .map(|ds| self.resolve_dsort(ds))
                    .unwrap_or(DerivedSort::Product(vec![]));
                let codomain = self
                    .get_func(cod_func, func_slid)
                    .map(|ds| self.resolve_dsort(ds))
                    .unwrap_or(DerivedSort::Product(vec![]));

                result.push(FuncInfo {
                    name: short_name,
                    slid: func_slid,
                    domain,
                    codomain,
                });
            }
        }
        result
    }

    /// Query all relations belonging to a theory.
    ///
    /// Returns RelInfo for each Rel where Rel/theory == theory_slid.
    pub fn query_theory_rels(&self, theory_slid: Slid) -> Vec<RelInfo> {
        let Some(rel_sort) = self.sort_ids.rel else {
            return vec![];
        };
        let Some(theory_func) = self.func_ids.rel_theory else {
            return vec![];
        };
        let Some(dom_func) = self.func_ids.rel_dom else {
            return vec![];
        };

        let mut result = Vec::new();
        for rel_slid in self.elements_of_sort(rel_sort) {
            if self.get_func(theory_func, rel_slid) == Some(theory_slid) {
                let name = self.get_element_name(rel_slid);
                let short_name = name.rsplit('/').next().unwrap_or(&name).to_string();

                let domain = self
                    .get_func(dom_func, rel_slid)
                    .map(|ds| self.resolve_dsort(ds))
                    .unwrap_or(DerivedSort::Product(vec![]));

                result.push(RelInfo {
                    name: short_name,
                    slid: rel_slid,
                    domain,
                });
            }
        }
        result
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

    /// Resolve a DSort slid to a DerivedSort.
    ///
    /// DSorts in GeologMeta are represented as either BaseDS or ProdDS elements.
    /// This traverses the structure to build the corresponding DerivedSort.
    fn resolve_dsort(&self, dsort_slid: Slid) -> DerivedSort {
        // Check if it's a BaseDS
        if let Some(base_ds_sort) = self.sort_ids.base_ds {
            if let Some(srt_func) = self.func_ids.base_ds_srt {
                // Check all BaseDS elements to find one whose dsort matches
                for base_slid in self.elements_of_sort(base_ds_sort) {
                    if let Some(dsort_func) = self.func_ids.base_ds_dsort {
                        if self.get_func(dsort_func, base_slid) == Some(dsort_slid) {
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
            }
        }

        // Check if it's a ProdDS
        if let Some(prod_ds_sort) = self.sort_ids.prod_ds {
            for prod_slid in self.elements_of_sort(prod_ds_sort) {
                if let Some(dsort_func) = self.func_ids.prod_ds_dsort {
                    if self.get_func(dsort_func, prod_slid) == Some(dsort_slid) {
                        // Found the ProdDS, get its fields
                        let fields = self.query_prod_fields(prod_slid);
                        return DerivedSort::Product(fields);
                    }
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
        for info in func_infos {
            let domain = remap_derived_sort(&info.domain, &srt_slid_to_idx);
            let codomain = remap_derived_sort(&info.codomain, &srt_slid_to_idx);
            signature.add_function(info.name, domain, codomain);
        }

        // Add relations with remapped DerivedSorts
        for info in rel_infos {
            let domain = remap_derived_sort(&info.domain, &srt_slid_to_idx);
            signature.add_relation(info.name, domain);
        }

        let theory = Theory {
            name: theory_name,
            signature,
            axioms: vec![], // TODO: persist and reconstruct axioms
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
        for (name, slid) in self.query_committed_theories() {
            if let Some(theory) = self.reconstruct_theory(slid) {
                result.insert(name, std::rc::Rc::new(theory));
            }
        }
        result
    }
}
