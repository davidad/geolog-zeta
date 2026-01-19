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
    pub fn query_instance_elems(&self, instance_slid: Slid) -> Vec<ElemInfo> {
        let Some(elem_sort) = self.sort_ids.elem else {
            return vec![];
        };
        let Some(instance_func) = self.func_ids.elem_instance else {
            return vec![];
        };
        let Some(sort_func) = self.func_ids.elem_sort else {
            return vec![];
        };

        let mut result = Vec::new();
        for elem_slid in self.elements_of_sort(elem_sort) {
            if self.get_func(instance_func, elem_slid) == Some(instance_slid) {
                let name = self.get_element_name(elem_slid);
                let short_name = name.rsplit('/').next().unwrap_or(&name).to_string();
                let srt_slid = self.get_func(sort_func, elem_slid);

                result.push(ElemInfo {
                    name: short_name,
                    slid: elem_slid,
                    srt_slid,
                });
            }
        }
        result
    }

    /// Query all function values in an instance.
    pub fn query_instance_func_vals(&self, instance_slid: Slid) -> Vec<FuncValInfo> {
        let Some(fv_sort) = self.sort_ids.func_val else {
            return vec![];
        };
        let Some(instance_func) = self.func_ids.func_val_instance else {
            return vec![];
        };
        let Some(func_func) = self.func_ids.func_val_func else {
            return vec![];
        };
        let Some(arg_func) = self.func_ids.func_val_arg else {
            return vec![];
        };
        let Some(result_func) = self.func_ids.func_val_result else {
            return vec![];
        };

        let mut result = Vec::new();
        for fv_slid in self.elements_of_sort(fv_sort) {
            if self.get_func(instance_func, fv_slid) == Some(instance_slid) {
                result.push(FuncValInfo {
                    slid: fv_slid,
                    func_slid: self.get_func(func_func, fv_slid),
                    arg_slid: self.get_func(arg_func, fv_slid),
                    result_slid: self.get_func(result_func, fv_slid),
                });
            }
        }
        result
    }

    /// Query all relation tuples in an instance.
    pub fn query_instance_rel_tuples(&self, instance_slid: Slid) -> Vec<RelTupleInfo> {
        let Some(rt_sort) = self.sort_ids.rel_tuple else {
            return vec![];
        };
        let Some(instance_func) = self.func_ids.rel_tuple_instance else {
            return vec![];
        };
        let Some(rel_func) = self.func_ids.rel_tuple_rel else {
            return vec![];
        };
        let Some(arg_func) = self.func_ids.rel_tuple_arg else {
            return vec![];
        };

        let mut result = Vec::new();
        for rt_slid in self.elements_of_sort(rt_sort) {
            if self.get_func(instance_func, rt_slid) == Some(instance_slid) {
                result.push(RelTupleInfo {
                    slid: rt_slid,
                    rel_slid: self.get_func(rel_func, rt_slid),
                    arg_slid: self.get_func(arg_func, rt_slid),
                });
            }
        }
        result
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
            if let Some(srt_slid) = elem_info.srt_slid {
                if let Some(&sort_idx) = srt_to_idx.get(&srt_slid) {
                    // Add element to structure
                    let (structure_slid, _luid) =
                        structure.add_element(&mut crate::universe::Universe::new(), sort_idx);
                    elem_to_structure_slid.insert(elem_info.slid, structure_slid);
                    element_names.insert(structure_slid, elem_info.name.clone());
                }
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
            {
                if let Some(&func_idx) = func_to_idx.get(&func_slid) {
                    if let (Some(&arg_struct), Some(&result_struct)) = (
                        elem_to_structure_slid.get(&arg_slid),
                        elem_to_structure_slid.get(&result_slid),
                    ) {
                        let _ = structure.define_function(func_idx, arg_struct, result_struct);
                    }
                }
            }
        }

        // Populate relation tuples
        // NOTE: Currently only reconstructs unary relations.
        // Product domain relations are skipped during persistence.
        let rel_tuples = self.query_instance_rel_tuples(instance_slid);
        for rt in rel_tuples {
            if let (Some(rel_slid), Some(arg_slid)) = (rt.rel_slid, rt.arg_slid) {
                if let Some(&rel_idx) = rel_to_idx.get(&rel_slid) {
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
