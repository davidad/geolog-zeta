//! Store query integration: using compiled queries to replace bootstrap_queries.
//!
//! This module provides query methods on Store that use the compiled Query API
//! instead of handcoded iterations. It demonstrates that the Query compiler
//! can replace bootstrap_queries.rs.
//!
//! # Migration Path
//!
//! 1. First, create query versions here that match bootstrap_queries behavior
//! 2. Add tests that validate both produce same results
//! 3. Once validated, swap implementations in bootstrap_queries
//! 4. Eventually deprecate bootstrap_queries in favor of these
//!
//! # Example
//!
//! ```ignore
//! // Old: bootstrap_queries.rs
//! for srt_slid in self.elements_of_sort(srt_sort) {
//!     if self.get_func(theory_func, srt_slid) == Some(theory_slid) { ... }
//! }
//!
//! // New: store_queries.rs using Query compiler
//! let plan = Query::scan(srt_sort)
//!     .filter_eq(theory_func, 0, theory_slid)
//!     .compile();
//! let result = execute(&plan, &store.meta);
//! ```

use crate::core::DerivedSort;
use crate::id::{NumericId, Slid, Uuid};
use crate::store::Store;
use crate::store::append::AppendOps;
use crate::store::bootstrap_queries::{SortInfo, FuncInfo, RelInfo, ElemInfo, FuncValInfo, RelTupleInfo};
use super::backend::execute;
use super::compile::compile_simple_filter;

impl Store {
    /// Get the UUID for an element in GeologMeta by its Slid.
    /// Used for deterministic ordering: UUIDs v7 are time-ordered.
    fn get_element_uuid(&self, slid: Slid) -> Uuid {
        if let Some(&luid) = self.meta.luids.get(slid.index()) {
            self.universe.get(luid).unwrap_or(Uuid::nil())
        } else {
            Uuid::nil()
        }
    }

    /// Query all sorts belonging to a theory (using compiled query engine).
    ///
    /// This is equivalent to `query_theory_sorts` in bootstrap_queries.rs,
    /// but uses the Query compiler instead of handcoded iteration.
    pub fn query_theory_sorts_compiled(&self, theory_slid: Slid) -> Vec<SortInfo> {
        let Some(srt_sort) = self.sort_ids.srt else {
            return vec![];
        };
        let Some(theory_func) = self.func_ids.srt_theory else {
            return vec![];
        };

        // Compile and execute the query
        let plan = compile_simple_filter(srt_sort, theory_func, theory_slid);
        let result = execute(&plan, &self.meta);

        // Convert query results to SortInfo
        let mut infos = Vec::new();
        for tuple in result.tuples.keys() {
            if let Some(&srt_slid) = tuple.first() {
                let name = self.get_element_name(srt_slid);
                let short_name = name.rsplit('/').next().unwrap_or(&name).to_string();
                infos.push(SortInfo {
                    name: short_name,
                    slid: srt_slid,
                });
            }
        }
        // Sort by UUID to ensure deterministic order matching original creation order
        // (UUIDs v7 are time-ordered, so earlier-created elements come first)
        infos.sort_by_key(|info| self.get_element_uuid(info.slid));
        infos
    }

    /// Query all functions belonging to a theory (using compiled query engine).
    ///
    /// This is equivalent to `query_theory_funcs` in bootstrap_queries.rs,
    /// but uses the Query compiler for the initial scan+filter.
    pub fn query_theory_funcs_compiled(&self, theory_slid: Slid) -> Vec<FuncInfo> {
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

        // Compile and execute the query to find matching functions
        let plan = compile_simple_filter(func_sort, theory_func, theory_slid);
        let result = execute(&plan, &self.meta);

        // Convert query results to FuncInfo (with domain/codomain lookups)
        let mut infos = Vec::new();
        for tuple in result.tuples.keys() {
            if let Some(&func_slid) = tuple.first() {
                let name = self.get_element_name(func_slid);
                let short_name = name.rsplit('/').next().unwrap_or(&name).to_string();

                // Get domain and codomain DSorts (using bootstrap logic)
                let domain = self
                    .get_func(dom_func, func_slid)
                    .map(|ds| self.resolve_dsort(ds))
                    .unwrap_or(DerivedSort::Product(vec![]));
                let codomain = self
                    .get_func(cod_func, func_slid)
                    .map(|ds| self.resolve_dsort(ds))
                    .unwrap_or(DerivedSort::Product(vec![]));

                infos.push(FuncInfo {
                    name: short_name,
                    slid: func_slid,
                    domain,
                    codomain,
                });
            }
        }
        // Sort by UUID to ensure deterministic order matching original creation order
        infos.sort_by_key(|info| self.get_element_uuid(info.slid));
        infos
    }

    /// Query all relations belonging to a theory (using compiled query engine).
    ///
    /// This is equivalent to `query_theory_rels` in bootstrap_queries.rs,
    /// but uses the Query compiler for the initial scan+filter.
    pub fn query_theory_rels_compiled(&self, theory_slid: Slid) -> Vec<RelInfo> {
        let Some(rel_sort) = self.sort_ids.rel else {
            return vec![];
        };
        let Some(theory_func) = self.func_ids.rel_theory else {
            return vec![];
        };
        let Some(dom_func) = self.func_ids.rel_dom else {
            return vec![];
        };

        // Compile and execute the query to find matching relations
        let plan = compile_simple_filter(rel_sort, theory_func, theory_slid);
        let result = execute(&plan, &self.meta);

        // Convert query results to RelInfo (with domain lookup)
        let mut infos = Vec::new();
        for tuple in result.tuples.keys() {
            if let Some(&rel_slid) = tuple.first() {
                let name = self.get_element_name(rel_slid);
                let short_name = name.rsplit('/').next().unwrap_or(&name).to_string();

                // Get domain DSort (using bootstrap logic)
                let domain = self
                    .get_func(dom_func, rel_slid)
                    .map(|ds| self.resolve_dsort(ds))
                    .unwrap_or(DerivedSort::Product(vec![]));

                infos.push(RelInfo {
                    name: short_name,
                    slid: rel_slid,
                    domain,
                });
            }
        }
        // Sort by UUID to ensure deterministic order matching original creation order
        infos.sort_by_key(|info| self.get_element_uuid(info.slid));
        infos
    }

    // ========================================================================
    // Instance queries (compiled versions)
    // ========================================================================

    /// Query all elements belonging to an instance (using compiled query engine).
    ///
    /// This is equivalent to `query_instance_elems` in bootstrap_queries.rs,
    /// but uses the Query compiler for the initial scan+filter.
    pub fn query_instance_elems_compiled(&self, instance_slid: Slid) -> Vec<ElemInfo> {
        let Some(elem_sort) = self.sort_ids.elem else {
            return vec![];
        };
        let Some(instance_func) = self.func_ids.elem_instance else {
            return vec![];
        };
        let Some(sort_func) = self.func_ids.elem_sort else {
            return vec![];
        };

        // Compile and execute the query to find matching elements
        let plan = compile_simple_filter(elem_sort, instance_func, instance_slid);
        let result = execute(&plan, &self.meta);

        // Convert query results to ElemInfo
        let mut infos = Vec::new();
        for tuple in result.tuples.keys() {
            if let Some(&elem_slid) = tuple.first() {
                let name = self.get_element_name(elem_slid);
                let short_name = name.rsplit('/').next().unwrap_or(&name).to_string();
                let srt_slid = self.get_func(sort_func, elem_slid);

                infos.push(ElemInfo {
                    name: short_name,
                    slid: elem_slid,
                    srt_slid,
                });
            }
        }
        // Sort by UUID to preserve original creation order
        infos.sort_by_key(|info| self.get_element_uuid(info.slid));
        infos
    }

    /// Query all function values in an instance (using compiled query engine).
    ///
    /// This is equivalent to `query_instance_func_vals` in bootstrap_queries.rs,
    /// but uses the Query compiler for the initial scan+filter.
    pub fn query_instance_func_vals_compiled(&self, instance_slid: Slid) -> Vec<FuncValInfo> {
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

        // Compile and execute the query
        let plan = compile_simple_filter(fv_sort, instance_func, instance_slid);
        let result = execute(&plan, &self.meta);

        // Convert query results to FuncValInfo
        let mut infos = Vec::new();
        for tuple in result.tuples.keys() {
            if let Some(&fv_slid) = tuple.first() {
                infos.push(FuncValInfo {
                    slid: fv_slid,
                    func_slid: self.get_func(func_func, fv_slid),
                    arg_slid: self.get_func(arg_func, fv_slid),
                    result_slid: self.get_func(result_func, fv_slid),
                });
            }
        }
        // Sort by UUID to preserve original creation order
        infos.sort_by_key(|info| self.get_element_uuid(info.slid));
        infos
    }

    /// Query all relation tuples in an instance (using compiled query engine).
    ///
    /// This is equivalent to `query_instance_rel_tuples` in bootstrap_queries.rs,
    /// but uses the Query compiler for the initial scan+filter.
    pub fn query_instance_rel_tuples_compiled(&self, instance_slid: Slid) -> Vec<RelTupleInfo> {
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

        // Compile and execute the query
        let plan = compile_simple_filter(rt_sort, instance_func, instance_slid);
        let result = execute(&plan, &self.meta);

        // Convert query results to RelTupleInfo
        let mut infos = Vec::new();
        for tuple in result.tuples.keys() {
            if let Some(&rt_slid) = tuple.first() {
                infos.push(RelTupleInfo {
                    slid: rt_slid,
                    rel_slid: self.get_func(rel_func, rt_slid),
                    arg_slid: self.get_func(arg_func, rt_slid),
                });
            }
        }
        // Sort by UUID to preserve original creation order
        infos.sort_by_key(|info| self.get_element_uuid(info.slid));
        infos
    }
}

#[cfg(test)]
mod tests {
    use crate::repl::ReplState;

    /// Test that compiled query matches bootstrap query results.
    #[test]
    fn test_compiled_matches_bootstrap_sorts() {
        let source = r#"
            theory TestTheory {
                A : Sort;
                B : Sort;
                C : Sort;
                f : A -> B;
            }
        "#;

        let mut repl = ReplState::new();
        let _ = repl.execute_geolog(source);

        let theory_slid = repl.store.resolve_name("TestTheory")
            .expect("Theory should exist").0;

        // Compare bootstrap vs compiled
        let bootstrap = repl.store.query_theory_sorts(theory_slid);
        let compiled = repl.store.query_theory_sorts_compiled(theory_slid);

        // Same number of results
        assert_eq!(
            bootstrap.len(), compiled.len(),
            "Bootstrap returned {} sorts, compiled returned {}",
            bootstrap.len(), compiled.len()
        );

        // Same names (order may differ)
        let mut bootstrap_names: Vec<_> = bootstrap.iter().map(|s| &s.name).collect();
        let mut compiled_names: Vec<_> = compiled.iter().map(|s| &s.name).collect();
        bootstrap_names.sort();
        compiled_names.sort();

        assert_eq!(bootstrap_names, compiled_names, "Sort names should match");
    }

    /// Test compiled query with theory that has no sorts.
    #[test]
    fn test_compiled_empty_theory() {
        let source = r#"
            theory EmptyTheory {
            }
        "#;

        let mut repl = ReplState::new();
        let _ = repl.execute_geolog(source);

        let theory_slid = repl.store.resolve_name("EmptyTheory")
            .expect("Theory should exist").0;

        let bootstrap = repl.store.query_theory_sorts(theory_slid);
        let compiled = repl.store.query_theory_sorts_compiled(theory_slid);

        assert_eq!(bootstrap.len(), 0);
        assert_eq!(compiled.len(), 0);
    }

    /// Test that multiple theories have independent sorts.
    #[test]
    fn test_compiled_multiple_theories() {
        let source = r#"
            theory Theory1 {
                X : Sort;
                Y : Sort;
            }
            theory Theory2 {
                P : Sort;
                Q : Sort;
                R : Sort;
            }
        "#;

        let mut repl = ReplState::new();
        let _ = repl.execute_geolog(source);

        let theory1_slid = repl.store.resolve_name("Theory1")
            .expect("Theory1 should exist").0;
        let theory2_slid = repl.store.resolve_name("Theory2")
            .expect("Theory2 should exist").0;

        // Theory1 should have X, Y
        let t1_bootstrap = repl.store.query_theory_sorts(theory1_slid);
        let t1_compiled = repl.store.query_theory_sorts_compiled(theory1_slid);

        assert_eq!(t1_bootstrap.len(), 2);
        assert_eq!(t1_compiled.len(), 2);

        // Theory2 should have P, Q, R
        let t2_bootstrap = repl.store.query_theory_sorts(theory2_slid);
        let t2_compiled = repl.store.query_theory_sorts_compiled(theory2_slid);

        assert_eq!(t2_bootstrap.len(), 3);
        assert_eq!(t2_compiled.len(), 3);

        // Names should be independent
        let t1_names: std::collections::HashSet<_> =
            t1_compiled.iter().map(|s| &s.name).collect();
        let t2_names: std::collections::HashSet<_> =
            t2_compiled.iter().map(|s| &s.name).collect();

        assert!(t1_names.contains(&"X".to_string()));
        assert!(t1_names.contains(&"Y".to_string()));
        assert!(t2_names.contains(&"P".to_string()));
        assert!(t2_names.contains(&"Q".to_string()));
        assert!(t2_names.contains(&"R".to_string()));
    }

    /// Test that compiled query matches bootstrap query for functions.
    #[test]
    fn test_compiled_matches_bootstrap_funcs() {
        let source = r#"
            theory FuncTheory {
                A : Sort;
                B : Sort;
                C : Sort;
                f : A -> B;
                g : B -> C;
                h : A -> C;
            }
        "#;

        let mut repl = ReplState::new();
        let _ = repl.execute_geolog(source);

        let theory_slid = repl.store.resolve_name("FuncTheory")
            .expect("Theory should exist").0;

        // Compare bootstrap vs compiled
        let bootstrap = repl.store.query_theory_funcs(theory_slid);
        let compiled = repl.store.query_theory_funcs_compiled(theory_slid);

        // Same number of results
        assert_eq!(
            bootstrap.len(), compiled.len(),
            "Bootstrap returned {} funcs, compiled returned {}",
            bootstrap.len(), compiled.len()
        );

        // Same names (order may differ)
        let mut bootstrap_names: Vec<_> = bootstrap.iter().map(|f| &f.name).collect();
        let mut compiled_names: Vec<_> = compiled.iter().map(|f| &f.name).collect();
        bootstrap_names.sort();
        compiled_names.sort();

        assert_eq!(bootstrap_names, compiled_names, "Function names should match");

        // Verify we have the expected functions
        assert!(compiled_names.contains(&&"f".to_string()));
        assert!(compiled_names.contains(&&"g".to_string()));
        assert!(compiled_names.contains(&&"h".to_string()));
    }

    /// Test that compiled query matches bootstrap query for relations.
    #[test]
    fn test_compiled_matches_bootstrap_rels() {
        let source = r#"
            theory RelTheory {
                Node : Sort;
                Source : Node -> Prop;
                Sink : Node -> Prop;
                Connected : [x: Node, y: Node] -> Prop;
            }
        "#;

        let mut repl = ReplState::new();
        let _ = repl.execute_geolog(source);

        let theory_slid = repl.store.resolve_name("RelTheory")
            .expect("Theory should exist").0;

        // Compare bootstrap vs compiled
        let bootstrap = repl.store.query_theory_rels(theory_slid);
        let compiled = repl.store.query_theory_rels_compiled(theory_slid);

        // Same number of results
        assert_eq!(
            bootstrap.len(), compiled.len(),
            "Bootstrap returned {} rels, compiled returned {}",
            bootstrap.len(), compiled.len()
        );

        // Same names (order may differ)
        let mut bootstrap_names: Vec<_> = bootstrap.iter().map(|r| &r.name).collect();
        let mut compiled_names: Vec<_> = compiled.iter().map(|r| &r.name).collect();
        bootstrap_names.sort();
        compiled_names.sort();

        assert_eq!(bootstrap_names, compiled_names, "Relation names should match");

        // Verify we have the expected relations
        assert!(compiled_names.contains(&&"Source".to_string()));
        assert!(compiled_names.contains(&&"Sink".to_string()));
        assert!(compiled_names.contains(&&"Connected".to_string()));
    }

    // ========================================================================
    // Instance query tests
    // ========================================================================

    /// Test that compiled query matches bootstrap for instance elements.
    #[test]
    fn test_compiled_matches_bootstrap_instance_elems() {
        let source = r#"
            theory Graph {
                V : Sort;
                E : Sort;
                src : E -> V;
                tgt : E -> V;
            }

            instance SimpleGraph : Graph = {
                a : V;
                b : V;
                c : V;
                e1 : E;
                e2 : E;
                e1 src = a;
                e1 tgt = b;
                e2 src = b;
                e2 tgt = c;
            }
        "#;

        let mut repl = ReplState::new();
        let _ = repl.execute_geolog(source);

        let instance_slid = repl.store.resolve_name("SimpleGraph")
            .expect("Instance should exist").0;

        // Compare bootstrap vs compiled
        let bootstrap = repl.store.query_instance_elems(instance_slid);
        let compiled = repl.store.query_instance_elems_compiled(instance_slid);

        // Same number of results
        assert_eq!(
            bootstrap.len(), compiled.len(),
            "Bootstrap returned {} elems, compiled returned {}",
            bootstrap.len(), compiled.len()
        );

        // Should have 5 elements: a, b, c, e1, e2
        assert_eq!(compiled.len(), 5, "Expected 5 elements");

        // Same names (order may differ)
        let mut bootstrap_names: Vec<_> = bootstrap.iter().map(|e| &e.name).collect();
        let mut compiled_names: Vec<_> = compiled.iter().map(|e| &e.name).collect();
        bootstrap_names.sort();
        compiled_names.sort();

        assert_eq!(bootstrap_names, compiled_names, "Element names should match");
    }

    /// Test that compiled query matches bootstrap for function values.
    #[test]
    fn test_compiled_matches_bootstrap_func_vals() {
        let source = r#"
            theory Graph {
                V : Sort;
                E : Sort;
                src : E -> V;
                tgt : E -> V;
            }

            instance TwoEdges : Graph = {
                v1 : V;
                v2 : V;
                v3 : V;
                edge1 : E;
                edge2 : E;
                edge1 src = v1;
                edge1 tgt = v2;
                edge2 src = v2;
                edge2 tgt = v3;
            }
        "#;

        let mut repl = ReplState::new();
        let _ = repl.execute_geolog(source);

        let instance_slid = repl.store.resolve_name("TwoEdges")
            .expect("Instance should exist").0;

        // Compare bootstrap vs compiled
        let bootstrap = repl.store.query_instance_func_vals(instance_slid);
        let compiled = repl.store.query_instance_func_vals_compiled(instance_slid);

        // Same number of results
        assert_eq!(
            bootstrap.len(), compiled.len(),
            "Bootstrap returned {} func_vals, compiled returned {}",
            bootstrap.len(), compiled.len()
        );

        // Should have 4 function values: edge1.src, edge1.tgt, edge2.src, edge2.tgt
        assert_eq!(compiled.len(), 4, "Expected 4 function values");
    }

    /// Test that compiled query matches bootstrap for relation tuples.
    #[test]
    fn test_compiled_matches_bootstrap_rel_tuples() {
        let source = r#"
            theory NodeMarking {
                Node : Sort;
                Marked : [n: Node] -> Prop;
            }

            instance ThreeNodes : NodeMarking = {
                n1 : Node;
                n2 : Node;
                n3 : Node;
                [n: n1] Marked;
                [n: n3] Marked;
            }
        "#;

        let mut repl = ReplState::new();
        let _ = repl.execute_geolog(source);

        let instance_slid = repl.store.resolve_name("ThreeNodes")
            .expect("Instance should exist").0;

        // Compare bootstrap vs compiled
        let bootstrap = repl.store.query_instance_rel_tuples(instance_slid);
        let compiled = repl.store.query_instance_rel_tuples_compiled(instance_slid);

        // Same number of results
        assert_eq!(
            bootstrap.len(), compiled.len(),
            "Bootstrap returned {} rel_tuples, compiled returned {}",
            bootstrap.len(), compiled.len()
        );

        // Should have 2 relation tuples: n1 Marked, n3 Marked
        assert_eq!(compiled.len(), 2, "Expected 2 relation tuples");
    }

    /// Test compiled query with empty instance.
    #[test]
    fn test_compiled_empty_instance() {
        let source = r#"
            theory Simple {
                T : Sort;
            }

            instance EmptyInst : Simple = {
            }
        "#;

        let mut repl = ReplState::new();
        let _ = repl.execute_geolog(source);

        let instance_slid = repl.store.resolve_name("EmptyInst")
            .expect("Instance should exist").0;

        let bootstrap_elems = repl.store.query_instance_elems(instance_slid);
        let compiled_elems = repl.store.query_instance_elems_compiled(instance_slid);
        assert_eq!(bootstrap_elems.len(), 0);
        assert_eq!(compiled_elems.len(), 0);

        let bootstrap_fvs = repl.store.query_instance_func_vals(instance_slid);
        let compiled_fvs = repl.store.query_instance_func_vals_compiled(instance_slid);
        assert_eq!(bootstrap_fvs.len(), 0);
        assert_eq!(compiled_fvs.len(), 0);

        let bootstrap_rts = repl.store.query_instance_rel_tuples(instance_slid);
        let compiled_rts = repl.store.query_instance_rel_tuples_compiled(instance_slid);
        assert_eq!(bootstrap_rts.len(), 0);
        assert_eq!(compiled_rts.len(), 0);
    }
}
