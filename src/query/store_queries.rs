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
use crate::id::Slid;
use crate::store::Store;
use crate::store::append::AppendOps;
use crate::store::bootstrap_queries::{SortInfo, FuncInfo, RelInfo};
use super::backend::execute;
use super::compile::compile_simple_filter;

impl Store {
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
}
