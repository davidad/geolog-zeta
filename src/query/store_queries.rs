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

use crate::id::Slid;
use crate::store::Store;
use crate::store::append::AppendOps;
use crate::store::bootstrap_queries::SortInfo;
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
}
