//! Query execution against a Store.
//!
//! This module executes Pattern queries against the GeologMeta store,
//! computing the unique maximal element (cofree model) for ∀-style queries.

use crate::id::Slid;
use crate::store::Store;
use crate::store::append::AppendOps;

use super::{Pattern, Projection};

/// Result of a pattern query.
///
/// For ∀-style queries (open sorts), this is the cofree model:
/// all elements satisfying the constraints.
#[derive(Debug, Clone)]
pub enum QueryResult {
    /// List of matching elements
    Elements(Vec<Slid>),
    /// List of projected values
    Values(Vec<Slid>),
    /// List of projected tuples
    Tuples(Vec<Vec<Slid>>),
}

impl QueryResult {
    /// Get as elements (panics if not Elements variant).
    pub fn into_elements(self) -> Vec<Slid> {
        match self {
            QueryResult::Elements(e) => e,
            _ => panic!("QueryResult is not Elements"),
        }
    }

    /// Get as values (panics if not Values variant).
    pub fn into_values(self) -> Vec<Slid> {
        match self {
            QueryResult::Values(v) => v,
            _ => panic!("QueryResult is not Values"),
        }
    }

    /// Get as tuples (panics if not Tuples variant).
    pub fn into_tuples(self) -> Vec<Vec<Slid>> {
        match self {
            QueryResult::Tuples(t) => t,
            _ => panic!("QueryResult is not Tuples"),
        }
    }

    /// Check if the result is empty.
    pub fn is_empty(&self) -> bool {
        match self {
            QueryResult::Elements(e) => e.is_empty(),
            QueryResult::Values(v) => v.is_empty(),
            QueryResult::Tuples(t) => t.is_empty(),
        }
    }

    /// Get the number of results.
    pub fn len(&self) -> usize {
        match self {
            QueryResult::Elements(e) => e.len(),
            QueryResult::Values(v) => v.len(),
            QueryResult::Tuples(t) => t.len(),
        }
    }
}

/// Execute a pattern query against a store.
///
/// This is the ∀-style query executor: scans all elements of source_sort,
/// filters by constraints, and projects the result.
///
/// In terms of query semantics: computes the unique maximal element
/// (cofree model) of the theory extension.
pub fn execute_pattern(store: &Store, pattern: &Pattern) -> QueryResult {
    // Scan all elements of source sort
    let candidates = store.elements_of_sort(pattern.source_sort);

    // Filter by constraints
    let matching: Vec<Slid> = candidates
        .into_iter()
        .filter(|&elem| {
            pattern.constraints.iter().all(|c| {
                store.get_func(c.func, elem) == Some(c.expected)
            })
        })
        .collect();

    // Project
    match &pattern.projection {
        Projection::Element => QueryResult::Elements(matching),
        Projection::Func(func) => {
            let values: Vec<Slid> = matching
                .into_iter()
                .filter_map(|elem| store.get_func(*func, elem))
                .collect();
            QueryResult::Values(values)
        }
        Projection::Tuple(funcs) => {
            let tuples: Vec<Vec<Slid>> = matching
                .into_iter()
                .filter_map(|elem| {
                    let tuple: Vec<Slid> = funcs
                        .iter()
                        .filter_map(|f| store.get_func(*f, elem))
                        .collect();
                    // Only include if all projections succeeded
                    if tuple.len() == funcs.len() {
                        Some(tuple)
                    } else {
                        None
                    }
                })
                .collect();
            QueryResult::Tuples(tuples)
        }
    }
}

/// Convenience methods on Store for pattern queries.
impl Store {
    /// Execute a pattern query.
    ///
    /// # Example
    ///
    /// ```ignore
    /// // Find all Srt where Srt.theory == theory_slid
    /// let result = store.query(
    ///     Pattern::new(store.sort_ids.srt.unwrap())
    ///         .filter(store.func_ids.srt_theory.unwrap(), theory_slid)
    /// );
    /// ```
    pub fn query(&self, pattern: &Pattern) -> QueryResult {
        execute_pattern(self, pattern)
    }

    /// Execute a pattern query and return just the matching elements.
    pub fn query_elements(&self, pattern: &Pattern) -> Vec<Slid> {
        execute_pattern(self, pattern).into_elements()
    }
}

// ============================================================================
// Typed query helpers that replace bootstrap_queries
// ============================================================================

/// Information about a sort (mirrors bootstrap_queries::SortInfo)
#[derive(Debug, Clone)]
pub struct SortInfo {
    pub name: String,
    pub slid: Slid,
}

impl Store {
    /// Query all sorts belonging to a theory using Pattern API.
    ///
    /// This is the Pattern-based equivalent of bootstrap_queries::query_theory_sorts.
    /// Both should return identical results.
    pub fn query_sorts_of_theory(&self, theory_slid: Slid) -> Vec<SortInfo> {
        let Some(srt_sort) = self.sort_ids.srt else {
            return vec![];
        };
        let Some(theory_func) = self.func_ids.srt_theory else {
            return vec![];
        };

        // The core pattern: find all Srt where Srt.theory == theory_slid
        let pattern = Pattern::new(srt_sort)
            .filter(theory_func, theory_slid);

        // Execute and post-process
        self.query_elements(&pattern)
            .into_iter()
            .map(|slid| {
                let name = self.get_element_name(slid);
                let short_name = name.rsplit('/').next().unwrap_or(&name).to_string();
                SortInfo { name: short_name, slid }
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Test that Pattern-based query matches bootstrap_queries.
    ///
    /// This is a sanity test to ensure the new query engine gives
    /// identical results to the hand-coded queries.
    #[test]
    fn test_query_sorts_matches_bootstrap() {
        // Parse and elaborate a theory via REPL
        let source = r#"
            theory Graph {
                V : Sort;
                E : Sort;
                src : E -> V;
                tgt : E -> V;
            }
        "#;

        // Use ReplState to execute
        let mut repl = crate::repl::ReplState::new();
        let _ = repl.execute_geolog(source);

        // Get the theory slid
        if let Some((theory_slid, _)) = repl.store.resolve_name("Graph") {
            // Query using bootstrap method
            let bootstrap_result = repl.store.query_theory_sorts(theory_slid);

            // Query using Pattern method
            let pattern_result = repl.store.query_sorts_of_theory(theory_slid);

            // Should have same number of results
            assert_eq!(
                bootstrap_result.len(),
                pattern_result.len(),
                "Different number of sorts returned: bootstrap={}, pattern={}",
                bootstrap_result.len(),
                pattern_result.len()
            );

            // Should have same sort names (V and E)
            let bootstrap_names: std::collections::HashSet<_> =
                bootstrap_result.iter().map(|s| &s.name).collect();
            let pattern_names: std::collections::HashSet<_> =
                pattern_result.iter().map(|s| &s.name).collect();

            assert_eq!(
                bootstrap_names,
                pattern_names,
                "Different sort names returned"
            );

            // Verify we got the expected sorts
            assert!(bootstrap_names.contains(&"V".to_string()), "Missing sort V");
            assert!(bootstrap_names.contains(&"E".to_string()), "Missing sort E");
        } else {
            panic!("Theory 'Graph' not found after execution");
        }
    }
}
