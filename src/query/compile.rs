//! Query compiler: high-level queries → QueryOp plans.
//!
//! This module compiles query specifications into executable QueryOp plans.
//! It supports:
//! - Single-sort queries (like `Pattern`)
//! - Multi-sort queries with joins
//! - Function application and projection
//!
//! # Query Styles
//!
//! **∀-style (open sorts):** Elements determined by constraints.
//! Compiled to relational algebra (scan, filter, join, project).
//!
//! **∃-style (closed sorts):** Elements are declared constants.
//! Compiled to constraint satisfaction (witness enumeration).
//! [Not yet implemented]
//!
//! # Design
//!
//! Query compilation is currently direct (Query → QueryOp).
//! A future homoiconic version would compile to RelAlgIR instances,
//! which would then be interpreted by the backend.

use crate::id::Slid;
use super::backend::{JoinCond, Predicate, QueryOp};

/// A query specification that can involve multiple sorts and joins.
///
/// This generalizes `Pattern` to handle:
/// - Multiple source sorts
/// - Joins between sorts
/// - Complex constraints across sorts
///
/// # Example: Find all Func where Func/theory == target
///
/// ```ignore
/// let query = Query::scan(func_sort)
///     .filter_eq(theory_func, 0, target_slid)
///     .build();
/// ```
///
/// # Example: Find all (Srt, Func) pairs where Srt/theory == Func/theory
///
/// ```ignore
/// let query = Query::scan(srt_sort)
///     .join_scan(func_sort)
///     .join_on_func(srt_theory_func, 0, func_theory_func, 1)
///     .build();
/// ```
#[derive(Debug, Clone)]
pub struct Query {
    /// Sources: each is (sort_idx, alias). Alias is used in constraints.
    sources: Vec<Source>,
    /// Constraints to apply (filters and join conditions)
    constraints: Vec<Constraint>,
    /// Projection: which columns to return
    projection: Projection,
}

/// A source in the query (a sort to scan).
#[derive(Debug, Clone)]
struct Source {
    /// Sort index to scan
    sort_idx: usize,
    /// Column offset in the combined tuple
    /// (each source adds 1 column for its element)
    #[allow(dead_code)] // Used for tracking, will be needed for complex projections
    col_offset: usize,
}

/// A constraint in the query.
#[derive(Debug, Clone)]
enum Constraint {
    /// func(col) == constant
    FuncEqConst {
        func_idx: usize,
        arg_col: usize,
        expected: Slid,
    },
    /// func1(col1) == func2(col2)
    FuncEqFunc {
        func1_idx: usize,
        arg1_col: usize,
        func2_idx: usize,
        arg2_col: usize,
    },
    /// col1 == col2 (direct element equality)
    ColEq {
        col1: usize,
        col2: usize,
    },
    /// col == constant
    ColEqConst {
        col: usize,
        expected: Slid,
    },
}

/// Projection specification.
#[derive(Debug, Clone)]
enum Projection {
    /// Return all columns
    All,
    /// Return specific columns
    Cols(Vec<usize>),
    /// Return specific columns with function applications
    FuncCols(Vec<FuncCol>),
}

/// A column in projection, possibly with function application.
#[derive(Debug, Clone)]
struct FuncCol {
    /// Column to use as argument
    arg_col: usize,
    /// Function to apply (None = just the element)
    func_idx: Option<usize>,
}

impl Query {
    /// Create a new query scanning a single sort.
    pub fn scan(sort_idx: usize) -> QueryBuilder {
        QueryBuilder {
            sources: vec![Source { sort_idx, col_offset: 0 }],
            constraints: vec![],
            projection: Projection::All,
            next_col: 1,
        }
    }
}

/// Builder for constructing queries fluently.
#[derive(Debug, Clone)]
pub struct QueryBuilder {
    sources: Vec<Source>,
    constraints: Vec<Constraint>,
    projection: Projection,
    next_col: usize,
}

impl QueryBuilder {
    /// Add another sort to scan (creates a cross join, to be constrained).
    pub fn join_scan(mut self, sort_idx: usize) -> Self {
        let col_offset = self.next_col;
        self.sources.push(Source { sort_idx, col_offset });
        self.next_col += 1;
        self
    }

    /// Add a filter: func(col) == expected.
    ///
    /// `col` is 0-indexed, referring to which source's element.
    pub fn filter_eq(mut self, func_idx: usize, arg_col: usize, expected: Slid) -> Self {
        self.constraints.push(Constraint::FuncEqConst {
            func_idx,
            arg_col,
            expected,
        });
        self
    }

    /// Add a join condition: func1(col1) == func2(col2).
    ///
    /// Used to join two scanned sorts by comparing function values.
    pub fn join_on_func(
        mut self,
        func1_idx: usize,
        arg1_col: usize,
        func2_idx: usize,
        arg2_col: usize,
    ) -> Self {
        self.constraints.push(Constraint::FuncEqFunc {
            func1_idx,
            arg1_col,
            func2_idx,
            arg2_col,
        });
        self
    }

    /// Add an element equality constraint: col1 == col2.
    pub fn where_eq(mut self, col1: usize, col2: usize) -> Self {
        self.constraints.push(Constraint::ColEq { col1, col2 });
        self
    }

    /// Add a constant equality constraint: col == expected.
    pub fn where_const(mut self, col: usize, expected: Slid) -> Self {
        self.constraints.push(Constraint::ColEqConst { col, expected });
        self
    }

    /// Project to specific columns.
    pub fn project(mut self, cols: Vec<usize>) -> Self {
        self.projection = Projection::Cols(cols);
        self
    }

    /// Project with function applications.
    pub fn project_funcs(mut self, func_cols: Vec<(usize, Option<usize>)>) -> Self {
        self.projection = Projection::FuncCols(
            func_cols
                .into_iter()
                .map(|(arg_col, func_idx)| FuncCol { arg_col, func_idx })
                .collect(),
        );
        self
    }

    /// Build the final Query.
    pub fn build(self) -> Query {
        Query {
            sources: self.sources,
            constraints: self.constraints,
            projection: self.projection,
        }
    }

    /// Compile directly to QueryOp (skipping Query intermediate).
    pub fn compile(self) -> QueryOp {
        self.build().compile()
    }
}

impl Query {
    /// Compile the query to a QueryOp plan.
    ///
    /// The compilation strategy:
    /// 1. Scan each source sort
    /// 2. Join scans together (cross join if >1)
    /// 3. Handle FuncEqFunc constraints by applying functions, then filtering
    /// 4. Apply other constraints as filters
    /// 5. Apply projection
    pub fn compile(&self) -> QueryOp {
        if self.sources.is_empty() {
            return QueryOp::Empty;
        }

        // Step 1: Build base plan from sources
        let mut plan = QueryOp::Scan {
            sort_idx: self.sources[0].sort_idx,
        };

        // Track current column count (each source adds 1 column)
        let mut current_cols = 1;

        // If multiple sources, join them
        for source in &self.sources[1..] {
            let right = QueryOp::Scan {
                sort_idx: source.sort_idx,
            };
            plan = QueryOp::Join {
                left: Box::new(plan),
                right: Box::new(right),
                cond: JoinCond::Cross, // Start with cross join, constraints will filter
            };
            current_cols += 1;
        }

        // Step 2: Separate FuncEqFunc constraints (need Apply) from others
        let mut func_eq_func_constraints = Vec::new();
        let mut simple_constraints = Vec::new();

        for constraint in &self.constraints {
            match constraint {
                Constraint::FuncEqFunc { .. } => func_eq_func_constraints.push(constraint),
                _ => simple_constraints.push(constraint),
            }
        }

        // Step 3: Handle FuncEqFunc constraints
        // For each, apply both functions, track the added columns, then filter on equality
        for constraint in func_eq_func_constraints {
            if let Constraint::FuncEqFunc {
                func1_idx,
                arg1_col,
                func2_idx,
                arg2_col,
            } = constraint
            {
                // Apply func1 to arg1_col, result goes in current_cols
                plan = QueryOp::Apply {
                    input: Box::new(plan),
                    func_idx: *func1_idx,
                    arg_col: *arg1_col,
                };
                let col1_result = current_cols;
                current_cols += 1;

                // Apply func2 to arg2_col, result goes in current_cols
                plan = QueryOp::Apply {
                    input: Box::new(plan),
                    func_idx: *func2_idx,
                    arg_col: *arg2_col,
                };
                let col2_result = current_cols;
                current_cols += 1;

                // Filter where the two result columns are equal
                plan = QueryOp::Filter {
                    input: Box::new(plan),
                    pred: Predicate::ColEqCol {
                        left: col1_result,
                        right: col2_result,
                    },
                };
            }
        }

        // Step 4: Apply simple constraints as filters
        for constraint in simple_constraints {
            let pred = match constraint {
                Constraint::FuncEqConst {
                    func_idx,
                    arg_col,
                    expected,
                } => Predicate::FuncEqConst {
                    func_idx: *func_idx,
                    arg_col: *arg_col,
                    expected: *expected,
                },
                Constraint::FuncEqFunc { .. } => {
                    unreachable!("FuncEqFunc already handled")
                }
                Constraint::ColEq { col1, col2 } => Predicate::ColEqCol {
                    left: *col1,
                    right: *col2,
                },
                Constraint::ColEqConst { col, expected } => Predicate::ColEqConst {
                    col: *col,
                    val: *expected,
                },
            };
            plan = QueryOp::Filter {
                input: Box::new(plan),
                pred,
            };
        }

        // Step 5: Apply projection
        match &self.projection {
            Projection::All => {
                // No projection needed, return all columns
            }
            Projection::Cols(cols) => {
                plan = QueryOp::Project {
                    input: Box::new(plan),
                    columns: cols.clone(),
                };
            }
            Projection::FuncCols(func_cols) => {
                // Apply each function, then project
                let base_col = current_cols; // Start adding func results here
                for fc in func_cols.iter() {
                    if let Some(func_idx) = fc.func_idx {
                        plan = QueryOp::Apply {
                            input: Box::new(plan),
                            func_idx,
                            arg_col: fc.arg_col,
                        };
                        current_cols += 1;
                    }
                }
                // Project to the added columns
                if current_cols > base_col {
                    let columns: Vec<usize> = (base_col..current_cols).collect();
                    plan = QueryOp::Project {
                        input: Box::new(plan),
                        columns,
                    };
                }
            }
        }

        plan
    }
}

// ============================================================================
// Convenience functions for common query patterns
// ============================================================================

/// Compile a simple single-sort query: scan sort, filter by func == value.
///
/// This is equivalent to `Pattern::new(sort).filter(func, value).compile()`
/// but uses the new Query API.
pub fn compile_simple_filter(sort_idx: usize, func_idx: usize, expected: Slid) -> QueryOp {
    Query::scan(sort_idx)
        .filter_eq(func_idx, 0, expected)
        .compile()
}

/// Compile a query that returns func(elem) for matching elements.
///
/// scan(sort) |> filter(filter_func(elem) == expected) |> project(project_func(elem))
pub fn compile_filter_project(
    sort_idx: usize,
    filter_func: usize,
    expected: Slid,
    project_func: usize,
) -> QueryOp {
    // scan → filter → apply → project
    let scan = QueryOp::Scan { sort_idx };
    let filter = QueryOp::Filter {
        input: Box::new(scan),
        pred: Predicate::FuncEqConst {
            func_idx: filter_func,
            arg_col: 0,
            expected,
        },
    };
    let apply = QueryOp::Apply {
        input: Box::new(filter),
        func_idx: project_func,
        arg_col: 0,
    };
    // Now we have (elem, func(elem)), project to just column 1
    QueryOp::Project {
        input: Box::new(apply),
        columns: vec![1],
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::id::NumericId;

    #[test]
    fn test_simple_scan_compiles() {
        let plan = Query::scan(0).compile();
        assert!(matches!(plan, QueryOp::Scan { sort_idx: 0 }));
    }

    /// Test that Query-compiled plans produce same results as Pattern.
    ///
    /// This validates that the new Query API is equivalent to the
    /// existing Pattern API for simple queries.
    #[test]
    fn test_query_matches_pattern() {
        use crate::core::Structure;
        use crate::query::backend::execute;
        use crate::query::{Pattern, Projection as PatternProjection};

        // Create a structure with some data
        let mut structure = Structure::new(2);
        // Sort 0: elements 0, 1, 2
        structure.carriers[0].insert(0);
        structure.carriers[0].insert(1);
        structure.carriers[0].insert(2);
        // Sort 1: elements 10, 11
        structure.carriers[1].insert(10);
        structure.carriers[1].insert(11);

        // Test 1: Simple scan
        let pattern_plan = Pattern {
            source_sort: 0,
            constraints: vec![],
            projection: PatternProjection::Element,
        }
        .compile();

        let query_plan = Query::scan(0).compile();

        let pattern_result = execute(&pattern_plan, &structure);
        let query_result = execute(&query_plan, &structure);

        assert_eq!(
            pattern_result.len(),
            query_result.len(),
            "Scan should return same number of results"
        );

        // Test 2: Scan with filter (using ColEqConst since we don't have functions)
        let pattern_plan = QueryOp::Filter {
            input: Box::new(QueryOp::Scan { sort_idx: 0 }),
            pred: Predicate::ColEqConst {
                col: 0,
                val: Slid::from_usize(1),
            },
        };

        let query_plan = Query::scan(0)
            .where_const(0, Slid::from_usize(1))
            .compile();

        let pattern_result = execute(&pattern_plan, &structure);
        let query_result = execute(&query_plan, &structure);

        assert_eq!(pattern_result.len(), 1);
        assert_eq!(query_result.len(), 1);
    }

    /// Test FuncEqFunc constraint: func1(col1) == func2(col2)
    #[test]
    fn test_func_eq_func_join() {
        use crate::core::Structure;
        use crate::query::backend::execute;
        use crate::universe::Universe;

        // Create a structure with two sorts
        let mut structure = Structure::new(2);
        let mut universe = Universe::new();

        // Sort 0: elements a, b
        let (a, _) = structure.add_element(&mut universe, 0);
        let (b, _) = structure.add_element(&mut universe, 0);

        // Sort 1: elements x, y, z
        let (x, _) = structure.add_element(&mut universe, 1);
        let (y, _) = structure.add_element(&mut universe, 1);
        let (z, _) = structure.add_element(&mut universe, 1);

        // Common target for function results
        let target1 = Slid::from_usize(100);
        let target2 = Slid::from_usize(200);

        // Initialize functions
        // func0: Sort0 -> targets (a→100, b→200)
        // func1: Sort1 -> targets (x→100, y→200, z→100)
        structure.init_functions(&[Some(0), Some(1)]);

        structure.define_function(0, a, target1).unwrap();
        structure.define_function(0, b, target2).unwrap();
        structure.define_function(1, x, target1).unwrap();
        structure.define_function(1, y, target2).unwrap();
        structure.define_function(1, z, target1).unwrap();

        // Query: Find all (s0, s1) where func0(s0) == func1(s1)
        // Expected matches:
        // - (a, x) because func0(a)=100 == func1(x)=100
        // - (a, z) because func0(a)=100 == func1(z)=100
        // - (b, y) because func0(b)=200 == func1(y)=200

        let plan = Query::scan(0)
            .join_scan(1)
            .join_on_func(0, 0, 1, 1) // func0(col0) == func1(col1)
            .compile();

        let result = execute(&plan, &structure);

        // Should have exactly 3 matching pairs
        assert_eq!(
            result.len(),
            3,
            "Expected 3 matching pairs, got {}",
            result.len()
        );
    }

    /// Integration test: validate compiled queries against bootstrap_queries.
    ///
    /// This test creates a real theory using the REPL, then verifies that
    /// queries compiled with the Query API produce the same results as
    /// the handcoded bootstrap_queries methods.
    #[test]
    fn test_query_matches_bootstrap_queries() {
        use crate::repl::ReplState;

        // Create a theory via REPL
        let source = r#"
            theory Graph {
                V : Sort;
                E : Sort;
                src : E -> V;
                tgt : E -> V;
            }
        "#;

        let mut repl = ReplState::new();
        let _ = repl.execute_geolog(source);

        // Get the theory slid
        let theory_slid = match repl.store.resolve_name("Graph") {
            Some((slid, _)) => slid,
            None => panic!("Theory 'Graph' not found"),
        };

        // Get bootstrap_queries result
        let bootstrap_sorts = repl.store.query_theory_sorts(theory_slid);

        // Now compile a Query that does the same thing:
        // "Find all Srt where Srt/theory == theory_slid"
        let srt_sort = repl.store.sort_ids.srt.expect("Srt sort not found");
        let theory_func = repl
            .store
            .func_ids
            .srt_theory
            .expect("Srt/theory func not found");

        // Compile the query
        let plan = compile_simple_filter(srt_sort, theory_func, theory_slid);

        // Execute against the store's meta structure
        let result = crate::query::backend::execute(&plan, &repl.store.meta);

        // Compare: should have same number of sorts
        assert_eq!(
            bootstrap_sorts.len(),
            result.len(),
            "Query should return same number of sorts as bootstrap_queries.\n\
             Bootstrap returned {} sorts: {:?}\n\
             Compiled query returned {} tuples",
            bootstrap_sorts.len(),
            bootstrap_sorts.iter().map(|s| &s.name).collect::<Vec<_>>(),
            result.len()
        );

        // Verify we got V and E
        assert!(
            bootstrap_sorts.len() >= 2,
            "Graph theory should have at least V and E sorts"
        );
    }

    #[test]
    fn test_filter_compiles() {
        let plan = Query::scan(0)
            .filter_eq(1, 0, Slid::from_usize(42))
            .compile();

        // Should be Filter(Scan)
        if let QueryOp::Filter { input, pred } = plan {
            assert!(matches!(*input, QueryOp::Scan { sort_idx: 0 }));
            assert!(matches!(
                pred,
                Predicate::FuncEqConst {
                    func_idx: 1,
                    arg_col: 0,
                    ..
                }
            ));
        } else {
            panic!("Expected Filter, got {:?}", plan);
        }
    }

    #[test]
    fn test_join_compiles() {
        let plan = Query::scan(0)
            .join_scan(1)
            .compile();

        // Should be Join(Scan, Scan)
        if let QueryOp::Join { left, right, .. } = plan {
            assert!(matches!(*left, QueryOp::Scan { sort_idx: 0 }));
            assert!(matches!(*right, QueryOp::Scan { sort_idx: 1 }));
        } else {
            panic!("Expected Join, got {:?}", plan);
        }
    }

    #[test]
    fn test_compile_simple_filter() {
        let plan = compile_simple_filter(5, 3, Slid::from_usize(100));

        if let QueryOp::Filter { input, pred } = plan {
            assert!(matches!(*input, QueryOp::Scan { sort_idx: 5 }));
            if let Predicate::FuncEqConst {
                func_idx,
                arg_col,
                expected,
            } = pred
            {
                assert_eq!(func_idx, 3);
                assert_eq!(arg_col, 0);
                assert_eq!(expected, Slid::from_usize(100));
            } else {
                panic!("Expected FuncEqConst predicate");
            }
        } else {
            panic!("Expected Filter");
        }
    }

    #[test]
    fn test_compile_filter_project() {
        let plan = compile_filter_project(0, 1, Slid::from_usize(42), 2);

        // Should be Project(Apply(Filter(Scan)))
        if let QueryOp::Project { input, columns } = plan {
            assert_eq!(columns, vec![1]);
            if let QueryOp::Apply {
                input,
                func_idx,
                arg_col,
            } = *input
            {
                assert_eq!(func_idx, 2);
                assert_eq!(arg_col, 0);
                if let QueryOp::Filter { input, .. } = *input {
                    assert!(matches!(*input, QueryOp::Scan { sort_idx: 0 }));
                } else {
                    panic!("Expected Filter inside Apply");
                }
            } else {
                panic!("Expected Apply inside Project");
            }
        } else {
            panic!("Expected Project");
        }
    }
}
