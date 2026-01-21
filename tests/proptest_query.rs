//! Property tests for query operations.
//!
//! Verifies that execute_optimized produces the same results as execute (naive).

use geolog::core::Structure;
use geolog::id::{NumericId, Slid};
use geolog::query::{JoinCond, Predicate, QueryOp, execute, execute_optimized};
use proptest::prelude::*;

// ============================================================================
// QueryOp Generators
// ============================================================================

/// Generate arbitrary Slid values (within reasonable range)
fn arb_slid() -> impl Strategy<Value = Slid> {
    (0..100usize).prop_map(Slid::from_usize)
}

/// Generate a simple structure with multiple sorts and elements
fn arb_query_structure(num_sorts: usize, max_per_sort: usize) -> impl Strategy<Value = Structure> {
    prop::collection::vec(
        prop::collection::vec(0..50u64, 0..=max_per_sort),
        num_sorts,
    )
    .prop_map(|sort_elements| {
        let mut structure = Structure::new(sort_elements.len());
        for (sort_idx, elements) in sort_elements.iter().enumerate() {
            for &elem in elements {
                structure.carriers[sort_idx].insert(elem);
            }
        }
        structure
    })
}

/// Generate a scan operation
fn arb_scan(max_sort: usize) -> impl Strategy<Value = QueryOp> {
    (0..max_sort).prop_map(|sort_idx| QueryOp::Scan { sort_idx })
}

/// Generate a constant tuple
fn arb_constant() -> impl Strategy<Value = QueryOp> {
    prop::collection::vec(arb_slid(), 1..=3)
        .prop_map(|tuple| QueryOp::Constant { tuple })
}

/// Generate empty
fn arb_empty() -> impl Strategy<Value = QueryOp> {
    Just(QueryOp::Empty)
}

/// Generate a simple query (scan, constant, or empty)
fn arb_simple_query(max_sort: usize) -> impl Strategy<Value = QueryOp> {
    prop_oneof![
        arb_scan(max_sort),
        arb_constant(),
        arb_empty(),
    ]
}

/// Generate a join condition for given arity
fn arb_join_cond(left_arity: usize, right_arity: usize) -> impl Strategy<Value = JoinCond> {
    if left_arity == 0 || right_arity == 0 {
        Just(JoinCond::Cross).boxed()
    } else {
        prop_oneof![
            Just(JoinCond::Cross),
            (0..left_arity, 0..right_arity)
                .prop_map(|(left_col, right_col)| JoinCond::Equi { left_col, right_col }),
        ]
        .boxed()
    }
}

/// Generate a join of two scans
fn arb_scan_join(max_sort: usize) -> impl Strategy<Value = QueryOp> {
    (0..max_sort, 0..max_sort)
        .prop_flat_map(move |(left_sort, right_sort)| {
            arb_join_cond(1, 1).prop_map(move |cond| QueryOp::Join {
                left: Box::new(QueryOp::Scan { sort_idx: left_sort }),
                right: Box::new(QueryOp::Scan { sort_idx: right_sort }),
                cond,
            })
        })
}

/// Generate a union of two simple queries
fn arb_union(max_sort: usize) -> impl Strategy<Value = QueryOp> {
    (arb_simple_query(max_sort), arb_simple_query(max_sort))
        .prop_map(|(left, right)| QueryOp::Union {
            left: Box::new(left),
            right: Box::new(right),
        })
}

/// Generate a negate of a simple query
fn arb_negate(max_sort: usize) -> impl Strategy<Value = QueryOp> {
    arb_simple_query(max_sort).prop_map(|input| QueryOp::Negate {
        input: Box::new(input),
    })
}

/// Generate a distinct of a simple query
fn arb_distinct(max_sort: usize) -> impl Strategy<Value = QueryOp> {
    arb_simple_query(max_sort).prop_map(|input| QueryOp::Distinct {
        input: Box::new(input),
    })
}

/// Generate a simple predicate (no recursion, no function predicates)
/// Use this for tests with structures that don't have functions.
fn arb_simple_predicate_no_funcs() -> impl Strategy<Value = Predicate> {
    prop_oneof![
        Just(Predicate::True),
        Just(Predicate::False),
        (0..5usize, 0..5usize).prop_map(|(left, right)| Predicate::ColEqCol { left, right }),
        (0..5usize, arb_slid()).prop_map(|(col, val)| Predicate::ColEqConst { col, val }),
    ]
}

/// Generate a simple predicate (no recursion) - includes function predicates
/// Use this for to_relalg compilation tests where functions don't need to evaluate.
fn arb_simple_predicate() -> impl Strategy<Value = Predicate> {
    prop_oneof![
        Just(Predicate::True),
        Just(Predicate::False),
        (0..5usize, 0..5usize).prop_map(|(left, right)| Predicate::ColEqCol { left, right }),
        (0..5usize, arb_slid()).prop_map(|(col, val)| Predicate::ColEqConst { col, val }),
        (0..3usize, 0..5usize, 0..5usize)
            .prop_map(|(func_idx, arg_col, result_col)| Predicate::FuncEq { func_idx, arg_col, result_col }),
        (0..3usize, 0..5usize, arb_slid())
            .prop_map(|(func_idx, arg_col, expected)| Predicate::FuncEqConst { func_idx, arg_col, expected }),
    ]
}

/// Generate a predicate with possible And/Or nesting (no function predicates)
fn arb_predicate_no_funcs() -> impl Strategy<Value = Predicate> {
    arb_simple_predicate_no_funcs().prop_recursive(2, 8, 2, |inner| {
        prop_oneof![
            inner.clone(),
            (inner.clone(), inner.clone()).prop_map(|(l, r)| Predicate::And(Box::new(l), Box::new(r))),
            (inner.clone(), inner).prop_map(|(l, r)| Predicate::Or(Box::new(l), Box::new(r))),
        ]
    })
}

/// Generate a predicate with possible And/Or nesting (includes function predicates)
fn arb_predicate() -> impl Strategy<Value = Predicate> {
    arb_simple_predicate().prop_recursive(2, 8, 2, |inner| {
        prop_oneof![
            inner.clone(),
            (inner.clone(), inner.clone()).prop_map(|(l, r)| Predicate::And(Box::new(l), Box::new(r))),
            (inner.clone(), inner).prop_map(|(l, r)| Predicate::Or(Box::new(l), Box::new(r))),
        ]
    })
}

/// Generate a filter with arbitrary predicate (no function predicates)
/// Safe for testing against structures without functions.
fn arb_filter_safe(max_sort: usize) -> impl Strategy<Value = QueryOp> {
    (arb_scan(max_sort), arb_predicate_no_funcs())
        .prop_map(|(input, pred)| QueryOp::Filter {
            input: Box::new(input),
            pred,
        })
}

/// Generate a filter with column equality predicate (simple version)
fn arb_filter_col_eq_const(max_sort: usize) -> impl Strategy<Value = QueryOp> {
    (arb_scan(max_sort), arb_slid())
        .prop_map(|(input, val)| QueryOp::Filter {
            input: Box::new(input),
            pred: Predicate::ColEqConst { col: 0, val },
        })
}

/// Generate a query without DBSP operators (for comparing naive vs optimized)
/// Uses arb_filter_safe to avoid function predicates that require functions in the structure.
fn arb_query_no_dbsp(max_sort: usize) -> impl Strategy<Value = QueryOp> {
    prop_oneof![
        4 => arb_scan(max_sort),
        2 => arb_constant(),
        1 => arb_empty(),
        3 => arb_scan_join(max_sort),
        2 => arb_union(max_sort),
        1 => arb_negate(max_sort),
        1 => arb_distinct(max_sort),
        2 => arb_filter_col_eq_const(max_sort),
        3 => arb_filter_safe(max_sort),
    ]
}

// ============================================================================
// Property Tests
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(500))]

    /// execute_optimized should produce identical results to execute for any query
    #[test]
    fn optimized_matches_naive(
        structure in arb_query_structure(4, 10),
        query in arb_query_no_dbsp(4)
    ) {
        let naive_result = execute(&query, &structure);
        let optimized_result = execute_optimized(&query, &structure);

        // Same number of unique tuples
        prop_assert_eq!(
            naive_result.len(),
            optimized_result.len(),
            "Length mismatch for query {:?}",
            query
        );

        // Same multiplicities for each tuple
        for (tuple, mult) in naive_result.iter() {
            prop_assert_eq!(
                optimized_result.tuples.get(tuple),
                Some(mult),
                "Multiplicity mismatch for tuple {:?}",
                tuple
            );
        }
    }

    /// Equi-join should be symmetric in a sense: swapping left/right and columns
    /// should produce equivalent results (after accounting for tuple order)
    #[test]
    fn equijoin_symmetric(
        structure in arb_query_structure(2, 8),
        left_sort in 0..2usize,
        right_sort in 0..2usize,
    ) {
        let join1 = QueryOp::Join {
            left: Box::new(QueryOp::Scan { sort_idx: left_sort }),
            right: Box::new(QueryOp::Scan { sort_idx: right_sort }),
            cond: JoinCond::Equi { left_col: 0, right_col: 0 },
        };

        let join2 = QueryOp::Join {
            left: Box::new(QueryOp::Scan { sort_idx: right_sort }),
            right: Box::new(QueryOp::Scan { sort_idx: left_sort }),
            cond: JoinCond::Equi { left_col: 0, right_col: 0 },
        };

        let result1 = execute_optimized(&join1, &structure);
        let result2 = execute_optimized(&join2, &structure);

        // Should have same number of tuples (with columns swapped)
        prop_assert_eq!(result1.len(), result2.len());
    }

    /// Nested equijoins: (A ⋈ B) ⋈ C should work correctly
    #[test]
    fn nested_equijoin(
        structure in arb_query_structure(3, 6),
    ) {
        let join_ab = QueryOp::Join {
            left: Box::new(QueryOp::Scan { sort_idx: 0 }),
            right: Box::new(QueryOp::Scan { sort_idx: 1 }),
            cond: JoinCond::Equi { left_col: 0, right_col: 0 },
        };

        let join_abc = QueryOp::Join {
            left: Box::new(join_ab.clone()),
            right: Box::new(QueryOp::Scan { sort_idx: 2 }),
            cond: JoinCond::Equi { left_col: 0, right_col: 0 },
        };

        let naive_result = execute(&join_abc, &structure);
        let optimized_result = execute_optimized(&join_abc, &structure);

        prop_assert_eq!(naive_result.len(), optimized_result.len());

        for (tuple, mult) in naive_result.iter() {
            prop_assert_eq!(
                optimized_result.tuples.get(tuple),
                Some(mult),
                "Mismatch in nested join"
            );
        }
    }

    /// Cross join should produce |A| * |B| results
    #[test]
    fn cross_join_cardinality(
        structure in arb_query_structure(2, 5),
    ) {
        let join = QueryOp::Join {
            left: Box::new(QueryOp::Scan { sort_idx: 0 }),
            right: Box::new(QueryOp::Scan { sort_idx: 1 }),
            cond: JoinCond::Cross,
        };

        let result = execute_optimized(&join, &structure);
        let expected_size = structure.carriers[0].len() as usize * structure.carriers[1].len() as usize;

        prop_assert_eq!(result.len(), expected_size);
    }

    /// Union is commutative: A ∪ B = B ∪ A
    #[test]
    fn union_commutative(
        structure in arb_query_structure(2, 5),
    ) {
        let union1 = QueryOp::Union {
            left: Box::new(QueryOp::Scan { sort_idx: 0 }),
            right: Box::new(QueryOp::Scan { sort_idx: 1 }),
        };

        let union2 = QueryOp::Union {
            left: Box::new(QueryOp::Scan { sort_idx: 1 }),
            right: Box::new(QueryOp::Scan { sort_idx: 0 }),
        };

        let result1 = execute_optimized(&union1, &structure);
        let result2 = execute_optimized(&union2, &structure);

        prop_assert_eq!(result1.len(), result2.len());

        for (tuple, mult) in result1.iter() {
            prop_assert_eq!(
                result2.tuples.get(tuple),
                Some(mult),
                "Union commutativity failed"
            );
        }
    }

    /// Distinct is idempotent: distinct(distinct(x)) = distinct(x)
    #[test]
    fn distinct_idempotent(
        structure in arb_query_structure(1, 10),
    ) {
        let scan = QueryOp::Scan { sort_idx: 0 };

        let distinct1 = QueryOp::Distinct {
            input: Box::new(scan.clone()),
        };

        let distinct2 = QueryOp::Distinct {
            input: Box::new(QueryOp::Distinct {
                input: Box::new(scan),
            }),
        };

        let result1 = execute_optimized(&distinct1, &structure);
        let result2 = execute_optimized(&distinct2, &structure);

        prop_assert_eq!(result1.len(), result2.len());

        for (tuple, mult) in result1.iter() {
            prop_assert_eq!(
                result2.tuples.get(tuple),
                Some(mult),
                "Distinct idempotency failed"
            );
        }
    }

    /// Negate twice is identity: negate(negate(x)) = x
    #[test]
    fn negate_involution(
        structure in arb_query_structure(1, 10),
    ) {
        let scan = QueryOp::Scan { sort_idx: 0 };

        let double_negate = QueryOp::Negate {
            input: Box::new(QueryOp::Negate {
                input: Box::new(scan.clone()),
            }),
        };

        let result_original = execute_optimized(&scan, &structure);
        let result_double_neg = execute_optimized(&double_negate, &structure);

        prop_assert_eq!(result_original.len(), result_double_neg.len());

        for (tuple, mult) in result_original.iter() {
            prop_assert_eq!(
                result_double_neg.tuples.get(tuple),
                Some(mult),
                "Negate involution failed"
            );
        }
    }
}

// ============================================================================
// RelAlgIR Compilation Property Tests
// ============================================================================

mod to_relalg_tests {
    use geolog::core::ElaboratedTheory;
    use geolog::query::{Predicate, QueryOp, to_relalg::compile_to_relalg};
    use geolog::universe::Universe;
    use geolog::repl::ReplState;
    use proptest::prelude::*;
    use std::rc::Rc;

    /// Load the RelAlgIR theory for testing
    fn load_relalg_theory() -> Rc<ElaboratedTheory> {
        let meta_content = std::fs::read_to_string("theories/GeologMeta.geolog")
            .expect("Failed to read GeologMeta.geolog");
        let ir_content = std::fs::read_to_string("theories/RelAlgIR.geolog")
            .expect("Failed to read RelAlgIR.geolog");

        let mut state = ReplState::new();
        state
            .execute_geolog(&meta_content)
            .expect("GeologMeta should load");
        state
            .execute_geolog(&ir_content)
            .expect("RelAlgIR should load");

        state
            .theories
            .get("RelAlgIR")
            .expect("RelAlgIR should exist")
            .clone()
    }

    /// Generate a simple QueryOp without Constant/Apply (which need target context)
    fn arb_simple_query_op() -> impl Strategy<Value = QueryOp> {
        prop_oneof![
            // Scan
            (0..10usize).prop_map(|sort_idx| QueryOp::Scan { sort_idx }),
            // Empty
            Just(QueryOp::Empty),
        ]
    }

    /// Generate a nested QueryOp (depth 2)
    fn arb_nested_query_op() -> impl Strategy<Value = QueryOp> {
        arb_simple_query_op().prop_flat_map(|base| {
            prop_oneof![
                // Filter with various predicates
                Just(QueryOp::Filter {
                    input: Box::new(base.clone()),
                    pred: Predicate::True,
                }),
                Just(QueryOp::Filter {
                    input: Box::new(base.clone()),
                    pred: Predicate::False,
                }),
                Just(QueryOp::Filter {
                    input: Box::new(base.clone()),
                    pred: Predicate::ColEqCol { left: 0, right: 0 },
                }),
                // Negate
                Just(QueryOp::Negate {
                    input: Box::new(base.clone()),
                }),
                // Distinct
                Just(QueryOp::Distinct {
                    input: Box::new(base.clone()),
                }),
                // Project
                prop::collection::vec(0..3usize, 1..=3).prop_map(move |columns| QueryOp::Project {
                    input: Box::new(base.clone()),
                    columns,
                }),
            ]
        })
    }

    proptest! {
        /// Compiling simple QueryOps to RelAlgIR should not panic
        #[test]
        fn compile_simple_query_no_panic(plan in arb_simple_query_op()) {
            let relalg_theory = load_relalg_theory();
            let mut universe = Universe::new();

            // Should not panic - may error for Constant/Apply but shouldn't crash
            let _ = compile_to_relalg(&plan, &relalg_theory, &mut universe);
        }

        /// Compiling nested QueryOps to RelAlgIR should not panic
        #[test]
        fn compile_nested_query_no_panic(plan in arb_nested_query_op()) {
            let relalg_theory = load_relalg_theory();
            let mut universe = Universe::new();

            // Should not panic
            let _ = compile_to_relalg(&plan, &relalg_theory, &mut universe);
        }

        /// Compiled instances should have at least output wire
        #[test]
        fn compile_produces_valid_instance(plan in arb_simple_query_op()) {
            let relalg_theory = load_relalg_theory();
            let mut universe = Universe::new();

            if let Ok(instance) = compile_to_relalg(&plan, &relalg_theory, &mut universe) {
                // Instance should have elements
                prop_assert!(!instance.structure.is_empty(), "Instance should have elements");
                // Should have named elements including output wire
                prop_assert!(!instance.names.is_empty(), "Instance should have named elements");
            }
        }

        /// Compiling binary operations should work
        #[test]
        fn compile_binary_ops_no_panic(
            left_sort in 0..5usize,
            right_sort in 0..5usize,
        ) {
            let relalg_theory = load_relalg_theory();
            let mut universe = Universe::new();

            // Join (cross)
            let join_plan = QueryOp::Join {
                left: Box::new(QueryOp::Scan { sort_idx: left_sort }),
                right: Box::new(QueryOp::Scan { sort_idx: right_sort }),
                cond: geolog::query::JoinCond::Cross,
            };
            let _ = compile_to_relalg(&join_plan, &relalg_theory, &mut universe);

            // Join (equi)
            let equi_plan = QueryOp::Join {
                left: Box::new(QueryOp::Scan { sort_idx: left_sort }),
                right: Box::new(QueryOp::Scan { sort_idx: right_sort }),
                cond: geolog::query::JoinCond::Equi { left_col: 0, right_col: 0 },
            };
            let _ = compile_to_relalg(&equi_plan, &relalg_theory, &mut universe);

            // Union
            let union_plan = QueryOp::Union {
                left: Box::new(QueryOp::Scan { sort_idx: left_sort }),
                right: Box::new(QueryOp::Scan { sort_idx: right_sort }),
            };
            let _ = compile_to_relalg(&union_plan, &relalg_theory, &mut universe);
        }

        /// Compiling DBSP operators should work
        #[test]
        fn compile_dbsp_ops_no_panic(sort_idx in 0..5usize, state_id in 0..3usize) {
            let relalg_theory = load_relalg_theory();
            let mut universe = Universe::new();

            let scan = QueryOp::Scan { sort_idx };

            // Delay
            let delay_plan = QueryOp::Delay {
                input: Box::new(scan.clone()),
                state_id,
            };
            let _ = compile_to_relalg(&delay_plan, &relalg_theory, &mut universe);

            // Diff
            let diff_plan = QueryOp::Diff {
                input: Box::new(scan.clone()),
                state_id,
            };
            let _ = compile_to_relalg(&diff_plan, &relalg_theory, &mut universe);

            // Integrate
            let integrate_plan = QueryOp::Integrate {
                input: Box::new(scan),
                state_id,
            };
            let _ = compile_to_relalg(&integrate_plan, &relalg_theory, &mut universe);
        }

        /// Compiling all predicate types should work
        #[test]
        fn compile_all_predicate_types_no_panic(pred in super::arb_predicate()) {
            let relalg_theory = load_relalg_theory();
            let mut universe = Universe::new();

            let filter_plan = QueryOp::Filter {
                input: Box::new(QueryOp::Scan { sort_idx: 0 }),
                pred,
            };

            // Should compile without panic
            let _ = compile_to_relalg(&filter_plan, &relalg_theory, &mut universe);
        }
    }
}

// ============================================================================
// Chase Algorithm Proptests
// ============================================================================

mod chase_proptest {
    use super::*;
    use geolog::core::{Context, DerivedSort, Formula, RelationStorage, Sequent, Signature, Structure, Term, Theory, VecRelation};
    use geolog::cc::CongruenceClosure;
    use geolog::query::chase::{chase_step, chase_fixpoint};
    use geolog::universe::Universe;

    /// Generate a simple theory with one sort and one unary relation
    fn simple_relation_theory() -> Theory {
        let mut sig = Signature::default();
        sig.add_sort("V".to_string());
        sig.add_relation("R".to_string(), DerivedSort::Base(0));
        Theory {
            name: "Simple".to_string(),
            signature: sig,
            axioms: vec![],
            axiom_names: vec![],
        }
    }

    proptest! {
        #[test]
        fn chase_step_no_panic_on_empty_axioms(
            num_elements in 0..10usize,
        ) {
            let mut universe = Universe::new();
            let mut structure = {
                let mut s = Structure::new(1);
                for i in 0..num_elements {
                    s.carriers[0].insert(i as u64);
                }
                s.relations.push(VecRelation::new(1));
                s
            };
            let theory = simple_relation_theory();

            // Empty axioms should not change anything
            let mut cc = CongruenceClosure::new();
            let changed = chase_step(&[], &mut structure, &mut cc, &mut universe, &theory.signature).unwrap();
            prop_assert!(!changed);
        }

        #[test]
        fn chase_step_adds_to_relation(
            num_elements in 1..10usize,
        ) {
            let mut universe = Universe::new();
            let mut structure = {
                let mut s = Structure::new(1);
                for i in 0..num_elements {
                    s.carriers[0].insert(i as u64);
                }
                s.relations.push(VecRelation::new(1)); // Unary relation
                s
            };
            let theory = simple_relation_theory();

            // Axiom: forall x : V. |- R(x)
            let axiom = Sequent {
                context: Context {
                    vars: vec![("x".to_string(), DerivedSort::Base(0))],
                },
                premise: Formula::True,
                conclusion: Formula::Rel(0, Term::Var("x".to_string(), DerivedSort::Base(0))),
            };

            // First chase step should add elements
            let mut cc = CongruenceClosure::new();
            let changed = chase_step(&[axiom.clone()], &mut structure, &mut cc, &mut universe, &theory.signature).unwrap();

            if num_elements > 0 {
                prop_assert!(changed);
                prop_assert_eq!(structure.relations[0].len(), num_elements);
            }

            // Second chase step should not change anything
            let changed2 = chase_step(&[axiom], &mut structure, &mut cc, &mut universe, &theory.signature).unwrap();
            prop_assert!(!changed2);
        }

        #[test]
        fn chase_fixpoint_converges(
            num_elements in 1..8usize,
        ) {
            let mut universe = Universe::new();
            let mut structure = {
                let mut s = Structure::new(1);
                for i in 0..num_elements {
                    s.carriers[0].insert(i as u64);
                }
                s.relations.push(VecRelation::new(1)); // Unary relation
                s
            };
            let theory = simple_relation_theory();

            // Axiom: forall x : V. |- R(x)
            let axiom = Sequent {
                context: Context {
                    vars: vec![("x".to_string(), DerivedSort::Base(0))],
                },
                premise: Formula::True,
                conclusion: Formula::Rel(0, Term::Var("x".to_string(), DerivedSort::Base(0))),
            };

            // Chase should converge in exactly 2 iterations:
            // 1. Add all elements to relation
            // 2. Verify no more changes
            let iterations = chase_fixpoint(
                &[axiom],
                &mut structure,
                &mut universe,
                &theory.signature,
                100,
            ).unwrap();

            prop_assert_eq!(iterations, 2);
            prop_assert_eq!(structure.relations[0].len(), num_elements);
        }
    }
}
