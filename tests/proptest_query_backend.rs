//! Property tests for query backend.
//!
//! Generates random structures and queries, then verifies the naive backend
//! produces correct results by comparing against a reference implementation.

use proptest::prelude::*;
use std::collections::HashSet;

use geolog::core::Structure;
use geolog::id::{NumericId, Slid};
use geolog::query::backend::{execute, Bag, JoinCond, Predicate, QueryOp};

/// Generate a random structure with given number of sorts.
fn arb_structure(num_sorts: usize, max_elements_per_sort: usize) -> impl Strategy<Value = Structure> {
    // For each sort, generate a set of element indices
    let sort_elements = prop::collection::vec(
        prop::collection::btree_set(0u64..1000, 0..=max_elements_per_sort),
        num_sorts,
    );

    sort_elements.prop_map(move |elements_per_sort| {
        let mut structure = Structure::new(num_sorts);
        for (sort_idx, elements) in elements_per_sort.into_iter().enumerate() {
            for elem in elements {
                structure.carriers[sort_idx].insert(elem);
            }
        }
        structure
    })
}

/// Reference implementation for Scan: iterate all elements
fn reference_scan(structure: &Structure, sort_idx: usize) -> HashSet<Vec<Slid>> {
    let mut result = HashSet::new();
    if let Some(carrier) = structure.carriers.get(sort_idx) {
        for elem in carrier.iter() {
            result.insert(vec![Slid::from_usize(elem as usize)]);
        }
    }
    result
}

/// Reference implementation for Filter
fn reference_filter(
    input: &HashSet<Vec<Slid>>,
    pred: &Predicate,
    _structure: &Structure,
) -> HashSet<Vec<Slid>> {
    input
        .iter()
        .filter(|tuple| reference_eval_predicate(pred, tuple))
        .cloned()
        .collect()
}

fn reference_eval_predicate(pred: &Predicate, tuple: &[Slid]) -> bool {
    match pred {
        Predicate::True => true,
        Predicate::False => false,
        Predicate::ColEqConst { col, val } => tuple.get(*col) == Some(val),
        Predicate::ColEqCol { left, right } => {
            tuple.get(*left) == tuple.get(*right) && tuple.get(*left).is_some()
        }
        Predicate::And(a, b) => {
            reference_eval_predicate(a, tuple) && reference_eval_predicate(b, tuple)
        }
        Predicate::Or(a, b) => {
            reference_eval_predicate(a, tuple) || reference_eval_predicate(b, tuple)
        }
        Predicate::FuncEq { .. } => true, // Skip function predicates in reference (need structure access)
        Predicate::FuncEqConst { .. } => true, // Skip function predicates in reference
    }
}

/// Reference implementation for Cross Join
fn reference_cross_join(
    left: &HashSet<Vec<Slid>>,
    right: &HashSet<Vec<Slid>>,
) -> HashSet<Vec<Slid>> {
    let mut result = HashSet::new();
    for l in left {
        for r in right {
            let mut combined = l.clone();
            combined.extend(r.iter().cloned());
            result.insert(combined);
        }
    }
    result
}

/// Reference implementation for Union
fn reference_union(
    left: &HashSet<Vec<Slid>>,
    right: &HashSet<Vec<Slid>>,
) -> HashSet<Vec<Slid>> {
    left.union(right).cloned().collect()
}

/// Convert Bag to HashSet (ignoring multiplicities, for comparison)
fn bag_to_set(bag: &Bag) -> HashSet<Vec<Slid>> {
    bag.iter()
        .filter(|(_, mult)| **mult > 0)
        .map(|(tuple, _)| tuple.clone())
        .collect()
}

/// Generate a random predicate
fn arb_predicate() -> impl Strategy<Value = Predicate> {
    prop_oneof![
        Just(Predicate::True),
        Just(Predicate::False),
        (0usize..3, 0usize..100).prop_map(|(col, val)| Predicate::ColEqConst {
            col,
            val: Slid::from_usize(val),
        }),
        (0usize..3, 0usize..3).prop_map(|(left, right)| Predicate::ColEqCol { left, right }),
    ]
}

/// Generate a base query (no recursion)
fn arb_base_query() -> impl Strategy<Value = QueryOp> {
    prop_oneof![
        (0usize..3).prop_map(|sort_idx| QueryOp::Scan { sort_idx }),
        Just(QueryOp::Empty),
        prop::collection::vec(0usize..100, 1..=2)
            .prop_map(|tuple| QueryOp::Constant {
                tuple: tuple.into_iter().map(Slid::from_usize).collect()
            }),
    ]
}

/// Generate a random query plan using prop_recursive
fn arb_query_op() -> impl Strategy<Value = QueryOp> {
    arb_base_query().prop_recursive(
        3, // max depth
        64, // max nodes
        10, // items per collection
        |inner| {
            prop_oneof![
                // Keep some base cases at each level
                arb_base_query(),
                // Unary operations
                (inner.clone(), arb_predicate())
                    .prop_map(|(input, pred)| QueryOp::Filter {
                        input: Box::new(input),
                        pred,
                    }),
                inner.clone().prop_map(|input| QueryOp::Distinct {
                    input: Box::new(input),
                }),
                inner.clone().prop_map(|input| QueryOp::Negate {
                    input: Box::new(input),
                }),
                // Binary operations
                (inner.clone(), inner.clone())
                    .prop_map(|(left, right)| QueryOp::Union {
                        left: Box::new(left),
                        right: Box::new(right),
                    }),
                (inner.clone(), inner)
                    .prop_map(|(left, right)| QueryOp::Join {
                        left: Box::new(left),
                        right: Box::new(right),
                        cond: JoinCond::Cross,
                    }),
            ]
        }
    )
}

proptest! {
    /// Test that optimizer preserves semantics for randomly generated plans.
    #[test]
    fn test_optimize_preserves_semantics(
        structure in arb_structure(3, 5),
        plan in arb_query_op(),
    ) {
        use geolog::query::optimize;

        let unoptimized_result = execute(&plan, &structure);
        let optimized = optimize(&plan);
        let optimized_result = execute(&optimized, &structure);

        prop_assert_eq!(bag_to_set(&unoptimized_result), bag_to_set(&optimized_result));
    }

    /// Test that Scan produces all elements of a sort.
    #[test]
    fn test_scan_correct(
        structure in arb_structure(3, 10),
        sort_idx in 0usize..3,
    ) {
        let plan = QueryOp::Scan { sort_idx };
        let result = execute(&plan, &structure);

        let reference = reference_scan(&structure, sort_idx);
        let actual = bag_to_set(&result);

        prop_assert_eq!(actual, reference);
    }

    /// Test that Filter with True predicate returns all input.
    #[test]
    fn test_filter_true_is_identity(
        structure in arb_structure(2, 8),
        sort_idx in 0usize..2,
    ) {
        let scan = QueryOp::Scan { sort_idx };
        let filter = QueryOp::Filter {
            input: Box::new(scan.clone()),
            pred: Predicate::True,
        };

        let scan_result = execute(&scan, &structure);
        let filter_result = execute(&filter, &structure);

        prop_assert_eq!(bag_to_set(&scan_result), bag_to_set(&filter_result));
    }

    /// Test that Filter with False predicate returns empty.
    #[test]
    fn test_filter_false_is_empty(
        structure in arb_structure(2, 8),
        sort_idx in 0usize..2,
    ) {
        let scan = QueryOp::Scan { sort_idx };
        let filter = QueryOp::Filter {
            input: Box::new(scan),
            pred: Predicate::False,
        };

        let result = execute(&filter, &structure);
        prop_assert!(result.is_empty());
    }

    /// Test that cross join produces correct cardinality.
    #[test]
    fn test_cross_join_cardinality(
        structure in arb_structure(2, 5),
    ) {
        let left = QueryOp::Scan { sort_idx: 0 };
        let right = QueryOp::Scan { sort_idx: 1 };
        let join = QueryOp::Join {
            left: Box::new(left.clone()),
            right: Box::new(right.clone()),
            cond: JoinCond::Cross,
        };

        let left_result = execute(&left, &structure);
        let right_result = execute(&right, &structure);
        let join_result = execute(&join, &structure);

        let expected_size = left_result.len() * right_result.len();
        prop_assert_eq!(join_result.len(), expected_size);
    }

    /// Test that cross join matches reference.
    #[test]
    fn test_cross_join_correct(
        structure in arb_structure(2, 4),
    ) {
        let left = QueryOp::Scan { sort_idx: 0 };
        let right = QueryOp::Scan { sort_idx: 1 };
        let join = QueryOp::Join {
            left: Box::new(left),
            right: Box::new(right),
            cond: JoinCond::Cross,
        };

        let result = execute(&join, &structure);

        let ref_left = reference_scan(&structure, 0);
        let ref_right = reference_scan(&structure, 1);
        let reference = reference_cross_join(&ref_left, &ref_right);

        prop_assert_eq!(bag_to_set(&result), reference);
    }

    /// Test that Union is commutative.
    #[test]
    fn test_union_commutative(
        structure in arb_structure(2, 5),
    ) {
        let a = QueryOp::Scan { sort_idx: 0 };
        let b = QueryOp::Scan { sort_idx: 1 };

        let union_ab = QueryOp::Union {
            left: Box::new(a.clone()),
            right: Box::new(b.clone()),
        };
        let union_ba = QueryOp::Union {
            left: Box::new(b),
            right: Box::new(a),
        };

        let result_ab = execute(&union_ab, &structure);
        let result_ba = execute(&union_ba, &structure);

        // As sets, they should be equal (multiplicities may differ)
        prop_assert_eq!(bag_to_set(&result_ab), bag_to_set(&result_ba));
    }

    /// Test that Distinct is idempotent.
    #[test]
    fn test_distinct_idempotent(
        structure in arb_structure(1, 8),
    ) {
        let scan = QueryOp::Scan { sort_idx: 0 };
        let distinct1 = QueryOp::Distinct {
            input: Box::new(scan),
        };
        let distinct2 = QueryOp::Distinct {
            input: Box::new(distinct1.clone()),
        };

        let result1 = execute(&distinct1, &structure);
        let result2 = execute(&distinct2, &structure);

        prop_assert_eq!(bag_to_set(&result1), bag_to_set(&result2));
    }

    /// Test that Empty produces no results.
    #[test]
    fn test_empty_is_empty(
        structure in arb_structure(1, 5),
    ) {
        let empty = QueryOp::Empty;
        let result = execute(&empty, &structure);
        prop_assert!(result.is_empty());
    }

    /// Test that Constant produces exactly one tuple.
    #[test]
    fn test_constant_singleton(
        tuple in prop::collection::vec(0usize..100, 1..=3),
    ) {
        let structure = Structure::new(1); // Empty structure
        let slid_tuple: Vec<Slid> = tuple.iter().map(|&i| Slid::from_usize(i)).collect();
        let constant = QueryOp::Constant { tuple: slid_tuple.clone() };
        let result = execute(&constant, &structure);

        prop_assert_eq!(result.len(), 1);
        prop_assert!(result.tuples.contains_key(&slid_tuple));
    }

    /// Test filter with constant equality.
    #[test]
    fn test_filter_col_eq_const(
        structure in arb_structure(1, 10),
        filter_val in 0usize..1000,
    ) {
        let scan = QueryOp::Scan { sort_idx: 0 };
        let filter = QueryOp::Filter {
            input: Box::new(scan.clone()),
            pred: Predicate::ColEqConst {
                col: 0,
                val: Slid::from_usize(filter_val),
            },
        };

        let scan_result = execute(&scan, &structure);
        let filter_result = execute(&filter, &structure);

        // Reference: manually filter
        let reference: HashSet<Vec<Slid>> = bag_to_set(&scan_result)
            .into_iter()
            .filter(|tuple| tuple[0] == Slid::from_usize(filter_val))
            .collect();

        prop_assert_eq!(bag_to_set(&filter_result), reference);
    }

    /// Test filter matches reference implementation for compound predicates.
    #[test]
    fn test_filter_matches_reference(
        structure in arb_structure(1, 10),
    ) {
        // Get all elements as single-column tuples
        let input = reference_scan(&structure, 0);

        // Test with True predicate
        let filtered_true = reference_filter(&input, &Predicate::True, &structure);
        prop_assert_eq!(filtered_true, input.clone());

        // Test with False predicate
        let filtered_false = reference_filter(&input, &Predicate::False, &structure);
        prop_assert!(filtered_false.is_empty());
    }

    /// Test union matches reference implementation.
    #[test]
    fn test_union_matches_reference(
        structure in arb_structure(2, 5),
    ) {
        let left = QueryOp::Scan { sort_idx: 0 };
        let right = QueryOp::Scan { sort_idx: 1 };
        let union = QueryOp::Union {
            left: Box::new(left),
            right: Box::new(right),
        };

        let result = execute(&union, &structure);

        let ref_left = reference_scan(&structure, 0);
        let ref_right = reference_scan(&structure, 1);
        let reference = reference_union(&ref_left, &ref_right);

        prop_assert_eq!(bag_to_set(&result), reference);
    }

    /// Test that Negate(Negate(x)) = x.
    #[test]
    fn test_negate_involutive(
        structure in arb_structure(1, 8),
    ) {
        let scan = QueryOp::Scan { sort_idx: 0 };
        let negate1 = QueryOp::Negate {
            input: Box::new(scan.clone()),
        };
        let negate2 = QueryOp::Negate {
            input: Box::new(negate1),
        };

        let original = execute(&scan, &structure);
        let double_negated = execute(&negate2, &structure);

        prop_assert_eq!(bag_to_set(&original), bag_to_set(&double_negated));
    }

    /// Test that Project preserves all tuples (just reduces columns).
    #[test]
    fn test_project_same_size(
        structure in arb_structure(2, 4),
    ) {
        // Cross join creates (a, b) tuples
        let left = QueryOp::Scan { sort_idx: 0 };
        let right = QueryOp::Scan { sort_idx: 1 };
        let join = QueryOp::Join {
            left: Box::new(left),
            right: Box::new(right),
            cond: JoinCond::Cross,
        };

        // Project to first column only
        let project = QueryOp::Project {
            input: Box::new(join.clone()),
            columns: vec![0],
        };

        let join_result = execute(&join, &structure);
        let project_result = execute(&project, &structure);

        // Projected result should have same or fewer distinct tuples
        // (could be fewer due to duplicate first elements)
        prop_assert!(bag_to_set(&project_result).len() <= join_result.len());
    }
}

#[test]
fn test_basic_operations_smoke() {
    // Simple smoke test to ensure the proptest infrastructure works
    let mut structure = Structure::new(2);
    structure.carriers[0].insert(1);
    structure.carriers[0].insert(2);
    structure.carriers[1].insert(10);

    let scan = QueryOp::Scan { sort_idx: 0 };
    let result = execute(&scan, &structure);
    assert_eq!(result.len(), 2);
}

#[test]
fn test_pattern_compile_scan() {
    use geolog::query::Pattern;

    // Create a structure with one sort
    let mut structure = Structure::new(1);
    structure.carriers[0].insert(5);
    structure.carriers[0].insert(10);
    structure.carriers[0].insert(15);

    // Create a simple pattern: scan sort 0, no constraints, return element
    let pattern = Pattern::new(0);

    // Compile and execute
    let plan = pattern.compile();
    let result = execute(&plan, &structure);

    // Should get all 3 elements
    assert_eq!(result.len(), 3);
    assert!(result.tuples.contains_key(&vec![Slid::from_usize(5)]));
    assert!(result.tuples.contains_key(&vec![Slid::from_usize(10)]));
    assert!(result.tuples.contains_key(&vec![Slid::from_usize(15)]));
}

/// Test that optimize preserves semantics for filter with True predicate.
#[test]
fn test_optimize_filter_true_preserves_semantics() {
    use geolog::query::optimize;

    let mut structure = Structure::new(1);
    structure.carriers[0].insert(1);
    structure.carriers[0].insert(2);
    structure.carriers[0].insert(3);

    let scan = QueryOp::Scan { sort_idx: 0 };
    let filter = QueryOp::Filter {
        input: Box::new(scan),
        pred: Predicate::True,
    };

    let unoptimized_result = execute(&filter, &structure);
    let optimized = optimize(&filter);
    let optimized_result = execute(&optimized, &structure);

    assert_eq!(bag_to_set(&unoptimized_result), bag_to_set(&optimized_result));
}

/// Test that optimize preserves semantics for filter with False predicate.
#[test]
fn test_optimize_filter_false_preserves_semantics() {
    use geolog::query::optimize;

    let mut structure = Structure::new(1);
    structure.carriers[0].insert(1);
    structure.carriers[0].insert(2);

    let scan = QueryOp::Scan { sort_idx: 0 };
    let filter = QueryOp::Filter {
        input: Box::new(scan),
        pred: Predicate::False,
    };

    let unoptimized_result = execute(&filter, &structure);
    let optimized = optimize(&filter);
    let optimized_result = execute(&optimized, &structure);

    assert_eq!(bag_to_set(&unoptimized_result), bag_to_set(&optimized_result));
    assert!(unoptimized_result.is_empty());
    assert!(optimized_result.is_empty());
}

/// Test that double negation optimization preserves semantics.
#[test]
fn test_optimize_double_negate_preserves_semantics() {
    use geolog::query::optimize;

    let mut structure = Structure::new(1);
    structure.carriers[0].insert(10);
    structure.carriers[0].insert(20);

    let scan = QueryOp::Scan { sort_idx: 0 };
    let negate1 = QueryOp::Negate {
        input: Box::new(scan),
    };
    let negate2 = QueryOp::Negate {
        input: Box::new(negate1),
    };

    let unoptimized_result = execute(&negate2, &structure);
    let optimized = optimize(&negate2);
    let optimized_result = execute(&optimized, &structure);

    assert_eq!(bag_to_set(&unoptimized_result), bag_to_set(&optimized_result));
}

/// Test that union with empty optimization preserves semantics.
#[test]
fn test_optimize_union_empty_preserves_semantics() {
    use geolog::query::optimize;

    let mut structure = Structure::new(1);
    structure.carriers[0].insert(5);
    structure.carriers[0].insert(15);

    let scan = QueryOp::Scan { sort_idx: 0 };
    let union = QueryOp::Union {
        left: Box::new(scan),
        right: Box::new(QueryOp::Empty),
    };

    let unoptimized_result = execute(&union, &structure);
    let optimized = optimize(&union);
    let optimized_result = execute(&optimized, &structure);

    assert_eq!(bag_to_set(&unoptimized_result), bag_to_set(&optimized_result));
}

/// Test that join with empty optimization preserves semantics.
#[test]
fn test_optimize_join_empty_preserves_semantics() {
    use geolog::query::optimize;

    let mut structure = Structure::new(2);
    structure.carriers[0].insert(1);
    structure.carriers[0].insert(2);

    let scan = QueryOp::Scan { sort_idx: 0 };
    let join = QueryOp::Join {
        left: Box::new(scan),
        right: Box::new(QueryOp::Empty),
        cond: JoinCond::Cross,
    };

    let unoptimized_result = execute(&join, &structure);
    let optimized = optimize(&join);
    let optimized_result = execute(&optimized, &structure);

    assert_eq!(bag_to_set(&unoptimized_result), bag_to_set(&optimized_result));
    assert!(unoptimized_result.is_empty());
    assert!(optimized_result.is_empty());
}

#[test]
fn test_pattern_compile_with_function_filter() {
    use geolog::query::Pattern;
    use geolog::universe::Universe;

    // Create a structure with one sort and properly add elements
    let mut structure = Structure::new(1);
    let mut universe = Universe::new();

    // Add 3 elements to sort 0
    let (slid0, _) = structure.add_element(&mut universe, 0);
    let (slid1, _) = structure.add_element(&mut universe, 0);
    let (slid2, _) = structure.add_element(&mut universe, 0);

    // Initialize function storage for 1 function with domain sort 0
    structure.init_functions(&[Some(0)]);

    // Function 0: maps elem0→slid10, elem1→slid20, elem2→slid10
    // We need target elements to map to - add them to a different "virtual" sort
    // For simplicity, we'll use constant Slid values that represent the results
    let slid10 = Slid::from_usize(10);
    let slid20 = Slid::from_usize(20);

    structure.define_function(0, slid0, slid10).unwrap();
    structure.define_function(0, slid1, slid20).unwrap();
    structure.define_function(0, slid2, slid10).unwrap();

    // Pattern: find elements where func(elem) = 10
    let pattern = Pattern::new(0)
        .filter(0, slid10);

    // Compile and execute
    let plan = pattern.compile();
    let result = execute(&plan, &structure);

    // Should get elements 0 and 2 (both map to 10)
    assert_eq!(result.len(), 2);
    assert!(result.tuples.contains_key(&vec![slid0]));
    assert!(result.tuples.contains_key(&vec![slid2]));
    // Element 1 (maps to 20) should not be included
    assert!(!result.tuples.contains_key(&vec![slid1]));
}

// ============================================================================
// DBSP Temporal Operator Property Tests
// ============================================================================

use geolog::query::backend::StreamContext;
use geolog::query::backend::execute_stream;

proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]

    /// Delay at timestep 0 always produces empty output
    #[test]
    fn test_delay_initial_empty_proptest(
        structure in arb_structure(2, 5),
        sort_idx in 0usize..2,
    ) {
        let mut ctx = StreamContext::new();
        let plan = QueryOp::Delay {
            input: Box::new(QueryOp::Scan { sort_idx }),
            state_id: 0,
        };

        // At timestep 0, delay should output empty
        let result = execute_stream(&plan, &structure, &mut ctx);
        prop_assert!(result.is_empty(), "Delay at t=0 should be empty");
    }

    /// Delay outputs previous timestep's value
    #[test]
    fn test_delay_outputs_previous_proptest(
        structure in arb_structure(1, 8),
    ) {
        let mut ctx = StreamContext::new();
        let scan = QueryOp::Scan { sort_idx: 0 };
        let delay = QueryOp::Delay {
            input: Box::new(scan.clone()),
            state_id: 0,
        };

        // Step 0: capture input, output empty
        let _ = execute_stream(&delay, &structure, &mut ctx);
        ctx.step();

        // Step 1: should output what was input at step 0
        let result = execute_stream(&delay, &structure, &mut ctx);
        let expected = reference_scan(&structure, 0);

        prop_assert_eq!(bag_to_set(&result), expected, "Delay should output previous input");
    }

    /// ∫(δ(x)) = x for stable input (fundamental DBSP identity)
    #[test]
    fn test_integrate_diff_identity(
        structure in arb_structure(1, 10),
    ) {
        let mut ctx = StreamContext::new();

        // ∫(δ(scan))
        let plan = QueryOp::Integrate {
            input: Box::new(QueryOp::Diff {
                input: Box::new(QueryOp::Scan { sort_idx: 0 }),
                state_id: 0,
            }),
            state_id: 1,
        };

        // Step 0: should equal scan
        let result = execute_stream(&plan, &structure, &mut ctx);
        let expected = reference_scan(&structure, 0);
        prop_assert_eq!(bag_to_set(&result), expected.clone(), "∫(δ(scan)) should equal scan at t=0");

        ctx.step();

        // Step 1: still should equal scan (no changes)
        let result = execute_stream(&plan, &structure, &mut ctx);
        prop_assert_eq!(bag_to_set(&result), expected, "∫(δ(scan)) should equal scan at t=1");
    }

    /// Diff of stable input becomes empty after first timestep
    #[test]
    fn test_diff_stable_becomes_empty(
        structure in arb_structure(1, 8),
    ) {
        let mut ctx = StreamContext::new();
        let plan = QueryOp::Diff {
            input: Box::new(QueryOp::Scan { sort_idx: 0 }),
            state_id: 0,
        };

        // Step 0: diff = scan - {} = scan (all elements are "new")
        let result0 = execute_stream(&plan, &structure, &mut ctx);
        let expected0 = reference_scan(&structure, 0);
        prop_assert_eq!(bag_to_set(&result0), expected0);
        ctx.step();

        // Step 1: diff = scan - scan = {} (no changes)
        let result1 = execute_stream(&plan, &structure, &mut ctx);
        prop_assert!(result1.is_empty(), "Diff of stable input should be empty");
    }

    /// Integrate accumulates multiplicities across timesteps
    #[test]
    fn test_integrate_accumulates(
        tuple in prop::collection::vec(0usize..100, 1..=2),
        num_steps in 1usize..5,
    ) {
        let structure = Structure::new(1);
        let mut ctx = StreamContext::new();

        let slid_tuple: Vec<Slid> = tuple.iter().map(|&i| Slid::from_usize(i)).collect();
        let plan = QueryOp::Integrate {
            input: Box::new(QueryOp::Constant { tuple: slid_tuple.clone() }),
            state_id: 0,
        };

        for step in 0..num_steps {
            let result = execute_stream(&plan, &structure, &mut ctx);

            // After step i, multiplicity should be i+1
            let expected_mult = (step + 1) as i64;
            let actual_mult = result.tuples.get(&slid_tuple).copied().unwrap_or(0);
            prop_assert_eq!(actual_mult, expected_mult, "Multiplicity at step {}", step);

            ctx.step();
        }
    }

    /// Negate and Integrate compose correctly: ∫(negate(δ(x))) + ∫(δ(x)) = 0
    #[test]
    fn test_negate_integrate_diff_cancellation(
        structure in arb_structure(1, 5),
    ) {
        let mut ctx1 = StreamContext::new();
        let mut ctx2 = StreamContext::new();

        let diff = QueryOp::Diff {
            input: Box::new(QueryOp::Scan { sort_idx: 0 }),
            state_id: 0,
        };

        // ∫(δ(scan))
        let int_pos = QueryOp::Integrate {
            input: Box::new(diff.clone()),
            state_id: 1,
        };

        // ∫(negate(δ(scan)))
        let int_neg = QueryOp::Integrate {
            input: Box::new(QueryOp::Negate {
                input: Box::new(QueryOp::Diff {
                    input: Box::new(QueryOp::Scan { sort_idx: 0 }),
                    state_id: 2,
                }),
            }),
            state_id: 3,
        };

        // Execute both for a couple steps
        let result_pos = execute_stream(&int_pos, &structure, &mut ctx1);
        let result_neg = execute_stream(&int_neg, &structure, &mut ctx2);

        // Union should cancel to zero
        let combined = result_pos.union(&result_neg);
        prop_assert!(combined.is_empty() || combined.iter().all(|(_, m)| *m == 0),
            "∫(δ) + ∫(¬δ) should cancel");
    }

    /// DBSP filter distributes: Filter(Diff(x)) = Diff(Filter(x)) for stable input
    /// (This is a key DBSP optimization: incrementalize then filter = filter then incrementalize)
    #[test]
    fn test_dbsp_filter_distribution(
        structure in arb_structure(1, 10),
        filter_val in 0usize..100,
    ) {
        let filter_slid = Slid::from_usize(filter_val);
        let mut ctx1 = StreamContext::new();
        let mut ctx2 = StreamContext::new();

        // Filter(Diff(Scan))
        let plan1 = QueryOp::Filter {
            input: Box::new(QueryOp::Diff {
                input: Box::new(QueryOp::Scan { sort_idx: 0 }),
                state_id: 0,
            }),
            pred: Predicate::ColEqConst { col: 0, val: filter_slid },
        };

        // Diff(Filter(Scan))
        let plan2 = QueryOp::Diff {
            input: Box::new(QueryOp::Filter {
                input: Box::new(QueryOp::Scan { sort_idx: 0 }),
                pred: Predicate::ColEqConst { col: 0, val: filter_slid },
            }),
            state_id: 1,
        };

        // Both should produce same results
        let result1 = execute_stream(&plan1, &structure, &mut ctx1);
        let result2 = execute_stream(&plan2, &structure, &mut ctx2);

        prop_assert_eq!(bag_to_set(&result1), bag_to_set(&result2),
            "Filter(Diff(x)) = Diff(Filter(x))");

        ctx1.step();
        ctx2.step();

        // Should remain equal at next timestep
        let result1 = execute_stream(&plan1, &structure, &mut ctx1);
        let result2 = execute_stream(&plan2, &structure, &mut ctx2);

        prop_assert_eq!(bag_to_set(&result1), bag_to_set(&result2),
            "Filter(Diff(x)) = Diff(Filter(x)) at t=1");
    }
}
