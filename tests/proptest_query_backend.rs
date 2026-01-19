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

proptest! {
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
