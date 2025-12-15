//! Property tests for tensor operations
//!
//! Tests algebraic properties of tensor operations using proptest.

mod generators;

use generators::{TensorParams, arb_sparse_tensor, arb_tensor_pair_same_dims, arb_sparse_tensor_with_dims};
use geolog::tensor::{SparseTensor, TensorExpr, conjunction, exists, conjunction_all, disjunction_all};
use proptest::prelude::*;

// ============================================================================
// SparseTensor Basic Properties
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1024))]

    /// Empty tensor has no tuples
    #[test]
    fn empty_tensor_is_empty(dims in proptest::collection::vec(1usize..10, 0..4)) {
        let tensor = SparseTensor::empty(dims.clone());
        prop_assert!(tensor.is_empty());
        prop_assert_eq!(tensor.len(), 0);
        prop_assert_eq!(tensor.dims, dims);
    }

    /// Scalar true contains the empty tuple
    #[test]
    fn scalar_true_contains_empty(_seed in any::<u64>()) {
        let tensor = SparseTensor::scalar(true);
        prop_assert!(tensor.contains(&[]));
        prop_assert_eq!(tensor.len(), 1);
        prop_assert!(tensor.dims.is_empty());
    }

    /// Scalar false is empty
    #[test]
    fn scalar_false_is_empty(_seed in any::<u64>()) {
        let tensor = SparseTensor::scalar(false);
        prop_assert!(!tensor.contains(&[]));
        prop_assert!(tensor.is_empty());
    }

    /// Insert/remove roundtrip
    #[test]
    fn insert_remove_roundtrip(
        dims in proptest::collection::vec(1usize..5, 1..3),
        tuple_idx in any::<prop::sample::Index>(),
    ) {
        let mut tensor = SparseTensor::empty(dims.clone());

        // Generate a valid tuple
        let tuple: Vec<usize> = dims.iter()
            .map(|&d| tuple_idx.index(d.max(1)))
            .collect();

        prop_assert!(!tensor.contains(&tuple));
        tensor.insert(tuple.clone());
        prop_assert!(tensor.contains(&tuple));
        tensor.remove(&tuple);
        prop_assert!(!tensor.contains(&tuple));
    }

    /// Generated tensor has valid tuples (within dimension bounds)
    #[test]
    fn generated_tensor_valid_tuples(
        tensor in arb_sparse_tensor(TensorParams::default())
    ) {
        for tuple in tensor.iter() {
            prop_assert_eq!(tuple.len(), tensor.dims.len());
            for (i, &val) in tuple.iter().enumerate() {
                prop_assert!(val < tensor.dims[i], "tuple value {} >= dim {}", val, tensor.dims[i]);
            }
        }
    }
}

// ============================================================================
// TensorExpr Product Properties
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(512))]

    /// Product of empty tensors is empty
    #[test]
    fn product_with_empty_is_empty(
        tensor in arb_sparse_tensor(TensorParams { max_dims: 2, max_dim_size: 5, max_tuples: 10 })
    ) {
        let empty = SparseTensor::empty(vec![3]);
        let expr = TensorExpr::Product(vec![
            TensorExpr::leaf(tensor),
            TensorExpr::leaf(empty),
        ]);
        let result = expr.materialize();
        prop_assert!(result.is_empty());
    }

    /// Product with scalar true is identity (dims extended but tuples preserved)
    #[test]
    fn product_with_scalar_true(
        tensor in arb_sparse_tensor(TensorParams { max_dims: 2, max_dim_size: 5, max_tuples: 10 })
    ) {
        let scalar_true = SparseTensor::scalar(true);
        let orig_len = tensor.len();
        let orig_dims = tensor.dims.clone();

        let expr = TensorExpr::Product(vec![
            TensorExpr::leaf(tensor),
            TensorExpr::leaf(scalar_true),
        ]);
        let result = expr.materialize();

        prop_assert_eq!(result.len(), orig_len);
        prop_assert_eq!(result.dims, orig_dims);
    }

    /// Empty product is scalar true
    #[test]
    fn empty_product_is_scalar_true(_seed in any::<u64>()) {
        let expr = TensorExpr::Product(vec![]);
        let result = expr.materialize();
        prop_assert!(result.contains(&[]));
        prop_assert_eq!(result.len(), 1);
    }

    /// Product dimensions are concatenation
    #[test]
    fn product_dims_concatenate(
        t1 in arb_sparse_tensor(TensorParams { max_dims: 2, max_dim_size: 4, max_tuples: 5 }),
        t2 in arb_sparse_tensor(TensorParams { max_dims: 2, max_dim_size: 4, max_tuples: 5 }),
    ) {
        let expected_dims: Vec<usize> = t1.dims.iter().chain(t2.dims.iter()).copied().collect();

        let expr = TensorExpr::Product(vec![
            TensorExpr::leaf(t1),
            TensorExpr::leaf(t2),
        ]);
        let result = expr.materialize();

        prop_assert_eq!(result.dims, expected_dims);
    }
}

// ============================================================================
// Sum (Disjunction) Properties
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(512))]

    /// Sum is commutative
    #[test]
    fn sum_commutative(
        (t1, t2) in arb_tensor_pair_same_dims(TensorParams { max_dims: 2, max_dim_size: 5, max_tuples: 10 })
    ) {
        let sum1 = TensorExpr::Sum(vec![
            TensorExpr::leaf(t1.clone()),
            TensorExpr::leaf(t2.clone()),
        ]).materialize();

        let sum2 = TensorExpr::Sum(vec![
            TensorExpr::leaf(t2),
            TensorExpr::leaf(t1),
        ]).materialize();

        prop_assert_eq!(sum1, sum2);
    }

    /// Sum is idempotent (T ∨ T = T)
    #[test]
    fn sum_idempotent(
        tensor in arb_sparse_tensor(TensorParams { max_dims: 2, max_dim_size: 5, max_tuples: 10 })
    ) {
        let sum = TensorExpr::Sum(vec![
            TensorExpr::leaf(tensor.clone()),
            TensorExpr::leaf(tensor.clone()),
        ]).materialize();

        prop_assert_eq!(sum, tensor);
    }

    /// Sum with empty is identity
    #[test]
    fn sum_with_empty_is_identity(
        tensor in arb_sparse_tensor(TensorParams { max_dims: 2, max_dim_size: 5, max_tuples: 10 })
    ) {
        let empty = SparseTensor::empty(tensor.dims.clone());
        let sum = TensorExpr::Sum(vec![
            TensorExpr::leaf(tensor.clone()),
            TensorExpr::leaf(empty),
        ]).materialize();

        prop_assert_eq!(sum, tensor);
    }

    /// Empty sum is scalar false
    #[test]
    fn empty_sum_is_scalar_false(_seed in any::<u64>()) {
        let sum = TensorExpr::Sum(vec![]).materialize();
        prop_assert!(sum.is_empty());
    }

    /// Sum extent is union of extents
    #[test]
    fn sum_is_union(
        (t1, t2) in arb_tensor_pair_same_dims(TensorParams { max_dims: 2, max_dim_size: 5, max_tuples: 10 })
    ) {
        let sum = TensorExpr::Sum(vec![
            TensorExpr::leaf(t1.clone()),
            TensorExpr::leaf(t2.clone()),
        ]).materialize();

        // Every tuple in t1 should be in sum
        for tuple in t1.iter() {
            prop_assert!(sum.contains(tuple));
        }

        // Every tuple in t2 should be in sum
        for tuple in t2.iter() {
            prop_assert!(sum.contains(tuple));
        }

        // Every tuple in sum should be in t1 or t2
        for tuple in sum.iter() {
            prop_assert!(t1.contains(tuple) || t2.contains(tuple));
        }
    }
}

// ============================================================================
// Conjunction Properties
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    /// Conjunction with scalar true is identity (modulo variable naming)
    #[test]
    fn conjunction_with_true(
        tensor in arb_sparse_tensor_with_dims(vec![3, 3], 5)
    ) {
        let vars = vec!["x".to_string(), "y".to_string()];
        let scalar_true = SparseTensor::scalar(true);

        let (expr, result_vars) = conjunction(
            TensorExpr::leaf(tensor.clone()),
            &vars,
            TensorExpr::leaf(scalar_true),
            &[],
        );
        let result = expr.materialize();

        prop_assert_eq!(result_vars, vars);
        prop_assert_eq!(result, tensor);
    }

    /// Conjunction with scalar false is empty
    #[test]
    fn conjunction_with_false(
        tensor in arb_sparse_tensor_with_dims(vec![3, 3], 5)
    ) {
        let vars = vec!["x".to_string(), "y".to_string()];
        let scalar_false = SparseTensor::scalar(false);

        let (expr, _result_vars) = conjunction(
            TensorExpr::leaf(tensor),
            &vars,
            TensorExpr::leaf(scalar_false),
            &[],
        );
        let result = expr.materialize();

        prop_assert!(result.is_empty());
    }

    /// Conjunction is commutative (on shared variables)
    #[test]
    fn conjunction_commutative(
        t1 in arb_sparse_tensor_with_dims(vec![3, 4], 5),
        t2 in arb_sparse_tensor_with_dims(vec![4, 5], 5),
    ) {
        let vars1 = vec!["x".to_string(), "y".to_string()];
        let vars2 = vec!["y".to_string(), "z".to_string()];

        let (expr1, _vars_result1) = conjunction(
            TensorExpr::leaf(t1.clone()),
            &vars1,
            TensorExpr::leaf(t2.clone()),
            &vars2,
        );

        let (expr2, _vars_result2) = conjunction(
            TensorExpr::leaf(t2),
            &vars2,
            TensorExpr::leaf(t1),
            &vars1,
        );

        let result1 = expr1.materialize();
        let result2 = expr2.materialize();

        // Same number of tuples (though variable order may differ)
        prop_assert_eq!(result1.len(), result2.len());
    }
}

// ============================================================================
// Exists (Contraction) Properties
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    /// Exists on non-existent variable is identity
    #[test]
    fn exists_nonexistent_var(
        tensor in arb_sparse_tensor_with_dims(vec![3, 3], 5)
    ) {
        let vars = vec!["x".to_string(), "y".to_string()];
        let (expr, result_vars) = exists(TensorExpr::leaf(tensor.clone()), &vars, "z");
        let result = expr.materialize();

        prop_assert_eq!(result_vars, vars);
        prop_assert_eq!(result, tensor);
    }

    /// Exists reduces arity by 1
    #[test]
    fn exists_reduces_arity(
        tensor in arb_sparse_tensor_with_dims(vec![3, 4], 8)
    ) {
        let vars = vec!["x".to_string(), "y".to_string()];
        let (expr, result_vars) = exists(TensorExpr::leaf(tensor), &vars, "y");
        let result = expr.materialize();

        prop_assert_eq!(result_vars, vec!["x"]);
        prop_assert_eq!(result.arity(), 1);
        prop_assert_eq!(result.dims, vec![3]);
    }

    /// Exists on scalar is identity
    #[test]
    fn exists_on_scalar(value in any::<bool>()) {
        let tensor = SparseTensor::scalar(value);
        let (expr, result_vars) = exists(TensorExpr::leaf(tensor.clone()), &[], "x");
        let result = expr.materialize();

        prop_assert!(result_vars.is_empty());
        prop_assert_eq!(result, tensor);
    }

    /// Double exists is same as single exists (idempotent on same var)
    #[test]
    fn exists_idempotent(
        tensor in arb_sparse_tensor_with_dims(vec![3, 4], 8)
    ) {
        let vars = vec!["x".to_string(), "y".to_string()];

        let (expr1, vars1) = exists(TensorExpr::leaf(tensor.clone()), &vars, "y");
        let (expr2, vars2) = exists(expr1, &vars1, "y");

        let result = expr2.materialize();

        prop_assert_eq!(vars2, vec!["x"]);
        prop_assert_eq!(result.arity(), 1);
    }
}

// ============================================================================
// Fusion Tests (Contract(Product(...)))
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(128))]

    /// Fused join produces same result as naive evaluation
    #[test]
    fn fused_join_correctness(
        t1 in arb_sparse_tensor_with_dims(vec![5, 5], 10),
        t2 in arb_sparse_tensor_with_dims(vec![5, 5], 10),
    ) {
        let vars1 = vec!["x".to_string(), "y".to_string()];
        let vars2 = vec!["y".to_string(), "z".to_string()];

        // This creates Contract(Product(...)) which gets fused
        let (conj_expr, conj_vars) = conjunction(
            TensorExpr::leaf(t1.clone()),
            &vars1,
            TensorExpr::leaf(t2.clone()),
            &vars2,
        );

        let (result_expr, _result_vars) = exists(conj_expr, &conj_vars, "y");
        let result = result_expr.materialize();

        // Verify result is correct by checking each tuple
        for tuple in result.iter() {
            let x = tuple[0];
            let z = tuple[1];

            // Should exist some y such that t1(x,y) and t2(y,z)
            let mut found = false;
            for y in 0..5 {
                if t1.contains(&[x, y]) && t2.contains(&[y, z]) {
                    found = true;
                    break;
                }
            }
            prop_assert!(found, "tuple {:?} in result but no witness y", tuple);
        }

        // And every valid (x,z) should be in result
        for x in 0..5 {
            for z in 0..5 {
                let mut should_be_in_result = false;
                for y in 0..5 {
                    if t1.contains(&[x, y]) && t2.contains(&[y, z]) {
                        should_be_in_result = true;
                        break;
                    }
                }
                prop_assert_eq!(
                    result.contains(&[x, z]),
                    should_be_in_result,
                    "({}, {}) expected {} but got {}",
                    x, z, should_be_in_result, result.contains(&[x, z])
                );
            }
        }
    }
}

// ============================================================================
// Disjunction Helper Tests
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    /// disjunction_all with empty is scalar false
    #[test]
    fn disjunction_all_empty(_seed in any::<u64>()) {
        let (expr, vars) = disjunction_all(vec![]);
        let result = expr.materialize();

        prop_assert!(vars.is_empty());
        prop_assert!(result.is_empty());
    }

    /// disjunction_all with single element is identity
    #[test]
    fn disjunction_all_single(
        tensor in arb_sparse_tensor_with_dims(vec![3, 3], 5)
    ) {
        let vars = vec!["x".to_string(), "y".to_string()];
        let (expr, result_vars) = disjunction_all(vec![
            (TensorExpr::leaf(tensor.clone()), vars.clone())
        ]);
        let result = expr.materialize();

        prop_assert_eq!(result_vars, vars);
        prop_assert_eq!(result, tensor);
    }

    /// conjunction_all with empty is scalar true
    #[test]
    fn conjunction_all_empty(_seed in any::<u64>()) {
        let (expr, vars) = conjunction_all(vec![]);
        let result = expr.materialize();

        prop_assert!(vars.is_empty());
        prop_assert!(result.contains(&[]));
        prop_assert_eq!(result.len(), 1);
    }
}
