//! Builder helpers for tensor expressions.
//!
//! High-level operations like conjunction, existential quantification, and disjunction.

use std::collections::{BTreeSet, HashMap};

use super::expr::TensorExpr;

/// Conjunction of two tensor expressions with variable alignment.
///
/// Given tensors T₁ and T₂ with named variables, compute their conjunction
/// by building Product + Contract to identify shared variables.
pub fn conjunction(
    t1: TensorExpr,
    vars1: &[String],
    t2: TensorExpr,
    vars2: &[String],
) -> (TensorExpr, Vec<String>) {
    // Compute combined variable list and mapping
    let mut combined_vars: Vec<String> = vars1.to_vec();
    let mut var_to_target: HashMap<&str, usize> = HashMap::new();

    for (i, v) in vars1.iter().enumerate() {
        var_to_target.insert(v, i);
    }

    let mut index_map: Vec<usize> = (0..vars1.len()).collect();

    for v in vars2 {
        if let Some(&target) = var_to_target.get(v.as_str()) {
            index_map.push(target);
        } else {
            let new_target = combined_vars.len();
            var_to_target.insert(v, new_target);
            combined_vars.push(v.clone());
            index_map.push(new_target);
        }
    }

    let output: BTreeSet<usize> = (0..combined_vars.len()).collect();

    let expr = TensorExpr::Contract {
        inner: Box::new(TensorExpr::Product(vec![t1, t2])),
        index_map,
        output,
    };

    (expr, combined_vars)
}

/// Existential quantification over a variable.
///
/// Removes the variable by OR-ing over all its values (contraction).
pub fn exists(tensor: TensorExpr, vars: &[String], var: &str) -> (TensorExpr, Vec<String>) {
    let var_idx = vars.iter().position(|v| v == var);

    match var_idx {
        None => (tensor, vars.to_vec()),
        Some(idx) => {
            let fresh_target = vars.len();
            let index_map: Vec<usize> = (0..vars.len())
                .map(|i| if i == idx { fresh_target } else { i })
                .collect();

            let output: BTreeSet<usize> = (0..vars.len()).filter(|&i| i != idx).collect();

            let result_vars: Vec<String> = vars
                .iter()
                .enumerate()
                .filter(|&(i, _)| i != idx)
                .map(|(_, v)| v.clone())
                .collect();

            let expr = TensorExpr::Contract {
                inner: Box::new(tensor),
                index_map,
                output,
            };

            (expr, result_vars)
        }
    }
}

/// Multi-way conjunction with variable alignment.
pub fn conjunction_all(tensors: Vec<(TensorExpr, Vec<String>)>) -> (TensorExpr, Vec<String>) {
    if tensors.is_empty() {
        return (TensorExpr::scalar(true), vec![]);
    }

    let mut result = tensors.into_iter();
    let (mut acc_expr, mut acc_vars) = result.next().unwrap();

    for (expr, vars) in result {
        let (new_expr, new_vars) = conjunction(acc_expr, &acc_vars, expr, &vars);
        acc_expr = new_expr;
        acc_vars = new_vars;
    }

    (acc_expr, acc_vars)
}

/// Disjunction of two tensor expressions with variable alignment.
///
/// Both tensors must have the same variables (possibly in different order).
/// The result is the pointwise OR.
pub fn disjunction(
    t1: TensorExpr,
    vars1: &[String],
    t2: TensorExpr,
    vars2: &[String],
) -> (TensorExpr, Vec<String>) {
    // Check that variables are the same set
    let set1: std::collections::HashSet<_> = vars1.iter().collect();
    let set2: std::collections::HashSet<_> = vars2.iter().collect();

    if set1 != set2 {
        // For disjunction, variables must match. If they don't, we need to
        // align them by extending each tensor with the missing variables
        // (treating them as "any value" via Product with full domain).
        // For now, we require exact match since this is the geometric logic case.
        panic!(
            "disjunction requires same variables; got {:?} vs {:?}",
            vars1, vars2
        );
    }

    // If vars2 is in different order than vars1, reorder t2 via Contract
    if vars1 == vars2 {
        // Same order, just union
        (TensorExpr::Sum(vec![t1, t2]), vars1.to_vec())
    } else {
        // Need to reorder t2 to match vars1 ordering
        // Build index_map from vars2 positions to vars1 positions
        let index_map: Vec<usize> = vars2
            .iter()
            .map(|v| vars1.iter().position(|v1| v1 == v).unwrap())
            .collect();
        let output: BTreeSet<usize> = (0..vars1.len()).collect();

        let t2_reordered = TensorExpr::Contract {
            inner: Box::new(t2),
            index_map,
            output,
        };

        (TensorExpr::Sum(vec![t1, t2_reordered]), vars1.to_vec())
    }
}

/// Multi-way disjunction with variable alignment.
///
/// All tensors must have the same variables.
pub fn disjunction_all(tensors: Vec<(TensorExpr, Vec<String>)>) -> (TensorExpr, Vec<String>) {
    if tensors.is_empty() {
        return (TensorExpr::scalar(false), vec![]);
    }

    let mut result = tensors.into_iter();
    let (mut acc_expr, mut acc_vars) = result.next().unwrap();

    for (expr, vars) in result {
        let (new_expr, new_vars) = disjunction(acc_expr, &acc_vars, expr, &vars);
        acc_expr = new_expr;
        acc_vars = new_vars;
    }

    (acc_expr, acc_vars)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tensor::sparse::SparseTensor;

    fn leaf(t: SparseTensor) -> TensorExpr {
        TensorExpr::leaf(t)
    }

    #[test]
    fn test_conjunction() {
        let mut r = SparseTensor::empty(vec![2, 2]);
        r.insert(vec![0, 1]);

        let mut s = SparseTensor::empty(vec![2, 2]);
        s.insert(vec![1, 0]);
        s.insert(vec![1, 1]);

        let vars_r = vec!["x".to_string(), "y".to_string()];
        let vars_s = vec!["y".to_string(), "z".to_string()];

        let (expr, vars) = conjunction(leaf(r), &vars_r, leaf(s), &vars_s);
        let result = expr.materialize();

        assert_eq!(vars, vec!["x", "y", "z"]);
        assert_eq!(result.dims, vec![2, 2, 2]);
        assert_eq!(result.len(), 2);
        assert!(result.contains(&[0, 1, 0]));
        assert!(result.contains(&[0, 1, 1]));
    }

    #[test]
    fn test_exists() {
        let mut t = SparseTensor::empty(vec![2, 2]);
        t.insert(vec![0, 0]);
        t.insert(vec![0, 1]);
        t.insert(vec![1, 1]);

        let vars = vec!["x".to_string(), "y".to_string()];
        let (expr, result_vars) = exists(leaf(t), &vars, "y");
        let result = expr.materialize();

        assert_eq!(result_vars, vec!["x"]);
        assert_eq!(result.dims, vec![2]);
        assert_eq!(result.len(), 2);
    }

    #[test]
    fn test_relational_join() {
        // R(x,y) ⋈ S(y,z) then ∃y
        let mut r = SparseTensor::empty(vec![3, 3]);
        r.insert(vec![0, 1]);
        r.insert(vec![1, 2]);

        let mut s = SparseTensor::empty(vec![3, 3]);
        s.insert(vec![0, 1]);
        s.insert(vec![1, 2]);

        let vars_r = vec!["x".to_string(), "y".to_string()];
        let vars_s = vec!["y".to_string(), "z".to_string()];

        let (conj, vars) = conjunction(leaf(r), &vars_r, leaf(s), &vars_s);
        assert_eq!(vars, vec!["x", "y", "z"]);

        let (result_expr, result_vars) = exists(conj, &vars, "y");
        let result = result_expr.materialize();

        assert_eq!(result_vars, vec!["x", "z"]);
        assert!(result.contains(&[0, 2])); // path 0→1→2
    }

    #[test]
    fn test_fused_join_uses_hash() {
        // Large-ish tensors to verify hash join path works
        let mut r = SparseTensor::empty(vec![100, 100]);
        let mut s = SparseTensor::empty(vec![100, 100]);

        // Sparse data
        for i in 0..50 {
            r.insert(vec![i, i + 1]);
            s.insert(vec![i + 1, i + 2]);
        }

        let vars_r = vec!["x".to_string(), "y".to_string()];
        let vars_s = vec!["y".to_string(), "z".to_string()];

        let (conj, vars) = conjunction(leaf(r), &vars_r, leaf(s), &vars_s);
        let (result_expr, _) = exists(conj, &vars, "y");
        let result = result_expr.materialize();

        // Should have 50 paths: 0→2, 1→3, ..., 49→51
        assert_eq!(result.len(), 50);
        assert!(result.contains(&[0, 2]));
        assert!(result.contains(&[49, 51]));
    }

    #[test]
    fn test_disjunction_same_vars() {
        // R(x,y) ∨ S(x,y) with same variable order
        let mut r = SparseTensor::empty(vec![2, 2]);
        r.insert(vec![0, 0]);

        let mut s = SparseTensor::empty(vec![2, 2]);
        s.insert(vec![1, 1]);

        let vars = vec!["x".to_string(), "y".to_string()];

        let (expr, result_vars) = disjunction(leaf(r), &vars, leaf(s), &vars);
        let result = expr.materialize();

        assert_eq!(result_vars, vec!["x", "y"]);
        assert_eq!(result.len(), 2);
        assert!(result.contains(&[0, 0]));
        assert!(result.contains(&[1, 1]));
    }

    #[test]
    fn test_disjunction_reordered_vars() {
        // R(x,y) ∨ S(y,x) - different variable order requires reordering
        let mut r = SparseTensor::empty(vec![2, 3]);
        r.insert(vec![0, 1]); // x=0, y=1

        let mut s = SparseTensor::empty(vec![3, 2]);
        s.insert(vec![2, 1]); // y=2, x=1

        let vars_r = vec!["x".to_string(), "y".to_string()];
        let vars_s = vec!["y".to_string(), "x".to_string()];

        let (expr, result_vars) = disjunction(leaf(r), &vars_r, leaf(s), &vars_s);
        let result = expr.materialize();

        assert_eq!(result_vars, vec!["x", "y"]);
        assert_eq!(result.len(), 2);
        assert!(result.contains(&[0, 1])); // from R
        assert!(result.contains(&[1, 2])); // from S reordered
    }

    #[test]
    fn test_disjunction_all() {
        // R(x) ∨ S(x) ∨ T(x)
        let mut r = SparseTensor::empty(vec![5]);
        r.insert(vec![0]);

        let mut s = SparseTensor::empty(vec![5]);
        s.insert(vec![1]);

        let mut t = SparseTensor::empty(vec![5]);
        t.insert(vec![2]);

        let vars = vec!["x".to_string()];

        let (expr, result_vars) = disjunction_all(vec![
            (leaf(r), vars.clone()),
            (leaf(s), vars.clone()),
            (leaf(t), vars.clone()),
        ]);
        let result = expr.materialize();

        assert_eq!(result_vars, vec!["x"]);
        assert_eq!(result.len(), 3);
        assert!(result.contains(&[0]));
        assert!(result.contains(&[1]));
        assert!(result.contains(&[2]));
    }

    #[test]
    fn test_disjunction_all_empty() {
        // Empty disjunction = false
        let (expr, vars) = disjunction_all(vec![]);
        let result = expr.materialize();

        assert!(vars.is_empty());
        assert!(result.is_empty());
    }

    #[test]
    fn test_geometric_formula_pattern() {
        // Test pattern from geometric logic: ∃y. (R(x,y) ∧ S(y)) ∨ (T(x))
        // This exercises Sum inside a more complex expression

        // R(x,y): edges 0→1, 1→2
        let mut r = SparseTensor::empty(vec![3, 3]);
        r.insert(vec![0, 1]);
        r.insert(vec![1, 2]);

        // S(y): valid y values {1, 2}
        let mut s = SparseTensor::empty(vec![3]);
        s.insert(vec![1]);
        s.insert(vec![2]);

        // T(x): alternative x values {2}
        let mut t = SparseTensor::empty(vec![3]);
        t.insert(vec![2]);

        // Build: R(x,y) ∧ S(y)
        let vars_r = vec!["x".to_string(), "y".to_string()];
        let vars_s = vec!["y".to_string()];
        let (conj, conj_vars) = conjunction(leaf(r), &vars_r, leaf(s), &vars_s);
        // conj_vars = ["x", "y"]

        // ∃y. (R(x,y) ∧ S(y))
        let (exists_expr, exists_vars) = exists(conj, &conj_vars, "y");
        // exists_vars = ["x"]

        // (∃y. R(x,y) ∧ S(y)) ∨ T(x)
        let vars_t = vec!["x".to_string()];
        let (result_expr, result_vars) = disjunction(exists_expr, &exists_vars, leaf(t), &vars_t);

        let result = result_expr.materialize();

        assert_eq!(result_vars, vec!["x"]);
        // From R ∧ S: x=0 (path 0→1, 1∈S) and x=1 (path 1→2, 2∈S)
        // From T: x=2
        assert_eq!(result.len(), 3);
        assert!(result.contains(&[0]));
        assert!(result.contains(&[1]));
        assert!(result.contains(&[2]));
    }
}
