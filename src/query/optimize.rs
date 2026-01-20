//! Query optimizer using algebraic laws.
//!
//! Applies rewrite rules corresponding to the algebraic laws defined in
//! RelAlgIR.geolog to transform query plans into more efficient forms.
//!
//! This is a simple "obviously correct" optimizer:
//! - Single-pass bottom-up rewriting
//! - No cost model (just simplification)
//! - Validated by proptests against the naive backend
//!
//! Key rewrites:
//! - Filter(True, x) → x
//! - Filter(False, x) → Empty
//! - Filter(p, Filter(q, x)) → Filter(And(p, q), x)
//! - Distinct(Distinct(x)) → Distinct(x)
//! - Union(x, Empty) → x
//! - Union(Empty, x) → x
//! - Negate(Negate(x)) → x
//! - Join(x, Empty) → Empty
//! - Join(Empty, x) → Empty

use super::backend::{Predicate, QueryOp};

/// Optimize a query plan by applying algebraic laws.
///
/// Returns an equivalent plan that may be more efficient to execute.
/// The optimization is semantics-preserving: optimize(p) produces the
/// same results as p for any structure.
pub fn optimize(plan: &QueryOp) -> QueryOp {
    // Bottom-up: optimize children first, then apply rules
    let optimized_children = optimize_children(plan);
    apply_rules(optimized_children)
}

/// Recursively optimize all children of a plan node.
fn optimize_children(plan: &QueryOp) -> QueryOp {
    match plan {
        QueryOp::Scan { sort_idx } => QueryOp::Scan { sort_idx: *sort_idx },

        QueryOp::ScanRelation { rel_id } => QueryOp::ScanRelation { rel_id: *rel_id },

        QueryOp::Filter { input, pred } => QueryOp::Filter {
            input: Box::new(optimize(input)),
            pred: pred.clone(),
        },

        QueryOp::Project { input, columns } => QueryOp::Project {
            input: Box::new(optimize(input)),
            columns: columns.clone(),
        },

        QueryOp::Join { left, right, cond } => QueryOp::Join {
            left: Box::new(optimize(left)),
            right: Box::new(optimize(right)),
            cond: cond.clone(),
        },

        QueryOp::Union { left, right } => QueryOp::Union {
            left: Box::new(optimize(left)),
            right: Box::new(optimize(right)),
        },

        QueryOp::Distinct { input } => QueryOp::Distinct {
            input: Box::new(optimize(input)),
        },

        QueryOp::Negate { input } => QueryOp::Negate {
            input: Box::new(optimize(input)),
        },

        QueryOp::Constant { tuple } => QueryOp::Constant { tuple: tuple.clone() },

        QueryOp::Empty => QueryOp::Empty,

        QueryOp::Apply { input, func_idx, arg_col } => QueryOp::Apply {
            input: Box::new(optimize(input)),
            func_idx: *func_idx,
            arg_col: *arg_col,
        },

        QueryOp::ApplyField { input, func_idx, arg_col, field_name } => QueryOp::ApplyField {
            input: Box::new(optimize(input)),
            func_idx: *func_idx,
            arg_col: *arg_col,
            field_name: field_name.clone(),
        },

        // DBSP temporal operators: optimize children, preserve state_id
        QueryOp::Delay { input, state_id } => QueryOp::Delay {
            input: Box::new(optimize(input)),
            state_id: *state_id,
        },

        QueryOp::Diff { input, state_id } => QueryOp::Diff {
            input: Box::new(optimize(input)),
            state_id: *state_id,
        },

        QueryOp::Integrate { input, state_id } => QueryOp::Integrate {
            input: Box::new(optimize(input)),
            state_id: *state_id,
        },
    }
}

/// Apply algebraic rewrite rules to a plan node.
/// Assumes children are already optimized.
fn apply_rules(plan: QueryOp) -> QueryOp {
    match plan {
        // ============================================================
        // Filter Laws
        // ============================================================

        // Filter(True, x) → x
        QueryOp::Filter { input, pred: Predicate::True } => *input,

        // Filter(False, x) → Empty
        QueryOp::Filter { pred: Predicate::False, .. } => QueryOp::Empty,

        // Filter(p, Filter(q, x)) → Filter(And(p, q), x)
        QueryOp::Filter { input, pred: outer_pred } => {
            if let QueryOp::Filter { input: inner_input, pred: inner_pred } = *input {
                QueryOp::Filter {
                    input: inner_input,
                    pred: Predicate::And(
                        Box::new(outer_pred),
                        Box::new(inner_pred),
                    ),
                }
            } else {
                QueryOp::Filter {
                    input: Box::new(*input),
                    pred: outer_pred,
                }
            }
        }

        // ============================================================
        // Distinct Laws
        // ============================================================

        // Distinct(Distinct(x)) → Distinct(x)
        QueryOp::Distinct { input } => {
            if matches!(*input, QueryOp::Distinct { .. }) {
                *input
            } else {
                QueryOp::Distinct { input }
            }
        }

        // ============================================================
        // Union Laws
        // ============================================================

        // Union(x, Empty) → x
        // Union(Empty, x) → x
        QueryOp::Union { left, right } => {
            match (&*left, &*right) {
                (QueryOp::Empty, _) => *right,
                (_, QueryOp::Empty) => *left,
                _ => QueryOp::Union { left, right },
            }
        }

        // ============================================================
        // Negate Laws
        // ============================================================

        // Negate(Negate(x)) → x
        QueryOp::Negate { input } => {
            if let QueryOp::Negate { input: inner } = *input {
                *inner
            } else {
                QueryOp::Negate { input }
            }
        }

        // ============================================================
        // Join Laws
        // ============================================================

        // Join(x, Empty) → Empty
        // Join(Empty, x) → Empty
        QueryOp::Join { left, right, cond } => {
            if matches!(*left, QueryOp::Empty) || matches!(*right, QueryOp::Empty) {
                QueryOp::Empty
            } else {
                QueryOp::Join { left, right, cond }
            }
        }

        // No rewrite applies
        other => other,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::query::backend::JoinCond;
    use crate::id::{NumericId, Slid};

    #[test]
    fn test_filter_true_elimination() {
        let scan = QueryOp::Scan { sort_idx: 0 };
        let filter = QueryOp::Filter {
            input: Box::new(scan.clone()),
            pred: Predicate::True,
        };
        let optimized = optimize(&filter);
        assert!(matches!(optimized, QueryOp::Scan { sort_idx: 0 }));
    }

    #[test]
    fn test_filter_false_to_empty() {
        let scan = QueryOp::Scan { sort_idx: 0 };
        let filter = QueryOp::Filter {
            input: Box::new(scan),
            pred: Predicate::False,
        };
        let optimized = optimize(&filter);
        assert!(matches!(optimized, QueryOp::Empty));
    }

    #[test]
    fn test_filter_fusion() {
        let scan = QueryOp::Scan { sort_idx: 0 };
        let filter1 = QueryOp::Filter {
            input: Box::new(scan),
            pred: Predicate::ColEqConst { col: 0, val: Slid::from_usize(1) },
        };
        let filter2 = QueryOp::Filter {
            input: Box::new(filter1),
            pred: Predicate::ColEqConst { col: 0, val: Slid::from_usize(2) },
        };
        let optimized = optimize(&filter2);

        // Should be a single filter with And predicate
        if let QueryOp::Filter { pred: Predicate::And(_, _), .. } = optimized {
            // Good!
        } else {
            panic!("Expected fused filter with And predicate, got {:?}", optimized);
        }
    }

    #[test]
    fn test_distinct_idempotent() {
        let scan = QueryOp::Scan { sort_idx: 0 };
        let distinct1 = QueryOp::Distinct {
            input: Box::new(scan),
        };
        let distinct2 = QueryOp::Distinct {
            input: Box::new(distinct1.clone()),
        };
        let optimized = optimize(&distinct2);

        // Should be single distinct
        if let QueryOp::Distinct { input } = optimized {
            assert!(matches!(*input, QueryOp::Scan { .. }));
        } else {
            panic!("Expected Distinct, got {:?}", optimized);
        }
    }

    #[test]
    fn test_union_empty_elimination() {
        let scan = QueryOp::Scan { sort_idx: 0 };
        let union = QueryOp::Union {
            left: Box::new(scan.clone()),
            right: Box::new(QueryOp::Empty),
        };
        let optimized = optimize(&union);
        assert!(matches!(optimized, QueryOp::Scan { sort_idx: 0 }));

        // Also test left empty
        let union2 = QueryOp::Union {
            left: Box::new(QueryOp::Empty),
            right: Box::new(scan),
        };
        let optimized2 = optimize(&union2);
        assert!(matches!(optimized2, QueryOp::Scan { sort_idx: 0 }));
    }

    #[test]
    fn test_negate_involution() {
        let scan = QueryOp::Scan { sort_idx: 0 };
        let negate1 = QueryOp::Negate {
            input: Box::new(scan),
        };
        let negate2 = QueryOp::Negate {
            input: Box::new(negate1),
        };
        let optimized = optimize(&negate2);
        assert!(matches!(optimized, QueryOp::Scan { sort_idx: 0 }));
    }

    #[test]
    fn test_join_empty_elimination() {
        let scan = QueryOp::Scan { sort_idx: 0 };
        let join = QueryOp::Join {
            left: Box::new(scan),
            right: Box::new(QueryOp::Empty),
            cond: JoinCond::Cross,
        };
        let optimized = optimize(&join);
        assert!(matches!(optimized, QueryOp::Empty));
    }
}
