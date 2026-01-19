//! Naive backend for executing RelAlgIR query plans.
//!
//! This is the "obviously correct" reference implementation:
//! - No optimization
//! - No indexing
//! - Just straightforward interpretation
//!
//! Used for proptest validation against optimized backends.

use std::collections::HashMap;

use crate::core::Structure;
use crate::id::{NumericId, Slid};

/// A tuple in a relation (bag of tuples with multiplicities).
/// For now we use positive multiplicities only (proper Z-sets would allow negatives).
pub type Tuple = Vec<Slid>;

/// A bag of tuples (multiset). Maps tuple -> multiplicity.
/// Multiplicity 0 means absent.
#[derive(Debug, Clone, Default)]
pub struct Bag {
    pub tuples: HashMap<Tuple, i64>,
}

impl Bag {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn singleton(tuple: Tuple) -> Self {
        let mut b = Self::new();
        b.insert(tuple, 1);
        b
    }

    pub fn insert(&mut self, tuple: Tuple, mult: i64) {
        let entry = self.tuples.entry(tuple.clone()).or_insert(0);
        *entry += mult;
        if *entry == 0 {
            self.tuples.remove(&tuple);
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = (&Tuple, &i64)> {
        self.tuples.iter().filter(|(_, m)| **m != 0)
    }

    /// Union (Z-set addition)
    pub fn union(&self, other: &Bag) -> Bag {
        let mut result = self.clone();
        for (tuple, mult) in other.iter() {
            result.insert(tuple.clone(), *mult);
        }
        result
    }

    /// Negate (flip multiplicities)
    pub fn negate(&self) -> Bag {
        let mut result = Bag::new();
        for (tuple, mult) in self.iter() {
            result.insert(tuple.clone(), -mult);
        }
        result
    }

    /// Distinct (clamp multiplicities to 0 or 1)
    pub fn distinct(&self) -> Bag {
        let mut result = Bag::new();
        for (tuple, mult) in self.iter() {
            if *mult > 0 {
                result.insert(tuple.clone(), 1);
            }
        }
        result
    }

    pub fn is_empty(&self) -> bool {
        self.tuples.is_empty()
    }

    pub fn len(&self) -> usize {
        self.tuples.len()
    }
}

/// Query plan operations (mirrors RelAlgIR but as Rust enums for execution)
#[derive(Debug, Clone)]
pub enum QueryOp {
    /// Scan all elements of a sort
    Scan { sort_idx: usize },

    /// Filter by predicate
    Filter {
        input: Box<QueryOp>,
        pred: Predicate,
    },

    /// Project to specific columns
    Project {
        input: Box<QueryOp>,
        columns: Vec<usize>,
    },

    /// Join two inputs on condition
    Join {
        left: Box<QueryOp>,
        right: Box<QueryOp>,
        cond: JoinCond,
    },

    /// Union (bag addition)
    Union {
        left: Box<QueryOp>,
        right: Box<QueryOp>,
    },

    /// Distinct (deduplicate)
    Distinct { input: Box<QueryOp> },

    /// Negate multiplicities
    Negate { input: Box<QueryOp> },

    /// Constant single tuple
    Constant { tuple: Tuple },

    /// Empty relation
    Empty,
}

/// Predicate for filtering
#[derive(Debug, Clone)]
pub enum Predicate {
    True,
    False,
    /// Column equals constant
    ColEqConst { col: usize, val: Slid },
    /// Two columns equal
    ColEqCol { left: usize, right: usize },
    /// Function application: func(col_arg) = col_result
    FuncEq {
        func_idx: usize,
        arg_col: usize,
        result_col: usize,
    },
    And(Box<Predicate>, Box<Predicate>),
    Or(Box<Predicate>, Box<Predicate>),
}

/// Join condition
#[derive(Debug, Clone)]
pub enum JoinCond {
    /// Cross product
    Cross,
    /// Equijoin on columns
    Equi { left_col: usize, right_col: usize },
}

/// Execute a query plan against a structure.
///
/// This is the naive, obviously-correct implementation.
pub fn execute(plan: &QueryOp, structure: &Structure) -> Bag {
    match plan {
        QueryOp::Scan { sort_idx } => {
            let mut result = Bag::new();
            if let Some(carrier) = structure.carriers.get(*sort_idx) {
                for elem in carrier.iter() {
                    result.insert(vec![Slid::from_usize(elem as usize)], 1);
                }
            }
            result
        }

        QueryOp::Filter { input, pred } => {
            let input_bag = execute(input, structure);
            let mut result = Bag::new();
            for (tuple, mult) in input_bag.iter() {
                if eval_predicate(pred, tuple, structure) {
                    result.insert(tuple.clone(), *mult);
                }
            }
            result
        }

        QueryOp::Project { input, columns } => {
            let input_bag = execute(input, structure);
            let mut result = Bag::new();
            for (tuple, mult) in input_bag.iter() {
                let projected: Tuple = columns.iter().map(|&c| tuple[c]).collect();
                result.insert(projected, *mult);
            }
            result
        }

        QueryOp::Join { left, right, cond } => {
            let left_bag = execute(left, structure);
            let right_bag = execute(right, structure);
            let mut result = Bag::new();

            for (l_tuple, l_mult) in left_bag.iter() {
                for (r_tuple, r_mult) in right_bag.iter() {
                    if eval_join_cond(cond, l_tuple, r_tuple) {
                        // Concatenate tuples
                        let mut combined = l_tuple.clone();
                        combined.extend(r_tuple.iter().cloned());
                        result.insert(combined, l_mult * r_mult);
                    }
                }
            }
            result
        }

        QueryOp::Union { left, right } => {
            let left_bag = execute(left, structure);
            let right_bag = execute(right, structure);
            left_bag.union(&right_bag)
        }

        QueryOp::Distinct { input } => {
            let input_bag = execute(input, structure);
            input_bag.distinct()
        }

        QueryOp::Negate { input } => {
            let input_bag = execute(input, structure);
            input_bag.negate()
        }

        QueryOp::Constant { tuple } => Bag::singleton(tuple.clone()),

        QueryOp::Empty => Bag::new(),
    }
}

fn eval_predicate(pred: &Predicate, tuple: &Tuple, structure: &Structure) -> bool {
    match pred {
        Predicate::True => true,
        Predicate::False => false,

        Predicate::ColEqConst { col, val } => tuple.get(*col) == Some(val),

        Predicate::ColEqCol { left, right } => {
            tuple.get(*left) == tuple.get(*right) && tuple.get(*left).is_some()
        }

        Predicate::FuncEq {
            func_idx,
            arg_col,
            result_col,
        } => {
            if let (Some(&arg), Some(&expected)) = (tuple.get(*arg_col), tuple.get(*result_col)) {
                // Look up function value in structure
                // We need to convert Slid to SortSlid for the function lookup
                use crate::id::SortSlid;
                let sort_slid = SortSlid::from_usize(arg.index());
                if let Some(actual) = structure.get_function(*func_idx, sort_slid) {
                    return actual == expected;
                }
            }
            false
        }

        Predicate::And(a, b) => {
            eval_predicate(a, tuple, structure) && eval_predicate(b, tuple, structure)
        }

        Predicate::Or(a, b) => {
            eval_predicate(a, tuple, structure) || eval_predicate(b, tuple, structure)
        }
    }
}

fn eval_join_cond(cond: &JoinCond, left: &Tuple, right: &Tuple) -> bool {
    match cond {
        JoinCond::Cross => true,
        JoinCond::Equi { left_col, right_col } => {
            left.get(*left_col) == right.get(*right_col) && left.get(*left_col).is_some()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::id::NumericId;

    #[test]
    fn test_scan_filter() {
        // Create a simple structure with one sort containing elements 0, 1, 2
        let mut structure = Structure::new(1);
        structure.carriers[0].insert(0);
        structure.carriers[0].insert(1);
        structure.carriers[0].insert(2);

        // Scan all elements
        let scan = QueryOp::Scan { sort_idx: 0 };
        let result = execute(&scan, &structure);
        assert_eq!(result.len(), 3);

        // Filter to just element 1
        let filter = QueryOp::Filter {
            input: Box::new(scan),
            pred: Predicate::ColEqConst {
                col: 0,
                val: Slid::from_usize(1),
            },
        };
        let result = execute(&filter, &structure);
        assert_eq!(result.len(), 1);
        assert!(result.tuples.contains_key(&vec![Slid::from_usize(1)]));
    }

    #[test]
    fn test_join() {
        let mut structure = Structure::new(2);
        // Sort 0: {a, b}
        structure.carriers[0].insert(0);
        structure.carriers[0].insert(1);
        // Sort 1: {x, y}
        structure.carriers[1].insert(10);
        structure.carriers[1].insert(11);

        let left = QueryOp::Scan { sort_idx: 0 };
        let right = QueryOp::Scan { sort_idx: 1 };
        let join = QueryOp::Join {
            left: Box::new(left),
            right: Box::new(right),
            cond: JoinCond::Cross,
        };

        let result = execute(&join, &structure);
        // Cross product: 2 * 2 = 4 tuples
        assert_eq!(result.len(), 4);
    }
}
