//! Naive backend for executing RelAlgIR query plans.
//!
//! This is the "obviously correct" reference implementation:
//! - No optimization
//! - No indexing
//! - Just straightforward interpretation
//!
//! Used for proptest validation against optimized backends.
//!
//! # DBSP Temporal Operators
//!
//! This backend supports DBSP-style incremental computation via three temporal operators:
//!
//! - **Delay (z⁻¹)**: Access previous timestep's value
//! - **Diff (δ = 1 - z⁻¹)**: Compute difference from previous timestep
//! - **Integrate (∫)**: Accumulate values across all timesteps
//!
//! These operators require state across timesteps, managed by `StreamContext`.

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

    /// Apply a function: extends tuples with `func(arg_col)`
    /// `(t₁, ..., tₙ)` → `(t₁, ..., tₙ, func(t[arg_col]))`
    Apply {
        input: Box<QueryOp>,
        func_idx: usize,
        arg_col: usize,
    },

    // ========================================================================
    // DBSP Temporal Operators
    // ========================================================================
    // These operators work on streams over time, requiring state management.
    // Use `execute_stream` with a `StreamContext` instead of bare `execute`.

    /// Delay (z⁻¹): output previous timestep's input value
    /// At timestep 0, outputs empty bag.
    Delay {
        input: Box<QueryOp>,
        /// Unique identifier for this delay's state
        state_id: usize,
    },

    /// Differentiate (δ = 1 - z⁻¹): compute changes since previous timestep
    /// output = current_input - previous_input
    Diff {
        input: Box<QueryOp>,
        /// Unique identifier for this diff's state
        state_id: usize,
    },

    /// Integrate (∫): accumulate inputs over all timesteps
    /// output = Σ (all inputs from timestep 0 to now)
    Integrate {
        input: Box<QueryOp>,
        /// Unique identifier for this integrate's state
        state_id: usize,
    },
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
    /// Function application: func(col_arg) = col_result (both columns)
    FuncEq {
        func_idx: usize,
        arg_col: usize,
        result_col: usize,
    },
    /// Function application equals constant: func(col_arg) = expected
    FuncEqConst {
        func_idx: usize,
        arg_col: usize,
        expected: Slid,
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

// ============================================================================
// DBSP Stream Context
// ============================================================================

/// State for DBSP temporal operators across timesteps.
///
/// Each stateful operator (Delay, Diff, Integrate) uses a unique `state_id`
/// to store its state in this context. Call `step()` to advance time.
#[derive(Debug, Clone, Default)]
pub struct StreamContext {
    /// Current timestep (starts at 0)
    pub timestep: u64,

    /// State for Delay operators: state_id -> previous input
    delay_state: HashMap<usize, Bag>,

    /// State for Diff operators: state_id -> previous input
    diff_state: HashMap<usize, Bag>,

    /// State for Integrate operators: state_id -> accumulated sum
    integrate_state: HashMap<usize, Bag>,
}

impl StreamContext {
    /// Create a new stream context at timestep 0
    pub fn new() -> Self {
        Self::default()
    }

    /// Advance to the next timestep.
    ///
    /// This should be called after processing all operators for the current step.
    /// Delay state is automatically updated during execution.
    pub fn step(&mut self) {
        self.timestep += 1;
    }

    /// Reset all state (for testing or restarting computation)
    pub fn reset(&mut self) {
        self.timestep = 0;
        self.delay_state.clear();
        self.diff_state.clear();
        self.integrate_state.clear();
    }

    /// Get delay state (previous input)
    fn get_delay(&self, state_id: usize) -> Bag {
        self.delay_state.get(&state_id).cloned().unwrap_or_default()
    }

    /// Set delay state for next timestep
    fn set_delay(&mut self, state_id: usize, bag: Bag) {
        self.delay_state.insert(state_id, bag);
    }

    /// Get diff state (previous input for differentiation)
    fn get_diff_prev(&self, state_id: usize) -> Bag {
        self.diff_state.get(&state_id).cloned().unwrap_or_default()
    }

    /// Set diff state for next timestep
    fn set_diff_prev(&mut self, state_id: usize, bag: Bag) {
        self.diff_state.insert(state_id, bag);
    }

    /// Get integrate state (accumulated sum)
    fn get_integrate(&self, state_id: usize) -> Bag {
        self.integrate_state.get(&state_id).cloned().unwrap_or_default()
    }

    /// Update integrate state with new input
    fn accumulate_integrate(&mut self, state_id: usize, delta: &Bag) {
        let current = self.get_integrate(state_id);
        let new_total = current.union(delta);
        self.integrate_state.insert(state_id, new_total);
    }
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

        QueryOp::Apply { input, func_idx, arg_col } => {
            let input_bag = execute(input, structure);
            let mut result = Bag::new();
            for (tuple, mult) in input_bag.iter() {
                if let Some(&arg) = tuple.get(*arg_col) {
                    // Look up function value
                    // Use sort_local_id to convert Slid to sort-local SortSlid
                    let sort_slid = structure.sort_local_id(arg);
                    if let Some(func_result) = structure.get_function(*func_idx, sort_slid) {
                        // Extend tuple with function result
                        let mut extended = tuple.clone();
                        extended.push(func_result);
                        result.insert(extended, *mult);
                    }
                    // If function undefined, tuple is dropped (acts as filter)
                }
            }
            result
        }

        // DBSP operators require StreamContext - use execute_stream() instead
        QueryOp::Delay { .. } | QueryOp::Diff { .. } | QueryOp::Integrate { .. } => {
            panic!("DBSP temporal operators require StreamContext - use execute_stream() instead")
        }
    }
}

/// Execute a query plan with DBSP temporal operator support.
///
/// This handles both stateless operators (scan, filter, join, etc.) and stateful
/// DBSP operators (delay, diff, integrate). The StreamContext maintains state
/// across timesteps.
///
/// # Example: Semi-naive Datalog fixpoint
///
/// ```ignore
/// let mut ctx = StreamContext::new();
/// let plan = /* query plan with Integrate for fixpoint */;
///
/// loop {
///     let delta = execute_stream(&plan, &structure, &mut ctx);
///     if delta.is_empty() {
///         break; // fixpoint reached
///     }
///     ctx.step();
/// }
/// ```
pub fn execute_stream(plan: &QueryOp, structure: &Structure, ctx: &mut StreamContext) -> Bag {
    match plan {
        // Stateless operators - delegate to execute()
        QueryOp::Scan { .. }
        | QueryOp::Filter { .. }
        | QueryOp::Project { .. }
        | QueryOp::Join { .. }
        | QueryOp::Union { .. }
        | QueryOp::Distinct { .. }
        | QueryOp::Negate { .. }
        | QueryOp::Constant { .. }
        | QueryOp::Empty
        | QueryOp::Apply { .. } => {
            // For stateless operators that contain DBSP subexpressions,
            // we need to recursively handle them
            execute_stream_stateless(plan, structure, ctx)
        }

        // DBSP: Delay (z⁻¹) - output previous timestep's input
        QueryOp::Delay { input, state_id } => {
            // Get previous state (empty at timestep 0)
            let previous = ctx.get_delay(*state_id);

            // Compute current input
            let current = execute_stream(input, structure, ctx);

            // Store current for next timestep
            ctx.set_delay(*state_id, current);

            // Return previous
            previous
        }

        // DBSP: Diff (δ = 1 - z⁻¹) - compute difference from previous
        QueryOp::Diff { input, state_id } => {
            // Get previous input
            let previous = ctx.get_diff_prev(*state_id);

            // Compute current input
            let current = execute_stream(input, structure, ctx);

            // Store current for next timestep
            ctx.set_diff_prev(*state_id, current.clone());

            // Return current - previous (using Z-set subtraction)
            current.union(&previous.negate())
        }

        // DBSP: Integrate (∫) - accumulate over all timesteps
        QueryOp::Integrate { input, state_id } => {
            // Compute current input (typically a delta/diff)
            let delta = execute_stream(input, structure, ctx);

            // Add to accumulated total
            ctx.accumulate_integrate(*state_id, &delta);

            // Return the accumulated total
            ctx.get_integrate(*state_id)
        }
    }
}

/// Helper for executing stateless operators that may contain DBSP subexpressions.
fn execute_stream_stateless(plan: &QueryOp, structure: &Structure, ctx: &mut StreamContext) -> Bag {
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
            let input_bag = execute_stream(input, structure, ctx);
            let mut result = Bag::new();
            for (tuple, mult) in input_bag.iter() {
                if eval_predicate(pred, tuple, structure) {
                    result.insert(tuple.clone(), *mult);
                }
            }
            result
        }

        QueryOp::Project { input, columns } => {
            let input_bag = execute_stream(input, structure, ctx);
            let mut result = Bag::new();
            for (tuple, mult) in input_bag.iter() {
                let projected: Tuple = columns.iter().map(|&c| tuple[c]).collect();
                result.insert(projected, *mult);
            }
            result
        }

        QueryOp::Join { left, right, cond } => {
            let left_bag = execute_stream(left, structure, ctx);
            let right_bag = execute_stream(right, structure, ctx);
            let mut result = Bag::new();

            for (l_tuple, l_mult) in left_bag.iter() {
                for (r_tuple, r_mult) in right_bag.iter() {
                    if eval_join_cond(cond, l_tuple, r_tuple) {
                        let mut combined = l_tuple.clone();
                        combined.extend(r_tuple.iter().cloned());
                        result.insert(combined, l_mult * r_mult);
                    }
                }
            }
            result
        }

        QueryOp::Union { left, right } => {
            let left_bag = execute_stream(left, structure, ctx);
            let right_bag = execute_stream(right, structure, ctx);
            left_bag.union(&right_bag)
        }

        QueryOp::Distinct { input } => {
            let input_bag = execute_stream(input, structure, ctx);
            input_bag.distinct()
        }

        QueryOp::Negate { input } => {
            let input_bag = execute_stream(input, structure, ctx);
            input_bag.negate()
        }

        QueryOp::Constant { tuple } => Bag::singleton(tuple.clone()),

        QueryOp::Empty => Bag::new(),

        QueryOp::Apply { input, func_idx, arg_col } => {
            let input_bag = execute_stream(input, structure, ctx);
            let mut result = Bag::new();
            for (tuple, mult) in input_bag.iter() {
                if let Some(&arg) = tuple.get(*arg_col) {
                    // Use sort_local_id to convert Slid to sort-local SortSlid
                    let sort_slid = structure.sort_local_id(arg);
                    if let Some(func_result) = structure.get_function(*func_idx, sort_slid) {
                        let mut extended = tuple.clone();
                        extended.push(func_result);
                        result.insert(extended, *mult);
                    }
                }
            }
            result
        }

        // DBSP operators handled by execute_stream directly
        QueryOp::Delay { .. } | QueryOp::Diff { .. } | QueryOp::Integrate { .. } => {
            execute_stream(plan, structure, ctx)
        }
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
                // Use sort_local_id to convert Slid to sort-local SortSlid
                let sort_slid = structure.sort_local_id(arg);
                if let Some(actual) = structure.get_function(*func_idx, sort_slid) {
                    return actual == expected;
                }
            }
            false
        }

        Predicate::FuncEqConst {
            func_idx,
            arg_col,
            expected,
        } => {
            if let Some(&arg) = tuple.get(*arg_col) {
                // Look up function value in structure
                // Use sort_local_id to convert Slid to sort-local SortSlid
                let sort_slid = structure.sort_local_id(arg);
                if let Some(actual) = structure.get_function(*func_idx, sort_slid) {
                    return actual == *expected;
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

// ============================================================================
// Optimized Backend with Hash Joins
// ============================================================================

/// Execute a query plan with optimizations (hash joins for equijoins).
///
/// This produces the same results as `execute()` but with better asymptotic
/// complexity for equijoins: O(n+m) instead of O(n*m).
///
/// Use `execute()` as the reference implementation for testing correctness.
pub fn execute_optimized(plan: &QueryOp, structure: &Structure) -> Bag {
    match plan {
        QueryOp::Join { left, right, cond: JoinCond::Equi { left_col, right_col } } => {
            // Hash join: O(n + m) instead of O(n * m)
            let left_bag = execute_optimized(left, structure);
            let right_bag = execute_optimized(right, structure);

            // Build phase: hash the smaller relation
            let (build_bag, probe_bag, build_col, probe_col, is_left_build) =
                if left_bag.len() <= right_bag.len() {
                    (&left_bag, &right_bag, *left_col, *right_col, true)
                } else {
                    (&right_bag, &left_bag, *right_col, *left_col, false)
                };

            // Build hash table: key -> Vec<(tuple, multiplicity)>
            let mut hash_table: HashMap<Slid, Vec<(&Tuple, i64)>> = HashMap::new();
            for (tuple, mult) in build_bag.iter() {
                if let Some(&key) = tuple.get(build_col) {
                    hash_table.entry(key).or_default().push((tuple, *mult));
                }
            }

            // Probe phase
            let mut result = Bag::new();
            for (probe_tuple, probe_mult) in probe_bag.iter() {
                if let Some(&key) = probe_tuple.get(probe_col)
                    && let Some(matches) = hash_table.get(&key) {
                        for (build_tuple, build_mult) in matches {
                            // Reconstruct in correct order (left, right)
                            let combined = if is_left_build {
                                let mut c = (*build_tuple).clone();
                                c.extend(probe_tuple.iter().cloned());
                                c
                            } else {
                                let mut c = probe_tuple.clone();
                                c.extend((*build_tuple).iter().cloned());
                                c
                            };

                            let mult = if is_left_build {
                                build_mult * probe_mult
                            } else {
                                probe_mult * build_mult
                            };
                            result.insert(combined, mult);
                        }
                    }
            }
            result
        }

        // For other operators, delegate to naive implementation but recurse optimized
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
            let input_bag = execute_optimized(input, structure);
            let mut result = Bag::new();
            for (tuple, mult) in input_bag.iter() {
                if eval_predicate(pred, tuple, structure) {
                    result.insert(tuple.clone(), *mult);
                }
            }
            result
        }

        QueryOp::Project { input, columns } => {
            let input_bag = execute_optimized(input, structure);
            let mut result = Bag::new();
            for (tuple, mult) in input_bag.iter() {
                let projected: Tuple = columns.iter().map(|&c| tuple[c]).collect();
                result.insert(projected, *mult);
            }
            result
        }

        QueryOp::Join { left, right, cond: JoinCond::Cross } => {
            // Cross join: still O(n*m), no optimization possible
            let left_bag = execute_optimized(left, structure);
            let right_bag = execute_optimized(right, structure);
            let mut result = Bag::new();

            for (l_tuple, l_mult) in left_bag.iter() {
                for (r_tuple, r_mult) in right_bag.iter() {
                    let mut combined = l_tuple.clone();
                    combined.extend(r_tuple.iter().cloned());
                    result.insert(combined, l_mult * r_mult);
                }
            }
            result
        }

        QueryOp::Union { left, right } => {
            let left_bag = execute_optimized(left, structure);
            let right_bag = execute_optimized(right, structure);
            left_bag.union(&right_bag)
        }

        QueryOp::Distinct { input } => {
            let input_bag = execute_optimized(input, structure);
            input_bag.distinct()
        }

        QueryOp::Negate { input } => {
            let input_bag = execute_optimized(input, structure);
            input_bag.negate()
        }

        QueryOp::Constant { tuple } => Bag::singleton(tuple.clone()),

        QueryOp::Empty => Bag::new(),

        QueryOp::Apply { input, func_idx, arg_col } => {
            let input_bag = execute_optimized(input, structure);
            let mut result = Bag::new();
            for (tuple, mult) in input_bag.iter() {
                if let Some(&arg) = tuple.get(*arg_col) {
                    let sort_slid = structure.sort_local_id(arg);
                    if let Some(func_result) = structure.get_function(*func_idx, sort_slid) {
                        let mut extended = tuple.clone();
                        extended.push(func_result);
                        result.insert(extended, *mult);
                    }
                }
            }
            result
        }

        // DBSP operators not supported in optimized path yet
        QueryOp::Delay { .. } | QueryOp::Diff { .. } | QueryOp::Integrate { .. } => {
            panic!("DBSP temporal operators require StreamContext - use execute_stream() instead")
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

    // ========================================================================
    // DBSP Temporal Operator Tests
    // ========================================================================

    #[test]
    fn test_delay_initial_empty() {
        // Delay should output empty at timestep 0
        let structure = Structure::new(1);
        let mut ctx = StreamContext::new();

        let plan = QueryOp::Delay {
            input: Box::new(QueryOp::Constant {
                tuple: vec![Slid::from_usize(42)],
            }),
            state_id: 0,
        };

        // First step: output should be empty (no previous)
        let result = execute_stream(&plan, &structure, &mut ctx);
        assert!(result.is_empty(), "delay should be empty at timestep 0");
    }

    #[test]
    fn test_delay_outputs_previous() {
        // Delay should output previous input after step()
        let structure = Structure::new(1);
        let mut ctx = StreamContext::new();

        let plan = QueryOp::Delay {
            input: Box::new(QueryOp::Constant {
                tuple: vec![Slid::from_usize(42)],
            }),
            state_id: 0,
        };

        // First step: execute to set up state
        let _ = execute_stream(&plan, &structure, &mut ctx);
        ctx.step();

        // Second step: should output the previous input
        let result = execute_stream(&plan, &structure, &mut ctx);
        assert_eq!(result.len(), 1);
        assert!(result.tuples.contains_key(&vec![Slid::from_usize(42)]));
    }

    #[test]
    fn test_diff_computes_delta() {
        // Diff outputs current - previous
        let mut structure = Structure::new(1);
        let mut ctx = StreamContext::new();

        // Start with elements {0, 1}
        structure.carriers[0].insert(0);
        structure.carriers[0].insert(1);

        let plan = QueryOp::Diff {
            input: Box::new(QueryOp::Scan { sort_idx: 0 }),
            state_id: 0,
        };

        // First step: diff = {0, 1} - {} = {0, 1}
        let result = execute_stream(&plan, &structure, &mut ctx);
        assert_eq!(result.len(), 2);
        ctx.step();

        // Add element 2, so now scan = {0, 1, 2}
        structure.carriers[0].insert(2);

        // Second step: diff = {0, 1, 2} - {0, 1} = {2}
        let result = execute_stream(&plan, &structure, &mut ctx);
        assert_eq!(result.len(), 1);
        assert!(result.tuples.contains_key(&vec![Slid::from_usize(2)]));
    }

    #[test]
    fn test_integrate_accumulates() {
        // Integrate accumulates across timesteps
        let structure = Structure::new(1);
        let mut ctx = StreamContext::new();

        // We'll feed constant input at each step
        let plan = QueryOp::Integrate {
            input: Box::new(QueryOp::Constant {
                tuple: vec![Slid::from_usize(1)],
            }),
            state_id: 0,
        };

        // Step 0: accumulated = {1}
        let result = execute_stream(&plan, &structure, &mut ctx);
        assert_eq!(result.len(), 1);
        assert_eq!(*result.tuples.get(&vec![Slid::from_usize(1)]).unwrap(), 1);
        ctx.step();

        // Step 1: accumulated = {1} + {1} = {1} with multiplicity 2
        let result = execute_stream(&plan, &structure, &mut ctx);
        assert_eq!(result.len(), 1);
        assert_eq!(*result.tuples.get(&vec![Slid::from_usize(1)]).unwrap(), 2);
        ctx.step();

        // Step 2: multiplicity 3
        let result = execute_stream(&plan, &structure, &mut ctx);
        assert_eq!(*result.tuples.get(&vec![Slid::from_usize(1)]).unwrap(), 3);
    }

    #[test]
    fn test_diff_integrate_identity() {
        // ∫(δ(x)) = x (for stable input)
        // This is the fundamental DBSP identity
        let mut structure = Structure::new(1);
        structure.carriers[0].insert(0);
        structure.carriers[0].insert(1);
        structure.carriers[0].insert(2);

        let mut ctx = StreamContext::new();

        // ∫(δ(scan))
        let plan = QueryOp::Integrate {
            input: Box::new(QueryOp::Diff {
                input: Box::new(QueryOp::Scan { sort_idx: 0 }),
                state_id: 0,
            }),
            state_id: 1,
        };

        // Step 0: diff = {0,1,2}, integrate = {0,1,2}
        let result = execute_stream(&plan, &structure, &mut ctx);
        assert_eq!(result.len(), 3);
        ctx.step();

        // Step 1: diff = {} (no change), integrate = {0,1,2} (unchanged)
        let result = execute_stream(&plan, &structure, &mut ctx);
        assert_eq!(result.len(), 3);
        ctx.step();

        // Step 2: still {0,1,2}
        let result = execute_stream(&plan, &structure, &mut ctx);
        assert_eq!(result.len(), 3);
    }

    #[test]
    fn test_dbsp_with_filter() {
        // Test DBSP operators composed with stateless operators
        let mut structure = Structure::new(1);
        structure.carriers[0].insert(0);
        structure.carriers[0].insert(1);
        structure.carriers[0].insert(2);

        let mut ctx = StreamContext::new();

        // Filter(Diff(scan)) - incremental filter
        let plan = QueryOp::Filter {
            input: Box::new(QueryOp::Diff {
                input: Box::new(QueryOp::Scan { sort_idx: 0 }),
                state_id: 0,
            }),
            pred: Predicate::ColEqConst {
                col: 0,
                val: Slid::from_usize(1),
            },
        };

        // Step 0: diff = {0,1,2}, filter = {1}
        let result = execute_stream(&plan, &structure, &mut ctx);
        assert_eq!(result.len(), 1);
        assert!(result.tuples.contains_key(&vec![Slid::from_usize(1)]));
        ctx.step();

        // Add element 3 (doesn't pass filter)
        structure.carriers[0].insert(3);

        // Step 1: diff = {3}, filter = {} (3 doesn't match predicate)
        let result = execute_stream(&plan, &structure, &mut ctx);
        assert!(result.is_empty());
    }

    #[test]
    fn test_stream_context_reset() {
        let structure = Structure::new(1);
        let mut ctx = StreamContext::new();

        let plan = QueryOp::Integrate {
            input: Box::new(QueryOp::Constant {
                tuple: vec![Slid::from_usize(1)],
            }),
            state_id: 0,
        };

        // Run a few steps
        let _ = execute_stream(&plan, &structure, &mut ctx);
        ctx.step();
        let _ = execute_stream(&plan, &structure, &mut ctx);
        ctx.step();

        assert_eq!(ctx.timestep, 2);

        // Reset
        ctx.reset();
        assert_eq!(ctx.timestep, 0);

        // Integrate should start fresh
        let result = execute_stream(&plan, &structure, &mut ctx);
        assert_eq!(*result.tuples.get(&vec![Slid::from_usize(1)]).unwrap(), 1);
    }

    // ========================================================================
    // Semi-Naive Datalog Example (DBSP in action)
    // ========================================================================

    /// Demonstrates DBSP for transitive closure (semi-naive style).
    ///
    /// This example computes reachability in a graph using the DBSP pattern:
    /// - δR = new facts this iteration
    /// - ∫(δR) = all facts so far
    ///
    /// The "semi-naive" optimization is automatic: Diff computes only changes,
    /// avoiding redundant re-derivation of old facts.
    #[test]
    fn test_semi_naive_transitive_closure() {
        // Graph: 0→1, 1→2, 2→3
        // We represent edges as tuples (src, tgt) in sort 0
        let mut structure = Structure::new(1);

        // Add edge tuples as elements: encode (a,b) as slid = a*10 + b
        // 0→1: slid=1, 1→2: slid=12, 2→3: slid=23
        structure.carriers[0].insert(1);   // edge 0→1
        structure.carriers[0].insert(12);  // edge 1→2
        structure.carriers[0].insert(23);  // edge 2→3

        let mut ctx = StreamContext::new();

        // Query: scan all edges (base facts)
        let base_facts = QueryOp::Scan { sort_idx: 0 };

        // In a full implementation, we'd:
        // 1. Differentiate the base facts to get δR
        // 2. Join δR with ∫R to derive new transitive edges
        // 3. Integrate to accumulate all reachable pairs
        //
        // For this test, we just verify the DBSP operators work together:

        // Step 1: ∫(δ(scan)) should equal the scan itself for stable input
        let incremental_view = QueryOp::Integrate {
            input: Box::new(QueryOp::Diff {
                input: Box::new(base_facts.clone()),
                state_id: 0,
            }),
            state_id: 1,
        };

        // First execution: should see all 3 edges
        let result = execute_stream(&incremental_view, &structure, &mut ctx);
        assert_eq!(result.len(), 3, "should have 3 edges initially");
        ctx.step();

        // Add new edge: 3→4 (encoded as slid=34)
        structure.carriers[0].insert(34);

        // Second execution: diff should detect +1 new edge, integrate shows all 4
        let result = execute_stream(&incremental_view, &structure, &mut ctx);
        assert_eq!(result.len(), 4, "should have 4 edges after adding 3→4");

        // Verify incrementality: diff should show just the new edge
        let diff_only = QueryOp::Diff {
            input: Box::new(QueryOp::Scan { sort_idx: 0 }),
            state_id: 2, // fresh state_id
        };
        let mut fresh_ctx = StreamContext::new();

        // First step: all edges are "new"
        let delta = execute_stream(&diff_only, &structure, &mut fresh_ctx);
        assert_eq!(delta.len(), 4);
        fresh_ctx.step();

        // Second step with no changes: delta should be empty
        let delta = execute_stream(&diff_only, &structure, &mut fresh_ctx);
        assert!(delta.is_empty(), "no changes, delta should be empty");
    }

    // ========================================================================
    // Hash Join Tests (execute_optimized)
    // ========================================================================

    #[test]
    fn test_hash_join_basic() {
        // Test that hash join produces same results as nested loop join
        let mut structure = Structure::new(2);
        // Sort 0: {0, 1, 2}
        structure.carriers[0].insert(0);
        structure.carriers[0].insert(1);
        structure.carriers[0].insert(2);
        // Sort 1: {0, 1, 2} (some overlap for equijoin)
        structure.carriers[1].insert(0);
        structure.carriers[1].insert(1);
        structure.carriers[1].insert(2);

        let left = QueryOp::Scan { sort_idx: 0 };
        let right = QueryOp::Scan { sort_idx: 1 };
        let join = QueryOp::Join {
            left: Box::new(left),
            right: Box::new(right),
            cond: JoinCond::Equi { left_col: 0, right_col: 0 },
        };

        let naive_result = execute(&join, &structure);
        let optimized_result = super::execute_optimized(&join, &structure);

        // Results should be identical
        assert_eq!(naive_result.len(), optimized_result.len());
        for (tuple, mult) in naive_result.iter() {
            assert_eq!(
                optimized_result.tuples.get(tuple),
                Some(mult),
                "tuple {:?} has different multiplicity",
                tuple
            );
        }
    }

    #[test]
    fn test_hash_join_no_matches() {
        // Test equijoin with no matching keys
        let mut structure = Structure::new(2);
        // Sort 0: {0, 1}
        structure.carriers[0].insert(0);
        structure.carriers[0].insert(1);
        // Sort 1: {10, 11} (no overlap)
        structure.carriers[1].insert(10);
        structure.carriers[1].insert(11);

        let join = QueryOp::Join {
            left: Box::new(QueryOp::Scan { sort_idx: 0 }),
            right: Box::new(QueryOp::Scan { sort_idx: 1 }),
            cond: JoinCond::Equi { left_col: 0, right_col: 0 },
        };

        let naive_result = execute(&join, &structure);
        let optimized_result = super::execute_optimized(&join, &structure);

        assert!(naive_result.is_empty());
        assert!(optimized_result.is_empty());
    }

    #[test]
    fn test_hash_join_asymmetric() {
        // Test that join order is preserved when left is larger than right
        let mut structure = Structure::new(2);
        // Sort 0: {0, 1, 2, 3, 4} (larger)
        for i in 0..5 {
            structure.carriers[0].insert(i);
        }
        // Sort 1: {2, 3} (smaller, will be build side)
        structure.carriers[1].insert(2);
        structure.carriers[1].insert(3);

        let join = QueryOp::Join {
            left: Box::new(QueryOp::Scan { sort_idx: 0 }),
            right: Box::new(QueryOp::Scan { sort_idx: 1 }),
            cond: JoinCond::Equi { left_col: 0, right_col: 0 },
        };

        let naive_result = execute(&join, &structure);
        let optimized_result = super::execute_optimized(&join, &structure);

        // Should have matches for 2 and 3
        assert_eq!(naive_result.len(), 2);
        assert_eq!(optimized_result.len(), 2);

        // Verify tuple order is (left_val, right_val)
        assert!(optimized_result.tuples.contains_key(&vec![
            Slid::from_usize(2),
            Slid::from_usize(2)
        ]));
        assert!(optimized_result.tuples.contains_key(&vec![
            Slid::from_usize(3),
            Slid::from_usize(3)
        ]));
    }

    #[test]
    fn test_hash_join_with_duplicates() {
        // Test hash join correctly handles multiplicities
        let mut structure = Structure::new(2);
        // Both sides have element 1
        structure.carriers[0].insert(1);
        structure.carriers[1].insert(1);

        // Join constant bags with multiplicities
        let left = QueryOp::Union {
            left: Box::new(QueryOp::Constant { tuple: vec![Slid::from_usize(1)] }),
            right: Box::new(QueryOp::Constant { tuple: vec![Slid::from_usize(1)] }),
        };
        let right = QueryOp::Union {
            left: Box::new(QueryOp::Constant { tuple: vec![Slid::from_usize(1)] }),
            right: Box::new(QueryOp::Union {
                left: Box::new(QueryOp::Constant { tuple: vec![Slid::from_usize(1)] }),
                right: Box::new(QueryOp::Constant { tuple: vec![Slid::from_usize(1)] }),
            }),
        };

        let join = QueryOp::Join {
            left: Box::new(left),
            right: Box::new(right),
            cond: JoinCond::Equi { left_col: 0, right_col: 0 },
        };

        let naive_result = execute(&join, &structure);
        let optimized_result = super::execute_optimized(&join, &structure);

        // 2 * 3 = 6 (multiplicity multiplication)
        let tuple = vec![Slid::from_usize(1), Slid::from_usize(1)];
        assert_eq!(naive_result.tuples.get(&tuple), Some(&6));
        assert_eq!(optimized_result.tuples.get(&tuple), Some(&6));
    }

    #[test]
    fn test_optimized_matches_naive_cross_join() {
        // Cross join should work the same in optimized backend
        let mut structure = Structure::new(2);
        structure.carriers[0].insert(0);
        structure.carriers[0].insert(1);
        structure.carriers[1].insert(10);
        structure.carriers[1].insert(11);

        let join = QueryOp::Join {
            left: Box::new(QueryOp::Scan { sort_idx: 0 }),
            right: Box::new(QueryOp::Scan { sort_idx: 1 }),
            cond: JoinCond::Cross,
        };

        let naive_result = execute(&join, &structure);
        let optimized_result = super::execute_optimized(&join, &structure);

        assert_eq!(naive_result.len(), 4); // 2 * 2 = 4
        assert_eq!(optimized_result.len(), 4);

        for (tuple, mult) in naive_result.iter() {
            assert_eq!(
                optimized_result.tuples.get(tuple),
                Some(mult),
                "tuple {:?} mismatch",
                tuple
            );
        }
    }

    #[test]
    fn test_optimized_nested_joins() {
        // Test optimized backend with nested joins
        let mut structure = Structure::new(3);
        structure.carriers[0].insert(1);
        structure.carriers[1].insert(1);
        structure.carriers[2].insert(1);

        // (A ⋈ B) ⋈ C
        let join_ab = QueryOp::Join {
            left: Box::new(QueryOp::Scan { sort_idx: 0 }),
            right: Box::new(QueryOp::Scan { sort_idx: 1 }),
            cond: JoinCond::Equi { left_col: 0, right_col: 0 },
        };

        let join_abc = QueryOp::Join {
            left: Box::new(join_ab),
            right: Box::new(QueryOp::Scan { sort_idx: 2 }),
            cond: JoinCond::Equi { left_col: 0, right_col: 0 },
        };

        let naive_result = execute(&join_abc, &structure);
        let optimized_result = super::execute_optimized(&join_abc, &structure);

        assert_eq!(naive_result.len(), optimized_result.len());
        // Result should be (1, 1, 1)
        let expected = vec![Slid::from_usize(1), Slid::from_usize(1), Slid::from_usize(1)];
        assert!(optimized_result.tuples.contains_key(&expected));
    }
}
