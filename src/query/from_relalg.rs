//! RelAlgIR Interpreter: Execute query plans represented as geolog instances.
//!
//! This module provides a CPU backend that interprets RelAlgIR instances.
//! It reads the string diagram structure from a geolog Structure and executes
//! the query operations to produce results.
//!
//! # Architecture
//!
//! A RelAlgIR instance encodes a query plan as a string diagram:
//! - Wire elements are edges carrying data streams (Z-sets of tuples)
//! - Op elements are boxes transforming data
//! - Composition is encoded by wire sharing (same Wire as output of one Op and input of another)
//!
//! The interpreter:
//! 1. Parses the instance structure to extract operations and wires
//! 2. Builds a dependency graph from wire connections
//! 3. Topologically sorts operations (respecting DBSP delay semantics)
//! 4. Executes each operation in order
//! 5. Returns the result on the designated output wire
//!
//! # Example
//!
//! ```ignore
//! use geolog::query::from_relalg::execute_relalg;
//!
//! let result = execute_relalg(
//!     &relalg_instance,    // The compiled query plan
//!     &relalg_theory,      // RelAlgIR theory
//!     &target_structure,   // Data to query
//! )?;
//! ```

use std::collections::{HashMap, VecDeque};

use crate::core::{ElaboratedTheory, Structure};
use crate::id::{NumericId, Slid, get_slid};
use crate::query::backend::Bag;
use crate::query::to_relalg::RelAlgInstance;

/// Error type for RelAlgIR execution
#[derive(Debug, Clone)]
pub enum RelAlgError {
    /// Missing required sort in RelAlgIR theory
    MissingSortId(String),
    /// Missing required function in RelAlgIR theory
    MissingFuncId(String),
    /// No output wire found
    NoOutputWire,
    /// Invalid operation structure
    InvalidOp(String),
    /// Cycle detected without delay
    InstantaneousCycle,
    /// Unsupported operation
    Unsupported(String),
}

impl std::fmt::Display for RelAlgError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MissingSortId(s) => write!(f, "Missing sort: {s}"),
            Self::MissingFuncId(s) => write!(f, "Missing function: {s}"),
            Self::NoOutputWire => write!(f, "No output wire found in plan"),
            Self::InvalidOp(s) => write!(f, "Invalid operation: {s}"),
            Self::InstantaneousCycle => write!(f, "Cycle detected without delay"),
            Self::Unsupported(s) => write!(f, "Unsupported: {s}"),
        }
    }
}

impl std::error::Error for RelAlgError {}

/// Cached sort/function IDs from RelAlgIR theory
struct RelAlgIds {
    // Core sorts
    wire: usize,
    op: usize,

    // Operation sorts
    scan_op: usize,
    filter_op: usize,
    distinct_op: usize,
    negate_op: usize,
    join_op: usize,
    union_op: usize,
    empty_op: usize,
    delay_op: usize,
    diff_op: usize,
    integrate_op: usize,

    // Predicate sorts
    pred: usize,
    true_pred: usize,
    false_pred: usize,
    col_eq_pred: usize,
    const_eq_pred: usize,
    and_pred: usize,
    or_pred: usize,

    // Join condition sorts
    join_cond: usize,
    equi_join_cond: usize,
    cross_join_cond: usize,

    // Column reference sorts
    col_ref: usize,
    col_path: usize,
    here_path: usize,
    left_path: usize,
    right_path: usize,

    // GeologMeta sorts (for references to target structure)
    srt: usize,
    elem: usize,
    func: usize,
}

impl RelAlgIds {
    fn from_theory(theory: &ElaboratedTheory) -> Result<Self, RelAlgError> {
        let sig = &theory.theory.signature;

        let get_sort = |name: &str| -> Result<usize, RelAlgError> {
            sig.sorts
                .iter()
                .position(|s| s == name)
                .ok_or_else(|| RelAlgError::MissingSortId(name.to_string()))
        };

        Ok(Self {
            wire: get_sort("Wire")?,
            op: get_sort("Op")?,

            scan_op: get_sort("ScanOp")?,
            filter_op: get_sort("FilterOp")?,
            distinct_op: get_sort("DistinctOp")?,
            negate_op: get_sort("NegateOp")?,
            join_op: get_sort("JoinOp")?,
            union_op: get_sort("UnionOp")?,
            empty_op: get_sort("EmptyOp")?,
            delay_op: get_sort("DelayOp")?,
            diff_op: get_sort("DiffOp")?,
            integrate_op: get_sort("IntegrateOp")?,

            pred: get_sort("Pred")?,
            true_pred: get_sort("TruePred")?,
            false_pred: get_sort("FalsePred")?,
            col_eq_pred: get_sort("ColEqPred")?,
            const_eq_pred: get_sort("ConstEqPred")?,
            and_pred: get_sort("AndPred")?,
            or_pred: get_sort("OrPred")?,

            join_cond: get_sort("JoinCond")?,
            equi_join_cond: get_sort("EquiJoinCond")?,
            cross_join_cond: get_sort("CrossJoinCond")?,

            col_ref: get_sort("ColRef")?,
            col_path: get_sort("ColPath")?,
            here_path: get_sort("HerePath")?,
            left_path: get_sort("LeftPath")?,
            right_path: get_sort("RightPath")?,

            srt: get_sort("GeologMeta/Srt")?,
            elem: get_sort("GeologMeta/Elem")?,
            func: get_sort("GeologMeta/Func")?,
        })
    }
}

/// Function IDs for navigating RelAlgIR structure
struct RelAlgFuncs {
    // ScanOp accessors
    scan_op_srt: usize,
    scan_op_out: usize,

    // FilterOp accessors
    filter_op_in: usize,
    filter_op_out: usize,
    filter_op_pred: usize,

    // DistinctOp accessors
    distinct_op_in: usize,
    distinct_op_out: usize,

    // NegateOp accessors
    negate_op_in: usize,
    negate_op_out: usize,

    // JoinOp accessors
    join_op_left_in: usize,
    join_op_right_in: usize,
    join_op_out: usize,
    join_op_cond: usize,

    // UnionOp accessors
    union_op_left_in: usize,
    union_op_right_in: usize,
    union_op_out: usize,

    // EmptyOp accessors
    empty_op_out: usize,

    // DelayOp accessors
    delay_op_in: usize,
    delay_op_out: usize,

    // DiffOp accessors
    diff_op_in: usize,
    diff_op_out: usize,

    // IntegrateOp accessors
    integrate_op_in: usize,
    integrate_op_out: usize,

    // Predicate accessors
    true_pred_pred: usize,
    false_pred_pred: usize,
    col_eq_pred_pred: usize,
    col_eq_pred_left: usize,
    col_eq_pred_right: usize,
    const_eq_pred_pred: usize,
    const_eq_pred_col: usize,
    const_eq_pred_val: usize,
    and_pred_pred: usize,
    and_pred_left: usize,
    and_pred_right: usize,
    or_pred_pred: usize,
    or_pred_left: usize,
    or_pred_right: usize,

    // Join condition accessors
    equi_join_cond_cond: usize,
    equi_join_cond_left_col: usize,
    equi_join_cond_right_col: usize,
    cross_join_cond_cond: usize,

    // ColRef accessors
    col_ref_wire: usize,
    col_ref_path: usize,

    // ColPath accessors
    here_path_path: usize,
    left_path_path: usize,
    left_path_rest: usize,
    right_path_path: usize,
    right_path_rest: usize,
}

impl RelAlgFuncs {
    fn from_theory(theory: &ElaboratedTheory) -> Result<Self, RelAlgError> {
        let sig = &theory.theory.signature;

        let get_func = |name: &str| -> Result<usize, RelAlgError> {
            sig.func_names
                .get(name)
                .copied()
                .ok_or_else(|| RelAlgError::MissingFuncId(name.to_string()))
        };

        Ok(Self {
            scan_op_srt: get_func("ScanOp/srt")?,
            scan_op_out: get_func("ScanOp/out")?,

            filter_op_in: get_func("FilterOp/in")?,
            filter_op_out: get_func("FilterOp/out")?,
            filter_op_pred: get_func("FilterOp/pred")?,

            distinct_op_in: get_func("DistinctOp/in")?,
            distinct_op_out: get_func("DistinctOp/out")?,

            negate_op_in: get_func("NegateOp/in")?,
            negate_op_out: get_func("NegateOp/out")?,

            join_op_left_in: get_func("JoinOp/left_in")?,
            join_op_right_in: get_func("JoinOp/right_in")?,
            join_op_out: get_func("JoinOp/out")?,
            join_op_cond: get_func("JoinOp/cond")?,

            union_op_left_in: get_func("UnionOp/left_in")?,
            union_op_right_in: get_func("UnionOp/right_in")?,
            union_op_out: get_func("UnionOp/out")?,

            empty_op_out: get_func("EmptyOp/out")?,

            delay_op_in: get_func("DelayOp/in")?,
            delay_op_out: get_func("DelayOp/out")?,

            diff_op_in: get_func("DiffOp/in")?,
            diff_op_out: get_func("DiffOp/out")?,

            integrate_op_in: get_func("IntegrateOp/in")?,
            integrate_op_out: get_func("IntegrateOp/out")?,

            true_pred_pred: get_func("TruePred/pred")?,
            false_pred_pred: get_func("FalsePred/pred")?,
            col_eq_pred_pred: get_func("ColEqPred/pred")?,
            col_eq_pred_left: get_func("ColEqPred/left")?,
            col_eq_pred_right: get_func("ColEqPred/right")?,
            const_eq_pred_pred: get_func("ConstEqPred/pred")?,
            const_eq_pred_col: get_func("ConstEqPred/col")?,
            const_eq_pred_val: get_func("ConstEqPred/val")?,
            and_pred_pred: get_func("AndPred/pred")?,
            and_pred_left: get_func("AndPred/left")?,
            and_pred_right: get_func("AndPred/right")?,
            or_pred_pred: get_func("OrPred/pred")?,
            or_pred_left: get_func("OrPred/left")?,
            or_pred_right: get_func("OrPred/right")?,

            equi_join_cond_cond: get_func("EquiJoinCond/cond")?,
            equi_join_cond_left_col: get_func("EquiJoinCond/left_col")?,
            equi_join_cond_right_col: get_func("EquiJoinCond/right_col")?,
            cross_join_cond_cond: get_func("CrossJoinCond/cond")?,

            col_ref_wire: get_func("ColRef/wire")?,
            col_ref_path: get_func("ColRef/path")?,

            here_path_path: get_func("HerePath/path")?,
            left_path_path: get_func("LeftPath/path")?,
            left_path_rest: get_func("LeftPath/rest")?,
            right_path_path: get_func("RightPath/path")?,
            right_path_rest: get_func("RightPath/rest")?,
        })
    }
}

/// Parsed operation from a RelAlgIR instance
#[derive(Debug, Clone)]
enum ParsedOp {
    Scan {
        sort_idx: usize,
        out_wire: Slid,
    },
    Filter {
        in_wire: Slid,
        out_wire: Slid,
        pred: Slid,
    },
    Distinct {
        in_wire: Slid,
        out_wire: Slid,
    },
    Negate {
        in_wire: Slid,
        out_wire: Slid,
    },
    Join {
        left_wire: Slid,
        right_wire: Slid,
        out_wire: Slid,
        cond: Slid,
    },
    Union {
        left_wire: Slid,
        right_wire: Slid,
        out_wire: Slid,
    },
    Empty {
        out_wire: Slid,
    },
    Delay {
        in_wire: Slid,
        out_wire: Slid,
    },
    Diff {
        in_wire: Slid,
        out_wire: Slid,
    },
    Integrate {
        in_wire: Slid,
        out_wire: Slid,
    },
}

impl ParsedOp {
    fn out_wire(&self) -> Slid {
        match self {
            Self::Scan { out_wire, .. }
            | Self::Filter { out_wire, .. }
            | Self::Distinct { out_wire, .. }
            | Self::Negate { out_wire, .. }
            | Self::Join { out_wire, .. }
            | Self::Union { out_wire, .. }
            | Self::Empty { out_wire, .. }
            | Self::Delay { out_wire, .. }
            | Self::Diff { out_wire, .. }
            | Self::Integrate { out_wire, .. } => *out_wire,
        }
    }

    fn in_wires(&self) -> Vec<Slid> {
        match self {
            Self::Scan { .. } | Self::Empty { .. } => vec![],
            Self::Filter { in_wire, .. }
            | Self::Distinct { in_wire, .. }
            | Self::Negate { in_wire, .. }
            | Self::Delay { in_wire, .. }
            | Self::Diff { in_wire, .. }
            | Self::Integrate { in_wire, .. } => vec![*in_wire],
            Self::Join {
                left_wire,
                right_wire,
                ..
            }
            | Self::Union {
                left_wire,
                right_wire,
                ..
            } => vec![*left_wire, *right_wire],
        }
    }

    /// Returns true if this operation breaks instantaneous cycles
    fn breaks_cycle(&self) -> bool {
        matches!(self, Self::Delay { .. } | Self::Integrate { .. })
    }
}

/// Parsed predicate from a RelAlgIR instance
#[derive(Debug, Clone)]
pub enum ParsedPred {
    True,
    False,
    ColEq { left: usize, right: usize },
    ConstEq { col: usize, val: Slid },
    And(Box<ParsedPred>, Box<ParsedPred>),
    Or(Box<ParsedPred>, Box<ParsedPred>),
}

/// Parsed join condition
#[derive(Debug, Clone)]
pub enum ParsedJoinCond {
    Cross,
    Equi { left_col: usize, right_col: usize },
}

/// Context for interpreting RelAlgIR instances
struct InterpretContext<'a> {
    /// The RelAlgIR instance being interpreted
    instance: &'a RelAlgInstance,
    /// RelAlgIR theory sort IDs
    ids: RelAlgIds,
    /// RelAlgIR theory function IDs
    funcs: RelAlgFuncs,
    /// Wire values during execution
    wire_values: HashMap<Slid, Bag>,
    /// Target structure being queried
    target: &'a Structure,
}

impl<'a> InterpretContext<'a> {
    fn new(
        instance: &'a RelAlgInstance,
        theory: &ElaboratedTheory,
        target: &'a Structure,
    ) -> Result<Self, RelAlgError> {
        Ok(Self {
            instance,
            ids: RelAlgIds::from_theory(theory)?,
            funcs: RelAlgFuncs::from_theory(theory)?,
            wire_values: HashMap::new(),
            target,
        })
    }

    /// Get function value for an element
    fn get_func_value(&self, func_id: usize, elem: Slid) -> Option<Slid> {
        let structure = &self.instance.structure;
        // Convert global Slid to sort-local index
        let local_idx = structure.sort_local_id(elem).index();
        structure
            .functions
            .get(func_id)
            .and_then(|f| get_slid(f.get_local(local_idx)))
    }

    /// Get sort index from a GeologMeta/Srt element using the sort_mapping
    fn get_srt_sort_idx(&self, srt_elem: Slid) -> Result<usize, RelAlgError> {
        self.instance
            .sort_mapping
            .get(&srt_elem)
            .copied()
            .ok_or_else(|| RelAlgError::InvalidOp(format!(
                "Unknown Srt element {:?} - not in sort_mapping",
                srt_elem
            )))
    }

    /// Parse all operations from the instance
    fn parse_operations(&self) -> Result<Vec<ParsedOp>, RelAlgError> {
        let mut ops = Vec::new();
        let structure = &self.instance.structure;

        // Find all ScanOp elements
        for elem_idx in structure.carriers[self.ids.scan_op].iter() {
            let elem = Slid::from_usize(elem_idx as usize);
            let srt = self
                .get_func_value(self.funcs.scan_op_srt, elem)
                .ok_or_else(|| RelAlgError::InvalidOp("ScanOp missing srt".into()))?;
            let out_wire = self
                .get_func_value(self.funcs.scan_op_out, elem)
                .ok_or_else(|| RelAlgError::InvalidOp("ScanOp missing out".into()))?;

            let sort_idx = self.get_srt_sort_idx(srt)?;
            ops.push(ParsedOp::Scan { sort_idx, out_wire });
        }

        // Find all FilterOp elements
        for elem_idx in structure.carriers[self.ids.filter_op].iter() {
            let elem = Slid::from_usize(elem_idx as usize);
            let in_wire = self
                .get_func_value(self.funcs.filter_op_in, elem)
                .ok_or_else(|| RelAlgError::InvalidOp("FilterOp missing in".into()))?;
            let out_wire = self
                .get_func_value(self.funcs.filter_op_out, elem)
                .ok_or_else(|| RelAlgError::InvalidOp("FilterOp missing out".into()))?;
            let pred = self
                .get_func_value(self.funcs.filter_op_pred, elem)
                .ok_or_else(|| RelAlgError::InvalidOp("FilterOp missing pred".into()))?;

            ops.push(ParsedOp::Filter {
                in_wire,
                out_wire,
                pred,
            });
        }

        // Find all DistinctOp elements
        for elem_idx in structure.carriers[self.ids.distinct_op].iter() {
            let elem = Slid::from_usize(elem_idx as usize);
            let in_wire = self
                .get_func_value(self.funcs.distinct_op_in, elem)
                .ok_or_else(|| RelAlgError::InvalidOp("DistinctOp missing in".into()))?;
            let out_wire = self
                .get_func_value(self.funcs.distinct_op_out, elem)
                .ok_or_else(|| RelAlgError::InvalidOp("DistinctOp missing out".into()))?;

            ops.push(ParsedOp::Distinct { in_wire, out_wire });
        }

        // Find all NegateOp elements
        for elem_idx in structure.carriers[self.ids.negate_op].iter() {
            let elem = Slid::from_usize(elem_idx as usize);
            let in_wire = self
                .get_func_value(self.funcs.negate_op_in, elem)
                .ok_or_else(|| RelAlgError::InvalidOp("NegateOp missing in".into()))?;
            let out_wire = self
                .get_func_value(self.funcs.negate_op_out, elem)
                .ok_or_else(|| RelAlgError::InvalidOp("NegateOp missing out".into()))?;

            ops.push(ParsedOp::Negate { in_wire, out_wire });
        }

        // Find all JoinOp elements
        for elem_idx in structure.carriers[self.ids.join_op].iter() {
            let elem = Slid::from_usize(elem_idx as usize);
            let left_wire = self
                .get_func_value(self.funcs.join_op_left_in, elem)
                .ok_or_else(|| RelAlgError::InvalidOp("JoinOp missing left_in".into()))?;
            let right_wire = self
                .get_func_value(self.funcs.join_op_right_in, elem)
                .ok_or_else(|| RelAlgError::InvalidOp("JoinOp missing right_in".into()))?;
            let out_wire = self
                .get_func_value(self.funcs.join_op_out, elem)
                .ok_or_else(|| RelAlgError::InvalidOp("JoinOp missing out".into()))?;
            let cond = self
                .get_func_value(self.funcs.join_op_cond, elem)
                .ok_or_else(|| RelAlgError::InvalidOp("JoinOp missing cond".into()))?;

            ops.push(ParsedOp::Join {
                left_wire,
                right_wire,
                out_wire,
                cond,
            });
        }

        // Find all UnionOp elements
        for elem_idx in structure.carriers[self.ids.union_op].iter() {
            let elem = Slid::from_usize(elem_idx as usize);
            let left_wire = self
                .get_func_value(self.funcs.union_op_left_in, elem)
                .ok_or_else(|| RelAlgError::InvalidOp("UnionOp missing left_in".into()))?;
            let right_wire = self
                .get_func_value(self.funcs.union_op_right_in, elem)
                .ok_or_else(|| RelAlgError::InvalidOp("UnionOp missing right_in".into()))?;
            let out_wire = self
                .get_func_value(self.funcs.union_op_out, elem)
                .ok_or_else(|| RelAlgError::InvalidOp("UnionOp missing out".into()))?;

            ops.push(ParsedOp::Union {
                left_wire,
                right_wire,
                out_wire,
            });
        }

        // Find all EmptyOp elements
        for elem_idx in structure.carriers[self.ids.empty_op].iter() {
            let elem = Slid::from_usize(elem_idx as usize);
            let out_wire = self
                .get_func_value(self.funcs.empty_op_out, elem)
                .ok_or_else(|| RelAlgError::InvalidOp("EmptyOp missing out".into()))?;

            ops.push(ParsedOp::Empty { out_wire });
        }

        // Find all DelayOp elements
        for elem_idx in structure.carriers[self.ids.delay_op].iter() {
            let elem = Slid::from_usize(elem_idx as usize);
            let in_wire = self
                .get_func_value(self.funcs.delay_op_in, elem)
                .ok_or_else(|| RelAlgError::InvalidOp("DelayOp missing in".into()))?;
            let out_wire = self
                .get_func_value(self.funcs.delay_op_out, elem)
                .ok_or_else(|| RelAlgError::InvalidOp("DelayOp missing out".into()))?;

            ops.push(ParsedOp::Delay { in_wire, out_wire });
        }

        // Find all DiffOp elements
        for elem_idx in structure.carriers[self.ids.diff_op].iter() {
            let elem = Slid::from_usize(elem_idx as usize);
            let in_wire = self
                .get_func_value(self.funcs.diff_op_in, elem)
                .ok_or_else(|| RelAlgError::InvalidOp("DiffOp missing in".into()))?;
            let out_wire = self
                .get_func_value(self.funcs.diff_op_out, elem)
                .ok_or_else(|| RelAlgError::InvalidOp("DiffOp missing out".into()))?;

            ops.push(ParsedOp::Diff { in_wire, out_wire });
        }

        // Find all IntegrateOp elements
        for elem_idx in structure.carriers[self.ids.integrate_op].iter() {
            let elem = Slid::from_usize(elem_idx as usize);
            let in_wire = self
                .get_func_value(self.funcs.integrate_op_in, elem)
                .ok_or_else(|| RelAlgError::InvalidOp("IntegrateOp missing in".into()))?;
            let out_wire = self
                .get_func_value(self.funcs.integrate_op_out, elem)
                .ok_or_else(|| RelAlgError::InvalidOp("IntegrateOp missing out".into()))?;

            ops.push(ParsedOp::Integrate { in_wire, out_wire });
        }

        Ok(ops)
    }

    /// Parse a predicate element
    fn parse_predicate(&self, pred: Slid) -> Result<ParsedPred, RelAlgError> {
        // Try to find which sort the predicate element belongs to
        let structure = &self.instance.structure;

        // Check if it's TruePred
        for elem_idx in structure.carriers[self.ids.true_pred].iter() {
            let elem = Slid::from_usize(elem_idx as usize);
            if let Some(p) = self.get_func_value(self.funcs.true_pred_pred, elem)
                && p == pred {
                    return Ok(ParsedPred::True);
                }
        }

        // Check if it's FalsePred
        for elem_idx in structure.carriers[self.ids.false_pred].iter() {
            let elem = Slid::from_usize(elem_idx as usize);
            if let Some(p) = self.get_func_value(self.funcs.false_pred_pred, elem)
                && p == pred {
                    return Ok(ParsedPred::False);
                }
        }

        // Check if it's ColEqPred
        for elem_idx in structure.carriers[self.ids.col_eq_pred].iter() {
            let elem = Slid::from_usize(elem_idx as usize);
            if let Some(p) = self.get_func_value(self.funcs.col_eq_pred_pred, elem)
                && p == pred {
                    let left_ref = self
                        .get_func_value(self.funcs.col_eq_pred_left, elem)
                        .ok_or_else(|| RelAlgError::InvalidOp("ColEqPred missing left".into()))?;
                    let right_ref = self
                        .get_func_value(self.funcs.col_eq_pred_right, elem)
                        .ok_or_else(|| RelAlgError::InvalidOp("ColEqPred missing right".into()))?;

                    let left = self.parse_col_ref(left_ref)?;
                    let right = self.parse_col_ref(right_ref)?;

                    return Ok(ParsedPred::ColEq { left, right });
                }
        }

        // Check if it's ConstEqPred
        for elem_idx in structure.carriers[self.ids.const_eq_pred].iter() {
            let elem = Slid::from_usize(elem_idx as usize);
            if let Some(p) = self.get_func_value(self.funcs.const_eq_pred_pred, elem)
                && p == pred {
                    let col_ref = self
                        .get_func_value(self.funcs.const_eq_pred_col, elem)
                        .ok_or_else(|| RelAlgError::InvalidOp("ConstEqPred missing col".into()))?;
                    let val = self
                        .get_func_value(self.funcs.const_eq_pred_val, elem)
                        .ok_or_else(|| RelAlgError::InvalidOp("ConstEqPred missing val".into()))?;

                    let col = self.parse_col_ref(col_ref)?;

                    return Ok(ParsedPred::ConstEq { col, val });
                }
        }

        // Check if it's AndPred
        for elem_idx in structure.carriers[self.ids.and_pred].iter() {
            let elem = Slid::from_usize(elem_idx as usize);
            if let Some(p) = self.get_func_value(self.funcs.and_pred_pred, elem)
                && p == pred {
                    let left = self
                        .get_func_value(self.funcs.and_pred_left, elem)
                        .ok_or_else(|| RelAlgError::InvalidOp("AndPred missing left".into()))?;
                    let right = self
                        .get_func_value(self.funcs.and_pred_right, elem)
                        .ok_or_else(|| RelAlgError::InvalidOp("AndPred missing right".into()))?;

                    let left_pred = self.parse_predicate(left)?;
                    let right_pred = self.parse_predicate(right)?;

                    return Ok(ParsedPred::And(Box::new(left_pred), Box::new(right_pred)));
                }
        }

        // Check if it's OrPred
        for elem_idx in structure.carriers[self.ids.or_pred].iter() {
            let elem = Slid::from_usize(elem_idx as usize);
            if let Some(p) = self.get_func_value(self.funcs.or_pred_pred, elem)
                && p == pred {
                    let left = self
                        .get_func_value(self.funcs.or_pred_left, elem)
                        .ok_or_else(|| RelAlgError::InvalidOp("OrPred missing left".into()))?;
                    let right = self
                        .get_func_value(self.funcs.or_pred_right, elem)
                        .ok_or_else(|| RelAlgError::InvalidOp("OrPred missing right".into()))?;

                    let left_pred = self.parse_predicate(left)?;
                    let right_pred = self.parse_predicate(right)?;

                    return Ok(ParsedPred::Or(Box::new(left_pred), Box::new(right_pred)));
                }
        }

        Err(RelAlgError::InvalidOp(format!(
            "Unknown predicate type for {:?}",
            pred
        )))
    }

    /// Parse a join condition element
    fn parse_join_cond(&self, cond: Slid) -> Result<ParsedJoinCond, RelAlgError> {
        let structure = &self.instance.structure;

        // Check if it's CrossJoinCond
        for elem_idx in structure.carriers[self.ids.cross_join_cond].iter() {
            let elem = Slid::from_usize(elem_idx as usize);
            if let Some(c) = self.get_func_value(self.funcs.cross_join_cond_cond, elem)
                && c == cond {
                    return Ok(ParsedJoinCond::Cross);
                }
        }

        // Check if it's EquiJoinCond
        for elem_idx in structure.carriers[self.ids.equi_join_cond].iter() {
            let elem = Slid::from_usize(elem_idx as usize);
            if let Some(c) = self.get_func_value(self.funcs.equi_join_cond_cond, elem)
                && c == cond {
                    let left_col_ref = self
                        .get_func_value(self.funcs.equi_join_cond_left_col, elem)
                        .ok_or_else(|| {
                            RelAlgError::InvalidOp("EquiJoinCond missing left_col".into())
                        })?;
                    let right_col_ref = self
                        .get_func_value(self.funcs.equi_join_cond_right_col, elem)
                        .ok_or_else(|| {
                            RelAlgError::InvalidOp("EquiJoinCond missing right_col".into())
                        })?;

                    let left_col = self.parse_col_ref(left_col_ref)?;
                    let right_col = self.parse_col_ref(right_col_ref)?;

                    return Ok(ParsedJoinCond::Equi { left_col, right_col });
                }
        }

        Err(RelAlgError::InvalidOp(format!(
            "Unknown join condition type for {:?}",
            cond
        )))
    }

    /// Parse a column reference to get the column index
    fn parse_col_ref(&self, col_ref: Slid) -> Result<usize, RelAlgError> {
        // Get the path from the ColRef
        let path = self
            .get_func_value(self.funcs.col_ref_path, col_ref)
            .ok_or_else(|| RelAlgError::InvalidOp("ColRef missing path".into()))?;

        self.parse_col_path(path)
    }

    /// Parse a column path to get the column index
    fn parse_col_path(&self, path: Slid) -> Result<usize, RelAlgError> {
        let structure = &self.instance.structure;

        // Check if it's HerePath (index 0)
        for elem_idx in structure.carriers[self.ids.here_path].iter() {
            let elem = Slid::from_usize(elem_idx as usize);
            if let Some(p) = self.get_func_value(self.funcs.here_path_path, elem)
                && p == path {
                    return Ok(0);
                }
        }

        // Check if it's LeftPath
        for elem_idx in structure.carriers[self.ids.left_path].iter() {
            let elem = Slid::from_usize(elem_idx as usize);
            if let Some(p) = self.get_func_value(self.funcs.left_path_path, elem)
                && p == path {
                    let rest = self
                        .get_func_value(self.funcs.left_path_rest, elem)
                        .ok_or_else(|| RelAlgError::InvalidOp("LeftPath missing rest".into()))?;
                    return self.parse_col_path(rest);
                }
        }

        // Check if it's RightPath
        for elem_idx in structure.carriers[self.ids.right_path].iter() {
            let elem = Slid::from_usize(elem_idx as usize);
            if let Some(p) = self.get_func_value(self.funcs.right_path_path, elem)
                && p == path {
                    let rest = self
                        .get_func_value(self.funcs.right_path_rest, elem)
                        .ok_or_else(|| RelAlgError::InvalidOp("RightPath missing rest".into()))?;
                    // Right path adds 1 to the column index
                    return Ok(1 + self.parse_col_path(rest)?);
                }
        }

        Err(RelAlgError::InvalidOp(format!(
            "Unknown path type for {:?}",
            path
        )))
    }

    /// Topologically sort operations (respecting dependencies)
    fn topological_sort(&self, ops: &[ParsedOp]) -> Result<Vec<usize>, RelAlgError> {
        // Build output wire -> operation index map
        let mut wire_to_op: HashMap<Slid, usize> = HashMap::new();
        for (idx, op) in ops.iter().enumerate() {
            wire_to_op.insert(op.out_wire(), idx);
        }

        // Build dependency graph
        let mut in_degree: Vec<usize> = vec![0; ops.len()];
        let mut dependents: Vec<Vec<usize>> = vec![Vec::new(); ops.len()];

        for (idx, op) in ops.iter().enumerate() {
            for in_wire in op.in_wires() {
                if let Some(&producer_idx) = wire_to_op.get(&in_wire) {
                    // Skip delay edges for cycle breaking
                    if !ops[producer_idx].breaks_cycle() {
                        in_degree[idx] += 1;
                        dependents[producer_idx].push(idx);
                    }
                }
            }
        }

        // Kahn's algorithm
        let mut queue: VecDeque<usize> = VecDeque::new();
        for (idx, &degree) in in_degree.iter().enumerate() {
            if degree == 0 {
                queue.push_back(idx);
            }
        }

        let mut sorted = Vec::new();
        while let Some(idx) = queue.pop_front() {
            sorted.push(idx);
            for &dep_idx in &dependents[idx] {
                in_degree[dep_idx] -= 1;
                if in_degree[dep_idx] == 0 {
                    queue.push_back(dep_idx);
                }
            }
        }

        if sorted.len() != ops.len() {
            return Err(RelAlgError::InstantaneousCycle);
        }

        Ok(sorted)
    }

    /// Execute a single operation
    fn execute_op(&mut self, op: &ParsedOp) -> Result<Bag, RelAlgError> {
        match op {
            ParsedOp::Scan { sort_idx, .. } => {
                // Emit all elements of the sort as singleton tuples
                let mut result = Bag::new();
                if let Some(carrier) = self.target.carriers.get(*sort_idx) {
                    for elem in carrier.iter() {
                        let tuple = vec![Slid::from_usize(elem as usize)];
                        result.insert(tuple, 1);
                    }
                }
                Ok(result)
            }

            ParsedOp::Filter {
                in_wire,
                pred,
                ..
            } => {
                let input = self
                    .wire_values
                    .get(in_wire)
                    .ok_or_else(|| RelAlgError::InvalidOp("Filter input wire not found".into()))?
                    .clone();

                let parsed_pred = self.parse_predicate(*pred)?;

                let mut result = Bag::new();
                for (tuple, mult) in input.iter() {
                    if self.evaluate_predicate(&parsed_pred, tuple)? {
                        result.insert(tuple.clone(), *mult);
                    }
                }
                Ok(result)
            }

            ParsedOp::Distinct { in_wire, .. } => {
                let input = self
                    .wire_values
                    .get(in_wire)
                    .ok_or_else(|| {
                        RelAlgError::InvalidOp("Distinct input wire not found".into())
                    })?
                    .clone();

                let mut result = Bag::new();
                for (tuple, mult) in input.iter() {
                    if *mult > 0 {
                        result.insert(tuple.clone(), 1);
                    }
                }
                Ok(result)
            }

            ParsedOp::Negate { in_wire, .. } => {
                let input = self
                    .wire_values
                    .get(in_wire)
                    .ok_or_else(|| {
                        RelAlgError::InvalidOp("Negate input wire not found".into())
                    })?
                    .clone();

                let mut result = Bag::new();
                for (tuple, mult) in input.iter() {
                    result.insert(tuple.clone(), -mult);
                }
                Ok(result)
            }

            ParsedOp::Join {
                left_wire,
                right_wire,
                cond,
                ..
            } => {
                let left = self
                    .wire_values
                    .get(left_wire)
                    .ok_or_else(|| {
                        RelAlgError::InvalidOp("Join left input wire not found".into())
                    })?
                    .clone();
                let right = self
                    .wire_values
                    .get(right_wire)
                    .ok_or_else(|| {
                        RelAlgError::InvalidOp("Join right input wire not found".into())
                    })?
                    .clone();

                let parsed_cond = self.parse_join_cond(*cond)?;

                let mut result = Bag::new();

                match parsed_cond {
                    ParsedJoinCond::Cross => {
                        // Cartesian product
                        for (l_tuple, l_mult) in left.iter() {
                            for (r_tuple, r_mult) in right.iter() {
                                let mut joined = l_tuple.clone();
                                joined.extend(r_tuple.iter().cloned());
                                result.insert(joined, l_mult * r_mult);
                            }
                        }
                    }
                    ParsedJoinCond::Equi { left_col, right_col } => {
                        // Hash join
                        let mut right_index: HashMap<Slid, Vec<(&Vec<Slid>, i64)>> = HashMap::new();
                        for (r_tuple, r_mult) in right.iter() {
                            if let Some(&key) = r_tuple.get(right_col) {
                                right_index.entry(key).or_default().push((r_tuple, *r_mult));
                            }
                        }

                        for (l_tuple, l_mult) in left.iter() {
                            if let Some(&key) = l_tuple.get(left_col)
                                && let Some(matches) = right_index.get(&key) {
                                    for (r_tuple, r_mult) in matches {
                                        let mut joined = l_tuple.clone();
                                        joined.extend(r_tuple.iter().cloned());
                                        result.insert(joined, l_mult * r_mult);
                                    }
                                }
                        }
                    }
                }

                Ok(result)
            }

            ParsedOp::Union {
                left_wire,
                right_wire,
                ..
            } => {
                let left = self
                    .wire_values
                    .get(left_wire)
                    .ok_or_else(|| {
                        RelAlgError::InvalidOp("Union left input wire not found".into())
                    })?
                    .clone();
                let right = self
                    .wire_values
                    .get(right_wire)
                    .ok_or_else(|| {
                        RelAlgError::InvalidOp("Union right input wire not found".into())
                    })?
                    .clone();

                let mut result = left;
                for (tuple, mult) in right.iter() {
                    result.insert(tuple.clone(), result.tuples.get(tuple).unwrap_or(&0) + mult);
                }
                Ok(result)
            }

            ParsedOp::Empty { .. } => Ok(Bag::new()),

            ParsedOp::Delay { in_wire, .. } => {
                // For non-streaming execution, delay is identity
                let input = self
                    .wire_values
                    .get(in_wire)
                    .ok_or_else(|| {
                        RelAlgError::InvalidOp("Delay input wire not found".into())
                    })?
                    .clone();
                Ok(input)
            }

            ParsedOp::Diff { in_wire, .. } => {
                // For non-streaming execution, diff is identity
                let input = self
                    .wire_values
                    .get(in_wire)
                    .ok_or_else(|| {
                        RelAlgError::InvalidOp("Diff input wire not found".into())
                    })?
                    .clone();
                Ok(input)
            }

            ParsedOp::Integrate { in_wire, .. } => {
                // For non-streaming execution, integrate is identity
                let input = self
                    .wire_values
                    .get(in_wire)
                    .ok_or_else(|| {
                        RelAlgError::InvalidOp("Integrate input wire not found".into())
                    })?
                    .clone();
                Ok(input)
            }
        }
    }

    /// Evaluate a predicate on a tuple
    #[allow(clippy::only_used_in_recursion)]
    fn evaluate_predicate(&self, pred: &ParsedPred, tuple: &[Slid]) -> Result<bool, RelAlgError> {
        match pred {
            ParsedPred::True => Ok(true),
            ParsedPred::False => Ok(false),
            ParsedPred::ColEq { left, right } => {
                let l = tuple.get(*left);
                let r = tuple.get(*right);
                Ok(l.is_some() && l == r)
            }
            ParsedPred::ConstEq { col, val } => {
                let c = tuple.get(*col);
                Ok(c == Some(val))
            }
            ParsedPred::And(left, right) => {
                Ok(self.evaluate_predicate(left, tuple)?
                    && self.evaluate_predicate(right, tuple)?)
            }
            ParsedPred::Or(left, right) => {
                Ok(self.evaluate_predicate(left, tuple)?
                    || self.evaluate_predicate(right, tuple)?)
            }
        }
    }
}

/// Execute a RelAlgIR instance against a target structure
///
/// # Arguments
/// * `instance` - The RelAlgIR instance representing the query plan
/// * `relalg_theory` - The RelAlgIR theory
/// * `target` - The structure to query
/// * `output_wire_name` - Name of the output wire (defaults to "output")
///
/// # Returns
/// The query result as a Z-set
pub fn execute_relalg(
    instance: &RelAlgInstance,
    relalg_theory: &ElaboratedTheory,
    target: &Structure,
    output_wire_name: Option<&str>,
) -> Result<Bag, RelAlgError> {
    let mut ctx = InterpretContext::new(instance, relalg_theory, target)?;

    // Parse all operations
    let ops = ctx.parse_operations()?;

    if ops.is_empty() {
        return Ok(Bag::new());
    }

    // Find output wire - use instance.output_wire by default, or look up by name
    let output_wire = if let Some(name) = output_wire_name {
        instance
            .names
            .iter()
            .find(|(_, n)| *n == name)
            .map(|(slid, _)| *slid)
            .ok_or(RelAlgError::NoOutputWire)?
    } else {
        instance.output_wire
    };

    // Topologically sort operations
    let sorted = ctx.topological_sort(&ops)?;

    // Execute in order
    for &idx in &sorted {
        let result = ctx.execute_op(&ops[idx])?;
        let out_wire = ops[idx].out_wire();
        ctx.wire_values.insert(out_wire, result);
    }

    // Return output wire value
    ctx.wire_values
        .remove(&output_wire)
        .ok_or(RelAlgError::NoOutputWire)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parsed_op_in_wires() {
        let scan = ParsedOp::Scan {
            sort_idx: 0,
            out_wire: Slid::from_usize(0),
        };
        assert!(scan.in_wires().is_empty());

        let filter = ParsedOp::Filter {
            in_wire: Slid::from_usize(0),
            out_wire: Slid::from_usize(1),
            pred: Slid::from_usize(2),
        };
        assert_eq!(filter.in_wires(), vec![Slid::from_usize(0)]);

        let join = ParsedOp::Join {
            left_wire: Slid::from_usize(0),
            right_wire: Slid::from_usize(1),
            out_wire: Slid::from_usize(2),
            cond: Slid::from_usize(3),
        };
        assert_eq!(
            join.in_wires(),
            vec![Slid::from_usize(0), Slid::from_usize(1)]
        );
    }

    #[test]
    fn test_parsed_op_breaks_cycle() {
        let scan = ParsedOp::Scan {
            sort_idx: 0,
            out_wire: Slid::from_usize(0),
        };
        assert!(!scan.breaks_cycle());

        let delay = ParsedOp::Delay {
            in_wire: Slid::from_usize(0),
            out_wire: Slid::from_usize(1),
        };
        assert!(delay.breaks_cycle());

        let integrate = ParsedOp::Integrate {
            in_wire: Slid::from_usize(0),
            out_wire: Slid::from_usize(1),
        };
        assert!(integrate.breaks_cycle());
    }
}
