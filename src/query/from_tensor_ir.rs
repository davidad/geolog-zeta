//! TensorIR Interpreter: Execute tensor plans represented as geolog instances.
//!
//! This module executes TensorIR instances using the tagless final TensorSym trait,
//! enabling both eager execution and incremental (delta-tracking) computation.
//!
//! # Architecture
//!
//! A TensorIR instance encodes a tensor computation as a string diagram:
//! - Wire elements are edges carrying tensors
//! - Op elements are boxes transforming tensors
//! - Composition is encoded by wire sharing
//!
//! The interpreter:
//! 1. Parses the instance structure to extract operations and wires
//! 2. Builds a dependency graph from wire connections
//! 3. Topologically sorts operations (respecting DBSP delay semantics)
//! 4. Executes each operation using TensorSym
//! 5. Returns the result tensor on the designated output wire
//!
//! # Execution Modes
//!
//! The same TensorIR instance can be executed in different modes:
//! - `Eager<BTreeSetPattern>`: Immediate materialization
//! - `Incremental<BTreeSetPattern>`: Track (value, delta) pairs for change propagation
//!
//! # Example
//!
//! ```ignore
//! use geolog::query::from_tensor_ir::{execute_tensor_ir, TensorIRExecutor};
//! use geolog::tensor::algebra::{Eager, Incremental};
//! use geolog::tensor::pattern::BTreeSetPattern;
//!
//! // Eager execution
//! let result = execute_tensor_ir::<Eager<BTreeSetPattern>>(
//!     &tensor_ir_instance,
//!     &tensor_ir_theory,
//!     &target_structure,
//! )?;
//!
//! // Incremental execution (with deltas)
//! let (result, delta) = execute_tensor_ir::<Incremental<BTreeSetPattern>>(
//!     &tensor_ir_instance,
//!     &tensor_ir_theory,
//!     &target_structure,
//! )?;
//! ```

use std::collections::{BTreeSet, HashMap, VecDeque};

use crate::core::{ElaboratedTheory, Structure};
use crate::id::{NumericId, Slid, get_slid};
use crate::query::to_tensor_ir::TensorIRInstance;
use crate::tensor::algebra::{Eager, TensorSym};
use crate::tensor::pattern::BTreeSetPattern;

/// Error type for TensorIR execution
#[derive(Debug, Clone)]
pub enum TensorIRError {
    /// Missing required sort in TensorIR theory
    MissingSortId(String),
    /// Missing required function in TensorIR theory
    MissingFuncId(String),
    /// No output wire found
    NoOutputWire,
    /// Invalid operation structure
    InvalidOp(String),
    /// Cycle detected without delay
    InstantaneousCycle,
    /// Unsupported operation
    Unsupported(String),
    /// Type mismatch
    TypeMismatch(String),
}

impl std::fmt::Display for TensorIRError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MissingSortId(s) => write!(f, "Missing sort: {s}"),
            Self::MissingFuncId(s) => write!(f, "Missing function: {s}"),
            Self::NoOutputWire => write!(f, "No output wire found in plan"),
            Self::InvalidOp(s) => write!(f, "Invalid operation: {s}"),
            Self::InstantaneousCycle => write!(f, "Cycle detected without delay"),
            Self::Unsupported(s) => write!(f, "Unsupported: {s}"),
            Self::TypeMismatch(s) => write!(f, "Type mismatch: {s}"),
        }
    }
}

impl std::error::Error for TensorIRError {}

/// Cached sort IDs from TensorIR theory
#[allow(dead_code)]
struct TensorIRSortIds {
    // GeologMeta sorts
    theory: usize,
    srt: usize,
    elem: usize,
    rel: usize,
    func: usize,

    // Core tensor sorts
    semiring: usize,
    index_space: usize,
    tensor_type: usize,
    indexed_type: usize,
    type_index: usize,
    wire: usize,
    op: usize,

    // Leaf operations
    leaf_op: usize,
    leaf_source: usize,
    carrier_source: usize,
    relation_source: usize,
    function_source: usize,
    equality_source: usize,
    constant_source: usize,

    // Scalar operations
    scalar_op: usize,
    scalar_value: usize,

    // Zero operation
    zero_op: usize,

    // Binary operations
    product_op: usize,
    sum_op: usize,
    hadamard_op: usize,

    // Contraction
    contract_op: usize,

    // Derived operations
    negate_op: usize,
    distinct_op: usize,

    // DBSP temporal operators
    delay_op: usize,
    diff_op: usize,
    integrate_op: usize,
}

impl TensorIRSortIds {
    fn from_theory(theory: &ElaboratedTheory) -> Result<Self, TensorIRError> {
        let sig = &theory.theory.signature;

        let get_sort = |name: &str| -> Result<usize, TensorIRError> {
            sig.sorts
                .iter()
                .position(|s| s == name)
                .ok_or_else(|| TensorIRError::MissingSortId(name.to_string()))
        };

        Ok(Self {
            theory: get_sort("GeologMeta/Theory")?,
            srt: get_sort("GeologMeta/Srt")?,
            elem: get_sort("GeologMeta/Elem")?,
            rel: get_sort("GeologMeta/Rel")?,
            func: get_sort("GeologMeta/Func")?,

            semiring: get_sort("Semiring")?,
            index_space: get_sort("IndexSpace")?,
            tensor_type: get_sort("TensorType")?,
            indexed_type: get_sort("IndexedType")?,
            type_index: get_sort("TypeIndex")?,
            wire: get_sort("Wire")?,
            op: get_sort("Op")?,

            leaf_op: get_sort("LeafOp")?,
            leaf_source: get_sort("LeafSource")?,
            carrier_source: get_sort("CarrierSource")?,
            relation_source: get_sort("RelationSource")?,
            function_source: get_sort("FunctionSource")?,
            equality_source: get_sort("EqualitySource")?,
            constant_source: get_sort("ConstantSource")?,

            scalar_op: get_sort("ScalarOp")?,
            scalar_value: get_sort("ScalarValue")?,

            zero_op: get_sort("ZeroOp")?,

            product_op: get_sort("ProductOp")?,
            sum_op: get_sort("SumOp")?,
            hadamard_op: get_sort("HadamardOp")?,

            contract_op: get_sort("ContractOp")?,

            negate_op: get_sort("NegateOp")?,
            distinct_op: get_sort("DistinctOp")?,

            delay_op: get_sort("DelayOp")?,
            diff_op: get_sort("DiffOp")?,
            integrate_op: get_sort("IntegrateOp")?,
        })
    }
}

/// Cached function IDs from TensorIR theory
#[allow(dead_code)]
struct TensorIRFuncIds {
    // LeafOp functions
    leaf_op_op: usize,
    leaf_op_out: usize,
    leaf_op_source: usize,

    // CarrierSource functions
    carrier_source_source: usize,
    carrier_source_srt: usize,

    // RelationSource functions
    relation_source_source: usize,
    relation_source_rel: usize,

    // FunctionSource functions
    function_source_source: usize,
    function_source_func: usize,

    // EqualitySource functions
    equality_source_source: usize,
    equality_source_srt: usize,

    // ConstantSource functions
    constant_source_source: usize,
    constant_source_elem: usize,

    // ZeroOp functions
    zero_op_op: usize,
    zero_op_out: usize,

    // ProductOp functions
    product_op_op: usize,
    product_op_left_in: usize,
    product_op_right_in: usize,
    product_op_out: usize,

    // SumOp functions
    sum_op_op: usize,
    sum_op_left_in: usize,
    sum_op_right_in: usize,
    sum_op_out: usize,

    // HadamardOp functions
    hadamard_op_op: usize,
    hadamard_op_left_in: usize,
    hadamard_op_right_in: usize,
    hadamard_op_out: usize,

    // ContractOp functions
    contract_op_op: usize,
    contract_op_in: usize,
    contract_op_out: usize,

    // NegateOp functions
    negate_op_op: usize,
    negate_op_in: usize,
    negate_op_out: usize,

    // DistinctOp functions
    distinct_op_op: usize,
    distinct_op_in: usize,
    distinct_op_out: usize,

    // DelayOp functions
    delay_op_op: usize,
    delay_op_in: usize,
    delay_op_out: usize,

    // DiffOp functions
    diff_op_op: usize,
    diff_op_in: usize,
    diff_op_out: usize,

    // IntegrateOp functions
    integrate_op_op: usize,
    integrate_op_in: usize,
    integrate_op_out: usize,

    // Wire type
    wire_type: usize,

    // IndexSpace/srt
    index_space_srt: usize,

    // IndexedType functions
    indexed_type_type: usize,

    // TypeIndex functions
    type_index_owner: usize,
    type_index_space: usize,
    type_index_position: usize,
}

impl TensorIRFuncIds {
    fn from_theory(theory: &ElaboratedTheory) -> Result<Self, TensorIRError> {
        let sig = &theory.theory.signature;

        let get_func = |name: &str| -> Result<usize, TensorIRError> {
            sig.lookup_func(name)
                .ok_or_else(|| TensorIRError::MissingFuncId(name.to_string()))
        };

        Ok(Self {
            leaf_op_op: get_func("LeafOp/op")?,
            leaf_op_out: get_func("LeafOp/out")?,
            leaf_op_source: get_func("LeafOp/source")?,

            carrier_source_source: get_func("CarrierSource/source")?,
            carrier_source_srt: get_func("CarrierSource/srt")?,

            relation_source_source: get_func("RelationSource/source")?,
            relation_source_rel: get_func("RelationSource/rel")?,

            function_source_source: get_func("FunctionSource/source")?,
            function_source_func: get_func("FunctionSource/func")?,

            equality_source_source: get_func("EqualitySource/source")?,
            equality_source_srt: get_func("EqualitySource/srt")?,

            constant_source_source: get_func("ConstantSource/source")?,
            constant_source_elem: get_func("ConstantSource/elem")?,

            zero_op_op: get_func("ZeroOp/op")?,
            zero_op_out: get_func("ZeroOp/out")?,

            product_op_op: get_func("ProductOp/op")?,
            product_op_left_in: get_func("ProductOp/left_in")?,
            product_op_right_in: get_func("ProductOp/right_in")?,
            product_op_out: get_func("ProductOp/out")?,

            sum_op_op: get_func("SumOp/op")?,
            sum_op_left_in: get_func("SumOp/left_in")?,
            sum_op_right_in: get_func("SumOp/right_in")?,
            sum_op_out: get_func("SumOp/out")?,

            hadamard_op_op: get_func("HadamardOp/op")?,
            hadamard_op_left_in: get_func("HadamardOp/left_in")?,
            hadamard_op_right_in: get_func("HadamardOp/right_in")?,
            hadamard_op_out: get_func("HadamardOp/out")?,

            contract_op_op: get_func("ContractOp/op")?,
            contract_op_in: get_func("ContractOp/in")?,
            contract_op_out: get_func("ContractOp/out")?,

            negate_op_op: get_func("NegateOp/op")?,
            negate_op_in: get_func("NegateOp/in")?,
            negate_op_out: get_func("NegateOp/out")?,

            distinct_op_op: get_func("DistinctOp/op")?,
            distinct_op_in: get_func("DistinctOp/in")?,
            distinct_op_out: get_func("DistinctOp/out")?,

            delay_op_op: get_func("DelayOp/op")?,
            delay_op_in: get_func("DelayOp/in")?,
            delay_op_out: get_func("DelayOp/out")?,

            diff_op_op: get_func("DiffOp/op")?,
            diff_op_in: get_func("DiffOp/in")?,
            diff_op_out: get_func("DiffOp/out")?,

            integrate_op_op: get_func("IntegrateOp/op")?,
            integrate_op_in: get_func("IntegrateOp/in")?,
            integrate_op_out: get_func("IntegrateOp/out")?,

            wire_type: get_func("Wire/type")?,

            index_space_srt: get_func("IndexSpace/srt")?,

            indexed_type_type: get_func("IndexedType/type")?,

            type_index_owner: get_func("TypeIndex/owner")?,
            type_index_space: get_func("TypeIndex/space")?,
            type_index_position: get_func("TypeIndex/position")?,
        })
    }
}

/// Parsed operation from a TensorIR instance
#[derive(Debug, Clone)]
#[allow(dead_code)] // Variants are for future extension
enum ParsedOp {
    /// Load carrier as 1-tensor
    LeafCarrier {
        sort_idx: usize,
        out_wire: Slid,
    },
    /// Load relation as n-tensor
    LeafRelation {
        rel_idx: usize,
        out_wire: Slid,
    },
    /// Load function graph as 2-tensor
    LeafFunction {
        func_idx: usize,
        out_wire: Slid,
    },
    /// Load equality diagonal
    LeafEquality {
        sort_idx: usize,
        out_wire: Slid,
    },
    /// Load constant indicator
    LeafConstant {
        elem: Slid, // original element from target
        sort_idx: usize,
        out_wire: Slid,
    },
    /// Zero tensor
    Zero {
        dims: Vec<usize>,
        out_wire: Slid,
    },
    /// Kronecker product
    Product {
        left_wire: Slid,
        right_wire: Slid,
        out_wire: Slid,
    },
    /// Pointwise sum
    Sum {
        left_wire: Slid,
        right_wire: Slid,
        out_wire: Slid,
    },
    /// Pointwise product
    Hadamard {
        left_wire: Slid,
        right_wire: Slid,
        out_wire: Slid,
    },
    /// Contract (einsum)
    Contract {
        in_wire: Slid,
        out_wire: Slid,
        /// Which output index each input index maps to
        index_map: Vec<usize>,
        /// Which indices appear in output
        output_indices: BTreeSet<usize>,
    },
    /// Negate
    Negate {
        in_wire: Slid,
        out_wire: Slid,
    },
    /// Distinct (collapse multiplicities)
    Distinct {
        in_wire: Slid,
        out_wire: Slid,
    },
    /// DBSP Delay
    Delay {
        in_wire: Slid,
        out_wire: Slid,
    },
    /// DBSP Diff
    Diff {
        in_wire: Slid,
        out_wire: Slid,
    },
    /// DBSP Integrate
    Integrate {
        in_wire: Slid,
        out_wire: Slid,
    },
}

impl ParsedOp {
    fn out_wire(&self) -> Slid {
        match self {
            Self::LeafCarrier { out_wire, .. }
            | Self::LeafRelation { out_wire, .. }
            | Self::LeafFunction { out_wire, .. }
            | Self::LeafEquality { out_wire, .. }
            | Self::LeafConstant { out_wire, .. }
            | Self::Zero { out_wire, .. }
            | Self::Product { out_wire, .. }
            | Self::Sum { out_wire, .. }
            | Self::Hadamard { out_wire, .. }
            | Self::Contract { out_wire, .. }
            | Self::Negate { out_wire, .. }
            | Self::Distinct { out_wire, .. }
            | Self::Delay { out_wire, .. }
            | Self::Diff { out_wire, .. }
            | Self::Integrate { out_wire, .. } => *out_wire,
        }
    }

    fn in_wires(&self) -> Vec<Slid> {
        match self {
            Self::LeafCarrier { .. }
            | Self::LeafRelation { .. }
            | Self::LeafFunction { .. }
            | Self::LeafEquality { .. }
            | Self::LeafConstant { .. }
            | Self::Zero { .. } => vec![],

            Self::Product {
                left_wire,
                right_wire,
                ..
            }
            | Self::Sum {
                left_wire,
                right_wire,
                ..
            }
            | Self::Hadamard {
                left_wire,
                right_wire,
                ..
            } => vec![*left_wire, *right_wire],

            Self::Contract { in_wire, .. }
            | Self::Negate { in_wire, .. }
            | Self::Distinct { in_wire, .. }
            | Self::Delay { in_wire, .. }
            | Self::Diff { in_wire, .. }
            | Self::Integrate { in_wire, .. } => vec![*in_wire],
        }
    }

    /// Returns true if this operation breaks instantaneous cycles (DBSP temporal operators)
    fn breaks_cycle(&self) -> bool {
        matches!(self, Self::Delay { .. } | Self::Integrate { .. })
    }
}

/// Context for interpreting TensorIR instances
struct InterpretContext<'a> {
    /// The TensorIR instance being interpreted
    instance: &'a TensorIRInstance,
    /// TensorIR theory sort IDs
    #[allow(dead_code)]
    ids: TensorIRSortIds,
    /// TensorIR theory function IDs
    funcs: TensorIRFuncIds,
    /// Target structure being queried
    target: &'a Structure,
}

impl<'a> InterpretContext<'a> {
    fn new(
        instance: &'a TensorIRInstance,
        theory: &ElaboratedTheory,
        target: &'a Structure,
    ) -> Result<Self, TensorIRError> {
        Ok(Self {
            instance,
            ids: TensorIRSortIds::from_theory(theory)?,
            funcs: TensorIRFuncIds::from_theory(theory)?,
            target,
        })
    }

    /// Get function value for an element
    fn get_func_value(&self, func_id: usize, elem: Slid) -> Option<Slid> {
        let structure = &self.instance.structure;
        let local_idx = structure.sort_local_id(elem).index();
        structure
            .functions
            .get(func_id)
            .and_then(|f| get_slid(f.get_local(local_idx)))
    }

    /// Get sort index from a GeologMeta/Srt element using the sort_mapping
    fn get_srt_sort_idx(&self, srt_elem: Slid) -> Result<usize, TensorIRError> {
        self.instance
            .sort_mapping
            .get(&srt_elem)
            .copied()
            .ok_or_else(|| {
                TensorIRError::InvalidOp(format!(
                    "Unknown Srt element {:?} - not in sort_mapping",
                    srt_elem
                ))
            })
    }

    /// Parse all operations from the instance
    fn parse_operations(&self) -> Result<Vec<ParsedOp>, TensorIRError> {
        let mut ops = Vec::new();
        let structure = &self.instance.structure;

        // Find all LeafOp elements
        for elem_idx in structure.carriers[self.ids.leaf_op].iter() {
            let elem = Slid::from_usize(elem_idx as usize);

            let source = self
                .get_func_value(self.funcs.leaf_op_source, elem)
                .ok_or_else(|| TensorIRError::InvalidOp("LeafOp missing source".into()))?;
            let out_wire = self
                .get_func_value(self.funcs.leaf_op_out, elem)
                .ok_or_else(|| TensorIRError::InvalidOp("LeafOp missing out".into()))?;

            // Determine source type
            if let Some(op) = self.parse_carrier_source(source, out_wire)? {
                ops.push(op);
            } else if let Some(op) = self.parse_relation_source(source, out_wire)? {
                ops.push(op);
            } else if let Some(op) = self.parse_function_source(source, out_wire)? {
                ops.push(op);
            } else if let Some(op) = self.parse_equality_source(source, out_wire)? {
                ops.push(op);
            } else if let Some(op) = self.parse_constant_source(source, out_wire)? {
                ops.push(op);
            } else {
                return Err(TensorIRError::InvalidOp(format!(
                    "LeafOp has unknown source type: {:?}",
                    source
                )));
            }
        }

        // Find all ZeroOp elements
        for elem_idx in structure.carriers[self.ids.zero_op].iter() {
            let elem = Slid::from_usize(elem_idx as usize);
            let out_wire = self
                .get_func_value(self.funcs.zero_op_out, elem)
                .ok_or_else(|| TensorIRError::InvalidOp("ZeroOp missing out".into()))?;

            // Get dimensions from wire type
            let dims = self.get_wire_dims(out_wire)?;
            ops.push(ParsedOp::Zero { dims, out_wire });
        }

        // Find all ProductOp elements
        for elem_idx in structure.carriers[self.ids.product_op].iter() {
            let elem = Slid::from_usize(elem_idx as usize);
            let left_wire = self
                .get_func_value(self.funcs.product_op_left_in, elem)
                .ok_or_else(|| TensorIRError::InvalidOp("ProductOp missing left_in".into()))?;
            let right_wire = self
                .get_func_value(self.funcs.product_op_right_in, elem)
                .ok_or_else(|| TensorIRError::InvalidOp("ProductOp missing right_in".into()))?;
            let out_wire = self
                .get_func_value(self.funcs.product_op_out, elem)
                .ok_or_else(|| TensorIRError::InvalidOp("ProductOp missing out".into()))?;

            ops.push(ParsedOp::Product {
                left_wire,
                right_wire,
                out_wire,
            });
        }

        // Find all SumOp elements
        for elem_idx in structure.carriers[self.ids.sum_op].iter() {
            let elem = Slid::from_usize(elem_idx as usize);
            let left_wire = self
                .get_func_value(self.funcs.sum_op_left_in, elem)
                .ok_or_else(|| TensorIRError::InvalidOp("SumOp missing left_in".into()))?;
            let right_wire = self
                .get_func_value(self.funcs.sum_op_right_in, elem)
                .ok_or_else(|| TensorIRError::InvalidOp("SumOp missing right_in".into()))?;
            let out_wire = self
                .get_func_value(self.funcs.sum_op_out, elem)
                .ok_or_else(|| TensorIRError::InvalidOp("SumOp missing out".into()))?;

            ops.push(ParsedOp::Sum {
                left_wire,
                right_wire,
                out_wire,
            });
        }

        // Find all HadamardOp elements
        for elem_idx in structure.carriers[self.ids.hadamard_op].iter() {
            let elem = Slid::from_usize(elem_idx as usize);
            let left_wire = self
                .get_func_value(self.funcs.hadamard_op_left_in, elem)
                .ok_or_else(|| TensorIRError::InvalidOp("HadamardOp missing left_in".into()))?;
            let right_wire = self
                .get_func_value(self.funcs.hadamard_op_right_in, elem)
                .ok_or_else(|| TensorIRError::InvalidOp("HadamardOp missing right_in".into()))?;
            let out_wire = self
                .get_func_value(self.funcs.hadamard_op_out, elem)
                .ok_or_else(|| TensorIRError::InvalidOp("HadamardOp missing out".into()))?;

            ops.push(ParsedOp::Hadamard {
                left_wire,
                right_wire,
                out_wire,
            });
        }

        // Find all ContractOp elements
        for elem_idx in structure.carriers[self.ids.contract_op].iter() {
            let elem = Slid::from_usize(elem_idx as usize);
            let in_wire = self
                .get_func_value(self.funcs.contract_op_in, elem)
                .ok_or_else(|| TensorIRError::InvalidOp("ContractOp missing in".into()))?;
            let out_wire = self
                .get_func_value(self.funcs.contract_op_out, elem)
                .ok_or_else(|| TensorIRError::InvalidOp("ContractOp missing out".into()))?;

            // Parse index mapping from the ContractOp structure
            // For now, use a simple projection (identity map, keep all)
            // TODO: Parse actual ContractMapping from instance
            let in_dims = self.get_wire_dims(in_wire)?;
            let out_dims = self.get_wire_dims(out_wire)?;

            // Build index_map and output_indices
            let (index_map, output_indices) =
                self.infer_contraction(in_dims.len(), out_dims.len())?;

            ops.push(ParsedOp::Contract {
                in_wire,
                out_wire,
                index_map,
                output_indices,
            });
        }

        // Find all NegateOp elements
        for elem_idx in structure.carriers[self.ids.negate_op].iter() {
            let elem = Slid::from_usize(elem_idx as usize);
            let in_wire = self
                .get_func_value(self.funcs.negate_op_in, elem)
                .ok_or_else(|| TensorIRError::InvalidOp("NegateOp missing in".into()))?;
            let out_wire = self
                .get_func_value(self.funcs.negate_op_out, elem)
                .ok_or_else(|| TensorIRError::InvalidOp("NegateOp missing out".into()))?;

            ops.push(ParsedOp::Negate { in_wire, out_wire });
        }

        // Find all DistinctOp elements
        for elem_idx in structure.carriers[self.ids.distinct_op].iter() {
            let elem = Slid::from_usize(elem_idx as usize);
            let in_wire = self
                .get_func_value(self.funcs.distinct_op_in, elem)
                .ok_or_else(|| TensorIRError::InvalidOp("DistinctOp missing in".into()))?;
            let out_wire = self
                .get_func_value(self.funcs.distinct_op_out, elem)
                .ok_or_else(|| TensorIRError::InvalidOp("DistinctOp missing out".into()))?;

            ops.push(ParsedOp::Distinct { in_wire, out_wire });
        }

        // Find all DelayOp elements
        for elem_idx in structure.carriers[self.ids.delay_op].iter() {
            let elem = Slid::from_usize(elem_idx as usize);
            let in_wire = self
                .get_func_value(self.funcs.delay_op_in, elem)
                .ok_or_else(|| TensorIRError::InvalidOp("DelayOp missing in".into()))?;
            let out_wire = self
                .get_func_value(self.funcs.delay_op_out, elem)
                .ok_or_else(|| TensorIRError::InvalidOp("DelayOp missing out".into()))?;

            ops.push(ParsedOp::Delay { in_wire, out_wire });
        }

        // Find all DiffOp elements
        for elem_idx in structure.carriers[self.ids.diff_op].iter() {
            let elem = Slid::from_usize(elem_idx as usize);
            let in_wire = self
                .get_func_value(self.funcs.diff_op_in, elem)
                .ok_or_else(|| TensorIRError::InvalidOp("DiffOp missing in".into()))?;
            let out_wire = self
                .get_func_value(self.funcs.diff_op_out, elem)
                .ok_or_else(|| TensorIRError::InvalidOp("DiffOp missing out".into()))?;

            ops.push(ParsedOp::Diff { in_wire, out_wire });
        }

        // Find all IntegrateOp elements
        for elem_idx in structure.carriers[self.ids.integrate_op].iter() {
            let elem = Slid::from_usize(elem_idx as usize);
            let in_wire = self
                .get_func_value(self.funcs.integrate_op_in, elem)
                .ok_or_else(|| TensorIRError::InvalidOp("IntegrateOp missing in".into()))?;
            let out_wire = self
                .get_func_value(self.funcs.integrate_op_out, elem)
                .ok_or_else(|| TensorIRError::InvalidOp("IntegrateOp missing out".into()))?;

            ops.push(ParsedOp::Integrate { in_wire, out_wire });
        }

        Ok(ops)
    }

    /// Parse a CarrierSource from a LeafSource element
    fn parse_carrier_source(
        &self,
        source: Slid,
        out_wire: Slid,
    ) -> Result<Option<ParsedOp>, TensorIRError> {
        let structure = &self.instance.structure;

        for elem_idx in structure.carriers[self.ids.carrier_source].iter() {
            let elem = Slid::from_usize(elem_idx as usize);
            if let Some(s) = self.get_func_value(self.funcs.carrier_source_source, elem) {
                if s == source {
                    let srt = self
                        .get_func_value(self.funcs.carrier_source_srt, elem)
                        .ok_or_else(|| {
                            TensorIRError::InvalidOp("CarrierSource missing srt".into())
                        })?;
                    let sort_idx = self.get_srt_sort_idx(srt)?;
                    return Ok(Some(ParsedOp::LeafCarrier { sort_idx, out_wire }));
                }
            }
        }
        Ok(None)
    }

    /// Parse a RelationSource from a LeafSource element
    fn parse_relation_source(
        &self,
        source: Slid,
        _out_wire: Slid,
    ) -> Result<Option<ParsedOp>, TensorIRError> {
        let structure = &self.instance.structure;

        for elem_idx in structure.carriers[self.ids.relation_source].iter() {
            let elem = Slid::from_usize(elem_idx as usize);
            if let Some(s) = self.get_func_value(self.funcs.relation_source_source, elem) {
                if s == source {
                    // TODO: Look up relation index from GeologMeta/Rel element
                    return Err(TensorIRError::Unsupported(
                        "RelationSource not yet implemented".into(),
                    ));
                }
            }
        }
        Ok(None)
    }

    /// Parse a FunctionSource from a LeafSource element
    fn parse_function_source(
        &self,
        source: Slid,
        _out_wire: Slid,
    ) -> Result<Option<ParsedOp>, TensorIRError> {
        let structure = &self.instance.structure;

        for elem_idx in structure.carriers[self.ids.function_source].iter() {
            let elem = Slid::from_usize(elem_idx as usize);
            if let Some(s) = self.get_func_value(self.funcs.function_source_source, elem) {
                if s == source {
                    return Err(TensorIRError::Unsupported(
                        "FunctionSource not yet implemented".into(),
                    ));
                }
            }
        }
        Ok(None)
    }

    /// Parse an EqualitySource from a LeafSource element
    fn parse_equality_source(
        &self,
        source: Slid,
        out_wire: Slid,
    ) -> Result<Option<ParsedOp>, TensorIRError> {
        let structure = &self.instance.structure;

        for elem_idx in structure.carriers[self.ids.equality_source].iter() {
            let elem = Slid::from_usize(elem_idx as usize);
            if let Some(s) = self.get_func_value(self.funcs.equality_source_source, elem) {
                if s == source {
                    let srt = self
                        .get_func_value(self.funcs.equality_source_srt, elem)
                        .ok_or_else(|| {
                            TensorIRError::InvalidOp("EqualitySource missing srt".into())
                        })?;
                    let sort_idx = self.get_srt_sort_idx(srt)?;
                    return Ok(Some(ParsedOp::LeafEquality { sort_idx, out_wire }));
                }
            }
        }
        Ok(None)
    }

    /// Parse a ConstantSource from a LeafSource element
    fn parse_constant_source(
        &self,
        source: Slid,
        out_wire: Slid,
    ) -> Result<Option<ParsedOp>, TensorIRError> {
        let structure = &self.instance.structure;

        for elem_idx in structure.carriers[self.ids.constant_source].iter() {
            let elem_slid = Slid::from_usize(elem_idx as usize);
            if let Some(s) = self.get_func_value(self.funcs.constant_source_source, elem_slid) {
                if s == source {
                    let elem_ref = self
                        .get_func_value(self.funcs.constant_source_elem, elem_slid)
                        .ok_or_else(|| {
                            TensorIRError::InvalidOp("ConstantSource missing elem".into())
                        })?;

                    // Look up the original target element from elem_value_mapping
                    let elem = self.instance.elem_value_mapping.get(&elem_ref).copied().ok_or_else(|| {
                        TensorIRError::InvalidOp(format!(
                            "ConstantSource elem {:?} not in elem_value_mapping",
                            elem_ref
                        ))
                    })?;

                    // Determine sort from element
                    // TODO: Proper sort lookup - for now assume sort 0
                    let sort_idx = 0;

                    return Ok(Some(ParsedOp::LeafConstant {
                        elem,
                        sort_idx,
                        out_wire,
                    }));
                }
            }
        }
        Ok(None)
    }

    /// Get the dimensions of a wire's tensor type
    fn get_wire_dims(&self, wire: Slid) -> Result<Vec<usize>, TensorIRError> {
        // Look up Wire/type
        let tensor_type = self.get_func_value(self.funcs.wire_type, wire).ok_or_else(|| {
            TensorIRError::InvalidOp(format!("Wire {:?} has no type", wire))
        })?;

        // Find all TypeIndex elements for this tensor type
        let structure = &self.instance.structure;
        let mut type_indices: Vec<(usize, usize)> = Vec::new(); // (position, sort_idx)

        for elem_idx in structure.carriers[self.ids.type_index].iter() {
            let elem = Slid::from_usize(elem_idx as usize);

            // Get IndexedType owner
            if let Some(owner) = self.get_func_value(self.funcs.type_index_owner, elem) {
                // Get IndexedType/type to find TensorType
                if let Some(owner_type) = self.get_func_value(self.funcs.indexed_type_type, owner) {
                    if owner_type == tensor_type {
                        // Get position and IndexSpace
                        let position = self
                            .get_func_value(self.funcs.type_index_position, elem)
                            .map(|p| p.index())
                            .unwrap_or(type_indices.len());

                        let space = self
                            .get_func_value(self.funcs.type_index_space, elem)
                            .ok_or_else(|| {
                                TensorIRError::InvalidOp("TypeIndex missing space".into())
                            })?;

                        // Get sort from IndexSpace
                        let srt = self
                            .get_func_value(self.funcs.index_space_srt, space)
                            .ok_or_else(|| {
                                TensorIRError::InvalidOp("IndexSpace missing srt".into())
                            })?;

                        let sort_idx = self.get_srt_sort_idx(srt)?;

                        // Get carrier size from target
                        let dim = self
                            .target
                            .carriers
                            .get(sort_idx)
                            .map(|c| c.len() as usize)
                            .unwrap_or(0);

                        type_indices.push((position, dim));
                    }
                }
            }
        }

        // Sort by position and extract dimensions
        type_indices.sort_by_key(|(pos, _)| *pos);
        let dims: Vec<usize> = type_indices.into_iter().map(|(_, dim)| dim).collect();

        // Default to 1D if no type information found
        if dims.is_empty() {
            // Scalar or unknown - return empty dims for scalar
            Ok(vec![])
        } else {
            Ok(dims)
        }
    }

    /// Infer contraction mapping from input/output dimensions
    fn infer_contraction(
        &self,
        in_ndims: usize,
        out_ndims: usize,
    ) -> Result<(Vec<usize>, BTreeSet<usize>), TensorIRError> {
        // Simple heuristic: project to first out_ndims indices
        let index_map: Vec<usize> = (0..in_ndims)
            .map(|i| if i < out_ndims { i } else { out_ndims })
            .collect();
        let output_indices: BTreeSet<usize> = (0..out_ndims).collect();
        Ok((index_map, output_indices))
    }

    /// Topologically sort operations (respecting dependencies)
    fn topological_sort(&self, ops: &[ParsedOp]) -> Result<Vec<usize>, TensorIRError> {
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
            return Err(TensorIRError::InstantaneousCycle);
        }

        Ok(sorted)
    }
}

// ============================================================================
// Executor: Execute TensorIR using TensorSym
// ============================================================================

/// Execute a TensorIR instance using the Eager interpreter
///
/// This produces tensors over the Bool semiring (set semantics).
pub fn execute_tensor_ir(
    instance: &TensorIRInstance,
    tensor_ir_theory: &ElaboratedTheory,
    target: &Structure,
) -> Result<BTreeSet<Vec<usize>>, TensorIRError> {
    let ctx = InterpretContext::new(instance, tensor_ir_theory, target)?;

    // Parse all operations
    let ops = ctx.parse_operations()?;

    if ops.is_empty() {
        return Ok(BTreeSet::new());
    }

    // Topologically sort operations
    let sorted = ctx.topological_sort(&ops)?;

    // Execute using Eager<BTreeSetPattern>
    let mut wire_values: HashMap<Slid, <Eager<BTreeSetPattern> as TensorSym>::Tensor<bool>> =
        HashMap::new();

    for &idx in &sorted {
        let result = execute_op::<Eager<BTreeSetPattern>>(&ops[idx], &wire_values, target)?;
        let out_wire = ops[idx].out_wire();
        wire_values.insert(out_wire, result);
    }

    // Get output wire value
    let output = wire_values
        .remove(&instance.output_wire)
        .ok_or(TensorIRError::NoOutputWire)?;

    // Convert tensor to set of tuples
    Ok(output.pattern.tuples().clone())
}

/// Execute a single operation using TensorSym
fn execute_op<T: TensorSym>(
    op: &ParsedOp,
    wire_values: &HashMap<Slid, T::Tensor<bool>>,
    target: &Structure,
) -> Result<T::Tensor<bool>, TensorIRError> {
    match op {
        ParsedOp::LeafCarrier { sort_idx, .. } => {
            // Create 1-tensor with true for each element in the carrier
            let carrier = target.carriers.get(*sort_idx);
            let dim = carrier.map(|c| c.len() as usize).unwrap_or(0);

            let entries: Vec<(Vec<usize>, bool)> = carrier
                .map(|c| {
                    c.iter()
                        .map(|elem| (vec![elem as usize], true))
                        .collect()
                })
                .unwrap_or_default();

            Ok(T::from_entries(vec![dim], entries))
        }

        ParsedOp::LeafRelation { .. } => Err(TensorIRError::Unsupported(
            "LeafRelation not yet implemented".into(),
        )),

        ParsedOp::LeafFunction { .. } => Err(TensorIRError::Unsupported(
            "LeafFunction not yet implemented".into(),
        )),

        ParsedOp::LeafEquality { sort_idx, .. } => {
            // Create diagonal 2-tensor
            let carrier = target.carriers.get(*sort_idx);
            let dim = carrier.map(|c| c.len() as usize).unwrap_or(0);

            let entries: Vec<(Vec<usize>, bool)> = carrier
                .map(|c| {
                    c.iter()
                        .map(|elem| (vec![elem as usize, elem as usize], true))
                        .collect()
                })
                .unwrap_or_default();

            Ok(T::from_entries(vec![dim, dim], entries))
        }

        ParsedOp::LeafConstant {
            elem, sort_idx, ..
        } => {
            // Create 1-tensor with true only at elem's index
            let carrier = target.carriers.get(*sort_idx);
            let dim = carrier.map(|c| c.len() as usize).unwrap_or(0);

            let elem_idx = elem.index();
            let entries = vec![(vec![elem_idx], true)];

            Ok(T::from_entries(vec![dim], entries))
        }

        ParsedOp::Zero { dims, .. } => Ok(T::zero(dims.clone())),

        ParsedOp::Product {
            left_wire,
            right_wire,
            ..
        } => {
            let left = wire_values
                .get(left_wire)
                .ok_or_else(|| TensorIRError::InvalidOp("Product left wire not found".into()))?
                .clone();
            let right = wire_values
                .get(right_wire)
                .ok_or_else(|| TensorIRError::InvalidOp("Product right wire not found".into()))?
                .clone();

            Ok(T::product(left, right))
        }

        ParsedOp::Sum {
            left_wire,
            right_wire,
            ..
        } => {
            let left = wire_values
                .get(left_wire)
                .ok_or_else(|| TensorIRError::InvalidOp("Sum left wire not found".into()))?
                .clone();
            let right = wire_values
                .get(right_wire)
                .ok_or_else(|| TensorIRError::InvalidOp("Sum right wire not found".into()))?
                .clone();

            Ok(T::sum(left, right))
        }

        ParsedOp::Hadamard {
            left_wire,
            right_wire,
            ..
        } => {
            let left = wire_values
                .get(left_wire)
                .ok_or_else(|| TensorIRError::InvalidOp("Hadamard left wire not found".into()))?
                .clone();
            let right = wire_values
                .get(right_wire)
                .ok_or_else(|| TensorIRError::InvalidOp("Hadamard right wire not found".into()))?
                .clone();

            Ok(T::hadamard(left, right))
        }

        ParsedOp::Contract {
            in_wire,
            index_map,
            output_indices,
            ..
        } => {
            let input = wire_values
                .get(in_wire)
                .ok_or_else(|| TensorIRError::InvalidOp("Contract input wire not found".into()))?
                .clone();

            Ok(T::contract(input, index_map, output_indices))
        }

        ParsedOp::Negate { in_wire, .. } => {
            // For Bool semiring, negate has no effect (true -> true)
            // This would matter for Z-sets
            let input = wire_values
                .get(in_wire)
                .ok_or_else(|| TensorIRError::InvalidOp("Negate input wire not found".into()))?
                .clone();

            Ok(input)
        }

        ParsedOp::Distinct { in_wire, .. } => {
            // For Bool semiring, distinct is identity
            let input = wire_values
                .get(in_wire)
                .ok_or_else(|| TensorIRError::InvalidOp("Distinct input wire not found".into()))?
                .clone();

            Ok(input)
        }

        ParsedOp::Delay { in_wire, .. }
        | ParsedOp::Diff { in_wire, .. }
        | ParsedOp::Integrate { in_wire, .. } => {
            // For non-streaming execution, DBSP operators are identity
            let input = wire_values
                .get(in_wire)
                .ok_or_else(|| TensorIRError::InvalidOp("DBSP input wire not found".into()))?
                .clone();

            Ok(input)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::query::backend::QueryOp;
    use crate::query::to_tensor_ir::compile_to_tensor_ir;
    use crate::repl::ReplState;
    use crate::universe::Universe;
    use std::fs;
    use std::rc::Rc;

    fn load_tensor_ir_theory() -> Rc<ElaboratedTheory> {
        let meta_content = fs::read_to_string("theories/GeologMeta.geolog")
            .expect("GeologMeta.geolog should exist");
        let ir_content =
            fs::read_to_string("theories/TensorIR.geolog").expect("TensorIR.geolog should exist");

        let mut state = ReplState::new();
        state
            .execute_geolog(&meta_content)
            .expect("GeologMeta should parse");
        state
            .execute_geolog(&ir_content)
            .expect("TensorIR should parse");

        state
            .theories
            .get("TensorIR")
            .expect("TensorIR theory should be loaded")
            .clone()
    }

    fn create_test_structure() -> (Structure, Universe) {
        let mut universe = Universe::new();
        let mut s = Structure::new(2); // 2 sorts: Person, City

        // Add some Person elements
        s.add_element(&mut universe, 0); // Person 0
        s.add_element(&mut universe, 0); // Person 1
        s.add_element(&mut universe, 0); // Person 2

        // Add some City elements
        s.add_element(&mut universe, 1); // City 0
        s.add_element(&mut universe, 1); // City 1

        (s, universe)
    }

    #[test]
    fn test_execute_scan_carrier() {
        let tensor_ir = load_tensor_ir_theory();
        let (target, mut universe) = create_test_structure();

        // Create a Scan plan for sort 0 (Person)
        let plan = QueryOp::Scan { sort_idx: 0 };

        // Compile to TensorIR
        let instance = compile_to_tensor_ir(&plan, &tensor_ir, &mut universe)
            .expect("compile should succeed");

        // Execute
        let result =
            execute_tensor_ir(&instance, &tensor_ir, &target).expect("execute should succeed");

        // Should have 3 tuples (one per Person)
        assert_eq!(result.len(), 3);
        assert!(result.contains(&vec![0]));
        assert!(result.contains(&vec![1]));
        assert!(result.contains(&vec![2]));
    }

    #[test]
    fn test_execute_empty() {
        let tensor_ir = load_tensor_ir_theory();
        let (target, mut universe) = create_test_structure();

        // Create an Empty plan
        let plan = QueryOp::Empty;

        // Compile to TensorIR
        let instance = compile_to_tensor_ir(&plan, &tensor_ir, &mut universe)
            .expect("compile should succeed");

        // Execute
        let result =
            execute_tensor_ir(&instance, &tensor_ir, &target).expect("execute should succeed");

        // Should be empty
        assert!(result.is_empty());
    }

    #[test]
    fn test_execute_union() {
        let tensor_ir = load_tensor_ir_theory();
        let (target, mut universe) = create_test_structure();

        // Create a Union plan: Scan(Person) ∪ Scan(Person)
        let scan = QueryOp::Scan { sort_idx: 0 };
        let plan = QueryOp::Union {
            left: Box::new(scan.clone()),
            right: Box::new(scan),
        };

        // Compile to TensorIR
        let instance = compile_to_tensor_ir(&plan, &tensor_ir, &mut universe)
            .expect("compile should succeed");

        // Execute
        let result =
            execute_tensor_ir(&instance, &tensor_ir, &target).expect("execute should succeed");

        // Should have same 3 tuples (union is idempotent for sets)
        assert_eq!(result.len(), 3);
    }

    #[test]
    fn test_parsed_op_in_wires() {
        let leaf = ParsedOp::LeafCarrier {
            sort_idx: 0,
            out_wire: Slid::from_usize(0),
        };
        assert!(leaf.in_wires().is_empty());

        let product = ParsedOp::Product {
            left_wire: Slid::from_usize(0),
            right_wire: Slid::from_usize(1),
            out_wire: Slid::from_usize(2),
        };
        assert_eq!(product.in_wires().len(), 2);

        let contract = ParsedOp::Contract {
            in_wire: Slid::from_usize(0),
            out_wire: Slid::from_usize(1),
            index_map: vec![0, 1],
            output_indices: [0].into_iter().collect(),
        };
        assert_eq!(contract.in_wires().len(), 1);
    }
}
