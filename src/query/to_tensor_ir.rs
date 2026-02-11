//! Compiler from QueryOp plans to TensorIR instances.
//!
//! This module creates geolog Structure instances (of the TensorIR theory)
//! from QueryOp query plans. TensorIR subsumes RelAlgIR: relational algebra
//! operations are special cases of tensor operations over the Boolean semiring.
//!
//! # Mapping from QueryOp to TensorIR
//!
//! | QueryOp          | TensorIR Sorts                  | Notes                        |
//! |------------------|----------------------------------|------------------------------|
//! | `Scan`           | `LeafOp + CarrierSource`        | Load carrier as 1-tensor     |
//! | `Filter`         | `HadamardOp` or `ContractOp`    | Mask or constrain indices    |
//! | `Distinct`       | `DistinctOp`                    | Collapse multiplicities      |
//! | `Join (Cross)`   | `ProductOp`                     | Kronecker product            |
//! | `Join (Equi)`    | `ProductOp + ContractOp`        | Product then identify cols   |
//! | `Union`          | `SumOp`                         | Pointwise addition           |
//! | `Project`        | `ContractOp`                    | Sum over dropped indices     |
//! | `Negate`         | `NegateOp`                      | Flip signs                   |
//! | `Empty`          | `ZeroOp`                        | All-zero tensor              |
//! | `Delay`          | `DelayOp`                       | DBSP: previous timestep      |
//! | `Diff`           | `DiffOp`                        | DBSP: change since last      |
//! | `Integrate`      | `IntegrateOp`                   | DBSP: accumulate             |

use std::collections::HashMap;

use crate::core::{ElaboratedTheory, SortId, Structure};
use crate::id::Slid;
use crate::query::backend::{JoinCond, Predicate, QueryOp};
use crate::universe::Universe;

/// Result of compiling a QueryOp to a TensorIR instance.
pub struct TensorIRInstance {
    /// The TensorIR structure
    pub structure: Structure,
    /// The output wire of the compiled plan
    pub output_wire: Slid,
    /// Mapping from Slid to element names (for debugging)
    pub names: HashMap<Slid, String>,
    /// Mapping from Srt elements to source sort indices (for interpreter)
    pub sort_mapping: HashMap<Slid, usize>,
    /// Mapping from Elem elements to original target Slid values (for interpreter)
    pub elem_value_mapping: HashMap<Slid, Slid>,
}

/// Context for the compilation process.
struct CompileContext<'a> {
    /// The TensorIR theory
    tensor_ir_theory: &'a ElaboratedTheory,
    /// Universe for generating Luids
    universe: &'a mut Universe,
    /// The structure being built
    structure: Structure,
    /// Element names for debugging
    names: HashMap<Slid, String>,
    /// Counter for generating unique names
    counter: usize,

    // Sort IDs in TensorIR (cached for efficiency)
    sort_ids: TensorIRSortIds,

    // GeologMeta sort elements already created
    // Maps source signature SortId -> TensorIR Slid for GeologMeta/Srt element
    srt_elements: HashMap<usize, Slid>,

    // GeologMeta/Elem elements for target instance elements
    elem_elements: HashMap<Slid, Slid>,

    // The "self-referencing" Theory element (for standalone queries)
    theory_elem: Option<Slid>,

    // Mapping from wire Slid to its TensorType Slid (for lookups)
    wire_types: HashMap<Slid, Slid>,
}

/// Cached sort IDs from the TensorIR theory.
#[allow(dead_code)]
struct TensorIRSortIds {
    // GeologMeta inherited sorts
    theory: SortId,
    srt: SortId,

    // TensorIR core sorts
    semiring: SortId,
    index_space: SortId,
    tensor_type: SortId,
    indexed_type: SortId,
    type_index: SortId,
    wire: SortId,
    op: SortId,

    // Leaf operations
    leaf_op: SortId,
    leaf_source: SortId,
    carrier_source: SortId,
    constant_source: SortId,

    // Zero operation
    zero_op: SortId,

    // Binary operations
    product_op: SortId,
    sum_op: SortId,
    hadamard_op: SortId,

    // Contraction
    contract_op: SortId,

    // Derived operations
    negate_op: SortId,
    distinct_op: SortId,

    // DBSP temporal operators
    delay_op: SortId,
    diff_op: SortId,
    integrate_op: SortId,

    // Primitives
    nat: SortId,
}

impl TensorIRSortIds {
    fn from_theory(theory: &ElaboratedTheory) -> Result<Self, String> {
        let sig = &theory.theory.signature;
        let lookup = |name: &str| -> Result<SortId, String> {
            sig.lookup_sort(name)
                .ok_or_else(|| format!("TensorIR theory missing sort: {}", name))
        };

        Ok(Self {
            theory: lookup("GeologMeta/Theory")?,
            srt: lookup("GeologMeta/Srt")?,

            semiring: lookup("Semiring")?,
            index_space: lookup("IndexSpace")?,
            tensor_type: lookup("TensorType")?,
            indexed_type: lookup("IndexedType")?,
            type_index: lookup("TypeIndex")?,
            wire: lookup("Wire")?,
            op: lookup("Op")?,

            leaf_op: lookup("LeafOp")?,
            leaf_source: lookup("LeafSource")?,
            carrier_source: lookup("CarrierSource")?,
            constant_source: lookup("ConstantSource")?,

            zero_op: lookup("ZeroOp")?,

            product_op: lookup("ProductOp")?,
            sum_op: lookup("SumOp")?,
            hadamard_op: lookup("HadamardOp")?,

            contract_op: lookup("ContractOp")?,

            negate_op: lookup("NegateOp")?,
            distinct_op: lookup("DistinctOp")?,

            delay_op: lookup("DelayOp")?,
            diff_op: lookup("DiffOp")?,
            integrate_op: lookup("IntegrateOp")?,

            nat: lookup("Nat")?,
        })
    }
}

impl<'a> CompileContext<'a> {
    fn new(
        tensor_ir_theory: &'a ElaboratedTheory,
        universe: &'a mut Universe,
    ) -> Result<Self, String> {
        let sort_ids = TensorIRSortIds::from_theory(tensor_ir_theory)?;
        let num_sorts = tensor_ir_theory.theory.signature.sorts.len();
        let num_funcs = tensor_ir_theory.theory.signature.functions.len();

        let mut structure = Structure::new(num_sorts);

        // Initialize function storage with empty columns
        structure.functions = (0..num_funcs)
            .map(|_| crate::core::FunctionColumn::Local(Vec::new()))
            .collect();

        // Initialize relation storage
        let rel_arities: Vec<usize> = tensor_ir_theory
            .theory
            .signature
            .relations
            .iter()
            .map(|r| r.domain.arity())
            .collect();
        structure.init_relations(&rel_arities);

        Ok(Self {
            tensor_ir_theory,
            universe,
            structure,
            names: HashMap::new(),
            counter: 0,
            sort_ids,
            srt_elements: HashMap::new(),
            elem_elements: HashMap::new(),
            theory_elem: None,
            wire_types: HashMap::new(),
        })
    }

    fn fresh_name(&mut self, prefix: &str) -> String {
        self.counter += 1;
        format!("{}_{}", prefix, self.counter)
    }

    /// Add an element to the structure with a name
    fn add_element(&mut self, sort: SortId, name: &str) -> Slid {
        let (slid, _luid) = self.structure.add_element(self.universe, sort);
        self.names.insert(slid, name.to_string());
        slid
    }

    /// Define a function value
    fn define_func(&mut self, func_name: &str, domain: Slid, codomain: Slid) -> Result<(), String> {
        let func_id = self
            .tensor_ir_theory
            .theory
            .signature
            .lookup_func(func_name)
            .ok_or_else(|| format!("TensorIR missing function: {}", func_name))?;

        self.structure
            .define_function(func_id, domain, codomain)
            .map_err(|existing| {
                format!(
                    "Conflicting definition for {} on {:?}: already defined as {:?}",
                    func_name, domain, existing
                )
            })
    }

    /// Get or create the Theory element (self-referencing for standalone queries)
    fn get_theory_elem(&mut self) -> Slid {
        if let Some(elem) = self.theory_elem {
            return elem;
        }

        let elem = self.add_element(self.sort_ids.theory, "query_theory");

        // Self-reference: Theory/parent = self
        let _ = self.define_func("GeologMeta/Theory/parent", elem, elem);

        self.theory_elem = Some(elem);
        elem
    }

    /// Get or create a GeologMeta/Srt element for a source sort
    fn get_srt_elem(&mut self, source_sort: usize) -> Result<Slid, String> {
        if let Some(&elem) = self.srt_elements.get(&source_sort) {
            return Ok(elem);
        }

        let theory = self.get_theory_elem();
        let name = self.fresh_name("srt");
        let elem = self.add_element(self.sort_ids.srt, &name);

        // Srt/theory = our theory element
        self.define_func("GeologMeta/Srt/theory", elem, theory)?;

        self.srt_elements.insert(source_sort, elem);
        Ok(elem)
    }

    /// Create an IndexSpace for a sort
    fn create_index_space(&mut self, srt_elem: Slid) -> Result<Slid, String> {
        let name = self.fresh_name("idx_space");
        let idx_space = self.add_element(self.sort_ids.index_space, &name);
        self.define_func("IndexSpace/srt", idx_space, srt_elem)?;
        Ok(idx_space)
    }

    /// Create a TensorType with a single index (for carriers)
    fn create_1tensor_type(&mut self, srt_elem: Slid) -> Result<Slid, String> {
        // Create IndexedType
        let indexed_name = self.fresh_name("indexed_type");
        let indexed_type = self.add_element(self.sort_ids.indexed_type, &indexed_name);

        // Create TensorType
        let tensor_name = self.fresh_name("tensor_type");
        let tensor_type = self.add_element(self.sort_ids.tensor_type, &tensor_name);

        // Link IndexedType -> TensorType
        self.define_func("IndexedType/type", indexed_type, tensor_type)?;

        // Create IndexSpace for the sort
        let idx_space = self.create_index_space(srt_elem)?;

        // Create TypeIndex linking to IndexSpace
        let ti_name = self.fresh_name("type_index");
        let type_index = self.add_element(self.sort_ids.type_index, &ti_name);

        self.define_func("TypeIndex/owner", type_index, indexed_type)?;
        self.define_func("TypeIndex/space", type_index, idx_space)?;

        // Create Nat for position (0)
        let zero = self.create_nat(0)?;
        self.define_func("TypeIndex/position", type_index, zero)?;

        // Set semiring (bool_semiring is a constant function, not an element)
        // For now, create a Semiring element as placeholder
        let semiring_name = self.fresh_name("semiring");
        let semiring = self.add_element(self.sort_ids.semiring, &semiring_name);
        self.define_func("TensorType/semiring", tensor_type, semiring)?;

        Ok(tensor_type)
    }

    /// Create a Nat element for a given value
    fn create_nat(&mut self, _value: usize) -> Result<Slid, String> {
        // For now, just create a Nat element
        // A proper implementation would use Peano encoding with zero and succ
        let name = self.fresh_name("nat");
        Ok(self.add_element(self.sort_ids.nat, &name))
    }

    /// Create a Wire with a given TensorType
    fn create_wire(&mut self, tensor_type: Slid) -> Result<Slid, String> {
        let name = self.fresh_name("wire");
        let wire = self.add_element(self.sort_ids.wire, &name);
        self.define_func("Wire/type", wire, tensor_type)?;
        self.wire_types.insert(wire, tensor_type);
        Ok(wire)
    }

    /// Get the TensorType of a wire
    fn get_wire_type(&self, wire: Slid) -> Result<Slid, String> {
        self.wire_types
            .get(&wire)
            .copied()
            .ok_or_else(|| format!("Wire {:?} has no type", wire))
    }
}

/// Compile a QueryOp to a TensorIR instance.
pub fn compile_to_tensor_ir(
    plan: &QueryOp,
    tensor_ir_theory: &ElaboratedTheory,
    universe: &mut Universe,
) -> Result<TensorIRInstance, String> {
    let mut ctx = CompileContext::new(tensor_ir_theory, universe)?;

    let output_wire = compile_op(&mut ctx, plan)?;

    // Invert the srt_elements map: it maps source_sort_idx -> Slid
    // but we need Slid -> source_sort_idx for the interpreter
    let sort_mapping: HashMap<Slid, usize> = ctx
        .srt_elements
        .iter()
        .map(|(&sort_idx, &slid)| (slid, sort_idx))
        .collect();

    Ok(TensorIRInstance {
        structure: ctx.structure,
        output_wire,
        names: ctx.names,
        sort_mapping,
        elem_value_mapping: ctx.elem_elements,
    })
}

/// Compile a single QueryOp node, returning the output wire.
fn compile_op(ctx: &mut CompileContext, op: &QueryOp) -> Result<Slid, String> {
    match op {
        QueryOp::Scan { sort_idx } => compile_scan(ctx, *sort_idx),
        QueryOp::ScanRelation { .. } => Err("ScanRelation not yet implemented".to_string()),
        QueryOp::Filter { input, pred } => compile_filter(ctx, input, pred),
        QueryOp::Distinct { input } => compile_distinct(ctx, input),
        QueryOp::Negate { input } => compile_negate(ctx, input),
        QueryOp::Join { left, right, cond } => compile_join(ctx, left, right, cond),
        QueryOp::Union { left, right } => compile_union(ctx, left, right),
        QueryOp::Project { input, columns: _ } => compile_project(ctx, input),
        QueryOp::Empty => compile_empty(ctx),
        QueryOp::Delay { input, .. } => compile_delay(ctx, input),
        QueryOp::Diff { input, .. } => compile_diff(ctx, input),
        QueryOp::Integrate { input, .. } => compile_integrate(ctx, input),
        QueryOp::Constant { .. } => Err("Constant compilation not yet implemented".to_string()),
        QueryOp::Apply { .. } => Err("Apply compilation not yet implemented".to_string()),
        QueryOp::ApplyField { .. } => Err("ApplyField compilation not yet implemented".to_string()),
    }
}

/// Compile a Scan operation -> LeafOp + CarrierSource
fn compile_scan(ctx: &mut CompileContext, sort_idx: usize) -> Result<Slid, String> {
    // Get or create Srt element for the source sort
    let srt_elem = ctx.get_srt_elem(sort_idx)?;

    // Create CarrierSource
    let carrier_name = ctx.fresh_name("carrier_source");
    let carrier_source = ctx.add_element(ctx.sort_ids.carrier_source, &carrier_name);

    // Create LeafSource
    let source_name = ctx.fresh_name("leaf_source");
    let leaf_source = ctx.add_element(ctx.sort_ids.leaf_source, &source_name);

    // Link CarrierSource -> LeafSource
    ctx.define_func("CarrierSource/source", carrier_source, leaf_source)?;
    ctx.define_func("CarrierSource/srt", carrier_source, srt_elem)?;

    // Create output tensor type (1-tensor over the sort)
    let tensor_type = ctx.create_1tensor_type(srt_elem)?;

    // Create output wire
    let out_wire = ctx.create_wire(tensor_type)?;

    // Create LeafOp
    let op_name = ctx.fresh_name("leaf_op");
    let leaf_op = ctx.add_element(ctx.sort_ids.leaf_op, &op_name);

    // Create Op element
    let op_elem_name = ctx.fresh_name("op");
    let op_elem = ctx.add_element(ctx.sort_ids.op, &op_elem_name);

    // Link LeafOp
    ctx.define_func("LeafOp/op", leaf_op, op_elem)?;
    ctx.define_func("LeafOp/out", leaf_op, out_wire)?;
    ctx.define_func("LeafOp/source", leaf_op, leaf_source)?;

    Ok(out_wire)
}

/// Compile a Filter operation
fn compile_filter(
    ctx: &mut CompileContext,
    input: &QueryOp,
    pred: &Predicate,
) -> Result<Slid, String> {
    let in_wire = compile_op(ctx, input)?;

    // For True predicate, just pass through (identity)
    if matches!(pred, Predicate::True) {
        return Ok(in_wire);
    }

    // For other predicates, create HadamardOp (simplified: uses input twice)
    let hadamard_name = ctx.fresh_name("hadamard_op");
    let hadamard_op = ctx.add_element(ctx.sort_ids.hadamard_op, &hadamard_name);

    let tensor_type = ctx.get_wire_type(in_wire)?;
    let out_wire = ctx.create_wire(tensor_type)?;

    let op_name = ctx.fresh_name("op");
    let op_elem = ctx.add_element(ctx.sort_ids.op, &op_name);

    ctx.define_func("HadamardOp/op", hadamard_op, op_elem)?;
    ctx.define_func("HadamardOp/left_in", hadamard_op, in_wire)?;
    ctx.define_func("HadamardOp/right_in", hadamard_op, in_wire)?; // placeholder
    ctx.define_func("HadamardOp/out", hadamard_op, out_wire)?;

    Ok(out_wire)
}

/// Compile a Distinct operation -> DistinctOp
fn compile_distinct(ctx: &mut CompileContext, input: &QueryOp) -> Result<Slid, String> {
    let in_wire = compile_op(ctx, input)?;

    let distinct_name = ctx.fresh_name("distinct_op");
    let distinct_op = ctx.add_element(ctx.sort_ids.distinct_op, &distinct_name);

    let tensor_type = ctx.get_wire_type(in_wire)?;
    let out_wire = ctx.create_wire(tensor_type)?;

    let op_name = ctx.fresh_name("op");
    let op_elem = ctx.add_element(ctx.sort_ids.op, &op_name);

    ctx.define_func("DistinctOp/op", distinct_op, op_elem)?;
    ctx.define_func("DistinctOp/in", distinct_op, in_wire)?;
    ctx.define_func("DistinctOp/out", distinct_op, out_wire)?;

    Ok(out_wire)
}

/// Compile a Negate operation -> NegateOp
fn compile_negate(ctx: &mut CompileContext, input: &QueryOp) -> Result<Slid, String> {
    let in_wire = compile_op(ctx, input)?;

    let negate_name = ctx.fresh_name("negate_op");
    let negate_op = ctx.add_element(ctx.sort_ids.negate_op, &negate_name);

    let tensor_type = ctx.get_wire_type(in_wire)?;
    let out_wire = ctx.create_wire(tensor_type)?;

    let op_name = ctx.fresh_name("op");
    let op_elem = ctx.add_element(ctx.sort_ids.op, &op_name);

    ctx.define_func("NegateOp/op", negate_op, op_elem)?;
    ctx.define_func("NegateOp/in", negate_op, in_wire)?;
    ctx.define_func("NegateOp/out", negate_op, out_wire)?;

    Ok(out_wire)
}

/// Compile a Join operation -> ProductOp (+ ContractOp for equijoin)
fn compile_join(
    ctx: &mut CompileContext,
    left: &QueryOp,
    right: &QueryOp,
    cond: &JoinCond,
) -> Result<Slid, String> {
    let left_wire = compile_op(ctx, left)?;
    let right_wire = compile_op(ctx, right)?;

    // Create ProductOp (Kronecker product)
    let product_name = ctx.fresh_name("product_op");
    let product_op = ctx.add_element(ctx.sort_ids.product_op, &product_name);

    // Create output type (for simplicity, reuse left type)
    let tensor_type = ctx.get_wire_type(left_wire)?;
    let product_out_wire = ctx.create_wire(tensor_type)?;

    let op_name = ctx.fresh_name("op");
    let op_elem = ctx.add_element(ctx.sort_ids.op, &op_name);

    ctx.define_func("ProductOp/op", product_op, op_elem)?;
    ctx.define_func("ProductOp/left_in", product_op, left_wire)?;
    ctx.define_func("ProductOp/right_in", product_op, right_wire)?;
    ctx.define_func("ProductOp/out", product_op, product_out_wire)?;

    match cond {
        JoinCond::Cross => Ok(product_out_wire),
        JoinCond::Equi { .. } => {
            // For equijoin, add ContractOp to identify join columns
            let contract_name = ctx.fresh_name("contract_op");
            let contract_op = ctx.add_element(ctx.sort_ids.contract_op, &contract_name);

            let contract_out_wire = ctx.create_wire(tensor_type)?;

            let op_name2 = ctx.fresh_name("op");
            let op_elem2 = ctx.add_element(ctx.sort_ids.op, &op_name2);

            ctx.define_func("ContractOp/op", contract_op, op_elem2)?;
            ctx.define_func("ContractOp/in", contract_op, product_out_wire)?;
            ctx.define_func("ContractOp/out", contract_op, contract_out_wire)?;

            Ok(contract_out_wire)
        }
    }
}

/// Compile a Union operation -> SumOp
fn compile_union(
    ctx: &mut CompileContext,
    left: &QueryOp,
    right: &QueryOp,
) -> Result<Slid, String> {
    let left_wire = compile_op(ctx, left)?;
    let right_wire = compile_op(ctx, right)?;

    let sum_name = ctx.fresh_name("sum_op");
    let sum_op = ctx.add_element(ctx.sort_ids.sum_op, &sum_name);

    let tensor_type = ctx.get_wire_type(left_wire)?;
    let out_wire = ctx.create_wire(tensor_type)?;

    let op_name = ctx.fresh_name("op");
    let op_elem = ctx.add_element(ctx.sort_ids.op, &op_name);

    ctx.define_func("SumOp/op", sum_op, op_elem)?;
    ctx.define_func("SumOp/left_in", sum_op, left_wire)?;
    ctx.define_func("SumOp/right_in", sum_op, right_wire)?;
    ctx.define_func("SumOp/out", sum_op, out_wire)?;

    Ok(out_wire)
}

/// Compile a Project operation -> ContractOp
fn compile_project(ctx: &mut CompileContext, input: &QueryOp) -> Result<Slid, String> {
    let in_wire = compile_op(ctx, input)?;

    let contract_name = ctx.fresh_name("contract_op");
    let contract_op = ctx.add_element(ctx.sort_ids.contract_op, &contract_name);

    let tensor_type = ctx.get_wire_type(in_wire)?;
    let out_wire = ctx.create_wire(tensor_type)?;

    let op_name = ctx.fresh_name("op");
    let op_elem = ctx.add_element(ctx.sort_ids.op, &op_name);

    ctx.define_func("ContractOp/op", contract_op, op_elem)?;
    ctx.define_func("ContractOp/in", contract_op, in_wire)?;
    ctx.define_func("ContractOp/out", contract_op, out_wire)?;

    Ok(out_wire)
}

/// Compile an Empty operation -> ZeroOp
fn compile_empty(ctx: &mut CompileContext) -> Result<Slid, String> {
    let zero_name = ctx.fresh_name("zero_op");
    let zero_op = ctx.add_element(ctx.sort_ids.zero_op, &zero_name);

    // Create placeholder tensor type
    let srt_elem = ctx.get_srt_elem(0)?;
    let tensor_type = ctx.create_1tensor_type(srt_elem)?;
    let out_wire = ctx.create_wire(tensor_type)?;

    let op_name = ctx.fresh_name("op");
    let op_elem = ctx.add_element(ctx.sort_ids.op, &op_name);

    ctx.define_func("ZeroOp/op", zero_op, op_elem)?;
    ctx.define_func("ZeroOp/out", zero_op, out_wire)?;

    Ok(out_wire)
}

/// Compile a Delay operation -> DelayOp
fn compile_delay(ctx: &mut CompileContext, input: &QueryOp) -> Result<Slid, String> {
    let in_wire = compile_op(ctx, input)?;

    let delay_name = ctx.fresh_name("delay_op");
    let delay_op = ctx.add_element(ctx.sort_ids.delay_op, &delay_name);

    let tensor_type = ctx.get_wire_type(in_wire)?;
    let out_wire = ctx.create_wire(tensor_type)?;

    let op_name = ctx.fresh_name("op");
    let op_elem = ctx.add_element(ctx.sort_ids.op, &op_name);

    ctx.define_func("DelayOp/op", delay_op, op_elem)?;
    ctx.define_func("DelayOp/in", delay_op, in_wire)?;
    ctx.define_func("DelayOp/out", delay_op, out_wire)?;

    Ok(out_wire)
}

/// Compile a Diff operation -> DiffOp
fn compile_diff(ctx: &mut CompileContext, input: &QueryOp) -> Result<Slid, String> {
    let in_wire = compile_op(ctx, input)?;

    let diff_name = ctx.fresh_name("diff_op");
    let diff_op = ctx.add_element(ctx.sort_ids.diff_op, &diff_name);

    let tensor_type = ctx.get_wire_type(in_wire)?;
    let out_wire = ctx.create_wire(tensor_type)?;

    let op_name = ctx.fresh_name("op");
    let op_elem = ctx.add_element(ctx.sort_ids.op, &op_name);

    ctx.define_func("DiffOp/op", diff_op, op_elem)?;
    ctx.define_func("DiffOp/in", diff_op, in_wire)?;
    ctx.define_func("DiffOp/out", diff_op, out_wire)?;

    Ok(out_wire)
}

/// Compile an Integrate operation -> IntegrateOp
fn compile_integrate(ctx: &mut CompileContext, input: &QueryOp) -> Result<Slid, String> {
    let in_wire = compile_op(ctx, input)?;

    let integrate_name = ctx.fresh_name("integrate_op");
    let integrate_op = ctx.add_element(ctx.sort_ids.integrate_op, &integrate_name);

    let tensor_type = ctx.get_wire_type(in_wire)?;
    let out_wire = ctx.create_wire(tensor_type)?;

    let op_name = ctx.fresh_name("op");
    let op_elem = ctx.add_element(ctx.sort_ids.op, &op_name);

    ctx.define_func("IntegrateOp/op", integrate_op, op_elem)?;
    ctx.define_func("IntegrateOp/in", integrate_op, in_wire)?;
    ctx.define_func("IntegrateOp/out", integrate_op, out_wire)?;

    Ok(out_wire)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::repl::ReplState;
    use std::fs;
    use std::rc::Rc;

    fn load_tensor_ir_theory() -> Rc<ElaboratedTheory> {
        let meta_content = fs::read_to_string("theories/GeologMeta.geolog")
            .expect("Failed to read GeologMeta.geolog");
        let ir_content = fs::read_to_string("theories/TensorIR.geolog")
            .expect("Failed to read TensorIR.geolog");

        let mut state = ReplState::new();
        state.execute_geolog(&meta_content).expect("GeologMeta should load");
        state.execute_geolog(&ir_content).expect("TensorIR should load");

        state.theories.get("TensorIR")
            .expect("TensorIR theory should exist")
            .clone()
    }

    #[test]
    fn test_compile_scan() {
        let theory = load_tensor_ir_theory();
        let mut universe = Universe::new();

        let plan = QueryOp::Scan { sort_idx: 0 };
        let result = compile_to_tensor_ir(&plan, &theory, &mut universe);

        assert!(result.is_ok(), "Scan compilation failed: {:?}", result.err());
        let instance = result.unwrap();
        assert!(!instance.names.is_empty());
    }

    #[test]
    fn test_compile_distinct_scan() {
        let theory = load_tensor_ir_theory();
        let mut universe = Universe::new();

        let plan = QueryOp::Distinct {
            input: Box::new(QueryOp::Scan { sort_idx: 0 }),
        };
        let result = compile_to_tensor_ir(&plan, &theory, &mut universe);

        assert!(result.is_ok(), "Distinct compilation failed: {:?}", result.err());
    }

    #[test]
    fn test_compile_union() {
        let theory = load_tensor_ir_theory();
        let mut universe = Universe::new();

        let plan = QueryOp::Union {
            left: Box::new(QueryOp::Scan { sort_idx: 0 }),
            right: Box::new(QueryOp::Scan { sort_idx: 0 }),
        };
        let result = compile_to_tensor_ir(&plan, &theory, &mut universe);

        assert!(result.is_ok(), "Union compilation failed: {:?}", result.err());
    }

    #[test]
    fn test_compile_dbsp_operators() {
        let theory = load_tensor_ir_theory();
        let mut universe = Universe::new();

        // Test Delay
        let delay_plan = QueryOp::Delay {
            input: Box::new(QueryOp::Scan { sort_idx: 0 }),
            state_id: 0,
        };
        assert!(compile_to_tensor_ir(&delay_plan, &theory, &mut universe).is_ok());

        // Test Diff
        let diff_plan = QueryOp::Diff {
            input: Box::new(QueryOp::Scan { sort_idx: 0 }),
            state_id: 1,
        };
        assert!(compile_to_tensor_ir(&diff_plan, &theory, &mut universe).is_ok());

        // Test Integrate
        let integrate_plan = QueryOp::Integrate {
            input: Box::new(QueryOp::Scan { sort_idx: 0 }),
            state_id: 2,
        };
        assert!(compile_to_tensor_ir(&integrate_plan, &theory, &mut universe).is_ok());
    }
}
