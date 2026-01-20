//! Compiler from QueryOp plans to RelAlgIR instances.
//!
//! This module creates geolog Structure instances (of the RelAlgIR theory)
//! from QueryOp query plans. The resulting structures can be:
//! - Inspected as first-class data
//! - Optimized using the RelAlgIR optimization axioms
//! - Executed via a RelAlgIR backend
//!
//! # Design
//!
//! The compiler traverses a QueryOp tree and for each node:
//! 1. Creates the corresponding Op element (ScanOp, FilterOp, etc.)
//! 2. Creates Wire elements for inputs/outputs
//! 3. Creates Schema elements describing wire types
//! 4. Sets up function values connecting the elements
//!
//! The resulting Structure includes:
//! - GeologMeta elements representing the source signature (Srt, Func)
//! - RelAlgIR elements representing the query plan (Wire, Op, Schema)
//!
//! # Supported Operators
//!
//! The following QueryOp variants are compiled:
//!
//! | QueryOp          | RelAlgIR Sort    | Notes                        |
//! |------------------|------------------|------------------------------|
//! | `Scan`           | `ScanOp`         | Emits elements of a sort     |
//! | `Filter`         | `FilterOp`       | With predicate compilation   |
//! | `Distinct`       | `DistinctOp`     | Deduplication                |
//! | `Join (Cross)`   | `JoinOp`         | Cartesian product            |
//! | `Join (Equi)`    | `JoinOp`         | Hash join on key columns     |
//! | `Union`          | `UnionOp`        | Bag union                    |
//! | `Project`        | `ProjectOp`      | Column selection/reordering  |
//! | `Negate`         | `NegateOp`       | Flip multiplicities          |
//! | `Empty`          | `EmptyOp`        | Identity for Union           |
//! | `Delay`          | `DelayOp`        | DBSP: previous timestep      |
//! | `Diff`           | `DiffOp`         | DBSP: change since last      |
//! | `Integrate`      | `IntegrateOp`    | DBSP: accumulate             |
//!
//! Not yet supported: `Constant` (needs Elem), `Apply` (needs Func).
//!
//! # Supported Predicates
//!
//! | Predicate        | RelAlgIR Sort       | Notes                        |
//! |------------------|---------------------|------------------------------|
//! | `True`           | `TruePred`          | Always true                  |
//! | `False`          | `FalsePred`         | Always false                 |
//! | `ColEqCol`       | `ColEqPred`         | Two columns equal            |
//! | `ColEqConst`     | `ConstEqPred`       | Column equals constant       |
//! | `FuncEq`         | `FuncEqPred`        | f(arg) = result              |
//! | `FuncEqConst`    | `FuncConstEqPred`   | f(arg) = expected            |
//! | `And`            | `AndPred`           | Conjunction                  |
//! | `Or`             | `OrPred`            | Disjunction                  |
//!
//! All predicate types are now supported!
//!
//! # Example
//!
//! ```ignore
//! use geolog::query::{QueryOp, to_relalg::compile_to_relalg};
//!
//! let plan = QueryOp::Filter {
//!     input: Box::new(QueryOp::Scan { sort_idx: 0 }),
//!     pred: Predicate::True,
//! };
//!
//! let instance = compile_to_relalg(&plan, &relalg_theory, &mut universe)?;
//! // instance.structure contains RelAlgIR elements
//! // instance.output_wire is the final Wire element
//! ```

use std::collections::HashMap;
use std::rc::Rc;

use crate::core::{ElaboratedTheory, SortId, Structure};
use crate::id::Slid;
use crate::query::backend::QueryOp;
use crate::universe::Universe;

/// Result of compiling a QueryOp to a RelAlgIR instance.
pub struct RelAlgInstance {
    /// The RelAlgIR structure
    pub structure: Structure,
    /// The output wire of the compiled plan
    pub output_wire: Slid,
    /// Mapping from Slid to element names (for debugging)
    pub names: HashMap<Slid, String>,
}

/// Context for the compilation process.
struct CompileContext<'a> {
    /// The RelAlgIR theory
    relalg_theory: &'a ElaboratedTheory,
    /// Universe for generating Luids
    universe: &'a mut Universe,
    /// The structure being built
    structure: Structure,
    /// Element names for debugging
    names: HashMap<Slid, String>,
    /// Counter for generating unique names
    counter: usize,

    // Sort IDs in RelAlgIR (cached for efficiency)
    sort_ids: RelAlgSortIds,

    // GeologMeta sort elements already created
    // Maps source signature SortId -> RelAlgIR Slid for GeologMeta/Srt element
    srt_elements: HashMap<usize, Slid>,

    // GeologMeta/Elem elements for target instance elements
    // Maps target instance Slid -> RelAlgIR Slid for GeologMeta/Elem element
    elem_elements: HashMap<Slid, Slid>,

    // GeologMeta/Func elements for target signature functions
    // Maps target func index -> RelAlgIR Slid for GeologMeta/Func element
    func_elements: HashMap<usize, Slid>,

    // The "self-referencing" Theory element (for standalone queries)
    theory_elem: Option<Slid>,

    // Placeholder Instance element for Elem references
    instance_elem: Option<Slid>,
}

/// Cached sort IDs from the RelAlgIR theory.
/// Many fields are reserved for future operator support.
#[allow(dead_code)]
struct RelAlgSortIds {
    // GeologMeta inherited sorts
    theory: SortId,
    srt: SortId,
    dsort: SortId,
    base_ds: SortId,
    func: SortId,
    elem: SortId,
    instance: SortId,

    // RelAlgIR sorts
    schema: SortId,
    unit_schema: SortId,
    base_schema: SortId,
    prod_schema: SortId,
    wire: SortId,
    op: SortId,
    scan_op: SortId,
    filter_op: SortId,
    distinct_op: SortId,
    negate_op: SortId,
    join_op: SortId,
    union_op: SortId,
    delay_op: SortId,
    diff_op: SortId,
    integrate_op: SortId,
    empty_op: SortId,
    const_op: SortId,
    project_op: SortId,
    apply_op: SortId,

    // Projection mapping
    proj_mapping: SortId,
    proj_entry: SortId,

    // Predicates
    pred: SortId,
    true_pred: SortId,
    false_pred: SortId,
    col_eq_pred: SortId,
    const_eq_pred: SortId,
    func_eq_pred: SortId,
    func_const_eq_pred: SortId,
    and_pred: SortId,
    or_pred: SortId,

    // Join conditions
    join_cond: SortId,
    equi_join_cond: SortId,
    cross_join_cond: SortId,

    // Column references
    col_ref: SortId,
    col_path: SortId,
    here_path: SortId,
}

impl RelAlgSortIds {
    fn from_theory(theory: &ElaboratedTheory) -> Result<Self, String> {
        let sig = &theory.theory.signature;
        let lookup = |name: &str| -> Result<SortId, String> {
            sig.lookup_sort(name)
                .ok_or_else(|| format!("RelAlgIR theory missing sort: {}", name))
        };

        Ok(Self {
            // GeologMeta sorts are prefixed
            theory: lookup("GeologMeta/Theory")?,
            srt: lookup("GeologMeta/Srt")?,
            dsort: lookup("GeologMeta/DSort")?,
            base_ds: lookup("GeologMeta/BaseDS")?,
            func: lookup("GeologMeta/Func")?,
            elem: lookup("GeologMeta/Elem")?,
            instance: lookup("GeologMeta/Instance")?,

            // RelAlgIR sorts
            schema: lookup("Schema")?,
            unit_schema: lookup("UnitSchema")?,
            base_schema: lookup("BaseSchema")?,
            prod_schema: lookup("ProdSchema")?,
            wire: lookup("Wire")?,
            op: lookup("Op")?,
            scan_op: lookup("ScanOp")?,
            filter_op: lookup("FilterOp")?,
            distinct_op: lookup("DistinctOp")?,
            negate_op: lookup("NegateOp")?,
            join_op: lookup("JoinOp")?,
            union_op: lookup("UnionOp")?,
            delay_op: lookup("DelayOp")?,
            diff_op: lookup("DiffOp")?,
            integrate_op: lookup("IntegrateOp")?,
            empty_op: lookup("EmptyOp")?,
            const_op: lookup("ConstOp")?,
            project_op: lookup("ProjectOp")?,
            apply_op: lookup("ApplyOp")?,

            proj_mapping: lookup("ProjMapping")?,
            proj_entry: lookup("ProjEntry")?,

            pred: lookup("Pred")?,
            true_pred: lookup("TruePred")?,
            false_pred: lookup("FalsePred")?,
            col_eq_pred: lookup("ColEqPred")?,
            const_eq_pred: lookup("ConstEqPred")?,
            func_eq_pred: lookup("FuncEqPred")?,
            func_const_eq_pred: lookup("FuncConstEqPred")?,
            and_pred: lookup("AndPred")?,
            or_pred: lookup("OrPred")?,

            join_cond: lookup("JoinCond")?,
            equi_join_cond: lookup("EquiJoinCond")?,
            cross_join_cond: lookup("CrossJoinCond")?,

            col_ref: lookup("ColRef")?,
            col_path: lookup("ColPath")?,
            here_path: lookup("HerePath")?,
        })
    }
}

impl<'a> CompileContext<'a> {
    fn new(
        relalg_theory: &'a ElaboratedTheory,
        universe: &'a mut Universe,
    ) -> Result<Self, String> {
        let sort_ids = RelAlgSortIds::from_theory(relalg_theory)?;
        let num_sorts = relalg_theory.theory.signature.sorts.len();
        let num_funcs = relalg_theory.theory.signature.functions.len();

        let mut structure = Structure::new(num_sorts);

        // Initialize function storage with empty columns for each function
        // We use Local columns that will grow as elements are added
        structure.functions = (0..num_funcs)
            .map(|_| crate::core::FunctionColumn::Local(Vec::new()))
            .collect();

        // Initialize relation storage
        let rel_arities: Vec<usize> = relalg_theory
            .theory
            .signature
            .relations
            .iter()
            .map(|r| r.domain.arity())
            .collect();
        structure.init_relations(&rel_arities);

        Ok(Self {
            relalg_theory,
            universe,
            structure,
            names: HashMap::new(),
            counter: 0,
            sort_ids,
            srt_elements: HashMap::new(),
            elem_elements: HashMap::new(),
            func_elements: HashMap::new(),
            theory_elem: None,
            instance_elem: None,
        })
    }

    fn fresh_name(&mut self, prefix: &str) -> String {
        self.counter += 1;
        format!("{}_{}", prefix, self.counter)
    }

    fn add_element(&mut self, sort_id: SortId, name: &str) -> Slid {
        let (slid, _) = self.structure.add_element(self.universe, sort_id);
        self.names.insert(slid, name.to_string());
        slid
    }

    fn define_func(&mut self, func_name: &str, domain: Slid, codomain: Slid) -> Result<(), String> {
        let func_id = self
            .relalg_theory
            .theory
            .signature
            .lookup_func(func_name)
            .ok_or_else(|| format!("RelAlgIR missing function: {}", func_name))?;

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

    /// Get or create a placeholder Instance element for Elem references.
    /// This represents "the instance being queried" - resolved at execution time.
    fn get_instance_elem(&mut self) -> Slid {
        if let Some(elem) = self.instance_elem {
            return elem;
        }

        let theory = self.get_theory_elem();
        let elem = self.add_element(self.sort_ids.instance, "query_instance");

        // Instance/theory = our theory element
        let _ = self.define_func("GeologMeta/Instance/theory", elem, theory);

        self.instance_elem = Some(elem);
        elem
    }

    /// Get or create an Elem element for a target instance element.
    ///
    /// Note: Slid doesn't encode the sort, so we use sort 0 as a placeholder.
    /// A full implementation would require passing the source structure to look up
    /// the actual sort. The Elem is still created and linked, just with incomplete
    /// sort information.
    fn get_elem(&mut self, target_slid: Slid) -> Result<Slid, String> {
        if let Some(&elem) = self.elem_elements.get(&target_slid) {
            return Ok(elem);
        }

        // TODO: To properly set Elem/sort, we'd need access to the source structure
        // to look up target_slid's sort. For now, use sort 0 as a placeholder.
        let placeholder_sort = 0;
        let srt_elem = self.get_srt_elem(placeholder_sort)?;
        let instance = self.get_instance_elem();

        let name = self.fresh_name("elem");
        let elem = self.add_element(self.sort_ids.elem, &name);

        // Elem/instance = our instance element
        self.define_func("GeologMeta/Elem/instance", elem, instance)?;
        // Elem/sort = the sort element (placeholder)
        self.define_func("GeologMeta/Elem/sort", elem, srt_elem)?;

        self.elem_elements.insert(target_slid, elem);
        Ok(elem)
    }

    /// Get or create a Func element for a target signature function.
    fn get_func_elem(&mut self, func_idx: usize) -> Result<Slid, String> {
        if let Some(&elem) = self.func_elements.get(&func_idx) {
            return Ok(elem);
        }

        let theory = self.get_theory_elem();
        let name = self.fresh_name("func");
        let elem = self.add_element(self.sort_ids.func, &name);

        // Func/theory = our theory element
        self.define_func("GeologMeta/Func/theory", elem, theory)?;
        // Note: Func/dom and Func/cod require DSort elements, which we don't
        // track. For now, these are left undefined (partial function).

        self.func_elements.insert(func_idx, elem);
        Ok(elem)
    }

    /// Create a BaseSchema for a sort
    fn create_base_schema(&mut self, srt_elem: Slid) -> Result<(Slid, Slid), String> {
        let bs_name = self.fresh_name("base_schema");
        let bs = self.add_element(self.sort_ids.base_schema, &bs_name);

        let schema_name = self.fresh_name("schema");
        let schema = self.add_element(self.sort_ids.schema, &schema_name);

        self.define_func("BaseSchema/schema", bs, schema)?;
        self.define_func("BaseSchema/srt", bs, srt_elem)?;

        Ok((bs, schema))
    }

    /// Create a Wire with a given schema
    fn create_wire(&mut self, schema: Slid) -> Result<Slid, String> {
        let name = self.fresh_name("wire");
        let wire = self.add_element(self.sort_ids.wire, &name);
        self.define_func("Wire/schema", wire, schema)?;
        Ok(wire)
    }

    /// Create a TruePred and return the Pred elem
    fn create_true_pred(&mut self) -> Result<(Slid, Slid), String> {
        let tp_name = self.fresh_name("true_pred");
        let tp = self.add_element(self.sort_ids.true_pred, &tp_name);

        let pred_name = self.fresh_name("pred");
        let pred = self.add_element(self.sort_ids.pred, &pred_name);

        self.define_func("TruePred/pred", tp, pred)?;

        Ok((tp, pred))
    }

    /// Create a FalsePred and return the Pred elem
    fn create_false_pred(&mut self) -> Result<Slid, String> {
        let fp_name = self.fresh_name("false_pred");
        let fp = self.add_element(self.sort_ids.false_pred, &fp_name);

        let pred_name = self.fresh_name("pred");
        let pred = self.add_element(self.sort_ids.pred, &pred_name);

        self.define_func("FalsePred/pred", fp, pred)?;

        Ok(pred)
    }

    /// Create an AndPred combining two predicates
    fn create_and_pred(&mut self, left: Slid, right: Slid) -> Result<Slid, String> {
        let and_name = self.fresh_name("and_pred");
        let and_pred = self.add_element(self.sort_ids.and_pred, &and_name);

        let pred_name = self.fresh_name("pred");
        let pred = self.add_element(self.sort_ids.pred, &pred_name);

        self.define_func("AndPred/pred", and_pred, pred)?;
        self.define_func("AndPred/left", and_pred, left)?;
        self.define_func("AndPred/right", and_pred, right)?;

        Ok(pred)
    }

    /// Create an OrPred combining two predicates
    fn create_or_pred(&mut self, left: Slid, right: Slid) -> Result<Slid, String> {
        let or_name = self.fresh_name("or_pred");
        let or_pred = self.add_element(self.sort_ids.or_pred, &or_name);

        let pred_name = self.fresh_name("pred");
        let pred = self.add_element(self.sort_ids.pred, &pred_name);

        self.define_func("OrPred/pred", or_pred, pred)?;
        self.define_func("OrPred/left", or_pred, left)?;
        self.define_func("OrPred/right", or_pred, right)?;

        Ok(pred)
    }

    /// Create a ColEqPred (left_col = right_col)
    fn create_col_eq_pred(&mut self, wire: Slid, left_col: usize, right_col: usize) -> Result<Slid, String> {
        // Create left ColRef
        let left_ref = self.create_col_ref(wire, left_col)?;
        // Create right ColRef
        let right_ref = self.create_col_ref(wire, right_col)?;

        let eq_name = self.fresh_name("col_eq_pred");
        let col_eq = self.add_element(self.sort_ids.col_eq_pred, &eq_name);

        let pred_name = self.fresh_name("pred");
        let pred = self.add_element(self.sort_ids.pred, &pred_name);

        self.define_func("ColEqPred/pred", col_eq, pred)?;
        self.define_func("ColEqPred/left", col_eq, left_ref)?;
        self.define_func("ColEqPred/right", col_eq, right_ref)?;

        Ok(pred)
    }

    /// Create a ColRef for column index
    fn create_col_ref(&mut self, wire: Slid, _col: usize) -> Result<Slid, String> {
        // For now, always use HerePath (column 0)
        // TODO: Implement proper column path navigation for nested schemas
        let here_name = self.fresh_name("here_path");
        let here = self.add_element(self.sort_ids.here_path, &here_name);

        let path_name = self.fresh_name("col_path");
        let col_path = self.add_element(self.sort_ids.col_path, &path_name);

        self.define_func("HerePath/path", here, col_path)?;

        let ref_name = self.fresh_name("col_ref");
        let col_ref = self.add_element(self.sort_ids.col_ref, &ref_name);

        self.define_func("ColRef/wire", col_ref, wire)?;
        self.define_func("ColRef/path", col_ref, col_path)?;

        Ok(col_ref)
    }

    /// Create a ConstEqPred (col = constant)
    fn create_const_eq_pred(&mut self, wire: Slid, col: usize, val: Slid) -> Result<Slid, String> {
        // Create ColRef for the column
        let col_ref = self.create_col_ref(wire, col)?;

        // Create Elem element for the constant value
        let elem = self.get_elem(val)?;

        let eq_name = self.fresh_name("const_eq_pred");
        let const_eq = self.add_element(self.sort_ids.const_eq_pred, &eq_name);

        let pred_name = self.fresh_name("pred");
        let pred = self.add_element(self.sort_ids.pred, &pred_name);

        self.define_func("ConstEqPred/pred", const_eq, pred)?;
        self.define_func("ConstEqPred/col", const_eq, col_ref)?;
        self.define_func("ConstEqPred/val", const_eq, elem)?;

        Ok(pred)
    }

    /// Create a FuncEqPred (func(arg_col) = result_col)
    fn create_func_eq_pred(
        &mut self,
        wire: Slid,
        func_idx: usize,
        arg_col: usize,
        result_col: usize,
    ) -> Result<Slid, String> {
        // Create Func element
        let func = self.get_func_elem(func_idx)?;

        // Create ColRefs
        let arg_ref = self.create_col_ref(wire, arg_col)?;
        let result_ref = self.create_col_ref(wire, result_col)?;

        let eq_name = self.fresh_name("func_eq_pred");
        let func_eq = self.add_element(self.sort_ids.func_eq_pred, &eq_name);

        let pred_name = self.fresh_name("pred");
        let pred = self.add_element(self.sort_ids.pred, &pred_name);

        self.define_func("FuncEqPred/pred", func_eq, pred)?;
        self.define_func("FuncEqPred/func", func_eq, func)?;
        self.define_func("FuncEqPred/arg", func_eq, arg_ref)?;
        self.define_func("FuncEqPred/result", func_eq, result_ref)?;

        Ok(pred)
    }

    /// Create a FuncConstEqPred (func(arg_col) = expected_elem)
    fn create_func_const_eq_pred(
        &mut self,
        wire: Slid,
        func_idx: usize,
        arg_col: usize,
        expected: Slid,
    ) -> Result<Slid, String> {
        // Create Func element
        let func = self.get_func_elem(func_idx)?;

        // Create ColRef for argument
        let arg_ref = self.create_col_ref(wire, arg_col)?;

        // Create Elem for expected value
        let expected_elem = self.get_elem(expected)?;

        let eq_name = self.fresh_name("func_const_eq_pred");
        let func_const_eq = self.add_element(self.sort_ids.func_const_eq_pred, &eq_name);

        let pred_name = self.fresh_name("pred");
        let pred = self.add_element(self.sort_ids.pred, &pred_name);

        self.define_func("FuncConstEqPred/pred", func_const_eq, pred)?;
        self.define_func("FuncConstEqPred/func", func_const_eq, func)?;
        self.define_func("FuncConstEqPred/arg", func_const_eq, arg_ref)?;
        self.define_func("FuncConstEqPred/expected", func_const_eq, expected_elem)?;

        Ok(pred)
    }
}

/// Compile a predicate to a Pred element
fn compile_predicate(
    ctx: &mut CompileContext<'_>,
    wire: Slid,
    pred: &crate::query::backend::Predicate,
) -> Result<Slid, String> {
    use crate::query::backend::Predicate;

    match pred {
        Predicate::True => {
            let (_, pred_elem) = ctx.create_true_pred()?;
            Ok(pred_elem)
        }
        Predicate::False => {
            ctx.create_false_pred()
        }
        Predicate::ColEqCol { left, right } => {
            ctx.create_col_eq_pred(wire, *left, *right)
        }
        Predicate::ColEqConst { col, val } => {
            ctx.create_const_eq_pred(wire, *col, *val)
        }
        Predicate::FuncEq {
            func_idx,
            arg_col,
            result_col,
        } => {
            ctx.create_func_eq_pred(wire, *func_idx, *arg_col, *result_col)
        }
        Predicate::FuncEqConst {
            func_idx,
            arg_col,
            expected,
        } => {
            ctx.create_func_const_eq_pred(wire, *func_idx, *arg_col, *expected)
        }
        Predicate::And(left, right) => {
            let left_pred = compile_predicate(ctx, wire, left)?;
            let right_pred = compile_predicate(ctx, wire, right)?;
            ctx.create_and_pred(left_pred, right_pred)
        }
        Predicate::Or(left, right) => {
            let left_pred = compile_predicate(ctx, wire, left)?;
            let right_pred = compile_predicate(ctx, wire, right)?;
            ctx.create_or_pred(left_pred, right_pred)
        }
    }
}

/// Compile a QueryOp into a RelAlgIR instance.
///
/// # Arguments
/// * `plan` - The query plan to compile
/// * `relalg_theory` - The RelAlgIR theory
/// * `universe` - Universe for Luid generation
///
/// # Returns
/// The compiled RelAlgIR instance, or an error message
pub fn compile_to_relalg(
    plan: &QueryOp,
    relalg_theory: &Rc<ElaboratedTheory>,
    universe: &mut Universe,
) -> Result<RelAlgInstance, String> {
    let mut ctx = CompileContext::new(relalg_theory, universe)?;

    // Initialize function storage (will be lazy-initialized on first use)
    // For now, we don't pre-init since we use define_function which auto-grows

    let output_wire = compile_op(&mut ctx, plan)?;

    Ok(RelAlgInstance {
        structure: ctx.structure,
        output_wire,
        names: ctx.names,
    })
}

/// Compile a single QueryOp, returning the output wire Slid.
fn compile_op(ctx: &mut CompileContext<'_>, op: &QueryOp) -> Result<Slid, String> {
    match op {
        QueryOp::Scan { sort_idx } => compile_scan(ctx, *sort_idx),

        QueryOp::Filter { input, pred } => {
            let input_wire = compile_op(ctx, input)?;
            compile_filter(ctx, input_wire, pred)
        }

        QueryOp::Distinct { input } => {
            let input_wire = compile_op(ctx, input)?;
            compile_distinct(ctx, input_wire)
        }

        QueryOp::Join { left, right, cond } => {
            let left_wire = compile_op(ctx, left)?;
            let right_wire = compile_op(ctx, right)?;
            compile_join(ctx, left_wire, right_wire, cond)
        }

        QueryOp::Union { left, right } => {
            let left_wire = compile_op(ctx, left)?;
            let right_wire = compile_op(ctx, right)?;
            compile_union(ctx, left_wire, right_wire)
        }

        // DBSP operators
        QueryOp::Delay { input, state_id: _ } => {
            let input_wire = compile_op(ctx, input)?;
            compile_delay(ctx, input_wire)
        }

        QueryOp::Diff { input, state_id: _ } => {
            let input_wire = compile_op(ctx, input)?;
            compile_diff(ctx, input_wire)
        }

        QueryOp::Integrate { input, state_id: _ } => {
            let input_wire = compile_op(ctx, input)?;
            compile_integrate(ctx, input_wire)
        }

        QueryOp::Negate { input } => {
            let input_wire = compile_op(ctx, input)?;
            compile_negate(ctx, input_wire)
        }

        QueryOp::Empty => compile_empty(ctx),

        QueryOp::Project { input, columns } => {
            let input_wire = compile_op(ctx, input)?;
            compile_project(ctx, input_wire, columns)
        }

        // Not yet implemented (require additional context)
        QueryOp::Constant { .. } => Err("ConstantOp compilation not yet implemented (needs Elem)".to_string()),
        QueryOp::Apply { .. } => Err("ApplyOp compilation not yet implemented (needs Func)".to_string()),
    }
}

fn compile_scan(ctx: &mut CompileContext<'_>, sort_idx: usize) -> Result<Slid, String> {
    // Get or create Srt element
    let srt_elem = ctx.get_srt_elem(sort_idx)?;

    // Create schema for output
    let (_, schema) = ctx.create_base_schema(srt_elem)?;

    // Create output wire
    let out_wire = ctx.create_wire(schema)?;

    // Create ScanOp
    let scan_name = ctx.fresh_name("scan");
    let scan = ctx.add_element(ctx.sort_ids.scan_op, &scan_name);

    // Create Op (sum type injection)
    let op_name = ctx.fresh_name("op");
    let op = ctx.add_element(ctx.sort_ids.op, &op_name);

    // Set function values
    ctx.define_func("ScanOp/op", scan, op)?;
    ctx.define_func("ScanOp/srt", scan, srt_elem)?;
    ctx.define_func("ScanOp/out", scan, out_wire)?;

    Ok(out_wire)
}

fn compile_filter(
    ctx: &mut CompileContext<'_>,
    input_wire: Slid,
    predicate: &crate::query::backend::Predicate,
) -> Result<Slid, String> {
    // Compile the predicate
    let pred = compile_predicate(ctx, input_wire, predicate)?;

    // Get input wire's schema for output
    // In a full implementation, we'd look this up. For now, create a dummy schema.
    let schema_name = ctx.fresh_name("schema");
    let out_schema = ctx.add_element(ctx.sort_ids.schema, &schema_name);

    // Create output wire
    let out_wire = ctx.create_wire(out_schema)?;

    // Create FilterOp
    let filter_name = ctx.fresh_name("filter");
    let filter = ctx.add_element(ctx.sort_ids.filter_op, &filter_name);

    let op_name = ctx.fresh_name("op");
    let op = ctx.add_element(ctx.sort_ids.op, &op_name);

    ctx.define_func("FilterOp/op", filter, op)?;
    ctx.define_func("FilterOp/in", filter, input_wire)?;
    ctx.define_func("FilterOp/out", filter, out_wire)?;
    ctx.define_func("FilterOp/pred", filter, pred)?;

    Ok(out_wire)
}

fn compile_distinct(ctx: &mut CompileContext<'_>, input_wire: Slid) -> Result<Slid, String> {
    // Create output schema (same as input)
    let schema_name = ctx.fresh_name("schema");
    let out_schema = ctx.add_element(ctx.sort_ids.schema, &schema_name);
    let out_wire = ctx.create_wire(out_schema)?;

    // Create DistinctOp
    let distinct_name = ctx.fresh_name("distinct");
    let distinct = ctx.add_element(ctx.sort_ids.distinct_op, &distinct_name);

    let op_name = ctx.fresh_name("op");
    let op = ctx.add_element(ctx.sort_ids.op, &op_name);

    ctx.define_func("DistinctOp/op", distinct, op)?;
    ctx.define_func("DistinctOp/in", distinct, input_wire)?;
    ctx.define_func("DistinctOp/out", distinct, out_wire)?;

    Ok(out_wire)
}

fn compile_join(
    ctx: &mut CompileContext<'_>,
    left_wire: Slid,
    right_wire: Slid,
    condition: &crate::query::backend::JoinCond,
) -> Result<Slid, String> {
    use crate::query::backend::JoinCond;

    // Create output schema (product of inputs) - simplified for now
    let schema_name = ctx.fresh_name("schema");
    let out_schema = ctx.add_element(ctx.sort_ids.schema, &schema_name);
    let out_wire = ctx.create_wire(out_schema)?;

    // Create join condition based on type
    let join_cond = match condition {
        JoinCond::Cross => {
            let cond_name = ctx.fresh_name("cross_join");
            let cross_join = ctx.add_element(ctx.sort_ids.cross_join_cond, &cond_name);
            let join_cond_name = ctx.fresh_name("join_cond");
            let join_cond_elem = ctx.add_element(ctx.sort_ids.join_cond, &join_cond_name);
            ctx.define_func("CrossJoinCond/cond", cross_join, join_cond_elem)?;
            join_cond_elem
        }
        JoinCond::Equi { left_col, right_col } => {
            // Create column references for the join keys
            let left_ref = ctx.create_col_ref(left_wire, *left_col)?;
            let right_ref = ctx.create_col_ref(right_wire, *right_col)?;

            let cond_name = ctx.fresh_name("equi_join");
            let equi_join = ctx.add_element(ctx.sort_ids.equi_join_cond, &cond_name);
            let join_cond_name = ctx.fresh_name("join_cond");
            let join_cond_elem = ctx.add_element(ctx.sort_ids.join_cond, &join_cond_name);

            ctx.define_func("EquiJoinCond/cond", equi_join, join_cond_elem)?;
            ctx.define_func("EquiJoinCond/left_col", equi_join, left_ref)?;
            ctx.define_func("EquiJoinCond/right_col", equi_join, right_ref)?;

            join_cond_elem
        }
    };

    // Create JoinOp
    let join_name = ctx.fresh_name("join");
    let join = ctx.add_element(ctx.sort_ids.join_op, &join_name);

    let op_name = ctx.fresh_name("op");
    let op = ctx.add_element(ctx.sort_ids.op, &op_name);

    ctx.define_func("JoinOp/op", join, op)?;
    ctx.define_func("JoinOp/left_in", join, left_wire)?;
    ctx.define_func("JoinOp/right_in", join, right_wire)?;
    ctx.define_func("JoinOp/out", join, out_wire)?;
    ctx.define_func("JoinOp/cond", join, join_cond)?;

    Ok(out_wire)
}

fn compile_union(
    ctx: &mut CompileContext<'_>,
    left_wire: Slid,
    right_wire: Slid,
) -> Result<Slid, String> {
    // Create output schema (same as inputs)
    let schema_name = ctx.fresh_name("schema");
    let out_schema = ctx.add_element(ctx.sort_ids.schema, &schema_name);
    let out_wire = ctx.create_wire(out_schema)?;

    // Create UnionOp
    let union_name = ctx.fresh_name("union");
    let union_op = ctx.add_element(ctx.sort_ids.union_op, &union_name);

    let op_name = ctx.fresh_name("op");
    let op = ctx.add_element(ctx.sort_ids.op, &op_name);

    ctx.define_func("UnionOp/op", union_op, op)?;
    ctx.define_func("UnionOp/left_in", union_op, left_wire)?;
    ctx.define_func("UnionOp/right_in", union_op, right_wire)?;
    ctx.define_func("UnionOp/out", union_op, out_wire)?;

    Ok(out_wire)
}

fn compile_delay(ctx: &mut CompileContext<'_>, input_wire: Slid) -> Result<Slid, String> {
    let schema_name = ctx.fresh_name("schema");
    let out_schema = ctx.add_element(ctx.sort_ids.schema, &schema_name);
    let out_wire = ctx.create_wire(out_schema)?;

    let delay_name = ctx.fresh_name("delay");
    let delay = ctx.add_element(ctx.sort_ids.delay_op, &delay_name);

    let op_name = ctx.fresh_name("op");
    let op = ctx.add_element(ctx.sort_ids.op, &op_name);

    ctx.define_func("DelayOp/op", delay, op)?;
    ctx.define_func("DelayOp/in", delay, input_wire)?;
    ctx.define_func("DelayOp/out", delay, out_wire)?;

    Ok(out_wire)
}

fn compile_diff(ctx: &mut CompileContext<'_>, input_wire: Slid) -> Result<Slid, String> {
    let schema_name = ctx.fresh_name("schema");
    let out_schema = ctx.add_element(ctx.sort_ids.schema, &schema_name);
    let out_wire = ctx.create_wire(out_schema)?;

    let diff_name = ctx.fresh_name("diff");
    let diff = ctx.add_element(ctx.sort_ids.diff_op, &diff_name);

    let op_name = ctx.fresh_name("op");
    let op = ctx.add_element(ctx.sort_ids.op, &op_name);

    ctx.define_func("DiffOp/op", diff, op)?;
    ctx.define_func("DiffOp/in", diff, input_wire)?;
    ctx.define_func("DiffOp/out", diff, out_wire)?;

    Ok(out_wire)
}

fn compile_integrate(ctx: &mut CompileContext<'_>, input_wire: Slid) -> Result<Slid, String> {
    let schema_name = ctx.fresh_name("schema");
    let out_schema = ctx.add_element(ctx.sort_ids.schema, &schema_name);
    let out_wire = ctx.create_wire(out_schema)?;

    let integrate_name = ctx.fresh_name("integrate");
    let integrate = ctx.add_element(ctx.sort_ids.integrate_op, &integrate_name);

    let op_name = ctx.fresh_name("op");
    let op = ctx.add_element(ctx.sort_ids.op, &op_name);

    ctx.define_func("IntegrateOp/op", integrate, op)?;
    ctx.define_func("IntegrateOp/in", integrate, input_wire)?;
    ctx.define_func("IntegrateOp/out", integrate, out_wire)?;

    Ok(out_wire)
}

fn compile_negate(ctx: &mut CompileContext<'_>, input_wire: Slid) -> Result<Slid, String> {
    // Negate preserves schema (from wf/negate_schema axiom)
    let schema_name = ctx.fresh_name("schema");
    let out_schema = ctx.add_element(ctx.sort_ids.schema, &schema_name);
    let out_wire = ctx.create_wire(out_schema)?;

    let negate_name = ctx.fresh_name("negate");
    let negate = ctx.add_element(ctx.sort_ids.negate_op, &negate_name);

    let op_name = ctx.fresh_name("op");
    let op = ctx.add_element(ctx.sort_ids.op, &op_name);

    ctx.define_func("NegateOp/op", negate, op)?;
    ctx.define_func("NegateOp/in", negate, input_wire)?;
    ctx.define_func("NegateOp/out", negate, out_wire)?;

    Ok(out_wire)
}

fn compile_empty(ctx: &mut CompileContext<'_>) -> Result<Slid, String> {
    // Empty produces a wire with some schema (we use a fresh placeholder)
    let schema_name = ctx.fresh_name("schema");
    let out_schema = ctx.add_element(ctx.sort_ids.schema, &schema_name);
    let out_wire = ctx.create_wire(out_schema)?;

    let empty_name = ctx.fresh_name("empty");
    let empty = ctx.add_element(ctx.sort_ids.empty_op, &empty_name);

    let op_name = ctx.fresh_name("op");
    let op = ctx.add_element(ctx.sort_ids.op, &op_name);

    ctx.define_func("EmptyOp/op", empty, op)?;
    ctx.define_func("EmptyOp/out", empty, out_wire)?;

    Ok(out_wire)
}

fn compile_project(
    ctx: &mut CompileContext<'_>,
    input_wire: Slid,
    columns: &[usize],
) -> Result<Slid, String> {
    // Create output schema (different from input - projected schema)
    let schema_name = ctx.fresh_name("schema");
    let out_schema = ctx.add_element(ctx.sort_ids.schema, &schema_name);
    let out_wire = ctx.create_wire(out_schema)?;

    // Create ProjMapping
    let mapping_name = ctx.fresh_name("proj_mapping");
    let proj_mapping = ctx.add_element(ctx.sort_ids.proj_mapping, &mapping_name);

    // Create ProjEntry for each column
    for (target_idx, &source_col) in columns.iter().enumerate() {
        let entry_name = ctx.fresh_name("proj_entry");
        let entry = ctx.add_element(ctx.sort_ids.proj_entry, &entry_name);

        // Source column reference (from input wire)
        let source_ref = ctx.create_col_ref(input_wire, source_col)?;

        // Target path (simplified: just use HerePath for now)
        // In a full implementation, we'd create proper paths for each output column
        let target_path_name = ctx.fresh_name("col_path");
        let target_path = ctx.add_element(ctx.sort_ids.col_path, &target_path_name);

        // If this is not the first column, we'd need FstPath/SndPath navigation
        // For now, we just use HerePath for all (placeholder behavior)
        if target_idx == 0 {
            let here_name = ctx.fresh_name("here_path");
            let here = ctx.add_element(ctx.sort_ids.here_path, &here_name);
            ctx.define_func("HerePath/path", here, target_path)?;
        }

        ctx.define_func("ProjEntry/mapping", entry, proj_mapping)?;
        ctx.define_func("ProjEntry/source", entry, source_ref)?;
        ctx.define_func("ProjEntry/target_path", entry, target_path)?;
    }

    // Create ProjectOp
    let project_name = ctx.fresh_name("project");
    let project = ctx.add_element(ctx.sort_ids.project_op, &project_name);

    let op_name = ctx.fresh_name("op");
    let op = ctx.add_element(ctx.sort_ids.op, &op_name);

    ctx.define_func("ProjectOp/op", project, op)?;
    ctx.define_func("ProjectOp/in", project, input_wire)?;
    ctx.define_func("ProjectOp/out", project, out_wire)?;
    ctx.define_func("ProjectOp/mapping", project, proj_mapping)?;

    Ok(out_wire)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::repl::ReplState;
    use egglog_numeric_id::NumericId;

    fn load_relalg_theory() -> Rc<ElaboratedTheory> {
        let meta_content = std::fs::read_to_string("theories/GeologMeta.geolog")
            .expect("Failed to read GeologMeta.geolog");
        let ir_content = std::fs::read_to_string("theories/RelAlgIR.geolog")
            .expect("Failed to read RelAlgIR.geolog");

        let mut state = ReplState::new();
        state
            .execute_geolog(&meta_content)
            .expect("GeologMeta should load");
        state
            .execute_geolog(&ir_content)
            .expect("RelAlgIR should load");

        state
            .theories
            .get("RelAlgIR")
            .expect("RelAlgIR should exist")
            .clone()
    }

    #[test]
    fn test_compile_scan() {
        let relalg_theory = load_relalg_theory();
        let mut universe = Universe::new();

        let plan = QueryOp::Scan { sort_idx: 0 };

        let result = compile_to_relalg(&plan, &relalg_theory, &mut universe);
        assert!(result.is_ok(), "Scan compilation should succeed");

        let instance = result.unwrap();
        // Should have: Theory, Srt, BaseSchema, Schema, Wire, ScanOp, Op
        assert!(
            instance.structure.len() >= 7,
            "Scan should create at least 7 elements"
        );
    }

    #[test]
    fn test_compile_filter_scan() {
        let relalg_theory = load_relalg_theory();
        let mut universe = Universe::new();

        let plan = QueryOp::Filter {
            input: Box::new(QueryOp::Scan { sort_idx: 0 }),
            pred: crate::query::backend::Predicate::True,
        };

        let result = compile_to_relalg(&plan, &relalg_theory, &mut universe);
        assert!(result.is_ok(), "Filter(Scan) compilation should succeed");

        let instance = result.unwrap();
        // Should have scan elements + filter elements
        assert!(
            instance.structure.len() >= 12,
            "Filter(Scan) should create at least 12 elements"
        );
    }

    #[test]
    fn test_compile_join() {
        let relalg_theory = load_relalg_theory();
        let mut universe = Universe::new();

        // Test cross join
        let plan = QueryOp::Join {
            left: Box::new(QueryOp::Scan { sort_idx: 0 }),
            right: Box::new(QueryOp::Scan { sort_idx: 1 }),
            cond: crate::query::backend::JoinCond::Cross,
        };

        let result = compile_to_relalg(&plan, &relalg_theory, &mut universe);
        assert!(result.is_ok(), "Cross join compilation should succeed");

        // Test equi-join
        let equi_plan = QueryOp::Join {
            left: Box::new(QueryOp::Scan { sort_idx: 0 }),
            right: Box::new(QueryOp::Scan { sort_idx: 1 }),
            cond: crate::query::backend::JoinCond::Equi { left_col: 0, right_col: 0 },
        };

        let result = compile_to_relalg(&equi_plan, &relalg_theory, &mut universe);
        assert!(result.is_ok(), "Equi-join compilation should succeed");
    }

    #[test]
    fn test_compile_predicate() {
        let relalg_theory = load_relalg_theory();
        let mut universe = Universe::new();

        // Test And predicate
        let plan = QueryOp::Filter {
            input: Box::new(QueryOp::Scan { sort_idx: 0 }),
            pred: crate::query::backend::Predicate::And(
                Box::new(crate::query::backend::Predicate::True),
                Box::new(crate::query::backend::Predicate::False),
            ),
        };

        let result = compile_to_relalg(&plan, &relalg_theory, &mut universe);
        assert!(result.is_ok(), "And predicate compilation should succeed");

        // Test Or predicate
        let plan = QueryOp::Filter {
            input: Box::new(QueryOp::Scan { sort_idx: 0 }),
            pred: crate::query::backend::Predicate::Or(
                Box::new(crate::query::backend::Predicate::True),
                Box::new(crate::query::backend::Predicate::True),
            ),
        };

        let result = compile_to_relalg(&plan, &relalg_theory, &mut universe);
        assert!(result.is_ok(), "Or predicate compilation should succeed");

        // Test ColEqCol predicate
        let plan = QueryOp::Filter {
            input: Box::new(QueryOp::Scan { sort_idx: 0 }),
            pred: crate::query::backend::Predicate::ColEqCol { left: 0, right: 1 },
        };

        let result = compile_to_relalg(&plan, &relalg_theory, &mut universe);
        assert!(result.is_ok(), "ColEqCol predicate compilation should succeed");

        // Test ColEqConst predicate
        let plan = QueryOp::Filter {
            input: Box::new(QueryOp::Scan { sort_idx: 0 }),
            pred: crate::query::backend::Predicate::ColEqConst {
                col: 0,
                val: Slid::from_usize(42),
            },
        };

        let result = compile_to_relalg(&plan, &relalg_theory, &mut universe);
        assert!(
            result.is_ok(),
            "ColEqConst predicate compilation should succeed"
        );
        let instance = result.unwrap();
        // Should have created an Elem element for the constant
        assert!(
            instance.names.values().any(|n| n.starts_with("elem_")),
            "Should create Elem element for constant"
        );

        // Test FuncEq predicate
        let plan = QueryOp::Filter {
            input: Box::new(QueryOp::Scan { sort_idx: 0 }),
            pred: crate::query::backend::Predicate::FuncEq {
                func_idx: 0,
                arg_col: 0,
                result_col: 1,
            },
        };

        let result = compile_to_relalg(&plan, &relalg_theory, &mut universe);
        assert!(result.is_ok(), "FuncEq predicate compilation should succeed");
        let instance = result.unwrap();
        // Should have created a Func element
        assert!(
            instance.names.values().any(|n| n.starts_with("func_")),
            "Should create Func element for function reference"
        );

        // Test FuncEqConst predicate
        let plan = QueryOp::Filter {
            input: Box::new(QueryOp::Scan { sort_idx: 0 }),
            pred: crate::query::backend::Predicate::FuncEqConst {
                func_idx: 0,
                arg_col: 0,
                expected: Slid::from_usize(99),
            },
        };

        let result = compile_to_relalg(&plan, &relalg_theory, &mut universe);
        assert!(
            result.is_ok(),
            "FuncEqConst predicate compilation should succeed"
        );
        let instance = result.unwrap();
        // Should have both Func and Elem elements
        assert!(
            instance.names.values().any(|n| n.starts_with("func_")),
            "Should create Func element"
        );
        assert!(
            instance.names.values().any(|n| n.starts_with("elem_")),
            "Should create Elem element for expected value"
        );
    }

    #[test]
    fn test_compile_dbsp_operators() {
        let relalg_theory = load_relalg_theory();
        let mut universe = Universe::new();

        // Test Delay
        let delay_plan = QueryOp::Delay {
            input: Box::new(QueryOp::Scan { sort_idx: 0 }),
            state_id: 0,
        };
        assert!(
            compile_to_relalg(&delay_plan, &relalg_theory, &mut universe).is_ok(),
            "Delay compilation should succeed"
        );

        // Test Diff
        let diff_plan = QueryOp::Diff {
            input: Box::new(QueryOp::Scan { sort_idx: 0 }),
            state_id: 0,
        };
        assert!(
            compile_to_relalg(&diff_plan, &relalg_theory, &mut universe).is_ok(),
            "Diff compilation should succeed"
        );

        // Test Integrate
        let integrate_plan = QueryOp::Integrate {
            input: Box::new(QueryOp::Scan { sort_idx: 0 }),
            state_id: 0,
        };
        assert!(
            compile_to_relalg(&integrate_plan, &relalg_theory, &mut universe).is_ok(),
            "Integrate compilation should succeed"
        );
    }

    #[test]
    fn test_compile_negate_and_empty() {
        let relalg_theory = load_relalg_theory();
        let mut universe = Universe::new();

        // Test Negate
        let negate_plan = QueryOp::Negate {
            input: Box::new(QueryOp::Scan { sort_idx: 0 }),
        };
        let result = compile_to_relalg(&negate_plan, &relalg_theory, &mut universe);
        assert!(result.is_ok(), "Negate compilation should succeed");

        // Test Empty
        let empty_plan = QueryOp::Empty;
        let result = compile_to_relalg(&empty_plan, &relalg_theory, &mut universe);
        assert!(result.is_ok(), "Empty compilation should succeed");

        // Should have: Schema, Wire, EmptyOp, Op
        let instance = result.unwrap();
        assert!(
            instance.structure.len() >= 4,
            "Empty should create at least 4 elements"
        );

        // Test Union with Empty (common pattern)
        let union_empty_plan = QueryOp::Union {
            left: Box::new(QueryOp::Scan { sort_idx: 0 }),
            right: Box::new(QueryOp::Empty),
        };
        let result = compile_to_relalg(&union_empty_plan, &relalg_theory, &mut universe);
        assert!(result.is_ok(), "Union(Scan, Empty) compilation should succeed");
    }

    #[test]
    fn test_compile_project() {
        let relalg_theory = load_relalg_theory();
        let mut universe = Universe::new();

        // Project columns 0 and 2 from a join result
        let project_plan = QueryOp::Project {
            input: Box::new(QueryOp::Join {
                left: Box::new(QueryOp::Scan { sort_idx: 0 }),
                right: Box::new(QueryOp::Scan { sort_idx: 1 }),
                cond: crate::query::backend::JoinCond::Cross,
            }),
            columns: vec![0, 2],
        };

        let result = compile_to_relalg(&project_plan, &relalg_theory, &mut universe);
        assert!(result.is_ok(), "Project compilation should succeed: {:?}", result.err());

        // Simple project: select single column
        let simple_project = QueryOp::Project {
            input: Box::new(QueryOp::Scan { sort_idx: 0 }),
            columns: vec![0],
        };
        let result = compile_to_relalg(&simple_project, &relalg_theory, &mut universe);
        assert!(result.is_ok(), "Single column project should succeed");

        // Identity project (all columns in order)
        let identity_project = QueryOp::Project {
            input: Box::new(QueryOp::Scan { sort_idx: 0 }),
            columns: vec![0, 1, 2],
        };
        let result = compile_to_relalg(&identity_project, &relalg_theory, &mut universe);
        assert!(result.is_ok(), "Identity project should succeed");
    }
}
