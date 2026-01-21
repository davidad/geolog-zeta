//! Conversion between ElaboratedTheory and GeologMeta instances
//!
//! This module provides homoiconic serialization: geolog theories can be
//! represented as instances of the GeologMeta theory, enabling persistence
//! and meta-programming.
//!
//! Note: Human-readable names are stored separately in a NamingIndex (keyed by UUID),
//! not in the Structure itself. This module populates both the Structure and NamingIndex.

use std::collections::HashMap;
use std::sync::{Arc, OnceLock};

use crate::core::{
    Context, DerivedSort, ElaboratedTheory, Formula, FuncId, RelId, Sequent, Signature, SortId,
    Structure, Term, TheoryParam,
};
use crate::elaborate::{Env, elaborate_theory};
use crate::id::{NumericId, Slid};
use crate::naming::NamingIndex;
use crate::universe::Universe;

/// GeologMeta source, embedded at compile time
const GEOLOG_META_SOURCE: &str = include_str!("../theories/GeologMeta.geolog");

/// Cached elaborated GeologMeta theory
static GEOLOG_META: OnceLock<Arc<ElaboratedTheory>> = OnceLock::new();

/// Get the elaborated GeologMeta theory, parsing and elaborating on first access
pub fn geolog_meta() -> Arc<ElaboratedTheory> {
    GEOLOG_META
        .get_or_init(|| {
            let file = crate::parse(GEOLOG_META_SOURCE).expect("GeologMeta.geolog should parse");

            let mut env = Env::new();
            for decl in &file.declarations {
                if let crate::ast::Declaration::Theory(t) = &decl.node {
                    let elab = elaborate_theory(&mut env, t).expect("GeologMeta should elaborate");
                    return Arc::new(elab);
                }
            }
            panic!("GeologMeta.geolog should contain a theory declaration");
        })
        .clone()
}

/// A builder for constructing GeologMeta instances
///
/// This manages the mapping from theory components to element IDs (Slids)
/// in the target structure.
pub struct MetaBuilder {
    /// The theory element (there's exactly one per ElaboratedTheory)
    pub theory_slid: u32,

    /// Maps SortId -> Srt element slid
    pub sort_map: HashMap<SortId, u32>,

    /// Maps function name -> Func element slid
    pub func_map: HashMap<String, u32>,

    /// Maps relation name -> Rel element slid
    pub rel_map: HashMap<String, u32>,

    /// Maps field name -> Field element slid (for RecEntry/field and ProjT/field)
    /// Note: This is a simplification; properly would need to track by product type
    pub field_map: HashMap<String, u32>,

    /// Counter for generating fresh element IDs
    next_slid: u32,

    /// Accumulated elements by sort (sort_name -> [(elem_name, slid)])
    /// Names are stored here for NamingIndex population, not in Structure
    elements: HashMap<String, Vec<(String, u32)>>,

    /// Accumulated function values (func_name -> [(domain_slid, codomain_slid)])
    functions: HashMap<String, Vec<(u32, u32)>>,
}

impl Default for MetaBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl MetaBuilder {
    pub fn new() -> Self {
        Self {
            theory_slid: 0,
            sort_map: HashMap::new(),
            func_map: HashMap::new(),
            rel_map: HashMap::new(),
            field_map: HashMap::new(),
            next_slid: 0,
            elements: HashMap::new(),
            functions: HashMap::new(),
        }
    }

    /// Allocate a fresh element in a given sort
    fn alloc(&mut self, sort: &str, name: String) -> u32 {
        let slid = self.next_slid;
        self.next_slid += 1;
        self.elements
            .entry(sort.to_string())
            .or_default()
            .push((name, slid));
        slid
    }

    /// Record a function value: domain_slid maps to codomain_slid via func_name
    fn set_func(&mut self, func_name: &str, domain_slid: u32, codomain_slid: u32) {
        self.functions
            .entry(func_name.to_string())
            .or_default()
            .push((domain_slid, codomain_slid));
    }
}

/// Convert an ElaboratedTheory to a GeologMeta instance description
///
/// Returns a MetaBuilder containing all the elements and function values
/// needed to construct the Structure.
pub fn theory_to_meta(theory: &ElaboratedTheory, _universe: &mut Universe) -> MetaBuilder {
    let mut builder = MetaBuilder::new();

    // Create the Theory element
    let theory_name = &theory.theory.name;
    builder.theory_slid = builder.alloc("Theory", theory_name.clone());

    // Convert signature
    convert_signature(&mut builder, &theory.theory.signature);

    // Convert params
    for param in &theory.params {
        convert_param(&mut builder, param);
    }

    // Convert axioms
    for (i, axiom) in theory.theory.axioms.iter().enumerate() {
        let axiom_name = format!("ax_{}", i);
        convert_sequent(&mut builder, axiom, &axiom_name);
    }

    builder
}

fn convert_signature(builder: &mut MetaBuilder, sig: &Signature) {
    // Convert sorts
    // Note: Human-readable names are stored in NamingIndex, not here
    for (sort_id, sort_name) in sig.sorts.iter().enumerate() {
        let srt_slid = builder.alloc("Srt", sort_name.clone());
        builder.sort_map.insert(sort_id, srt_slid);

        // Srt/theory points to the theory
        builder.set_func("Srt/theory", srt_slid, builder.theory_slid);
    }

    // Convert functions
    for func in &sig.functions {
        let func_slid = builder.alloc("Func", func.name.clone());
        builder.func_map.insert(func.name.clone(), func_slid);

        // Func/theory
        builder.set_func("Func/theory", func_slid, builder.theory_slid);

        // Func/dom and Func/cod
        let dom_slid = convert_dsort(builder, &func.domain);
        let cod_slid = convert_dsort(builder, &func.codomain);
        builder.set_func("Func/dom", func_slid, dom_slid);
        builder.set_func("Func/cod", func_slid, cod_slid);
    }

    // Convert relations
    for rel in &sig.relations {
        let rel_slid = builder.alloc("Rel", rel.name.clone());
        builder.rel_map.insert(rel.name.clone(), rel_slid);

        // Rel/theory
        builder.set_func("Rel/theory", rel_slid, builder.theory_slid);

        // Rel/dom
        let dom_slid = convert_dsort(builder, &rel.domain);
        builder.set_func("Rel/dom", rel_slid, dom_slid);
    }
}

fn convert_dsort(builder: &mut MetaBuilder, dsort: &DerivedSort) -> u32 {
    match dsort {
        DerivedSort::Base(sort_id) => {
            // Create a BaseDS element
            let base_slid = builder.alloc("BaseDS", format!("base_{}", sort_id));

            // BaseDS/dsort - embed into DSort
            let dsort_slid = builder.alloc("DSort", format!("dsort_base_{}", sort_id));
            builder.set_func("BaseDS/dsort", base_slid, dsort_slid);

            // BaseDS/srt - point to the Srt element
            if let Some(&srt_slid) = builder.sort_map.get(sort_id) {
                builder.set_func("BaseDS/srt", base_slid, srt_slid);
            }

            dsort_slid
        }
        DerivedSort::Product(fields) => {
            // Create a ProdDS element
            let prod_slid = builder.alloc("ProdDS", "prod".to_string());

            // ProdDS/dsort - embed into DSort
            let dsort_slid = builder.alloc("DSort", "dsort_prod".to_string());
            builder.set_func("ProdDS/dsort", prod_slid, dsort_slid);

            // Create Field elements for each field
            for (field_name, field_type) in fields {
                let field_slid = builder.alloc("Field", field_name.clone());

                // Track field for later use in RecEntry/field and ProjT/field
                builder.field_map.insert(field_name.clone(), field_slid);

                // Field/prod
                builder.set_func("Field/prod", field_slid, prod_slid);

                // Field/type (recursive)
                let type_slid = convert_dsort(builder, field_type);
                builder.set_func("Field/type", field_slid, type_slid);
            }

            dsort_slid
        }
    }
}

fn convert_param(builder: &mut MetaBuilder, param: &TheoryParam) {
    let param_slid = builder.alloc("Param", param.name.clone());

    // Param/theory (which theory has this param)
    builder.set_func("Param/theory", param_slid, builder.theory_slid);

    // Param/type - we'd need to look up the theory by name
    // For now, create a placeholder Theory element
    let type_theory_slid = builder.alloc("Theory", param.theory_name.clone());
    builder.set_func("Param/type", param_slid, type_theory_slid);
}

fn convert_sequent(builder: &mut MetaBuilder, sequent: &Sequent, name: &str) -> u32 {
    let seq_slid = builder.alloc("Sequent", name.to_string());

    // Sequent/theory
    builder.set_func("Sequent/theory", seq_slid, builder.theory_slid);

    // Create binders for context variables
    let mut binder_map = HashMap::new();
    for (var_name, var_type) in &sequent.context.vars {
        let binder_slid = builder.alloc("Binder", var_name.clone());

        // Binder/type
        let type_slid = convert_dsort(builder, var_type);
        builder.set_func("Binder/type", binder_slid, type_slid);

        // CtxVar linking binder to sequent
        let ctxvar_slid = builder.alloc("CtxVar", format!("cv_{}", var_name));
        builder.set_func("CtxVar/sequent", ctxvar_slid, seq_slid);
        builder.set_func("CtxVar/binder", ctxvar_slid, binder_slid);

        binder_map.insert(var_name.clone(), binder_slid);
    }

    // Sequent/premise
    let premise_slid = convert_formula(builder, &sequent.premise, &binder_map);
    builder.set_func("Sequent/premise", seq_slid, premise_slid);

    // Sequent/conclusion
    let conclusion_slid = convert_formula(builder, &sequent.conclusion, &binder_map);
    builder.set_func("Sequent/conclusion", seq_slid, conclusion_slid);

    seq_slid
}

fn convert_formula(
    builder: &mut MetaBuilder,
    formula: &Formula,
    binder_map: &HashMap<String, u32>,
) -> u32 {
    match formula {
        Formula::True => {
            let truef_slid = builder.alloc("TrueF", "true".to_string());
            let formula_slid = builder.alloc("Formula", "true".to_string());
            builder.set_func("TrueF/formula", truef_slid, formula_slid);
            formula_slid
        }
        Formula::False => {
            let falsef_slid = builder.alloc("FalseF", "false".to_string());
            let formula_slid = builder.alloc("Formula", "false".to_string());
            builder.set_func("FalseF/formula", falsef_slid, formula_slid);
            formula_slid
        }
        Formula::Eq(lhs, rhs) => {
            let eqf_slid = builder.alloc("EqF", "eq".to_string());
            let formula_slid = builder.alloc("Formula", "eq".to_string());
            builder.set_func("EqF/formula", eqf_slid, formula_slid);

            let lhs_slid = convert_term(builder, lhs, binder_map);
            let rhs_slid = convert_term(builder, rhs, binder_map);
            builder.set_func("EqF/lhs", eqf_slid, lhs_slid);
            builder.set_func("EqF/rhs", eqf_slid, rhs_slid);

            formula_slid
        }
        Formula::Conj(conjuncts) => {
            let conjf_slid = builder.alloc("ConjF", "conj".to_string());
            let formula_slid = builder.alloc("Formula", "conj".to_string());
            builder.set_func("ConjF/formula", conjf_slid, formula_slid);

            for (i, conjunct) in conjuncts.iter().enumerate() {
                let arm_slid = builder.alloc("ConjArm", format!("arm_{}", i));
                builder.set_func("ConjArm/conj", arm_slid, conjf_slid);

                let child_slid = convert_formula(builder, conjunct, binder_map);
                builder.set_func("ConjArm/child", arm_slid, child_slid);
            }

            formula_slid
        }
        Formula::Disj(disjuncts) => {
            let disjf_slid = builder.alloc("DisjF", "disj".to_string());
            let formula_slid = builder.alloc("Formula", "disj".to_string());
            builder.set_func("DisjF/formula", disjf_slid, formula_slid);

            for (i, disjunct) in disjuncts.iter().enumerate() {
                let arm_slid = builder.alloc("DisjArm", format!("arm_{}", i));
                builder.set_func("DisjArm/disj", arm_slid, disjf_slid);

                let child_slid = convert_formula(builder, disjunct, binder_map);
                builder.set_func("DisjArm/child", arm_slid, child_slid);
            }

            formula_slid
        }
        Formula::Exists(var_name, var_type, body) => {
            let existsf_slid = builder.alloc("ExistsF", format!("exists_{}", var_name));
            let formula_slid = builder.alloc("Formula", format!("exists_{}", var_name));
            builder.set_func("ExistsF/formula", existsf_slid, formula_slid);

            // Create a new binder for this existential
            let binder_slid = builder.alloc("Binder", var_name.clone());

            let type_slid = convert_dsort(builder, var_type);
            builder.set_func("Binder/type", binder_slid, type_slid);

            builder.set_func("ExistsF/binder", existsf_slid, binder_slid);

            // Extend binder map for body
            let mut extended_map = binder_map.clone();
            extended_map.insert(var_name.clone(), binder_slid);

            let body_slid = convert_formula(builder, body, &extended_map);
            builder.set_func("ExistsF/body", existsf_slid, body_slid);

            formula_slid
        }
        Formula::Rel(rel_id, arg) => {
            let relf_slid = builder.alloc("RelF", format!("rel_{}", rel_id));
            let formula_slid = builder.alloc("Formula", format!("rel_{}", rel_id));
            builder.set_func("RelF/formula", relf_slid, formula_slid);

            // RelF/rel - need to look up the Rel element by ID
            // For now, just use the ID directly (we'd need the rel_map to be indexed by ID)
            // This is a simplification - in practice we'd track rel_id -> slid

            let arg_slid = convert_term(builder, arg, binder_map);
            builder.set_func("RelF/arg", relf_slid, arg_slid);

            formula_slid
        }
    }
}

fn convert_term(builder: &mut MetaBuilder, term: &Term, binder_map: &HashMap<String, u32>) -> u32 {
    match term {
        Term::Var(name, _sort) => {
            let vart_slid = builder.alloc("VarT", name.clone());
            let term_slid = builder.alloc("Term", name.clone());
            builder.set_func("VarT/term", vart_slid, term_slid);

            // VarT/binder - look up in binder map
            if let Some(&binder_slid) = binder_map.get(name) {
                builder.set_func("VarT/binder", vart_slid, binder_slid);
            }

            term_slid
        }
        Term::App(func_id, arg) => {
            let appt_slid = builder.alloc("AppT", format!("app_{}", func_id));
            let term_slid = builder.alloc("Term", format!("app_{}", func_id));
            builder.set_func("AppT/term", appt_slid, term_slid);

            // AppT/func - need to look up Func element by ID
            // Similar simplification as with relations

            let arg_slid = convert_term(builder, arg, binder_map);
            builder.set_func("AppT/arg", appt_slid, arg_slid);

            term_slid
        }
        Term::Record(fields) => {
            let recordt_slid = builder.alloc("RecordT", "record".to_string());
            let term_slid = builder.alloc("Term", "record".to_string());
            builder.set_func("RecordT/term", recordt_slid, term_slid);

            for (field_name, field_val) in fields {
                let entry_slid = builder.alloc("RecEntry", field_name.clone());
                builder.set_func("RecEntry/record", entry_slid, recordt_slid);

                // RecEntry/field points to the Field element (if known)
                if let Some(&field_slid) = builder.field_map.get(field_name) {
                    builder.set_func("RecEntry/field", entry_slid, field_slid);
                }

                let val_slid = convert_term(builder, field_val, binder_map);
                builder.set_func("RecEntry/val", entry_slid, val_slid);
            }

            term_slid
        }
        Term::Project(base, field) => {
            let projt_slid = builder.alloc("ProjT", format!("proj_{}", field));
            let term_slid = builder.alloc("Term", format!("proj_{}", field));
            builder.set_func("ProjT/term", projt_slid, term_slid);

            let base_slid = convert_term(builder, base, binder_map);
            builder.set_func("ProjT/base", projt_slid, base_slid);

            // ProjT/field points to the Field element (if known)
            if let Some(&field_slid) = builder.field_map.get(field) {
                builder.set_func("ProjT/field", projt_slid, field_slid);
            }

            term_slid
        }
    }
}

/// Convert a MetaBuilder into an actual Structure (GeologMeta instance)
///
/// This is the final step in theory serialization:
/// ElaboratedTheory → MetaBuilder → Structure
///
/// Also populates the NamingIndex with human-readable names for all elements.
pub fn builder_to_structure(
    builder: &MetaBuilder,
    universe: &mut Universe,
    naming: &mut NamingIndex,
    theory_name: &str,
) -> Structure {
    let meta_theory = geolog_meta();
    let sig = &meta_theory.theory.signature;

    let num_sorts = sig.sorts.len();
    let mut structure = Structure::new(num_sorts);

    // Map MetaBuilder internal slids → Structure Slids
    let mut slid_map: HashMap<u32, Slid> = HashMap::new();

    // Phase 1: Add all elements
    // Iterate through MetaBuilder's elements by sort, adding them to Structure
    for (sort_name, elems) in &builder.elements {
        let sort_id = sig
            .lookup_sort(sort_name)
            .unwrap_or_else(|| panic!("Sort '{}' not found in GeologMeta", sort_name));

        for (elem_name, internal_slid) in elems {
            let (struct_slid, luid) = structure.add_element(universe, sort_id);
            slid_map.insert(*internal_slid, struct_slid);

            // Register name in NamingIndex (qualified by theory name)
            let uuid = universe
                .get(luid)
                .expect("freshly created luid should have uuid");
            naming.insert(uuid, vec![theory_name.to_string(), elem_name.clone()]);
        }
    }

    // Phase 2: Initialize function storage
    // Build domain sort mapping for each function
    let domain_sort_ids: Vec<Option<SortId>> = sig
        .functions
        .iter()
        .map(|f| {
            match &f.domain {
                DerivedSort::Base(sort_id) => Some(*sort_id),
                DerivedSort::Product(_) => None, // Product domains deferred
            }
        })
        .collect();

    structure.init_functions(&domain_sort_ids);

    // Phase 3: Define function values
    for (func_name, values) in &builder.functions {
        let func_id = sig
            .lookup_func(func_name)
            .unwrap_or_else(|| panic!("Function '{}' not found in GeologMeta", func_name));

        for (internal_dom, internal_cod) in values {
            let dom_slid = slid_map
                .get(internal_dom)
                .unwrap_or_else(|| panic!("Domain slid {} not mapped", internal_dom));
            let cod_slid = slid_map
                .get(internal_cod)
                .unwrap_or_else(|| panic!("Codomain slid {} not mapped", internal_cod));

            structure
                .define_function(func_id, *dom_slid, *cod_slid)
                .unwrap_or_else(|e| panic!("Function definition failed: {}", e));
        }
    }

    structure
}

/// Full conversion: ElaboratedTheory → Structure (GeologMeta instance)
///
/// This is the main entry point for theory serialization.
/// Names are registered in the provided NamingIndex.
pub fn theory_to_structure(
    theory: &ElaboratedTheory,
    universe: &mut Universe,
    naming: &mut NamingIndex,
) -> Structure {
    let builder = theory_to_meta(theory, universe);
    builder_to_structure(&builder, universe, naming, &theory.theory.name)
}

// ============================================================================
// REVERSE CONVERSION: Structure → ElaboratedTheory
// ============================================================================

/// A reader for navigating GeologMeta structures
///
/// Provides convenient access to follow function pointers and collect elements.
/// Uses NamingIndex and Universe to look up human-readable names.
pub struct MetaReader<'a> {
    structure: &'a Structure,
    universe: &'a Universe,
    naming: &'a NamingIndex,
    /// The GeologMeta theory (Arc keeps signature alive)
    meta: Arc<ElaboratedTheory>,
    // Cached function IDs for quick lookup
    func_ids: HashMap<&'static str, FuncId>,
    // Cached sort IDs
    sort_ids: HashMap<&'static str, SortId>,
}

impl<'a> MetaReader<'a> {
    pub fn new(structure: &'a Structure, universe: &'a Universe, naming: &'a NamingIndex) -> Self {
        let meta = geolog_meta();
        let sig = &meta.theory.signature;

        // Pre-cache commonly used function IDs
        // Note: No */name functions - names are in NamingIndex
        let func_names = [
            "Srt/theory",
            "Func/theory",
            "Func/dom",
            "Func/cod",
            "Rel/theory",
            "Rel/dom",
            "Param/theory",
            "Param/type",
            "BaseDS/dsort",
            "BaseDS/srt",
            "ProdDS/dsort",
            "Field/prod",
            "Field/type",
            "Sequent/theory",
            "Sequent/premise",
            "Sequent/conclusion",
            "CtxVar/sequent",
            "CtxVar/binder",
            "Binder/type",
            "VarT/term",
            "VarT/binder",
            "AppT/term",
            "AppT/func",
            "AppT/arg",
            "RecordT/term",
            "RecEntry/record",
            "RecEntry/val",
            "RecEntry/field",
            "ProjT/term",
            "ProjT/base",
            "ProjT/field",
            "TrueF/formula",
            "FalseF/formula",
            "EqF/formula",
            "EqF/lhs",
            "EqF/rhs",
            "ConjF/formula",
            "ConjArm/conj",
            "ConjArm/child",
            "DisjF/formula",
            "DisjArm/disj",
            "DisjArm/child",
            "ExistsF/formula",
            "ExistsF/binder",
            "ExistsF/body",
            "RelF/formula",
            "RelF/rel",
            "RelF/arg",
            "Term/node",
            "Formula/node",
        ];

        let mut func_ids = HashMap::new();
        for name in func_names {
            if let Some(id) = sig.lookup_func(name) {
                func_ids.insert(name, id);
            }
        }

        // Note: No "Name" sort - names are in NamingIndex
        let sort_names = [
            "Theory", "Param", "Srt", "DSort", "BaseDS", "ProdDS", "Field", "Func", "Rel",
            "Binder", "Term", "VarT", "AppT", "RecordT", "RecEntry", "ProjT", "Formula", "RelF",
            "TrueF", "FalseF", "EqF", "ConjF", "ConjArm", "DisjF", "DisjArm", "ExistsF", "Sequent",
            "CtxVar", "Node",
        ];

        let mut sort_ids = HashMap::new();
        for name in sort_names {
            if let Some(id) = sig.lookup_sort(name) {
                sort_ids.insert(name, id);
            }
        }

        Self {
            structure,
            universe,
            naming,
            meta,
            func_ids,
            sort_ids,
        }
    }

    /// Get all elements of a given sort
    fn elements_of_sort(&self, sort_name: &str) -> Vec<Slid> {
        let sort_id = self.sort_ids.get(sort_name).copied().unwrap_or(usize::MAX);
        if sort_id == usize::MAX {
            return vec![];
        }
        self.structure.carriers[sort_id]
            .iter()
            .map(|x| Slid::from_usize(x as usize))
            .collect()
    }

    /// Follow a function from an element, returning the target Slid if defined
    fn follow(&self, func_name: &str, elem: Slid) -> Option<Slid> {
        let func_id = *self.func_ids.get(func_name)?;
        let sort_slid = self.structure.sort_local_id(elem);
        self.structure.get_function(func_id, sort_slid)
    }

    /// Get the name of an element (from NamingIndex via UUID lookup)
    fn name(&self, elem: Slid) -> String {
        let luid = self.structure.get_luid(elem);
        if let Some(uuid) = self.universe.get(luid) {
            self.naming.display_name(&uuid)
        } else {
            format!("slid_{}", elem)
        }
    }

    /// Find elements where a given function points to target
    fn find_by_func(&self, func_name: &str, target: Slid) -> Vec<Slid> {
        let Some(&func_id) = self.func_ids.get(func_name) else {
            return vec![];
        };

        // Get the domain sort for this function
        let func = &self.meta.theory.signature.functions[func_id];
        let DerivedSort::Base(domain_sort) = &func.domain else {
            return vec![]; // Product domains not supported yet
        };

        // Iterate through all elements of the domain sort
        let mut results = vec![];
        for elem in self.structure.carriers[*domain_sort].iter() {
            let elem = Slid::from_usize(elem as usize);
            if self.follow(func_name, elem) == Some(target) {
                results.push(elem);
            }
        }
        results
    }
}

/// Reconstruct a DerivedSort from its GeologMeta representation
fn reconstruct_dsort(
    reader: &MetaReader,
    dsort_elem: Slid,
    slid_to_sort_id: &HashMap<Slid, SortId>,
) -> DerivedSort {
    // Check if it's a BaseDS (find BaseDS where BaseDS/dsort = dsort_elem)
    let base_elems = reader.find_by_func("BaseDS/dsort", dsort_elem);
    if !base_elems.is_empty() {
        let base_elem = base_elems[0];
        if let Some(srt_elem) = reader.follow("BaseDS/srt", base_elem)
            && let Some(&sort_id) = slid_to_sort_id.get(&srt_elem)
        {
            return DerivedSort::Base(sort_id);
        }
    }

    // Check if it's a ProdDS
    let prod_elems = reader.find_by_func("ProdDS/dsort", dsort_elem);
    if !prod_elems.is_empty() {
        let prod_elem = prod_elems[0];
        let field_elems = reader.find_by_func("Field/prod", prod_elem);

        let mut fields = vec![];
        for field_elem in field_elems {
            let field_name = reader.name(field_elem);
            // Recursively reconstruct field type
            if let Some(type_dsort) = reader.follow("Field/type", field_elem) {
                let field_type = reconstruct_dsort(reader, type_dsort, slid_to_sort_id);
                fields.push((field_name, field_type));
            }
        }
        return DerivedSort::Product(fields);
    }

    // Default to unit
    DerivedSort::unit()
}

/// Recursively reconstruct a Term from its GeologMeta representation
fn reconstruct_term_inner(
    reader: &MetaReader,
    term_elem: Slid,
    binder_map: &HashMap<Slid, (String, DerivedSort)>,
    slid_to_func_id: &HashMap<Slid, FuncId>,
) -> Option<Term> {
    // Check VarT
    let var_elems = reader.find_by_func("VarT/term", term_elem);
    if !var_elems.is_empty() {
        let var_t = var_elems[0];
        if let Some(binder) = reader.follow("VarT/binder", var_t)
            && let Some((name, sort)) = binder_map.get(&binder) {
                return Some(Term::Var(name.clone(), sort.clone()));
            }
        return None;
    }

    // Check AppT
    let app_elems = reader.find_by_func("AppT/term", term_elem);
    if !app_elems.is_empty() {
        let app_t = app_elems[0];
        if let Some(func_elem) = reader.follow("AppT/func", app_t)
            && let Some(&func_id) = slid_to_func_id.get(&func_elem)
            && let Some(arg_term) = reader.follow("AppT/arg", app_t)
        {
            // Recursively reconstruct argument term
            if let Some(arg) = reconstruct_term_inner(reader, arg_term, binder_map, slid_to_func_id) {
                return Some(Term::App(func_id, Box::new(arg)));
            }
        }
        return None;
    }

    // Check ProjT
    let proj_elems = reader.find_by_func("ProjT/term", term_elem);
    if !proj_elems.is_empty() {
        let proj_t = proj_elems[0];
        let field_name = reader
            .follow("ProjT/field", proj_t)
            .map(|f| reader.name(f))
            .unwrap_or_default();
        if let Some(base_term) = reader.follow("ProjT/base", proj_t) {
            // Recursively reconstruct base term
            if let Some(base) = reconstruct_term_inner(reader, base_term, binder_map, slid_to_func_id) {
                return Some(Term::Project(Box::new(base), field_name));
            }
        }
        return None;
    }

    // Check RecordT
    let rec_elems = reader.find_by_func("RecordT/term", term_elem);
    if !rec_elems.is_empty() {
        let rec_t = rec_elems[0];
        let entry_elems = reader.find_by_func("RecEntry/record", rec_t);
        let mut fields = vec![];
        for entry_elem in entry_elems {
            let field_name = reader
                .follow("RecEntry/field", entry_elem)
                .map(|f| reader.name(f))
                .unwrap_or_default();
            if let Some(val_term) = reader.follow("RecEntry/val", entry_elem) {
                // Recursively reconstruct value term
                if let Some(val) = reconstruct_term_inner(reader, val_term, binder_map, slid_to_func_id) {
                    fields.push((field_name, val));
                }
            }
        }
        return Some(Term::Record(fields));
    }

    None
}

/// Recursively reconstruct a Formula from its GeologMeta representation
fn reconstruct_formula_inner(
    reader: &MetaReader,
    formula_elem: Slid,
    binder_map: &HashMap<Slid, (String, DerivedSort)>,
    slid_to_sort_id: &HashMap<Slid, SortId>,
    slid_to_func_id: &HashMap<Slid, FuncId>,
    slid_to_rel_id: &HashMap<Slid, RelId>,
) -> Option<Formula> {
    // Check TrueF
    let true_elems = reader.find_by_func("TrueF/formula", formula_elem);
    if !true_elems.is_empty() {
        return Some(Formula::True);
    }

    // Check FalseF
    let false_elems = reader.find_by_func("FalseF/formula", formula_elem);
    if !false_elems.is_empty() {
        return Some(Formula::False);
    }

    // Check EqF
    let eq_elems = reader.find_by_func("EqF/formula", formula_elem);
    if !eq_elems.is_empty() {
        let eq_f = eq_elems[0];
        if let Some(lhs_term) = reader.follow("EqF/lhs", eq_f)
            && let Some(rhs_term) = reader.follow("EqF/rhs", eq_f)
            && let Some(lhs) = reconstruct_term_inner(reader, lhs_term, binder_map, slid_to_func_id)
            && let Some(rhs) = reconstruct_term_inner(reader, rhs_term, binder_map, slid_to_func_id)
        {
            return Some(Formula::Eq(lhs, rhs));
        }
        return None;
    }

    // Check RelF
    let rel_elems = reader.find_by_func("RelF/formula", formula_elem);
    if !rel_elems.is_empty() {
        let rel_f = rel_elems[0];
        if let Some(rel_elem) = reader.follow("RelF/rel", rel_f)
            && let Some(&rel_id) = slid_to_rel_id.get(&rel_elem)
            && let Some(arg_term) = reader.follow("RelF/arg", rel_f)
            && let Some(arg) = reconstruct_term_inner(reader, arg_term, binder_map, slid_to_func_id)
        {
            return Some(Formula::Rel(rel_id, arg));
        }
        return None;
    }

    // Check ConjF
    let conj_elems = reader.find_by_func("ConjF/formula", formula_elem);
    if !conj_elems.is_empty() {
        let conj_f = conj_elems[0];
        let arm_elems = reader.find_by_func("ConjArm/conj", conj_f);
        let mut children = vec![];
        for arm_elem in arm_elems {
            if let Some(child_formula) = reader.follow("ConjArm/child", arm_elem)
                && let Some(child) = reconstruct_formula_inner(
                    reader,
                    child_formula,
                    binder_map,
                    slid_to_sort_id,
                    slid_to_func_id,
                    slid_to_rel_id,
                ) {
                    children.push(child);
                }
        }
        return Some(Formula::Conj(children));
    }

    // Check DisjF
    let disj_elems = reader.find_by_func("DisjF/formula", formula_elem);
    if !disj_elems.is_empty() {
        let disj_f = disj_elems[0];
        let arm_elems = reader.find_by_func("DisjArm/disj", disj_f);
        let mut children = vec![];
        for arm_elem in arm_elems {
            if let Some(child_formula) = reader.follow("DisjArm/child", arm_elem)
                && let Some(child) = reconstruct_formula_inner(
                    reader,
                    child_formula,
                    binder_map,
                    slid_to_sort_id,
                    slid_to_func_id,
                    slid_to_rel_id,
                ) {
                    children.push(child);
                }
        }
        return Some(Formula::Disj(children));
    }

    // Check ExistsF
    let exists_elems = reader.find_by_func("ExistsF/formula", formula_elem);
    if !exists_elems.is_empty() {
        let exists_f = exists_elems[0];
        // Get the binder for this existential
        if let Some(binder_elem) = reader.follow("ExistsF/binder", exists_f) {
            let var_name = reader.name(binder_elem);
            let var_sort = reader
                .follow("Binder/type", binder_elem)
                .map(|d| reconstruct_dsort(reader, d, slid_to_sort_id))
                .unwrap_or_else(DerivedSort::unit);

            // Create new binder map with this binder
            let mut new_binder_map = binder_map.clone();
            new_binder_map.insert(binder_elem, (var_name.clone(), var_sort.clone()));

            // Recursively reconstruct body
            if let Some(body_formula) = reader.follow("ExistsF/body", exists_f)
                && let Some(body) = reconstruct_formula_inner(
                    reader,
                    body_formula,
                    &new_binder_map,
                    slid_to_sort_id,
                    slid_to_func_id,
                    slid_to_rel_id,
                ) {
                    return Some(Formula::Exists(var_name, var_sort, Box::new(body)));
                }
        }
        return None;
    }

    None
}

/// Convert a GeologMeta Structure back to an ElaboratedTheory
///
/// This is the reverse of theory_to_structure, used for loading saved theories.
/// Requires Universe and NamingIndex to look up human-readable names.
pub fn structure_to_theory(
    structure: &Structure,
    universe: &Universe,
    naming: &NamingIndex,
) -> Result<ElaboratedTheory, String> {
    let reader = MetaReader::new(structure, universe, naming);

    // Find the Theory element (assume exactly one for now)
    let theory_elems = reader.elements_of_sort("Theory");
    if theory_elems.is_empty() {
        return Err("No Theory element found".to_string());
    }
    let theory_elem = theory_elems[0];
    let theory_name = reader.name(theory_elem);

    // Build signature
    let mut sig = Signature::new();

    // Reconstruct sorts: find all Srt elements pointing to this theory
    let srt_elems = reader.find_by_func("Srt/theory", theory_elem);
    let mut slid_to_sort_id: HashMap<Slid, SortId> = HashMap::new();

    for srt_elem in &srt_elems {
        let name = reader.name(*srt_elem);
        let sort_id = sig.add_sort(name);
        slid_to_sort_id.insert(*srt_elem, sort_id);
    }

    // Reconstruct functions (using standalone reconstruct_dsort helper)
    let func_elems = reader.find_by_func("Func/theory", theory_elem);
    let mut slid_to_func_id: HashMap<Slid, FuncId> = HashMap::new();

    for func_elem in &func_elems {
        let name = reader.name(*func_elem);

        let domain = reader
            .follow("Func/dom", *func_elem)
            .map(|d| reconstruct_dsort(&reader, d, &slid_to_sort_id))
            .unwrap_or_else(DerivedSort::unit);

        let codomain = reader
            .follow("Func/cod", *func_elem)
            .map(|c| reconstruct_dsort(&reader, c, &slid_to_sort_id))
            .unwrap_or_else(DerivedSort::unit);

        let func_id = sig.add_function(name, domain, codomain);
        slid_to_func_id.insert(*func_elem, func_id);
    }

    // Reconstruct relations
    let rel_elems = reader.find_by_func("Rel/theory", theory_elem);
    let mut slid_to_rel_id: HashMap<Slid, RelId> = HashMap::new();

    for rel_elem in &rel_elems {
        let name = reader.name(*rel_elem);

        let domain = reader
            .follow("Rel/dom", *rel_elem)
            .map(|d| reconstruct_dsort(&reader, d, &slid_to_sort_id))
            .unwrap_or_else(DerivedSort::unit);

        let rel_id = sig.add_relation(name, domain);
        slid_to_rel_id.insert(*rel_elem, rel_id);
    }

    // Reconstruct params
    let param_elems = reader.find_by_func("Param/theory", theory_elem);
    let mut params = vec![];

    for param_elem in param_elems {
        let name = reader.name(param_elem);
        let type_theory = reader
            .follow("Param/type", param_elem)
            .map(|t| reader.name(t))
            .unwrap_or_default();

        params.push(TheoryParam {
            name,
            theory_name: type_theory,
        });
    }

    // Reconstruct axioms (sequents)
    let sequent_elems = reader.find_by_func("Sequent/theory", theory_elem);
    let mut axioms = vec![];

    for sequent_elem in sequent_elems {
        // Build binder map: Slid -> (name, DerivedSort)
        let mut binder_map: HashMap<Slid, (String, DerivedSort)> = HashMap::new();

        // Get context variables (CtxVar elements for this sequent)
        let ctx_var_elems = reader.find_by_func("CtxVar/sequent", sequent_elem);
        let mut context_vars = vec![];

        for ctx_var_elem in ctx_var_elems {
            let var_name = reader.name(ctx_var_elem);
            if let Some(binder_elem) = reader.follow("CtxVar/binder", ctx_var_elem) {
                let var_sort = reader
                    .follow("Binder/type", binder_elem)
                    .map(|d| reconstruct_dsort(&reader, d, &slid_to_sort_id))
                    .unwrap_or_else(DerivedSort::unit);
                binder_map.insert(binder_elem, (var_name.clone(), var_sort.clone()));
                context_vars.push((var_name, var_sort));
            }
        }

        let context = Context { vars: context_vars };

        // Get premise and conclusion using standalone recursive helpers
        let premise = reader
            .follow("Sequent/premise", sequent_elem)
            .and_then(|f| {
                reconstruct_formula_inner(
                    &reader,
                    f,
                    &binder_map,
                    &slid_to_sort_id,
                    &slid_to_func_id,
                    &slid_to_rel_id,
                )
            })
            .unwrap_or(Formula::True);

        let conclusion = reader
            .follow("Sequent/conclusion", sequent_elem)
            .and_then(|f| {
                reconstruct_formula_inner(
                    &reader,
                    f,
                    &binder_map,
                    &slid_to_sort_id,
                    &slid_to_func_id,
                    &slid_to_rel_id,
                )
            })
            .unwrap_or(Formula::True);

        axioms.push(Sequent {
            context,
            premise,
            conclusion,
        });
    }

    Ok(ElaboratedTheory {
        params,
        theory: crate::core::Theory {
            name: theory_name,
            signature: sig,
            axioms,
            axiom_names: vec![], // TODO: collect axiom names from GeologMeta
        },
    })
}

// Unit tests moved to tests/unit_meta.rs
