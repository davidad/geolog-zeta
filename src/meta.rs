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
    DerivedSort, ElaboratedTheory, Formula, Sequent, Signature, SortId, Structure,
    Term, TheoryParam,
};
use crate::id::Slid;
use crate::elaborate::{elaborate_theory, Env};
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
            let file = crate::parse(GEOLOG_META_SOURCE)
                .expect("GeologMeta.geolog should parse");

            let mut env = Env::new();
            for decl in &file.declarations {
                if let crate::ast::Declaration::Theory(t) = &decl.node {
                    let elab = elaborate_theory(&mut env, t)
                        .expect("GeologMeta should elaborate");
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

fn convert_term(
    builder: &mut MetaBuilder,
    term: &Term,
    binder_map: &HashMap<String, u32>,
) -> u32 {
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
            let uuid = universe.get(luid).expect("freshly created luid should have uuid");
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
    sig: &'a Signature,
    // Cached function IDs for quick lookup
    func_ids: HashMap<&'static str, FuncId>,
    // Cached sort IDs
    sort_ids: HashMap<&'static str, SortId>,
}

use crate::core::FuncId;

impl<'a> MetaReader<'a> {
    pub fn new(structure: &'a Structure, universe: &'a Universe, naming: &'a NamingIndex) -> Self {
        let meta = geolog_meta();
        let sig = &meta.theory.signature;

        // Pre-cache commonly used function IDs
        // Note: No */name functions - names are in NamingIndex
        let func_names = [
            "Srt/theory", "Func/theory", "Func/dom", "Func/cod",
            "Rel/theory", "Rel/dom", "Param/theory", "Param/type",
            "BaseDS/dsort", "BaseDS/srt", "ProdDS/dsort", "Field/prod", "Field/type",
            "Sequent/theory", "Sequent/premise", "Sequent/conclusion",
            "CtxVar/sequent", "CtxVar/binder", "Binder/type",
            "VarT/term", "VarT/binder", "AppT/term", "AppT/func", "AppT/arg",
            "RecordT/term", "RecEntry/record", "RecEntry/val", "RecEntry/field",
            "ProjT/term", "ProjT/base", "ProjT/field",
            "TrueF/formula", "FalseF/formula", "EqF/formula", "EqF/lhs", "EqF/rhs",
            "ConjF/formula", "ConjArm/conj", "ConjArm/child",
            "DisjF/formula", "DisjArm/disj", "DisjArm/child",
            "ExistsF/formula", "ExistsF/binder", "ExistsF/body",
            "RelF/formula", "RelF/rel", "RelF/arg",
            "Term/node", "Formula/node",
        ];

        let mut func_ids = HashMap::new();
        for name in func_names {
            if let Some(id) = sig.lookup_func(name) {
                func_ids.insert(name, id);
            }
        }

        // Note: No "Name" sort - names are in NamingIndex
        let sort_names = [
            "Theory", "Param", "Srt", "DSort", "BaseDS", "ProdDS", "Field",
            "Func", "Rel", "Binder", "Term", "VarT", "AppT", "RecordT", "RecEntry", "ProjT",
            "Formula", "RelF", "TrueF", "FalseF", "EqF", "ConjF", "ConjArm", "DisjF", "DisjArm",
            "ExistsF", "Sequent", "CtxVar", "Node",
        ];

        let mut sort_ids = HashMap::new();
        for name in sort_names {
            if let Some(id) = sig.lookup_sort(name) {
                sort_ids.insert(name, id);
            }
        }

        // We need to keep sig alive, but it's behind Arc. Let's store the Arc.
        // Actually, we can just clone the relevant parts we need.
        Self {
            structure,
            universe,
            naming,
            sig: Box::leak(Box::new(meta.theory.signature.clone())),
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
        self.structure.carriers[sort_id].iter().map(|x| x as Slid).collect()
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
        let func = &self.sig.functions[func_id];
        let DerivedSort::Base(domain_sort) = &func.domain else {
            return vec![]; // Product domains not supported yet
        };

        // Iterate through all elements of the domain sort
        let mut results = vec![];
        for elem in self.structure.carriers[*domain_sort].iter() {
            let elem = elem as Slid;
            if self.follow(func_name, elem) == Some(target) {
                results.push(elem);
            }
        }
        results
    }
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

    // Helper to reconstruct DerivedSort from DSort element
    let reconstruct_dsort = |reader: &MetaReader, dsort_elem: Slid| -> DerivedSort {
        // Check if it's a BaseDS (find BaseDS where BaseDS/dsort = dsort_elem)
        let base_elems = reader.find_by_func("BaseDS/dsort", dsort_elem);
        if !base_elems.is_empty() {
            let base_elem = base_elems[0];
            if let Some(srt_elem) = reader.follow("BaseDS/srt", base_elem) {
                if let Some(&sort_id) = slid_to_sort_id.get(&srt_elem) {
                    return DerivedSort::Base(sort_id);
                }
            }
        }

        // Check if it's a ProdDS
        let prod_elems = reader.find_by_func("ProdDS/dsort", dsort_elem);
        if !prod_elems.is_empty() {
            let prod_elem = prod_elems[0];
            let field_elems = reader.find_by_func("Field/prod", prod_elem);

            let mut fields = vec![];
            for field_elem in field_elems {
                // Field name is looked up directly from NamingIndex
                let field_name = reader.name(field_elem);

                // Recursive call would need the full closure; for now, assume base types in products
                if let Some(type_dsort) = reader.follow("Field/type", field_elem) {
                    let base_elems = reader.find_by_func("BaseDS/dsort", type_dsort);
                    if !base_elems.is_empty() {
                        if let Some(srt_elem) = reader.follow("BaseDS/srt", base_elems[0]) {
                            if let Some(&sort_id) = slid_to_sort_id.get(&srt_elem) {
                                fields.push((field_name, DerivedSort::Base(sort_id)));
                            }
                        }
                    }
                }
            }
            return DerivedSort::Product(fields);
        }

        // Default to unit if we can't figure it out
        DerivedSort::unit()
    };

    // Reconstruct functions
    let func_elems = reader.find_by_func("Func/theory", theory_elem);
    let mut slid_to_func_id: HashMap<Slid, FuncId> = HashMap::new();

    for func_elem in &func_elems {
        let name = reader.name(*func_elem);

        let domain = reader
            .follow("Func/dom", *func_elem)
            .map(|d| reconstruct_dsort(&reader, d))
            .unwrap_or_else(DerivedSort::unit);

        let codomain = reader
            .follow("Func/cod", *func_elem)
            .map(|c| reconstruct_dsort(&reader, c))
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
            .map(|d| reconstruct_dsort(&reader, d))
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
    // This is more complex - for now, we'll skip axiom reconstruction
    // as it requires rebuilding the full formula/term AST
    let axioms = vec![]; // TODO: Full axiom reconstruction

    Ok(ElaboratedTheory {
        params,
        theory: crate::core::Theory {
            name: theory_name,
            signature: sig,
            axioms,
        },
    })
}

use crate::core::RelId;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::Theory;

    #[test]
    fn test_simple_theory_to_meta() {
        // Create a simple theory
        let mut sig = Signature::new();
        sig.add_sort("P".to_string());
        sig.add_sort("T".to_string());
        sig.add_function(
            "src".to_string(),
            DerivedSort::Base(1), // T
            DerivedSort::Base(0), // P
        );

        let theory = ElaboratedTheory {
            params: vec![],
            theory: Theory {
                name: "PetriNet".to_string(),
                signature: sig,
                axioms: vec![],
            },
        };

        let mut universe = Universe::new();
        let builder = theory_to_meta(&theory, &mut universe);

        // Check we created the expected elements
        assert!(builder.elements.get("Theory").is_some());
        assert!(builder.elements.get("Srt").is_some());
        assert_eq!(builder.elements.get("Srt").unwrap().len(), 2); // P and T
        assert!(builder.elements.get("Func").is_some());
        assert_eq!(builder.elements.get("Func").unwrap().len(), 1); // src
    }

    #[test]
    fn test_theory_to_structure() {
        // Create a simple theory
        let mut sig = Signature::new();
        sig.add_sort("P".to_string());
        sig.add_sort("T".to_string());
        sig.add_function(
            "src".to_string(),
            DerivedSort::Base(1), // T
            DerivedSort::Base(0), // P
        );

        let theory = ElaboratedTheory {
            params: vec![],
            theory: Theory {
                name: "PetriNet".to_string(),
                signature: sig,
                axioms: vec![],
            },
        };

        let mut universe = Universe::new();
        let mut naming = NamingIndex::new();
        let structure = theory_to_structure(&theory, &mut universe, &mut naming);

        // Check basic structure properties
        assert!(!structure.is_empty());

        // Check we have elements in the structure
        // Should have: 1 Theory, 2 Srt, 1 Func, plus DSort/BaseDS elements
        assert!(structure.len() > 5, "Expected more than 5 elements, got {}", structure.len());

        // Verify names were registered in naming index
        assert!(naming.lookup_unique("PetriNet").is_some());
        assert!(naming.lookup_unique("P").is_some());
        assert!(naming.lookup_unique("T").is_some());
        assert!(naming.lookup_unique("src").is_some());
    }

    #[test]
    fn test_geolog_meta_parses() {
        // Just ensure GeologMeta itself can be loaded
        let meta = geolog_meta();
        assert_eq!(meta.theory.name, "GeologMeta");

        // Should have lots of sorts and functions (no Name sort anymore)
        assert!(meta.theory.signature.sorts.len() >= 25, "Expected many sorts, got {}", meta.theory.signature.sorts.len());
        assert!(meta.theory.signature.functions.len() >= 40, "Expected many functions, got {}", meta.theory.signature.functions.len());
        assert!(meta.theory.signature.relations.len() >= 3, "Expected some relations");
    }

    #[test]
    fn test_theory_roundtrip() {
        // Create a theory with sorts, functions, and a relation
        let mut sig = Signature::new();
        let p_id = sig.add_sort("P".to_string());
        let t_id = sig.add_sort("T".to_string());
        sig.add_function(
            "src".to_string(),
            DerivedSort::Base(t_id),
            DerivedSort::Base(p_id),
        );
        sig.add_function(
            "tgt".to_string(),
            DerivedSort::Base(t_id),
            DerivedSort::Base(p_id),
        );
        // Add a relation with record domain
        sig.add_relation(
            "enabled".to_string(),
            DerivedSort::Product(vec![
                ("place".to_string(), DerivedSort::Base(p_id)),
                ("trans".to_string(), DerivedSort::Base(t_id)),
            ]),
        );

        let original = ElaboratedTheory {
            params: vec![],
            theory: Theory {
                name: "PetriNet".to_string(),
                signature: sig,
                axioms: vec![],
            },
        };

        // Convert to structure
        let mut universe = Universe::new();
        let mut naming = NamingIndex::new();
        let structure = theory_to_structure(&original, &mut universe, &mut naming);

        // Convert back
        let reconstructed = structure_to_theory(&structure, &universe, &naming)
            .expect("roundtrip should succeed");

        // Verify basic properties match
        assert_eq!(reconstructed.theory.name, "PetriNet");
        assert_eq!(reconstructed.theory.signature.sorts.len(), 2);
        assert_eq!(reconstructed.theory.signature.functions.len(), 2);
        assert_eq!(reconstructed.theory.signature.relations.len(), 1);

        // Verify sort names
        assert!(reconstructed.theory.signature.lookup_sort("P").is_some());
        assert!(reconstructed.theory.signature.lookup_sort("T").is_some());

        // Verify function names
        assert!(reconstructed.theory.signature.lookup_func("src").is_some());
        assert!(reconstructed.theory.signature.lookup_func("tgt").is_some());

        // Verify relation name
        assert!(reconstructed.theory.signature.lookup_rel("enabled").is_some());
    }
}
