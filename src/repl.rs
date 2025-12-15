//! REPL (Read-Eval-Print Loop) for Geolog
//!
//! Provides an interactive environment for defining theories and instances,
//! inspecting structures, and managing workspaces.

use std::path::PathBuf;

use crate::ast;
use crate::core::DerivedSort;
use crate::elaborate::{Env, elaborate_instance, elaborate_theory};
use crate::id::{NumericId, Slid};
use crate::workspace::{InstanceEntry, Workspace};

/// REPL state - now a thin wrapper around Workspace
pub struct ReplState {
    /// The unified workspace (owns universe, naming, theories, instances)
    pub workspace: Workspace,

    /// Multi-line input buffer
    pub input_buffer: String,

    /// Bracket depth for multi-line detection
    pub bracket_depth: i32,
}

impl Default for ReplState {
    fn default() -> Self {
        Self::new()
    }
}

impl ReplState {
    /// Create a new REPL state with empty workspace
    pub fn new() -> Self {
        Self {
            workspace: Workspace::new(),
            input_buffer: String::new(),
            bracket_depth: 0,
        }
    }

    /// Reset to initial state (clear all theories and instances)
    pub fn reset(&mut self) {
        self.workspace = Workspace::new();
        self.input_buffer.clear();
        self.bracket_depth = 0;
    }

    /// Get a structure by instance name
    pub fn get_structure(&self, name: &str) -> Option<&crate::core::Structure> {
        self.workspace.get_structure(name)
    }

    /// Process a line of input, handling multi-line bracket matching
    pub fn process_line(&mut self, line: &str) -> InputResult {
        let trimmed = line.trim();

        // Empty line while buffering - submit incomplete input (will error)
        if trimmed.is_empty() {
            if self.input_buffer.is_empty() {
                return InputResult::Empty;
            }
            // Double-empty-line to force submit
            return InputResult::Incomplete;
        }

        // Meta-command (only at start, not in continuation)
        if trimmed.starts_with(':') && self.input_buffer.is_empty() {
            return InputResult::MetaCommand(MetaCommand::parse(trimmed));
        }

        // Accumulate geolog input
        if !self.input_buffer.is_empty() {
            self.input_buffer.push('\n');
        }
        self.input_buffer.push_str(line);

        // Update bracket depth (ignoring brackets in strings/comments)
        for ch in line.chars() {
            match ch {
                '{' | '(' | '[' => self.bracket_depth += 1,
                '}' | ')' | ']' => self.bracket_depth -= 1,
                _ => {}
            }
        }

        // Complete when brackets balanced and line ends with } or ;
        if self.bracket_depth <= 0 && (trimmed.ends_with('}') || trimmed.ends_with(';')) {
            let input = std::mem::take(&mut self.input_buffer);
            self.bracket_depth = 0;
            InputResult::GeologInput(input)
        } else {
            InputResult::Incomplete
        }
    }

    /// Force submit current buffer (for Ctrl-D or double-empty-line)
    pub fn force_submit(&mut self) -> Option<String> {
        if self.input_buffer.is_empty() {
            None
        } else {
            self.bracket_depth = 0;
            Some(std::mem::take(&mut self.input_buffer))
        }
    }

    /// Execute geolog source code (theory or instance definition)
    pub fn execute_geolog(&mut self, source: &str) -> Result<ExecuteResult, String> {
        // Parse the input
        let file = crate::parse(source).map_err(|e| format!("Parse error: {}", e))?;

        let mut results = Vec::new();

        for decl in &file.declarations {
            match &decl.node {
                ast::Declaration::Namespace(name) => {
                    results.push(ExecuteResult::Namespace(name.clone()));
                }
                ast::Declaration::Theory(t) => {
                    // Check for duplicate theory name
                    if self.workspace.theories.contains_key(&t.name) {
                        return Err(format!(
                            "Theory '{}' already exists. Use a different name or :reset to clear.",
                            t.name
                        ));
                    }

                    // TRANSITIONAL: Build an Env from workspace.theories for elaborate_theory
                    let mut env = Env::new();
                    for (name, theory) in &self.workspace.theories {
                        env.theories.insert(name.clone(), theory.clone());
                    }

                    let elab = elaborate_theory(&mut env, t)
                        .map_err(|e| format!("Elaboration error: {}", e))?;

                    let name = elab.theory.name.clone();
                    let num_sorts = elab.theory.signature.sorts.len();
                    let num_functions = elab.theory.signature.functions.len();
                    let num_relations = elab.theory.signature.relations.len();

                    self.workspace.add_theory(elab);

                    results.push(ExecuteResult::Theory {
                        name,
                        num_sorts,
                        num_functions,
                        num_relations,
                    });
                }
                ast::Declaration::Instance(inst) => {
                    // Check for duplicate instance name
                    if self.workspace.instances.contains_key(&inst.name) {
                        return Err(format!(
                            "Instance '{}' already exists. Use a different name or :reset to clear.",
                            inst.name
                        ));
                    }

                    // TRANSITIONAL: Build an Env from workspace.theories
                    let env = Env {
                        theories: self.workspace.theories.clone(),
                        ..Env::new()
                    };

                    let structure = elaborate_instance(&env, inst, &mut self.workspace.universe)
                        .map_err(|e| format!("Elaboration error: {}", e))?;

                    let instance_name = inst.name.clone();
                    let theory_name = type_expr_to_theory_name(&inst.theory);
                    let num_elements = structure.len();

                    // Build InstanceEntry with element names
                    let mut entry = InstanceEntry::new(structure, theory_name.clone());

                    // Register element names (same iteration order as elaborate_instance)
                    let mut slid_counter: usize = 0;
                    for item in &inst.body {
                        if let ast::InstanceItem::Element(elem_name, _sort_expr) = &item.node {
                            let slid = Slid::from_usize(slid_counter);
                            entry.register_element(elem_name.clone(), slid);

                            // Also register in global naming index
                            let luid = entry.structure.get_luid(slid);
                            let _ = self.workspace.register_element_name(
                                &instance_name,
                                elem_name,
                                luid,
                            );

                            slid_counter += 1;
                        }
                    }

                    self.workspace.add_instance(instance_name.clone(), entry);

                    results.push(ExecuteResult::Instance {
                        name: instance_name,
                        theory_name,
                        num_elements,
                    });
                }
                ast::Declaration::Query(_q) => {
                    return Err("Queries not yet implemented".to_string());
                }
            }
        }

        // Return first result (usually there's just one)
        results
            .into_iter()
            .next()
            .ok_or_else(|| "No declarations found".to_string())
    }

    /// List all theories
    pub fn list_theories(&self) -> Vec<TheoryInfo> {
        self.workspace
            .theories
            .iter()
            .map(|(name, theory)| TheoryInfo {
                name: name.clone(),
                num_sorts: theory.theory.signature.sorts.len(),
                num_functions: theory.theory.signature.functions.len(),
                num_relations: theory.theory.signature.relations.len(),
                num_axioms: theory.theory.axioms.len(),
            })
            .collect()
    }

    /// List all instances
    pub fn list_instances(&self) -> Vec<InstanceInfo> {
        self.workspace
            .instances
            .iter()
            .map(|(name, entry)| InstanceInfo {
                name: name.clone(),
                theory_name: entry.theory_name.clone(),
                num_elements: entry.structure.len(),
            })
            .collect()
    }

    /// Inspect a theory or instance by name
    pub fn inspect(&self, name: &str) -> Option<InspectResult> {
        // Check theories first
        if let Some(theory) = self.workspace.theories.get(name) {
            return Some(InspectResult::Theory(TheoryDetail {
                name: name.to_string(),
                params: theory
                    .params
                    .iter()
                    .map(|p| (p.name.clone(), p.theory_name.clone()))
                    .collect(),
                sorts: theory.theory.signature.sorts.clone(),
                functions: theory
                    .theory
                    .signature
                    .functions
                    .iter()
                    .map(|f| {
                        let domain = format_derived_sort(&f.domain, &theory.theory.signature);
                        let codomain = format_derived_sort(&f.codomain, &theory.theory.signature);
                        (f.name.clone(), domain, codomain)
                    })
                    .collect(),
                relations: theory
                    .theory
                    .signature
                    .relations
                    .iter()
                    .map(|r| {
                        let domain = format_derived_sort(&r.domain, &theory.theory.signature);
                        (r.name.clone(), domain)
                    })
                    .collect(),
                axioms: theory
                    .theory
                    .axioms
                    .iter()
                    .map(|ax| format_axiom(ax, &theory.theory.signature))
                    .collect(),
            }));
        }

        // Check instances
        if let Some(entry) = self.workspace.instances.get(name) {
            let theory = self.workspace.theories.get(&entry.theory_name)?;
            return Some(InspectResult::Instance(InstanceDetail {
                name: name.to_string(),
                theory_name: entry.theory_name.clone(),
                elements: self.collect_elements(entry, &theory.theory.signature),
                functions: self.collect_function_values(entry, &theory.theory.signature),
            }));
        }

        None
    }

    /// Collect elements grouped by sort
    fn collect_elements(
        &self,
        entry: &InstanceEntry,
        signature: &crate::core::Signature,
    ) -> Vec<(String, Vec<String>)> {
        let mut result = Vec::new();
        for (sort_id, sort_name) in signature.sorts.iter().enumerate() {
            let elements: Vec<String> = entry
                .structure
                .carriers[sort_id]
                .iter()
                .map(|slid_u64| {
                    let slid = Slid::from_usize(slid_u64 as usize);
                    entry
                        .get_name(slid)
                        .map(|s| s.to_string())
                        .unwrap_or_else(|| format!("#{}", slid_u64))
                })
                .collect();
            if !elements.is_empty() {
                result.push((sort_name.clone(), elements));
            }
        }
        result
    }

    /// Collect function values as "domain func = codomain"
    fn collect_function_values(
        &self,
        entry: &InstanceEntry,
        signature: &crate::core::Signature,
    ) -> Vec<(String, Vec<String>)> {
        let mut result = Vec::new();
        for (func_id, func_sym) in signature.functions.iter().enumerate() {
            if func_id >= entry.structure.functions.len() {
                continue;
            }
            let mut values = Vec::new();

            if let DerivedSort::Base(domain_sort_id) = &func_sym.domain {
                for slid_u64 in entry.structure.carriers[*domain_sort_id].iter() {
                    let slid = Slid::from_usize(slid_u64 as usize);
                    let sort_slid = entry.structure.sort_local_id(slid);
                    if let Some(codomain_slid) = entry.structure.get_function(func_id, sort_slid) {
                        let domain_name = entry
                            .get_name(slid)
                            .map(|s| s.to_string())
                            .unwrap_or_else(|| format!("#{}", slid_u64));
                        let codomain_name = entry
                            .get_name(codomain_slid)
                            .map(|s| s.to_string())
                            .unwrap_or_else(|| format!("#{}", codomain_slid));
                        values.push(format!(
                            "{} {} = {}",
                            domain_name, func_sym.name, codomain_name
                        ));
                    }
                }
            }
            if !values.is_empty() {
                result.push((func_sym.name.clone(), values));
            }
        }
        result
    }
}

/// Helper to extract theory name from a type expression
fn type_expr_to_theory_name(type_expr: &ast::TypeExpr) -> String {
    match type_expr {
        ast::TypeExpr::Sort => "Sort".to_string(),
        ast::TypeExpr::Prop => "Prop".to_string(),
        ast::TypeExpr::Path(path) => path
            .segments
            .first()
            .cloned()
            .unwrap_or_else(|| "Unknown".to_string()),
        ast::TypeExpr::App(base, _) => type_expr_to_theory_name(base),
        ast::TypeExpr::Arrow(_, _) => "Arrow".to_string(),
        ast::TypeExpr::Record(_) => "Record".to_string(),
        ast::TypeExpr::Instance(inner) => type_expr_to_theory_name(inner),
    }
}

/// Format a DerivedSort as a string using sort names from the signature
fn format_derived_sort(ds: &DerivedSort, sig: &crate::core::Signature) -> String {
    match ds {
        DerivedSort::Base(sort_id) => sig
            .sorts
            .get(*sort_id)
            .cloned()
            .unwrap_or_else(|| format!("Sort#{}", sort_id)),
        DerivedSort::Product(fields) => {
            if fields.is_empty() {
                "Unit".to_string()
            } else {
                let field_strs: Vec<String> = fields
                    .iter()
                    .map(|(name, ds)| format!("{}: {}", name, format_derived_sort(ds, sig)))
                    .collect();
                format!("[{}]", field_strs.join(", "))
            }
        }
    }
}

/// Format a core::Sequent (axiom) for display
fn format_axiom(ax: &crate::core::Sequent, sig: &crate::core::Signature) -> AxiomDetail {
    let context: Vec<(String, String)> = ax
        .context
        .vars
        .iter()
        .map(|(name, sort)| (name.clone(), format_derived_sort(sort, sig)))
        .collect();
    let premise = format_core_formula(&ax.premise, sig);
    let conclusion = format_core_formula(&ax.conclusion, sig);
    AxiomDetail {
        context,
        premise,
        conclusion,
    }
}

/// Format a core::Term for display
fn format_core_term(term: &crate::core::Term, sig: &crate::core::Signature) -> String {
    match term {
        crate::core::Term::Var(name, _) => name.clone(),
        crate::core::Term::App(func_id, arg) => {
            let func_name = sig
                .functions
                .get(*func_id)
                .map(|f| f.name.clone())
                .unwrap_or_else(|| format!("func#{}", func_id));
            format!("{} {}", format_core_term(arg, sig), func_name)
        }
        crate::core::Term::Record(fields) => {
            let field_strs: Vec<String> = fields
                .iter()
                .map(|(name, t)| format!("{}: {}", name, format_core_term(t, sig)))
                .collect();
            format!("[{}]", field_strs.join(", "))
        }
        crate::core::Term::Project(base, field) => {
            format!("{} .{}", format_core_term(base, sig), field)
        }
    }
}

/// Format a core::Formula for display
fn format_core_formula(formula: &crate::core::Formula, sig: &crate::core::Signature) -> String {
    match formula {
        crate::core::Formula::True => "true".to_string(),
        crate::core::Formula::False => "false".to_string(),
        crate::core::Formula::Eq(lhs, rhs) => {
            format!(
                "{} = {}",
                format_core_term(lhs, sig),
                format_core_term(rhs, sig)
            )
        }
        crate::core::Formula::Rel(rel_id, arg) => {
            let rel_name = sig
                .relations
                .get(*rel_id)
                .map(|r| r.name.clone())
                .unwrap_or_else(|| format!("rel#{}", rel_id));
            format!("{} {}", format_core_term(arg, sig), rel_name)
        }
        crate::core::Formula::Conj(conjuncts) => {
            if conjuncts.is_empty() {
                "true".to_string()
            } else {
                conjuncts
                    .iter()
                    .map(|f| format_core_formula(f, sig))
                    .collect::<Vec<_>>()
                    .join(", ")
            }
        }
        crate::core::Formula::Disj(disjuncts) => {
            if disjuncts.is_empty() {
                "false".to_string()
            } else {
                disjuncts
                    .iter()
                    .map(|f| {
                        let s = format_core_formula(f, sig);
                        if matches!(
                            f,
                            crate::core::Formula::Conj(_) | crate::core::Formula::Disj(_)
                        ) {
                            format!("({})", s)
                        } else {
                            s
                        }
                    })
                    .collect::<Vec<_>>()
                    .join(" \\/ ")
            }
        }
        crate::core::Formula::Exists(name, sort, body) => {
            format!(
                "(exists {} : {}. {})",
                name,
                format_derived_sort(sort, sig),
                format_core_formula(body, sig)
            )
        }
    }
}

/// Result of processing a line of input
#[derive(Debug)]
pub enum InputResult {
    MetaCommand(MetaCommand),
    GeologInput(String),
    Incomplete,
    Empty,
}

/// Meta-commands supported by the REPL
#[derive(Debug)]
pub enum MetaCommand {
    Help(Option<String>),
    Quit,
    List(ListTarget),
    Inspect(String),
    Clear,
    Reset,
    Source(PathBuf),
    Unknown(String),
}

impl MetaCommand {
    pub fn parse(input: &str) -> Self {
        let input = input.trim_start_matches(':').trim();
        let mut parts = input.split_whitespace();
        let cmd = parts.next().unwrap_or("");
        let arg = parts.next();

        match cmd {
            "help" | "h" | "?" => MetaCommand::Help(arg.map(String::from)),
            "quit" | "q" | "exit" => MetaCommand::Quit,
            "list" | "ls" | "l" => {
                let target = match arg {
                    Some("theories") | Some("theory") | Some("t") => ListTarget::Theories,
                    Some("instances") | Some("instance") | Some("i") => ListTarget::Instances,
                    _ => ListTarget::All,
                };
                MetaCommand::List(target)
            }
            "inspect" | "i" | "show" => {
                if let Some(name) = arg {
                    MetaCommand::Inspect(name.to_string())
                } else {
                    MetaCommand::Unknown(":inspect requires a name".to_string())
                }
            }
            "clear" | "cls" => MetaCommand::Clear,
            "reset" => MetaCommand::Reset,
            "source" | "load" => {
                if let Some(path) = arg {
                    MetaCommand::Source(PathBuf::from(path))
                } else {
                    MetaCommand::Unknown(":source requires a file path".to_string())
                }
            }
            other => MetaCommand::Unknown(format!("Unknown command: :{}", other)),
        }
    }
}

#[derive(Debug)]
pub enum ListTarget {
    Theories,
    Instances,
    All,
}

#[derive(Debug)]
pub enum ExecuteResult {
    Namespace(String),
    Theory {
        name: String,
        num_sorts: usize,
        num_functions: usize,
        num_relations: usize,
    },
    Instance {
        name: String,
        theory_name: String,
        num_elements: usize,
    },
}

#[derive(Debug)]
pub struct TheoryInfo {
    pub name: String,
    pub num_sorts: usize,
    pub num_functions: usize,
    pub num_relations: usize,
    pub num_axioms: usize,
}

#[derive(Debug)]
pub struct InstanceInfo {
    pub name: String,
    pub theory_name: String,
    pub num_elements: usize,
}

#[derive(Debug)]
pub struct TheoryDetail {
    pub name: String,
    pub params: Vec<(String, String)>,
    pub sorts: Vec<String>,
    pub functions: Vec<(String, String, String)>,
    pub relations: Vec<(String, String)>,
    pub axioms: Vec<AxiomDetail>,
}

#[derive(Debug)]
pub struct AxiomDetail {
    pub context: Vec<(String, String)>,
    pub premise: String,
    pub conclusion: String,
}

#[derive(Debug)]
pub struct InstanceDetail {
    pub name: String,
    pub theory_name: String,
    pub elements: Vec<(String, Vec<String>)>,
    pub functions: Vec<(String, Vec<String>)>,
}

#[derive(Debug)]
pub enum InspectResult {
    Theory(TheoryDetail),
    Instance(InstanceDetail),
}

/// Format instance detail as geolog-like syntax
pub fn format_instance_detail(detail: &InstanceDetail) -> String {
    let mut out = String::new();
    out.push_str(&format!(
        "instance {} : {} = {{\n",
        detail.name, detail.theory_name
    ));

    for (sort_name, elements) in &detail.elements {
        out.push_str(&format!("  // {} ({}):\n", sort_name, elements.len()));
        for elem in elements {
            out.push_str(&format!("  {} : {};\n", elem, sort_name));
        }
    }

    for (func_name, values) in &detail.functions {
        if !values.is_empty() {
            out.push_str(&format!("  // {}:\n", func_name));
            for value in values {
                out.push_str(&format!("  {};\n", value));
            }
        }
    }

    out.push_str("}\n");
    out
}

/// Format theory detail
pub fn format_theory_detail(detail: &TheoryDetail) -> String {
    let mut out = String::new();

    out.push_str("theory ");
    for (param_name, theory_name) in &detail.params {
        if theory_name == "Sort" {
            out.push_str(&format!("({} : Sort) ", param_name));
        } else {
            out.push_str(&format!("({} : {} instance) ", param_name, theory_name));
        }
    }
    out.push_str(&format!("{} {{\n", detail.name));

    for sort in &detail.sorts {
        out.push_str(&format!("  {} : Sort;\n", sort));
    }

    for (name, domain, codomain) in &detail.functions {
        out.push_str(&format!("  {} : {} -> {};\n", name, domain, codomain));
    }

    for (name, domain) in &detail.relations {
        out.push_str(&format!("  {} : {} -> Prop;\n", name, domain));
    }

    for axiom in &detail.axioms {
        let quantified: Vec<String> = axiom
            .context
            .iter()
            .map(|(name, sort)| format!("{} : {}", name, sort))
            .collect();

        if axiom.premise == "true" {
            out.push_str(&format!(
                "  forall {}. |- {};\n",
                quantified.join(", "),
                axiom.conclusion
            ));
        } else {
            out.push_str(&format!(
                "  forall {}. {} |- {};\n",
                quantified.join(", "),
                axiom.premise,
                axiom.conclusion
            ));
        }
    }

    out.push_str("}\n");
    out
}
