//! REPL (Read-Eval-Print Loop) for Geolog
//!
//! Provides an interactive environment for defining theories and instances,
//! inspecting structures, and managing workspaces.

use std::collections::HashMap;
use std::path::PathBuf;
use std::rc::Rc;

use crate::ast;
use crate::core::Structure;
use crate::elaborate::{elaborate_instance, elaborate_theory, Env};
use crate::universe::Universe;

/// REPL state - holds all session data
pub struct ReplState {
    /// Elaboration environment (theories in scope)
    pub env: Env,
    /// Named instances (Structure values)
    pub instances: HashMap<String, Structure>,
    /// Universe for UUID<->Luid mapping
    pub universe: Universe,
    /// Current workspace path (None = ephemeral session)
    pub workspace_path: Option<PathBuf>,
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
    /// Create a new REPL state with empty environment
    pub fn new() -> Self {
        Self {
            env: Env::new(),
            instances: HashMap::new(),
            universe: Universe::new(),
            workspace_path: None,
            input_buffer: String::new(),
            bracket_depth: 0,
        }
    }

    /// Reset to initial state (clear all theories and instances)
    pub fn reset(&mut self) {
        self.env = Env::new();
        self.instances.clear();
        self.universe = Universe::new();
        self.input_buffer.clear();
        self.bracket_depth = 0;
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
        if self.bracket_depth <= 0
            && (trimmed.ends_with('}') || trimmed.ends_with(';'))
        {
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
                    let elab = elaborate_theory(&mut self.env, t)
                        .map_err(|e| format!("Elaboration error: {}", e))?;
                    let name = elab.theory.name.clone();
                    let num_sorts = elab.theory.signature.sorts.len();
                    let num_functions = elab.theory.signature.functions.len();
                    self.env.theories.insert(name.clone(), Rc::new(elab));
                    results.push(ExecuteResult::Theory {
                        name,
                        num_sorts,
                        num_functions,
                    });
                }
                ast::Declaration::Instance(i) => {
                    let structure = elaborate_instance(&self.env, i, &mut self.universe)
                        .map_err(|e| format!("Elaboration error: {}", e))?;
                    let name = i.name.clone();
                    let theory_name = structure.theory_name.clone();
                    let num_elements = structure.len();
                    self.instances.insert(name.clone(), structure);
                    results.push(ExecuteResult::Instance {
                        name,
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
        results.into_iter().next().ok_or_else(|| "No declarations found".to_string())
    }

    /// List all theories
    pub fn list_theories(&self) -> Vec<TheoryInfo> {
        self.env
            .theories
            .iter()
            .map(|(name, theory)| TheoryInfo {
                name: name.clone(),
                num_sorts: theory.theory.signature.sorts.len(),
                num_functions: theory.theory.signature.functions.len(),
                num_axioms: theory.theory.axioms.len(),
            })
            .collect()
    }

    /// List all instances
    pub fn list_instances(&self) -> Vec<InstanceInfo> {
        self.instances
            .iter()
            .map(|(name, structure)| InstanceInfo {
                name: name.clone(),
                theory_name: structure.theory_name.clone(),
                num_elements: structure.len(),
            })
            .collect()
    }

    /// Inspect a theory or instance by name
    pub fn inspect(&self, name: &str) -> Option<InspectResult> {
        // Check theories first
        if let Some(theory) = self.env.theories.get(name) {
            return Some(InspectResult::Theory(TheoryDetail {
                name: name.to_string(),
                sorts: theory.theory.signature.sorts.clone(),
                functions: theory
                    .theory
                    .signature
                    .functions
                    .iter()
                    .map(|f| f.name.clone())
                    .collect(),
                num_axioms: theory.theory.axioms.len(),
            }));
        }

        // Check instances
        if let Some(structure) = self.instances.get(name) {
            let theory = self.env.theories.get(&structure.theory_name)?;
            return Some(InspectResult::Instance(InstanceDetail {
                name: name.to_string(),
                theory_name: structure.theory_name.clone(),
                elements: self.collect_elements(structure, &theory.theory.signature),
                functions: self.collect_function_values(structure, &theory.theory.signature),
            }));
        }

        None
    }

    /// Collect elements grouped by sort
    fn collect_elements(
        &self,
        structure: &Structure,
        signature: &crate::core::Signature,
    ) -> Vec<(String, Vec<String>)> {
        let mut result = Vec::new();
        for (sort_id, sort_name) in signature.sorts.iter().enumerate() {
            let elements: Vec<String> = structure.carriers[sort_id]
                .iter()
                .map(|slid| structure.names[slid as usize].clone())
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
        structure: &Structure,
        signature: &crate::core::Signature,
    ) -> Vec<(String, Vec<String>)> {
        let mut result = Vec::new();
        for (func_id, func_sym) in signature.functions.iter().enumerate() {
            if func_id >= structure.functions.len() {
                continue;
            }
            let mut values = Vec::new();

            // Get the domain sort ID from the function signature
            if let crate::core::DerivedSort::Base(domain_sort_id) = &func_sym.domain {
                for slid in structure.carriers[*domain_sort_id].iter() {
                    let slid = slid as usize;
                    let sort_slid = structure.sort_local_id(slid);
                    if sort_slid < structure.functions[func_id].len() {
                        if let Some(codomain_slid) = crate::id::get_slid(structure.functions[func_id][sort_slid]) {
                            values.push(format!(
                                "{} {} = {}",
                                structure.names[slid],
                                func_sym.name,
                                structure.names[codomain_slid]
                            ));
                        }
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

/// Result of processing a line of input
#[derive(Debug)]
pub enum InputResult {
    /// Meta-command to execute
    MetaCommand(MetaCommand),
    /// Complete geolog input ready to elaborate
    GeologInput(String),
    /// Incomplete input (waiting for more lines)
    Incomplete,
    /// Empty line (no action needed)
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
    /// Parse a meta-command from input (line starts with ':')
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

/// Target for :list command
#[derive(Debug)]
pub enum ListTarget {
    Theories,
    Instances,
    All,
}

/// Result of executing geolog code
#[derive(Debug)]
pub enum ExecuteResult {
    Namespace(String),
    Theory {
        name: String,
        num_sorts: usize,
        num_functions: usize,
    },
    Instance {
        name: String,
        theory_name: String,
        num_elements: usize,
    },
}

/// Info about a theory (for listing)
#[derive(Debug)]
pub struct TheoryInfo {
    pub name: String,
    pub num_sorts: usize,
    pub num_functions: usize,
    pub num_axioms: usize,
}

/// Info about an instance (for listing)
#[derive(Debug)]
pub struct InstanceInfo {
    pub name: String,
    pub theory_name: String,
    pub num_elements: usize,
}

/// Detailed info about a theory (for inspection)
#[derive(Debug)]
pub struct TheoryDetail {
    pub name: String,
    pub sorts: Vec<String>,
    pub functions: Vec<String>,
    pub num_axioms: usize,
}

/// Detailed info about an instance (for inspection)
#[derive(Debug)]
pub struct InstanceDetail {
    pub name: String,
    pub theory_name: String,
    /// Elements grouped by sort: (sort_name, [element_names])
    pub elements: Vec<(String, Vec<String>)>,
    /// Function values grouped by function: (func_name, ["domain func = codomain"])
    pub functions: Vec<(String, Vec<String>)>,
}

/// Result of inspecting a name
#[derive(Debug)]
pub enum InspectResult {
    Theory(TheoryDetail),
    Instance(InstanceDetail),
}

/// Format instance detail as geolog-like syntax
pub fn format_instance_detail(detail: &InstanceDetail) -> String {
    let mut out = String::new();
    out.push_str(&format!("instance {} : {} = {{\n", detail.name, detail.theory_name));

    // Elements by sort
    for (sort_name, elements) in &detail.elements {
        out.push_str(&format!("  // {} ({}):\n", sort_name, elements.len()));
        for elem in elements {
            out.push_str(&format!("  {} : {};\n", elem, sort_name));
        }
    }

    // Function values
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
    out.push_str(&format!("theory {} {{\n", detail.name));

    for sort in &detail.sorts {
        out.push_str(&format!("  {} : Sort;\n", sort));
    }

    for func in &detail.functions {
        out.push_str(&format!("  {} : ...;\n", func));
    }

    if detail.num_axioms > 0 {
        out.push_str(&format!("  // {} axiom(s)\n", detail.num_axioms));
    }

    out.push_str("}\n");
    out
}
