//! REPL (Read-Eval-Print Loop) for Geolog
//!
//! Provides an interactive environment for defining theories and instances,
//! inspecting structures, and managing workspaces.
//!
//! ## Architecture Note
//!
//! This module uses `Store` as the source of truth for all data. The `theories`
//! and `instances` HashMaps are TRANSITIONAL: they maintain runtime objects
//! needed for elaboration until the full GeologMeta-based elaboration is complete.

use std::collections::HashMap;
use std::path::PathBuf;
use std::rc::Rc;

use crate::ast;
use crate::core::{DerivedSort, ElaboratedTheory, Structure};
use crate::elaborate::{Env, ElaborationContext, InstanceElaborationResult, elaborate_instance_ctx, elaborate_theory};
use crate::id::{NumericId, Slid};
use crate::store::Store;

// Re-export InstanceEntry from elaborate for backwards compatibility
pub use crate::elaborate::InstanceEntry;

/// REPL state - backed by Store with transitional runtime objects.
///
/// The `store` is the source of truth for persistence and version control.
/// The `theories` and `instances` HashMaps are transitional: they hold
/// runtime objects needed for elaboration until we complete the migration
/// to fully GeologMeta-based elaboration.
pub struct ReplState {
    /// The append-only store (source of truth for persistence)
    pub store: Store,

    /// TRANSITIONAL: Runtime theories for elaboration
    /// Will be removed once elaboration writes directly to Store
    pub theories: HashMap<String, Rc<ElaboratedTheory>>,

    /// TRANSITIONAL: Runtime instances for elaboration and display
    /// Will be removed once elaboration and display use Store directly
    pub instances: HashMap<String, InstanceEntry>,

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
    /// Create a new REPL state with empty store
    pub fn new() -> Self {
        Self {
            store: Store::new(),
            theories: HashMap::new(),
            instances: HashMap::new(),
            input_buffer: String::new(),
            bracket_depth: 0,
        }
    }

    /// Create a new REPL state with a persistence path
    ///
    /// If the path exists, loads the persisted Store and reconstructs runtime objects.
    pub fn with_path(path: impl Into<PathBuf>) -> Self {
        let path = path.into();
        let store = Store::load_or_create(&path);

        // Reconstruct theories from persisted GeologMeta
        let theories = store.reconstruct_all_theories();

        // Reconstruct instances from persisted GeologMeta
        let reconstructed = store.reconstruct_all_instances();
        let instances: HashMap<String, InstanceEntry> = reconstructed
            .into_iter()
            .map(|(name, ri)| {
                // For now, use theory_name as theory_type too
                // TODO: Store full theory_type in GeologMeta for proper reconstruction
                let theory_type = ri.theory_name.clone();
                let mut entry = InstanceEntry::new(ri.structure, ri.theory_name, theory_type);
                // Populate element names
                for (slid, elem_name) in ri.element_names {
                    entry.register_element(elem_name, slid);
                }
                (name, entry)
            })
            .collect();

        Self {
            store,
            theories,
            instances,
            input_buffer: String::new(),
            bracket_depth: 0,
        }
    }

    /// Reset to initial state (clear all theories and instances)
    pub fn reset(&mut self) {
        self.store = Store::new();
        self.theories.clear();
        self.instances.clear();
        self.input_buffer.clear();
        self.bracket_depth = 0;
    }

    /// Get a structure by instance name
    pub fn get_structure(&self, name: &str) -> Option<&Structure> {
        self.instances.get(name).map(|e| &e.structure)
    }

    /// Check if the state has uncommitted changes
    pub fn is_dirty(&self) -> bool {
        self.store.is_dirty()
    }

    /// Commit current changes to the store
    pub fn commit(&mut self, message: Option<&str>) -> Result<Slid, String> {
        self.store.commit(message)
    }

    /// Get commit history
    pub fn commit_history(&self) -> Vec<Slid> {
        self.store.commit_history()
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

    /// Execute geolog source code (theory or instance definitions)
    ///
    /// Returns a list of results, one for each declaration processed.
    pub fn execute_geolog(&mut self, source: &str) -> Result<Vec<ExecuteResult>, String> {
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
                    if self.theories.contains_key(&t.name) {
                        return Err(format!(
                            "Theory '{}' already exists. Use a different name or :reset to clear.",
                            t.name
                        ));
                    }

                    // TRANSITIONAL: Build an Env from self.theories for elaborate_theory
                    let mut env = Env::new();
                    for (name, theory) in &self.theories {
                        env.theories.insert(name.clone(), theory.clone());
                    }

                    let elab = elaborate_theory(&mut env, t)
                        .map_err(|e| format!("Elaboration error: {}", e))?;

                    let name = elab.theory.name.clone();
                    let num_sorts = elab.theory.signature.sorts.len();
                    let num_functions = elab.theory.signature.functions.len();
                    let num_relations = elab.theory.signature.relations.len();

                    // Register in Store with full signature
                    let theory_slid = self.store.create_theory(&name)?;
                    self.store.persist_signature(theory_slid, &elab.theory.signature)?;

                    // Store in transitional HashMap (will be removed once we query Store directly)
                    self.theories.insert(name.clone(), Rc::new(elab));

                    results.push(ExecuteResult::Theory {
                        name,
                        num_sorts,
                        num_functions,
                        num_relations,
                    });
                }
                ast::Declaration::Instance(inst) => {
                    // Check for duplicate instance name
                    if self.instances.contains_key(&inst.name) {
                        return Err(format!(
                            "Instance '{}' already exists. Use a different name or :reset to clear.",
                            inst.name
                        ));
                    }

                    // Use the elaboration that works with our transitional state
                    // If totality check fails, try again with partial elaboration
                    let (elab_result, is_partial) = match self.elaborate_instance_internal(inst) {
                        Ok(result) => (result, false),
                        Err(e) if e.contains("partial function") => {
                            // Retry with partial elaboration
                            eprintln!("Note: Instance has partial functions, allowing for chase to complete them");
                            let result = self.elaborate_instance_partial(inst)
                                .map_err(|e| format!("Elaboration error: {}", e))?;
                            (result, true)
                        }
                        Err(e) => return Err(format!("Elaboration error: {}", e)),
                    };
                    let _ = is_partial; // Used for logging/warnings

                    let instance_name = inst.name.clone();
                    let theory_name = type_expr_to_theory_name(&inst.theory);
                    let theory_type = type_expr_to_full_string(&inst.theory);
                    let num_elements = elab_result.structure.len();

                    // Build InstanceEntry with element names from elaboration
                    // This includes BOTH imported elements AND locally declared elements
                    let mut entry = InstanceEntry::new(elab_result.structure, theory_name.clone(), theory_type);

                    // Copy nested instance metadata for cross-instance references
                    entry.nested_meta = elab_result.nested_meta;

                    // Register ALL element names from elaboration result
                    for (slid, elem_name) in elab_result.slid_to_name {
                        entry.register_element(elem_name.clone(), slid);

                        // Register local (non-qualified) names in store's naming index
                        // Only register names that don't contain '/' (local to this instance)
                        if !elem_name.contains('/') {
                            let luid = entry.structure.get_luid(slid);
                            if let Some(uuid) = self.store.universe.get(luid) {
                                self.store.naming.insert(
                                    uuid,
                                    vec![instance_name.clone(), elem_name.clone()],
                                );
                            }
                        }
                    }

                    // Register in Store and persist instance data
                    if let Some((theory_slid, _)) = self.store.resolve_name(&theory_name) {
                        let instance_slid = self.store.create_instance(&instance_name, theory_slid)?;

                        // Build element name map (Slid -> String) for persistence
                        let elem_names: HashMap<Slid, String> = entry
                            .slid_to_name
                            .iter()
                            .map(|(&slid, name)| (slid, name.clone()))
                            .collect();

                        // Persist all instance data to GeologMeta
                        self.store.persist_instance_data(
                            instance_slid,
                            theory_slid,
                            &entry.structure,
                            &elem_names,
                        )?;
                    }

                    // Store in transitional HashMap
                    self.instances.insert(instance_name.clone(), entry);

                    results.push(ExecuteResult::Instance {
                        name: instance_name,
                        theory_name,
                        num_elements,
                    });
                }
                ast::Declaration::Query(q) => {
                    let result = self.execute_query(q)?;
                    results.push(ExecuteResult::Query(result));
                }
            }
        }

        // Return all results
        if results.is_empty() {
            Err("No declarations found".to_string())
        } else {
            Ok(results)
        }
    }

    /// Internal instance elaboration that works with our transitional state
    fn elaborate_instance_internal(&mut self, inst: &ast::InstanceDecl) -> Result<InstanceElaborationResult, String> {
        // Build elaboration context from our state
        let mut ctx = ElaborationContext {
            theories: &self.theories,
            instances: &self.instances,
            universe: &mut self.store.universe,
            siblings: HashMap::new(),
        };

        elaborate_instance_ctx(&mut ctx, inst)
            .map_err(|e| e.to_string())
    }

    /// Internal instance elaboration that skips totality validation.
    /// Use this for instances that will be completed by the chase algorithm.
    pub fn elaborate_instance_partial(&mut self, inst: &ast::InstanceDecl) -> Result<InstanceElaborationResult, String> {
        use crate::elaborate::elaborate_instance_ctx_partial;

        // Build elaboration context from our state
        let mut ctx = ElaborationContext {
            theories: &self.theories,
            instances: &self.instances,
            universe: &mut self.store.universe,
            siblings: HashMap::new(),
        };

        elaborate_instance_ctx_partial(&mut ctx, inst)
            .map_err(|e| e.to_string())
    }

    /// Execute a query: find an instance satisfying the goal type.
    ///
    /// For a query like `query q { ? : ExampleNet problem0 Solution instance; }`:
    /// 1. Parse the goal type to get theory name and type arguments
    /// 2. Look up the theory and param instances
    /// 3. Build a base structure with imported elements from param instances
    /// 4. Run the solver to find a satisfying extension
    fn execute_query(&mut self, q: &ast::QueryDecl) -> Result<QueryResult, String> {
        use crate::solver::{query, Budget, EnumerationResult};

        let start = std::time::Instant::now();

        // The goal should be an Instance type: tokens ending with `instance`
        if !q.goal.is_instance() {
            return Err("Query goal must be an instance type (e.g., `T instance`)".to_string());
        }
        let inner_type = q.goal.instance_inner()
            .ok_or_else(|| "Failed to extract inner type from instance".to_string())?;

        // Resolve the instance type to get theory name and arguments
        let resolved = self.resolve_query_type(&inner_type)?;
        let theory = self.theories.get(&resolved.theory_name)
            .ok_or_else(|| format!("Unknown theory: {}", resolved.theory_name))?
            .clone();

        // Build base structure from param instances
        let (base_structure, universe) = self.build_query_base(&resolved, &theory)?;

        // Run the solver
        let budget = Budget::new(5000, 10000); // 5 second timeout, 10k step limit
        let result = query(base_structure, universe, theory.clone(), budget);

        let time_ms = start.elapsed().as_secs_f64() * 1000.0;

        match result {
            EnumerationResult::Found { model, .. } => Ok(QueryResult::Found {
                query_name: q.name.clone(),
                theory_name: resolved.theory_name,
                model,
                time_ms,
            }),
            EnumerationResult::Unsat { .. } => Ok(QueryResult::Unsat {
                query_name: q.name.clone(),
                theory_name: resolved.theory_name,
                time_ms,
            }),
            EnumerationResult::Incomplete { reason, .. } => Ok(QueryResult::Incomplete {
                query_name: q.name.clone(),
                theory_name: resolved.theory_name,
                reason,
                time_ms,
            }),
        }
    }

    /// Resolve a query goal type expression to get theory name and param bindings.
    fn resolve_query_type(&self, ty: &ast::TypeExpr) -> Result<ResolvedQueryType, String> {
        use crate::ast::TypeToken;

        // Collect all path tokens from the type expression
        let all_paths: Vec<String> = ty.tokens.iter()
            .filter_map(|t| match t {
                TypeToken::Path(p) => Some(p.to_string()),
                _ => None,
            })
            .collect();

        if all_paths.is_empty() {
            return Err("Query type has no path components".to_string());
        }

        // Simple case: just one path
        if all_paths.len() == 1 {
            return Ok(ResolvedQueryType {
                theory_name: all_paths[0].clone(),
                arguments: vec![],
            });
        }

        // Multiple paths: rightmost is theory name, rest are args
        let theory_name = all_paths.last().unwrap().clone();
        let args: Vec<String> = all_paths[..all_paths.len() - 1].to_vec();

        // Look up theory to match params
        let theory = self.theories.get(&theory_name)
            .ok_or_else(|| format!("Unknown theory: {}", theory_name))?;

        if args.len() != theory.params.len() {
            return Err(format!(
                "Theory {} expects {} parameters, got {}",
                theory_name, theory.params.len(), args.len()
            ));
        }

        let arguments: Vec<(String, String)> = theory.params
            .iter()
            .zip(args.iter())
            .map(|(param, arg)| (param.name.clone(), arg.clone()))
            .collect();

        Ok(ResolvedQueryType {
            theory_name,
            arguments,
        })
    }

    /// Build a base structure for a query by importing elements from param instances.
    fn build_query_base(
        &self,
        resolved: &ResolvedQueryType,
        theory: &Rc<ElaboratedTheory>,
    ) -> Result<(Structure, crate::universe::Universe), String> {
        use crate::core::FunctionDomainInfo;

        let sig = &theory.theory.signature;
        let mut structure = Structure::new(sig.sorts.len());
        let mut universe = crate::universe::Universe::new();

        // Initialize relation storage
        let relation_arities: Vec<usize> = sig.relations
            .iter()
            .map(|rel| rel.domain.arity())
            .collect();
        structure.init_relations(&relation_arities);

        // Track imported UUIDs to avoid duplicates across params
        let mut imported_uuids = std::collections::HashSet::new();
        // Track Luid -> new Slid mapping for importing function values later
        let mut luid_to_new_slid: std::collections::HashMap<crate::id::Luid, Slid> = std::collections::HashMap::new();

        // Import elements from each param instance
        for (param_name, instance_name) in &resolved.arguments {
            let param_entry = self.instances.get(instance_name)
                .ok_or_else(|| format!("Unknown instance: {}", instance_name))?;

            let param_theory = self.theories.get(&param_entry.theory_name)
                .ok_or_else(|| format!("Unknown theory: {}", param_entry.theory_name))?;

            // Import each element from the param instance
            for &slid in param_entry.slid_to_name.keys() {
                let param_sort_id = param_entry.structure.sorts[slid.index()];
                let param_sort_name = &param_theory.theory.signature.sorts[param_sort_id];

                // Try different mappings for the local sort name.
                // The sort might be:
                // 1. param_name/param_sort_name (e.g., "N/P" for a PetriNet param)
                // 2. Just param_sort_name if it already has a prefix (for nested params)
                let local_sort_id = if let Some(id) = sig.lookup_sort(&format!("{}/{}", param_name, param_sort_name)) {
                    id
                } else if let Some(id) = sig.lookup_sort(param_sort_name) {
                    // The sort might already be prefixed from an earlier param in the chain
                    // (e.g., "N/P" in problem0 should map to "N/P" in Solution, not "RP/N/P")
                    id
                } else {
                    // Sort not found - skip this element (might be from a nested instance
                    // that will be imported separately or doesn't map to this theory)
                    continue;
                };

                // Get the existing Luid and its Uuid
                let luid = param_entry.structure.get_luid(slid);
                let uuid = self.store.universe.get(luid)
                    .ok_or_else(|| format!("No Uuid for Luid {:?}", luid))?;

                // Skip if already imported from an earlier param
                if imported_uuids.contains(&uuid) {
                    continue;
                }
                imported_uuids.insert(uuid);

                // Register in our new universe and add element
                let new_luid = universe.intern(uuid);
                let local_slid = structure.add_element_with_luid(new_luid, local_sort_id);
                luid_to_new_slid.insert(luid, local_slid);
            }

            // Import elements from nested structures (e.g., initial_marking, target_marking in ReachabilityProblem)
            for (nested_name, nested_struct) in &param_entry.structure.nested {
                // Nested structure elements have sorts like "initial_marking/token" in the param theory
                // They map to sorts like "RP/initial_marking/token" in the target theory
                for slid_idx in 0..nested_struct.sorts.len() {
                    let slid = crate::id::Slid::from_usize(slid_idx);
                    let _nested_sort_id = nested_struct.sorts[slid_idx];

                    // Get sort name from the nested theory (we don't have it directly, so reconstruct)
                    // The nested structure sorts are indexed locally starting from 0
                    // We need to find the corresponding sort name in the target theory
                    let nested_sort_prefix = format!("{}/{}", param_name, nested_name);

                    // Try to find a sort in the target theory that matches this nested element
                    let local_sort_id = sig.sorts.iter().position(|s| {
                        s.starts_with(&nested_sort_prefix)
                    });

                    if let Some(local_sort_id) = local_sort_id {
                        // Get the Luid and Uuid
                        let luid = nested_struct.get_luid(slid);
                        if let Some(uuid) = self.store.universe.get(luid)
                            && !imported_uuids.contains(&uuid) {
                                imported_uuids.insert(uuid);
                                let new_luid = universe.intern(uuid);
                                let local_slid = structure.add_element_with_luid(new_luid, local_sort_id);
                                luid_to_new_slid.insert(luid, local_slid);
                            }
                    }
                }
            }
        }

        // Initialize function storage
        let domains: Vec<FunctionDomainInfo> = sig.functions
            .iter()
            .map(|func| match &func.domain {
                DerivedSort::Base(id) => FunctionDomainInfo::Base(*id),
                DerivedSort::Product(fields) => {
                    let field_sorts: Vec<usize> = fields
                        .iter()
                        .filter_map(|(_, ds)| match ds {
                            DerivedSort::Base(id) => Some(*id),
                            DerivedSort::Product(_) => None,
                        })
                        .collect();
                    FunctionDomainInfo::Product(field_sorts)
                }
            })
            .collect();
        structure.init_functions_full(&domains);

        // Import function values from param instances
        for (param_name, instance_name) in &resolved.arguments {
            let param_entry = self.instances.get(instance_name).unwrap();
            let param_theory = self.theories.get(&param_entry.theory_name).unwrap();
            let param_sig = &param_theory.theory.signature;

            // For each function in the param theory
            for (param_func_id, param_func) in param_sig.functions.iter().enumerate() {
                // Find the corresponding function in the target theory
                // It should be named "{param_name}/{func_name}"
                let target_func_name = format!("{}/{}", param_name, param_func.name);
                let target_func_id = sig.functions.iter().position(|f| f.name == target_func_name);

                if let Some(target_func_id) = target_func_id {
                    // Copy function values
                    // Iterate over all elements in the domain of the param function
                    if let DerivedSort::Base(domain_sort) = &param_func.domain {
                        // Get all elements of the domain sort in the param instance
                        for (idx, &sort_id) in param_entry.structure.sorts.iter().enumerate() {
                            if sort_id == *domain_sort {
                                let domain_slid = Slid::from_usize(idx);
                                let domain_sort_slid = param_entry.structure.sort_local_id(domain_slid);

                                // Get the function value in the param instance
                                if let Some(codomain_slid) = param_entry.structure.get_function(param_func_id, domain_sort_slid) {
                                    // Map both domain and codomain to new Slids
                                    let domain_luid = param_entry.structure.get_luid(domain_slid);
                                    let codomain_luid = param_entry.structure.get_luid(codomain_slid);

                                    if let (Some(&new_domain_slid), Some(&new_codomain_slid)) =
                                        (luid_to_new_slid.get(&domain_luid), luid_to_new_slid.get(&codomain_luid))
                                    {
                                        // Define the function value in the new structure
                                        let _ = structure.define_function(target_func_id, new_domain_slid, new_codomain_slid);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        Ok((structure, universe))
    }

    /// List all theories (runtime + persisted)
    pub fn list_theories(&self) -> Vec<TheoryInfo> {
        use crate::store::BindingKind;
        use std::collections::HashSet;

        let mut result: Vec<TheoryInfo> = self.theories
            .iter()
            .map(|(name, theory)| TheoryInfo {
                name: name.clone(),
                num_sorts: theory.theory.signature.sorts.len(),
                num_functions: theory.theory.signature.functions.len(),
                num_relations: theory.theory.signature.relations.len(),
                num_axioms: theory.theory.axioms.len(),
            })
            .collect();

        // Add persisted theories that aren't in runtime
        let runtime_names: HashSet<_> = self.theories.keys().cloned().collect();
        for (name, kind, slid) in self.store.list_bindings() {
            if kind == BindingKind::Theory && !runtime_names.contains(&name) {
                // Query the Store for theory structure
                let sorts = self.store.query_theory_sorts(slid);
                let funcs = self.store.query_theory_funcs(slid);
                let rels = self.store.query_theory_rels(slid);
                result.push(TheoryInfo {
                    name,
                    num_sorts: sorts.len(),
                    num_functions: funcs.len(),
                    num_relations: rels.len(),
                    num_axioms: 0,  // TODO: persist axioms
                });
            }
        }

        result
    }

    /// List all instances (runtime + persisted)
    pub fn list_instances(&self) -> Vec<InstanceInfo> {
        use crate::store::BindingKind;
        use std::collections::HashSet;

        let mut result: Vec<InstanceInfo> = self.instances
            .iter()
            .map(|(name, entry)| InstanceInfo {
                name: name.clone(),
                theory_name: entry.theory_name.clone(),
                num_elements: entry.structure.len(),
            })
            .collect();

        // Add persisted instances that aren't in runtime
        let runtime_names: HashSet<_> = self.instances.keys().cloned().collect();
        for (name, kind, _slid) in self.store.list_bindings() {
            if kind == BindingKind::Instance && !runtime_names.contains(&name) {
                result.push(InstanceInfo {
                    name,
                    theory_name: "(persisted)".to_string(),  // Would need query to get
                    num_elements: 0,  // Unknown
                });
            }
        }

        result
    }

    /// Inspect a theory or instance by name
    pub fn inspect(&self, name: &str) -> Option<InspectResult> {
        // Check theories first
        if let Some(theory) = self.theories.get(name) {
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
                instance_fields: theory
                    .theory
                    .signature
                    .instance_fields
                    .iter()
                    .map(|f| (f.name.clone(), f.theory_type.clone()))
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
        if let Some(entry) = self.instances.get(name) {
            let theory = self.theories.get(&entry.theory_name)?;

            // Collect nested instance info
            let nested: Vec<(String, usize)> = entry
                .structure
                .nested
                .iter()
                .map(|(field_name, nested_struct)| {
                    (field_name.clone(), nested_struct.len())
                })
                .collect();

            return Some(InspectResult::Instance(InstanceDetail {
                name: name.to_string(),
                theory_name: entry.theory_name.clone(),
                elements: self.collect_elements(entry, &theory.theory.signature),
                functions: self.collect_function_values(entry, &theory.theory.signature),
                relations: self.collect_relation_tuples(entry, &theory.theory.signature),
                nested,
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
        use crate::core::FunctionColumn;

        let mut result = Vec::new();
        for (func_id, func_sym) in signature.functions.iter().enumerate() {
            if func_id >= entry.structure.functions.len() {
                continue;
            }
            let mut values = Vec::new();

            match &func_sym.domain {
                DerivedSort::Base(domain_sort_id) => {
                    // Check if this is a product codomain function
                    if let FunctionColumn::ProductCodomain { field_columns, field_names, .. } =
                        &entry.structure.functions[func_id]
                    {
                        // Product codomain: format as `domain func = [field1: v1, ...]`
                        for slid_u64 in entry.structure.carriers[*domain_sort_id].iter() {
                            let slid = Slid::from_usize(slid_u64 as usize);
                            let sort_slid = entry.structure.sort_local_id(slid);
                            let idx = sort_slid.index();

                            // Check if all fields are defined for this element
                            let all_defined = field_columns.iter().all(|col| {
                                col.get(idx)
                                    .and_then(|opt| crate::id::get_slid(*opt))
                                    .is_some()
                            });

                            if all_defined {
                                let domain_name = entry
                                    .get_name(slid)
                                    .map(|s| s.to_string())
                                    .unwrap_or_else(|| format!("#{}", slid_u64));

                                let field_strs: Vec<String> = field_names
                                    .iter()
                                    .zip(field_columns.iter())
                                    .map(|(name, col)| {
                                        let codomain_slid = crate::id::get_slid(col[idx]).unwrap();
                                        let codomain_name = entry
                                            .get_name(codomain_slid)
                                            .map(|s| s.to_string())
                                            .unwrap_or_else(|| format!("#{}", codomain_slid));
                                        format!("{}: {}", name, codomain_name)
                                    })
                                    .collect();

                                values.push(format!(
                                    "{} {} = [{}]",
                                    domain_name, func_sym.name, field_strs.join(", ")
                                ));
                            }
                        }
                    } else {
                        // Base codomain: iterate over carrier elements
                        for slid_u64 in entry.structure.carriers[*domain_sort_id].iter() {
                            let slid = Slid::from_usize(slid_u64 as usize);
                            let sort_slid = entry.structure.sort_local_id(slid);
                            if let Some(codomain_slid) =
                                entry.structure.get_function(func_id, sort_slid)
                            {
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
                }
                DerivedSort::Product(fields) => {
                    // Product domain: iterate over defined entries in storage
                    if let FunctionColumn::ProductLocal { storage, .. } =
                        &entry.structure.functions[func_id]
                    {
                        for (tuple_indices, codomain_slid) in storage.iter_defined() {
                            // Map sort-local indices back to Slids for name lookup
                            let tuple_strs: Vec<String> = tuple_indices
                                .iter()
                                .zip(fields.iter())
                                .map(|(&local_idx, (field_name, field_sort))| {
                                    // Get the Slid at this sort-local position
                                    let slid = if let DerivedSort::Base(sort_id) = field_sort {
                                        entry.structure.carriers[*sort_id]
                                            .iter()
                                            .nth(local_idx)
                                            .map(|u| Slid::from_usize(u as usize))
                                    } else {
                                        None
                                    };

                                    let elem_name = slid
                                        .and_then(|s| entry.get_name(s).map(|n| n.to_string()))
                                        .unwrap_or_else(|| format!("#{}", local_idx));

                                    format!("{}: {}", field_name, elem_name)
                                })
                                .collect();

                            let codomain_name = entry
                                .get_name(codomain_slid)
                                .map(|s| s.to_string())
                                .unwrap_or_else(|| format!("#{}", codomain_slid));

                            values.push(format!(
                                "[{}] {} = {}",
                                tuple_strs.join(", "),
                                func_sym.name,
                                codomain_name
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

    /// Collect relation tuples as vectors of element names
    fn collect_relation_tuples(
        &self,
        entry: &InstanceEntry,
        signature: &crate::core::Signature,
    ) -> Vec<(String, Vec<Vec<String>>)> {
        let mut result = Vec::new();

        for (rel_id, rel_sym) in signature.relations.iter().enumerate() {
            if rel_id >= entry.structure.relations.len() {
                continue;
            }

            let relation = &entry.structure.relations[rel_id];
            let mut tuples: Vec<Vec<String>> = Vec::new();

            for tuple in relation.iter() {
                let tuple_names: Vec<String> = tuple
                    .iter()
                    .map(|&slid| {
                        entry
                            .get_name(slid)
                            .map(|s| s.to_string())
                            .unwrap_or_else(|| format!("#{}", slid))
                    })
                    .collect();
                tuples.push(tuple_names);
            }

            if !tuples.is_empty() {
                result.push((rel_sym.name.clone(), tuples));
            }
        }

        result
    }

    /// Execute a query on an instance.
    ///
    /// Returns all elements of the given sort in the instance.
    pub fn query_sort(&self, instance_name: &str, sort_name: &str) -> Result<Vec<String>, String> {
        // Get the instance
        let entry = self.instances.get(instance_name)
            .ok_or_else(|| format!("Instance '{}' not found", instance_name))?;

        // Get the theory
        let theory = self.theories.get(&entry.theory_name)
            .ok_or_else(|| format!("Theory '{}' not found", entry.theory_name))?;

        // Find the sort index
        let sort_idx = theory.theory.signature.sorts
            .iter()
            .position(|s| s == sort_name)
            .ok_or_else(|| format!("Sort '{}' not found in theory '{}'", sort_name, entry.theory_name))?;

        // Use the query backend to scan all elements
        use crate::query::{QueryOp, execute};

        let plan = QueryOp::Scan { sort_idx };
        let result = execute(&plan, &entry.structure);

        // Convert results to element names
        let elements: Vec<String> = result.iter()
            .filter_map(|(tuple, _)| tuple.first())
            .map(|&slid| {
                entry.get_name(slid)
                    .map(|s| s.to_string())
                    .unwrap_or_else(|| format!("#{}", slid))
            })
            .collect();

        Ok(elements)
    }
}

/// Helper to extract theory name from a type expression
///
/// For parameterized types like `ExampleNet Trace`, the theory is the rightmost
/// path element, not the first argument.
fn type_expr_to_theory_name(type_expr: &ast::TypeExpr) -> String {
    use crate::ast::TypeToken;

    // Handle special cases first
    if type_expr.is_sort() {
        return "Sort".to_string();
    }
    if type_expr.is_prop() {
        return "Prop".to_string();
    }

    // For instance types, recurse on the inner type
    if let Some(inner) = type_expr.instance_inner() {
        return type_expr_to_theory_name(&inner);
    }

    // Find the last path token - that's the theory name
    for token in type_expr.tokens.iter().rev() {
        if let TypeToken::Path(path) = token {
            return path.segments.join("/");
        }
    }

    // Fallback for arrows, records, etc.
    if type_expr.tokens.iter().any(|t| matches!(t, TypeToken::Arrow)) {
        return "Arrow".to_string();
    }
    if type_expr.as_record().is_some() {
        return "Record".to_string();
    }

    "Unknown".to_string()
}

/// Convert a type expression to its full string representation.
/// E.g., tokens [Path(ExampleNet), Path(problem0), Path(Solution)] -> "ExampleNet problem0 Solution"
fn type_expr_to_full_string(type_expr: &ast::TypeExpr) -> String {
    use crate::ast::TypeToken;

    let mut parts: Vec<String> = vec![];

    for token in &type_expr.tokens {
        match token {
            TypeToken::Sort => parts.push("Sort".to_string()),
            TypeToken::Prop => parts.push("Prop".to_string()),
            TypeToken::Path(path) => parts.push(path.segments.join("/")),
            TypeToken::Arrow => parts.push("->".to_string()),
            TypeToken::Instance => parts.push("instance".to_string()),
            TypeToken::Record(fields) => {
                let field_strs: Vec<String> = fields
                    .iter()
                    .map(|(name, ty)| format!("{}: {}", name, type_expr_to_full_string(ty)))
                    .collect();
                parts.push(format!("[{}]", field_strs.join(", ")));
            }
        }
    }

    parts.join(" ")
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

/// Resolved query type with theory name and argument bindings.
struct ResolvedQueryType {
    /// The base theory name (e.g., "Solution")
    theory_name: String,
    /// Param bindings: (param_name, instance_name) pairs
    /// e.g., [("N", "ExampleNet"), ("RP", "problem0")]
    arguments: Vec<(String, String)>,
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
    /// Commit current changes with optional message
    Commit(Option<String>),
    /// Show commit history
    History,
    /// Add element to instance: `:add <instance> <element> <sort>`
    Add { instance: String, element: String, sort: String },
    /// Assert relation tuple: `:assert <instance> <relation> <args...>`
    Assert { instance: String, relation: String, args: Vec<String> },
    /// Retract element from instance: `:retract <instance> <element>`
    Retract { instance: String, element: String },
    /// Query instance: `:query <instance> <sort> [filter conditions]`
    Query { instance: String, sort: String },
    /// Explain query plan: `:explain <instance> <sort>`
    Explain { instance: String, sort: String },
    /// Compile query to RelAlgIR: `:compile <instance> <sort>`
    Compile { instance: String, sort: String },
    /// Solve: find an instance of a theory using the geometric logic solver
    /// `:solve <theory> [budget_ms]`
    Solve { theory: String, budget_ms: Option<u64> },
    /// Extend: find extensions of an existing instance to a (larger) theory
    /// `:extend <instance> <theory> [budget_ms]`
    Extend { instance: String, theory: String, budget_ms: Option<u64> },
    /// Chase: run chase algorithm on instance to compute derived relations/functions
    /// `:chase <instance> [max_iterations]`
    Chase { instance: String, max_iterations: Option<usize> },
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
                    Some("theories" | "theory" | "t") => ListTarget::Theories,
                    Some("instances" | "instance" | "i") => ListTarget::Instances,
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
            "commit" | "ci" => {
                // Collect remaining args as message
                let message: Vec<&str> = parts.collect();
                let msg = if let Some(first) = arg {
                    let mut full_msg = first.to_string();
                    for part in message {
                        full_msg.push(' ');
                        full_msg.push_str(part);
                    }
                    Some(full_msg)
                } else {
                    None
                };
                MetaCommand::Commit(msg)
            }
            "history" | "log" => MetaCommand::History,
            "add" => {
                let args: Vec<&str> = std::iter::once(arg).flatten().chain(parts).collect();
                if args.len() >= 3 {
                    MetaCommand::Add {
                        instance: args[0].to_string(),
                        element: args[1].to_string(),
                        sort: args[2].to_string(),
                    }
                } else {
                    MetaCommand::Unknown(":add requires <instance> <element> <sort>".to_string())
                }
            }
            "assert" => {
                let args: Vec<&str> = std::iter::once(arg).flatten().chain(parts).collect();
                if args.len() >= 2 {
                    MetaCommand::Assert {
                        instance: args[0].to_string(),
                        relation: args[1].to_string(),
                        args: args[2..].iter().map(|s| s.to_string()).collect(),
                    }
                } else {
                    MetaCommand::Unknown(":assert requires <instance> <relation> [args...]".to_string())
                }
            }
            "retract" => {
                let args: Vec<&str> = std::iter::once(arg).flatten().chain(parts).collect();
                if args.len() >= 2 {
                    MetaCommand::Retract {
                        instance: args[0].to_string(),
                        element: args[1].to_string(),
                    }
                } else {
                    MetaCommand::Unknown(":retract requires <instance> <element>".to_string())
                }
            }
            "query" => {
                let args: Vec<&str> = std::iter::once(arg).flatten().chain(parts).collect();
                if args.len() >= 2 {
                    MetaCommand::Query {
                        instance: args[0].to_string(),
                        sort: args[1].to_string(),
                    }
                } else {
                    MetaCommand::Unknown(":query requires <instance> <sort>".to_string())
                }
            }
            "explain" => {
                let args: Vec<&str> = std::iter::once(arg).flatten().chain(parts).collect();
                if args.len() >= 2 {
                    MetaCommand::Explain {
                        instance: args[0].to_string(),
                        sort: args[1].to_string(),
                    }
                } else {
                    MetaCommand::Unknown(":explain requires <instance> <sort>".to_string())
                }
            }
            "compile" => {
                let args: Vec<&str> = std::iter::once(arg).flatten().chain(parts).collect();
                if args.len() >= 2 {
                    MetaCommand::Compile {
                        instance: args[0].to_string(),
                        sort: args[1].to_string(),
                    }
                } else {
                    MetaCommand::Unknown(":compile requires <instance> <sort>".to_string())
                }
            }
            "solve" => {
                if let Some(theory_name) = arg {
                    // Optional budget in ms
                    let budget_ms = parts.next().and_then(|s| s.parse().ok());
                    MetaCommand::Solve {
                        theory: theory_name.to_string(),
                        budget_ms,
                    }
                } else {
                    MetaCommand::Unknown(":solve requires <theory> [budget_ms]".to_string())
                }
            }
            "extend" => {
                let args: Vec<&str> = std::iter::once(arg).flatten().chain(parts).collect();
                if args.len() >= 2 {
                    let budget_ms = args.get(2).and_then(|s| s.parse().ok());
                    MetaCommand::Extend {
                        instance: args[0].to_string(),
                        theory: args[1].to_string(),
                        budget_ms,
                    }
                } else {
                    MetaCommand::Unknown(":extend requires <instance> <theory> [budget_ms]".to_string())
                }
            }
            "chase" => {
                if let Some(instance_name) = arg {
                    let max_iterations = parts.next().and_then(|s| s.parse().ok());
                    MetaCommand::Chase {
                        instance: instance_name.to_string(),
                        max_iterations,
                    }
                } else {
                    MetaCommand::Unknown(":chase requires <instance> [max_iterations]".to_string())
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
    Query(QueryResult),
}

/// Result of executing a query
#[derive(Debug)]
pub enum QueryResult {
    /// Found a satisfying instance
    Found {
        query_name: String,
        theory_name: String,
        model: crate::core::Structure,
        time_ms: f64,
    },
    /// No solution exists
    Unsat {
        query_name: String,
        theory_name: String,
        time_ms: f64,
    },
    /// Search incomplete (timeout or other reason)
    Incomplete {
        query_name: String,
        theory_name: String,
        reason: String,
        time_ms: f64,
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
    /// Instance fields: (name, theory_type)
    pub instance_fields: Vec<(String, String)>,
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
    /// Relations: (name, list of tuples-as-element-names)
    pub relations: Vec<(String, Vec<Vec<String>>)>,
    /// Nested instances: (field_name, element_count)
    pub nested: Vec<(String, usize)>,
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

    // Relations
    for (rel_name, tuples) in &detail.relations {
        if !tuples.is_empty() {
            out.push_str(&format!("  // {} ({} tuples):\n", rel_name, tuples.len()));
            for tuple in tuples {
                // Format as [field1: val1, field2: val2] rel_name;
                // For simplicity, show as positional for now
                out.push_str(&format!(
                    "  [{}] {};\n",
                    tuple.join(", "),
                    rel_name
                ));
            }
        }
    }

    // Nested instances
    if !detail.nested.is_empty() {
        out.push_str("  // Nested instances:\n");
        for (field_name, element_count) in &detail.nested {
            out.push_str(&format!("  {} = {{ /* {} elements */ }};\n", field_name, element_count));
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

    for (name, theory_type) in &detail.instance_fields {
        out.push_str(&format!("  {} : {} instance;\n", name, theory_type));
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
