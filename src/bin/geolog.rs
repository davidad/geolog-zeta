//! Geolog REPL - Interactive environment for geometric logic
//!
//! Usage: geolog [workspace]
//!
//! Commands:
//!   :help       - Show help
//!   :quit       - Exit REPL
//!   :list       - List theories and instances
//!   :inspect X  - Show details of theory/instance X
//!   :clear      - Clear screen
//!   :reset      - Reset all state

use std::fs;
use std::path::PathBuf;

use rustyline::error::ReadlineError;
use rustyline::history::DefaultHistory;
use rustyline::{Config, Editor};

use geolog::id::NumericId;
use geolog::repl::{
    ExecuteResult, InputResult, InspectResult, ListTarget, MetaCommand, QueryResult, ReplState,
    format_instance_detail, format_theory_detail,
};

const VERSION: &str = env!("CARGO_PKG_VERSION");
const PROMPT: &str = "geolog> ";
const CONTINUATION: &str = "......  ";

/// Parse command line arguments.
///
/// Usage: geolog [-d <workspace>] [source_files...]
///
/// Options:
///   -d, --dir <path>   Use <path> as the workspace directory for persistence
///   -h, --help         Show help and exit
///   -v, --version      Show version and exit
///
/// Returns (workspace_path, source_files)
fn parse_args(args: &[String]) -> (Option<PathBuf>, Vec<PathBuf>) {
    let mut workspace_path = None;
    let mut source_files = Vec::new();
    let mut i = 0;

    while i < args.len() {
        let arg = &args[i];
        match arg.as_str() {
            "-d" | "--dir" => {
                if i + 1 < args.len() {
                    workspace_path = Some(PathBuf::from(&args[i + 1]));
                    i += 2;
                } else {
                    eprintln!("Error: -d requires a path argument");
                    std::process::exit(1);
                }
            }
            "-h" | "--help" => {
                println!("geolog v{} - Geometric Logic REPL", VERSION);
                println!();
                println!("Usage: geolog [OPTIONS] [source_files...]");
                println!();
                println!("Options:");
                println!("  -d, --dir <path>   Use <path> as workspace directory for persistence");
                println!("  -h, --help         Show this help message");
                println!("  -v, --version      Show version");
                println!();
                println!("Examples:");
                println!("  geolog                     Start REPL (in-memory, no persistence)");
                println!("  geolog -d ./myproject      Start REPL with workspace persistence");
                println!("  geolog file.geolog         Load file.geolog on startup");
                println!("  geolog -d ./proj f.geolog  Load file into persistent workspace");
                std::process::exit(0);
            }
            "-v" | "--version" => {
                println!("geolog v{}", VERSION);
                std::process::exit(0);
            }
            _ if arg.starts_with('-') => {
                eprintln!("Error: Unknown option '{}'", arg);
                eprintln!("Try 'geolog --help' for usage information");
                std::process::exit(1);
            }
            _ => {
                // Positional argument - treat as source file
                source_files.push(PathBuf::from(arg));
                i += 1;
            }
        }
    }

    (workspace_path, source_files)
}

fn main() {
    // Parse command line args
    let args: Vec<String> = std::env::args().skip(1).collect();
    let (workspace_path, source_files) = parse_args(&args);

    // Print banner
    println!("geolog v{} - Geometric Logic REPL", VERSION);
    println!("Type :help for help, :quit to exit\n");

    // Initialize state
    let mut state = if let Some(ref path) = workspace_path {
        println!("Workspace: {}", path.display());
        ReplState::with_path(path)
    } else {
        ReplState::new()
    };

    // Load any source files specified on command line
    for source_file in &source_files {
        handle_source(&mut state, source_file);
    }

    // Set up rustyline
    let config = Config::builder().auto_add_history(true).build();
    let mut rl: Editor<(), DefaultHistory> =
        Editor::with_config(config).expect("Failed to create editor");

    // Try to load history
    let history_path = dirs_history_path();
    if let Some(ref path) = history_path {
        let _ = rl.load_history(path);
    }

    // Main REPL loop
    loop {
        let prompt = if state.input_buffer.is_empty() {
            PROMPT
        } else {
            CONTINUATION
        };

        match rl.readline(prompt) {
            Ok(line) => {
                match state.process_line(&line) {
                    InputResult::MetaCommand(cmd) => {
                        if !handle_command(&mut state, cmd) {
                            break; // :quit
                        }
                    }
                    InputResult::GeologInput(source) => {
                        handle_geolog(&mut state, &source);
                    }
                    InputResult::Incomplete => {
                        // Continue reading
                    }
                    InputResult::Empty => {
                        // Nothing to do
                    }
                }
            }
            Err(ReadlineError::Interrupted) => {
                // Ctrl-C - clear current buffer
                if !state.input_buffer.is_empty() {
                    state.input_buffer.clear();
                    state.bracket_depth = 0;
                    println!("^C");
                } else {
                    println!("Use :quit or Ctrl-D to exit");
                }
            }
            Err(ReadlineError::Eof) => {
                // Ctrl-D - submit buffer or quit
                if let Some(source) = state.force_submit() {
                    handle_geolog(&mut state, &source);
                } else {
                    // Save store before quitting
                    if let Err(e) = state.store.save() {
                        eprintln!("Warning: Failed to save store: {}", e);
                    }
                    println!("\nGoodbye!");
                    break;
                }
            }
            Err(err) => {
                eprintln!("Error: {:?}", err);
                break;
            }
        }
    }

    // Save history
    if let Some(ref path) = history_path {
        if let Some(parent) = path.parent() {
            let _ = fs::create_dir_all(parent);
        }
        let _ = rl.save_history(path);
    }
}

/// Handle a meta-command. Returns false if we should exit.
fn handle_command(state: &mut ReplState, cmd: MetaCommand) -> bool {
    match cmd {
        MetaCommand::Help(topic) => {
            print_help(topic.as_deref());
        }
        MetaCommand::Quit => {
            // Save store before quitting
            if let Err(e) = state.store.save() {
                eprintln!("Warning: Failed to save store: {}", e);
            }
            println!("Goodbye!");
            return false;
        }
        MetaCommand::List(target) => {
            handle_list(state, target);
        }
        MetaCommand::Inspect(name) => {
            handle_inspect(state, &name);
        }
        MetaCommand::Clear => {
            // ANSI escape to clear screen
            print!("\x1B[2J\x1B[H");
        }
        MetaCommand::Reset => {
            state.reset();
            println!("State reset.");
        }
        MetaCommand::Source(path) => {
            handle_source(state, &path);
        }
        MetaCommand::Commit(msg) => {
            handle_commit(state, msg.as_deref());
        }
        MetaCommand::History => {
            handle_history(state);
        }
        MetaCommand::Add { instance, element, sort } => {
            handle_add(state, &instance, &element, &sort);
        }
        MetaCommand::Assert { instance, relation, args } => {
            handle_assert(state, &instance, &relation, &args);
        }
        MetaCommand::Retract { instance, element } => {
            handle_retract(state, &instance, &element);
        }
        MetaCommand::Query { instance, sort } => {
            handle_query(state, &instance, &sort);
        }
        MetaCommand::Explain { instance, sort } => {
            handle_explain(state, &instance, &sort);
        }
        MetaCommand::Compile { instance, sort } => {
            handle_compile(state, &instance, &sort);
        }
        MetaCommand::Solve { theory, budget_ms } => {
            handle_solve(state, &theory, budget_ms);
        }
        MetaCommand::Extend { instance, theory, budget_ms } => {
            handle_extend(state, &instance, &theory, budget_ms);
        }
        MetaCommand::Chase { instance, max_iterations } => {
            handle_chase(state, &instance, max_iterations);
        }
        MetaCommand::Unknown(msg) => {
            eprintln!("Error: {}", msg);
            eprintln!("Type :help for available commands");
        }
    }
    true
}

/// Handle geolog source input
fn handle_geolog(state: &mut ReplState, source: &str) {
    match state.execute_geolog(source) {
        Ok(results) => {
            for result in results {
                match result {
                    ExecuteResult::Namespace(name) => {
                        println!("Namespace: {}", name);
                    }
                    ExecuteResult::Theory {
                        name,
                        num_sorts,
                        num_functions,
                        num_relations,
                        num_axioms,
                    } => {
                        let mut parts = vec![format!("{} sorts", num_sorts)];
                        if num_functions > 0 {
                            parts.push(format!("{} functions", num_functions));
                        }
                        if num_relations > 0 {
                            parts.push(format!("{} relations", num_relations));
                        }
                        if num_axioms > 0 {
                            parts.push(format!("{} axioms", num_axioms));
                        }
                        println!("Defined theory {} ({})", name, parts.join(", "));
                    }
                    ExecuteResult::Instance {
                        name,
                        theory_name,
                        num_elements,
                    } => {
                        println!(
                            "Defined instance {} : {} ({} elements)",
                            name, theory_name, num_elements
                        );
                    }
                    ExecuteResult::Query(result) => {
                        handle_query_result(state, result);
                    }
                }
            }
        }
        Err(e) => {
            eprintln!("Error: {}", e);
        }
    }
}

/// Print help message
fn print_help(topic: Option<&str>) {
    match topic {
        None => {
            println!("Geolog REPL Commands:");
            println!();
            println!("  :help [topic]    Show help (topics: syntax, examples)");
            println!("  :quit            Exit the REPL");
            println!(
                "  :list [target]   List theories/instances (target: theories, instances, all)"
            );
            println!("  :inspect <name>  Show details of a theory or instance");
            println!("  :source <file>   Load and execute a geolog file");
            println!("  :clear           Clear the screen");
            println!("  :reset           Reset all state");
            println!();
            println!("Version Control:");
            println!("  :commit [msg]    Commit current changes");
            println!("  :history         Show commit history");
            println!();
            println!("Instance Mutation:");
            println!("  :add <inst> <elem> <sort>   Add element to instance");
            println!("  :assert <inst> <rel> [args] Assert relation tuple");
            println!("  :retract <inst> <elem>      Retract element from instance");
            println!();
            println!("Query:");
            println!("  :query <inst> <sort>        List all elements of a sort");
            println!("  :explain <inst> <sort>      Show query execution plan");
            println!("  :compile <inst> <sort>      Show RelAlgIR compilation");
            println!("  :chase <inst> [max_iter]    Run chase on instance axioms");
            println!();
            println!("Solver:");
            println!("  :solve <theory> [budget_ms]          Find model of theory from scratch");
            println!("  :extend <inst> <theory> [budget_ms]  Find extension of instance to theory");
            println!();
            println!("Enter geolog definitions directly (theories, instances).");
            println!("Multi-line input is supported - brackets are matched automatically.");
        }
        Some("syntax") => {
            println!("Geolog Syntax:");
            println!();
            println!("  theory Name {{");
            println!("    Sort1 : Sort;");
            println!("    Sort2 : Sort;");
            println!("    func : Sort1 -> Sort2;");
            println!("  }}");
            println!();
            println!("  instance Name : Theory = {{");
            println!("    elem1 : Sort1;");
            println!("    elem2 : Sort2;");
            println!("    elem1 func = elem2;");
            println!("  }}");
        }
        Some("examples") => {
            println!("Examples:");
            println!();
            println!("  theory Graph {{");
            println!("    V : Sort;");
            println!("    E : Sort;");
            println!("    src : E -> V;");
            println!("    tgt : E -> V;");
            println!("  }}");
            println!();
            println!("  instance Triangle : Graph = {{");
            println!("    a : V; b : V; c : V;");
            println!("    ab : E; ab src = a; ab tgt = b;");
            println!("    bc : E; bc src = b; bc tgt = c;");
            println!("    ca : E; ca src = c; ca tgt = a;");
            println!("  }}");
        }
        Some(other) => {
            println!("Unknown help topic: {}", other);
            println!("Available topics: syntax, examples");
        }
    }
}

/// Handle :list command
fn handle_list(state: &ReplState, target: ListTarget) {
    match target {
        ListTarget::Theories | ListTarget::All => {
            let theories = state.list_theories();
            if theories.is_empty() {
                println!("No theories defined.");
            } else {
                println!("Theories:");
                for t in theories {
                    let mut parts = vec![format!("{} sorts", t.num_sorts)];
                    if t.num_functions > 0 {
                        parts.push(format!("{} functions", t.num_functions));
                    }
                    if t.num_relations > 0 {
                        parts.push(format!("{} relations", t.num_relations));
                    }
                    if t.num_axioms > 0 {
                        parts.push(format!("{} axioms", t.num_axioms));
                    }
                    println!("  {} ({})", t.name, parts.join(", "));
                }
            }
        }
        ListTarget::Instances => {}
    }

    match target {
        ListTarget::Instances | ListTarget::All => {
            let instances = state.list_instances();
            if instances.is_empty() {
                if matches!(target, ListTarget::Instances) {
                    println!("No instances defined.");
                }
            } else {
                println!("Instances:");
                for i in instances {
                    println!(
                        "  {} : {} ({} elements)",
                        i.name, i.theory_name, i.num_elements
                    );
                }
            }
        }
        ListTarget::Theories => {}
    }
}

/// Handle :inspect command
fn handle_inspect(state: &ReplState, name: &str) {
    match state.inspect(name) {
        Some(InspectResult::Theory(detail)) => {
            println!("{}", format_theory_detail(&detail));
        }
        Some(InspectResult::Instance(detail)) => {
            println!("{}", format_instance_detail(&detail));
        }
        None => {
            eprintln!("Not found: {}", name);
            eprintln!("Use :list to see available theories and instances");
        }
    }
}

/// Handle :source command
fn handle_source(state: &mut ReplState, path: &PathBuf) {
    match fs::read_to_string(path) {
        Ok(source) => {
            println!("Loading {}...", path.display());
            handle_geolog(state, &source);
        }
        Err(e) => {
            eprintln!("Error reading {}: {}", path.display(), e);
        }
    }
}

/// Handle :commit command
fn handle_commit(state: &mut ReplState, message: Option<&str>) {
    if !state.is_dirty() {
        println!("Nothing to commit.");
        return;
    }

    match state.commit(message) {
        Ok(commit_slid) => {
            let msg = message.unwrap_or("(no message)");
            println!("Committed: {} (commit #{})", msg, commit_slid);
        }
        Err(e) => {
            eprintln!("Commit failed: {}", e);
        }
    }
}

/// Handle :history command
fn handle_history(state: &ReplState) {
    let history = state.commit_history();
    if history.is_empty() {
        println!("No commits yet.");
        return;
    }

    println!("Commit history ({} commits):", history.len());
    for (i, commit_slid) in history.iter().enumerate() {
        let marker = if Some(*commit_slid) == state.store.head {
            " <- HEAD"
        } else {
            ""
        };
        println!("  {}. commit #{}{}", i + 1, commit_slid, marker);
    }
}

/// Handle :add command
fn handle_add(state: &mut ReplState, instance_name: &str, element_name: &str, sort_name: &str) {
    // Look up the instance in the Store
    let Some((instance_slid, _)) = state.store.resolve_name(instance_name) else {
        eprintln!("Instance '{}' not found", instance_name);
        return;
    };

    // Look up the sort in the Store
    // For now, we use a simple name-based lookup
    // In full implementation, we'd look up the sort from the theory
    let sort_slid = match state.store.resolve_name(sort_name) {
        Some((slid, _)) => slid,
        None => {
            // Try to find sort in the theory
            eprintln!(
                "Sort '{}' not found. Note: Full sort lookup requires querying the theory.",
                sort_name
            );
            eprintln!("This feature is partially implemented pending query engine (geolog-7tt).");
            return;
        }
    };

    match state.store.add_elem(instance_slid, sort_slid, element_name) {
        Ok(elem_slid) => {
            println!(
                "Added element '{}' of sort '{}' to instance '{}' (elem #{})",
                element_name, sort_name, instance_name, elem_slid
            );
        }
        Err(e) => {
            eprintln!("Failed to add element: {}", e);
        }
    }
}

/// Handle :assert command
fn handle_assert(state: &mut ReplState, instance_name: &str, relation_name: &str, args: &[String]) {
    use geolog::core::RelationStorage;

    // Get the instance entry
    let entry = match state.instances.get_mut(instance_name) {
        Some(e) => e,
        None => {
            eprintln!("Instance '{}' not found", instance_name);
            return;
        }
    };

    // Get the theory to look up the relation
    let theory = match state.theories.get(&entry.theory_name) {
        Some(t) => t.clone(),
        None => {
            eprintln!("Theory '{}' not found", entry.theory_name);
            return;
        }
    };

    // Find the relation by name
    let sig = &theory.theory.signature;
    let rel_id = match sig.relations.iter().position(|r| r.name == relation_name) {
        Some(id) => id,
        None => {
            eprintln!(
                "Relation '{}' not found in theory '{}'",
                relation_name, entry.theory_name
            );
            eprintln!("Available relations: {:?}", sig.relations.iter().map(|r| &r.name).collect::<Vec<_>>());
            return;
        }
    };

    let rel = &sig.relations[rel_id];

    // Resolve argument elements by name from the instance's element_names map
    let mut arg_slids = Vec::new();
    for arg_name in args {
        if let Some(slid) = entry.element_names.get(arg_name) {
            arg_slids.push(*slid);
        } else {
            eprintln!("Element '{}' not found in instance '{}'", arg_name, instance_name);
            eprintln!("Available elements: {:?}", entry.element_names.keys().collect::<Vec<_>>());
            return;
        }
    }

    // Check arity matches (for product domains, flatten the field count)
    let expected_arity = match &rel.domain {
        geolog::core::DerivedSort::Base(_) => 1,
        geolog::core::DerivedSort::Product(fields) => fields.len(),
    };

    if arg_slids.len() != expected_arity {
        eprintln!(
            "Relation '{}' expects {} argument(s), got {}",
            relation_name, expected_arity, arg_slids.len()
        );
        return;
    }

    // Add the tuple to the relation
    if entry.structure.relations.len() <= rel_id {
        eprintln!("Relation storage not initialized for relation {}", rel_id);
        return;
    }

    let already_present = entry.structure.relations[rel_id].contains(&arg_slids);
    if already_present {
        println!("Tuple already present in relation '{}'", relation_name);
        return;
    }

    entry.structure.relations[rel_id].insert(arg_slids.clone());

    let arg_names: Vec<_> = args.to_vec();
    println!(
        "Asserted {}({}) in instance '{}'",
        relation_name, arg_names.join(", "), instance_name
    );
}

/// Handle :retract command
fn handle_retract(state: &mut ReplState, instance_name: &str, element_name: &str) {
    // Look up the instance
    let Some((instance_slid, _)) = state.store.resolve_name(instance_name) else {
        eprintln!("Instance '{}' not found", instance_name);
        return;
    };

    // Look up the element
    let Some((elem_slid, _)) = state.store.resolve_name(element_name) else {
        eprintln!("Element '{}' not found", element_name);
        return;
    };

    match state.store.retract_elem(instance_slid, elem_slid) {
        Ok(retract_slid) => {
            println!(
                "Retracted element '{}' from instance '{}' (retraction #{})",
                element_name, instance_name, retract_slid
            );
        }
        Err(e) => {
            eprintln!("Failed to retract element: {}", e);
        }
    }
}

/// Handle :query command
fn handle_query(state: &ReplState, instance_name: &str, sort_name: &str) {
    match state.query_sort(instance_name, sort_name) {
        Ok(elements) => {
            if elements.is_empty() {
                println!("No elements of sort '{}' in instance '{}'", sort_name, instance_name);
            } else {
                println!("Elements of {} in {}:", sort_name, instance_name);
                for elem in elements {
                    println!("  {}", elem);
                }
            }
        }
        Err(e) => {
            eprintln!("Query error: {}", e);
        }
    }
}

/// Handle :explain command - show query execution plan
fn handle_explain(state: &ReplState, instance_name: &str, sort_name: &str) {
    use geolog::query::QueryOp;

    // Get the instance
    let entry = match state.instances.get(instance_name) {
        Some(e) => e,
        None => {
            eprintln!("Instance '{}' not found", instance_name);
            return;
        }
    };

    // Get the theory
    let theory = match state.theories.get(&entry.theory_name) {
        Some(t) => t,
        None => {
            eprintln!("Theory '{}' not found", entry.theory_name);
            return;
        }
    };

    // Find the sort index
    let sort_idx = match theory.theory.signature.sorts.iter().position(|s| s == sort_name) {
        Some(idx) => idx,
        None => {
            eprintln!(
                "Sort '{}' not found in theory '{}'",
                sort_name, entry.theory_name
            );
            return;
        }
    };

    // Build the query plan (same as query_sort in repl.rs)
    let plan = QueryOp::Scan { sort_idx };

    // Display the plan using the Display impl
    println!("Query plan for ':query {} {}':", instance_name, sort_name);
    println!();
    println!("{}", plan);
    println!();
    println!("Sort: {} (index {})", sort_name, sort_idx);
    println!("Instance: {} (theory: {})", instance_name, entry.theory_name);
}

/// Handle :compile command - compile query to RelAlgIR instance
fn handle_compile(state: &mut ReplState, instance_name: &str, sort_name: &str) {
    use geolog::query::{to_relalg::compile_to_relalg, QueryOp};
    use geolog::universe::Universe;

    // Get the instance
    let entry = match state.instances.get(instance_name) {
        Some(e) => e,
        None => {
            eprintln!("Instance '{}' not found", instance_name);
            return;
        }
    };

    // Get the theory
    let theory = match state.theories.get(&entry.theory_name) {
        Some(t) => t,
        None => {
            eprintln!("Theory '{}' not found", entry.theory_name);
            return;
        }
    };

    // Find the sort index
    let sort_idx = match theory.theory.signature.sorts.iter().position(|s| s == sort_name) {
        Some(idx) => idx,
        None => {
            eprintln!(
                "Sort '{}' not found in theory '{}'",
                sort_name, entry.theory_name
            );
            return;
        }
    };

    // Check if RelAlgIR theory is loaded
    let relalg_theory = match state.theories.get("RelAlgIR") {
        Some(t) => t.clone(),
        None => {
            eprintln!("RelAlgIR theory not loaded. Loading it now...");
            // Try to load it
            let meta_content = std::fs::read_to_string("theories/GeologMeta.geolog")
                .unwrap_or_else(|_| {
                    eprintln!("Could not read theories/GeologMeta.geolog");
                    String::new()
                });
            let ir_content = std::fs::read_to_string("theories/RelAlgIR.geolog")
                .unwrap_or_else(|_| {
                    eprintln!("Could not read theories/RelAlgIR.geolog");
                    String::new()
                });

            if meta_content.is_empty() || ir_content.is_empty() {
                return;
            }

            if let Err(e) = state.execute_geolog(&meta_content) {
                eprintln!("Failed to load GeologMeta: {}", e);
                return;
            }
            if let Err(e) = state.execute_geolog(&ir_content) {
                eprintln!("Failed to load RelAlgIR: {}", e);
                return;
            }

            state.theories.get("RelAlgIR").unwrap().clone()
        }
    };

    // Build the query plan
    let plan = QueryOp::Scan { sort_idx };

    // Compile to RelAlgIR
    let mut universe = Universe::new();
    match compile_to_relalg(&plan, &relalg_theory, &mut universe) {
        Ok(instance) => {
            println!("RelAlgIR compilation for ':query {} {}':", instance_name, sort_name);
            println!();
            println!("QueryOp plan:");
            println!("{}", plan);
            println!();
            println!("Compiled to RelAlgIR instance:");
            println!("  Elements: {}", instance.structure.len());
            println!("  Output wire: {:?}", instance.output_wire);
            println!();

            // Group elements by sort and show with sort names
            let sig = &relalg_theory.theory.signature;
            println!("Elements by sort:");
            for (sort_idx, sort_name) in sig.sorts.iter().enumerate() {
                let count = instance.structure.carrier_size(sort_idx);
                if count > 0 {
                    println!("  {}: {} element(s)", sort_name, count);
                }
            }
            println!();

            // Show named elements with their sorts
            println!("Named elements:");
            for (slid, name) in instance.names.iter() {
                let sort_idx = instance.structure.sorts[slid.index()];
                let sort_name = &sig.sorts[sort_idx];
                println!("  {} : {} = {:?}", name, sort_name, slid);
            }
        }
        Err(e) => {
            eprintln!("Failed to compile query to RelAlgIR: {}", e);
        }
    }
}

/// Handle :solve command - find a model of a theory from scratch
fn handle_solve(state: &ReplState, theory_name: &str, budget_ms: Option<u64>) {
    use geolog::solver::{solve, Budget, EnumerationResult};

    // Look up the theory
    let theory = match state.theories.get(theory_name) {
        Some(t) => t.clone(),
        None => {
            eprintln!("Theory '{}' not found", theory_name);
            eprintln!("Use :list theories to see available theories");
            return;
        }
    };

    println!("Solving theory '{}'...", theory_name);
    let sig = &theory.theory.signature;
    println!(
        "  {} sorts, {} functions, {} relations, {} axioms",
        sig.sorts.len(),
        sig.functions.len(),
        sig.relations.len(),
        theory.theory.axioms.len()
    );

    // Use unified solver API
    let budget = Budget::new(budget_ms.unwrap_or(5000), 10000);
    let result = solve(theory.clone(), budget);

    // Report result
    match result {
        EnumerationResult::Found { model, time_ms } => {
            println!("✓ SOLVED in {:.2}ms", time_ms);
            print_witness_structure(&model, sig);
        }
        EnumerationResult::Unsat { time_ms } => {
            println!("✗ UNSAT in {:.2}ms", time_ms);
            println!("  The theory has no models (derives False).");
        }
        EnumerationResult::Incomplete { time_ms, reason, .. } => {
            println!("◯ INCOMPLETE after {:.2}ms", time_ms);
            println!("  {}", reason);
            println!("  Try increasing the budget: :solve {} <budget_ms>", theory_name);
        }
    }
}

/// Print a witness structure (model) to stdout
fn print_witness_structure(model: &geolog::core::Structure, sig: &geolog::core::Signature) {
    use geolog::core::RelationStorage;
    use geolog::id::NumericId;

    let total_elements: usize = (0..sig.sorts.len())
        .map(|s| model.carrier_size(s))
        .sum();

    if total_elements == 0 {
        println!("\nWitness: empty structure (trivial model)");
    } else {
        println!("\nWitness structure:");
        // Show sorts with elements
        for (sort_id, sort_name) in sig.sorts.iter().enumerate() {
            let size = model.carrier_size(sort_id);
            if size > 0 {
                if size <= 10 {
                    let ids: Vec<String> = (0..size).map(|i| format!("#{}", i)).collect();
                    println!("  {}: {{ {} }}", sort_name, ids.join(", "));
                } else {
                    println!("  {}: {} element(s)", sort_name, size);
                }
            }
        }
        // Show relations with tuples
        for (rel_id, rel) in sig.relations.iter().enumerate() {
            if rel_id < model.relations.len() {
                let rel_storage = &model.relations[rel_id];
                let tuple_count = rel_storage.len();
                if tuple_count > 0 {
                    if tuple_count <= 10 {
                        let tuples: Vec<String> = rel_storage
                            .iter()
                            .map(|t| {
                                let coords: Vec<String> =
                                    t.iter().map(|s| format!("#{}", s.index())).collect();
                                format!("({})", coords.join(", "))
                            })
                            .collect();
                        println!("  {}: {{ {} }}", rel.name, tuples.join(", "));
                    } else {
                        println!("  {}: {} tuple(s)", rel.name, tuple_count);
                    }
                }
            }
        }
    }
}

/// Handle :extend command - find extensions of an existing instance to a theory
///
/// This uses the unified model enumeration API: `query(base, theory, budget)` finds
/// models of `theory` that extend `base`. This is the unified generalization of
/// `:solve` (where base is empty) and "find models extending M".
fn handle_extend(state: &ReplState, instance_name: &str, theory_name: &str, budget_ms: Option<u64>) {
    use geolog::solver::{query, Budget, EnumerationResult};
    use geolog::universe::Universe;

    // Look up the base instance
    let base_entry = match state.instances.get(instance_name) {
        Some(entry) => entry,
        None => {
            eprintln!("Instance '{}' not found", instance_name);
            eprintln!("Use :list instances to see available instances");
            return;
        }
    };

    // Look up the extension theory
    let theory = match state.theories.get(theory_name) {
        Some(t) => t.clone(),
        None => {
            eprintln!("Theory '{}' not found", theory_name);
            eprintln!("Use :list theories to see available theories");
            return;
        }
    };

    println!("Extending instance '{}' to theory '{}'...", instance_name, theory_name);
    let sig = &theory.theory.signature;
    println!(
        "  Base: {} (theory {})",
        instance_name, base_entry.theory_name
    );
    println!(
        "  Target: {} sorts, {} functions, {} relations, {} axioms",
        sig.sorts.len(),
        sig.functions.len(),
        sig.relations.len(),
        theory.theory.axioms.len()
    );

    // Clone base structure and create a fresh universe for the extension
    // (The solver will allocate new elements as needed)
    let base_structure = base_entry.structure.clone();
    let universe = Universe::new(); // Fresh universe for new allocations

    // Use unified query API
    let budget = Budget::new(budget_ms.unwrap_or(5000), 10000);
    let result = query(base_structure, universe, theory.clone(), budget);

    // Report result
    match result {
        EnumerationResult::Found { model, time_ms } => {
            println!("✓ EXTENDED in {:.2}ms", time_ms);
            print_witness_structure(&model, sig);
        }
        EnumerationResult::Unsat { time_ms } => {
            println!("✗ NO EXTENSION EXISTS in {:.2}ms", time_ms);
            println!("  The base instance cannot be extended to satisfy '{}'.", theory_name);
        }
        EnumerationResult::Incomplete { time_ms, reason, .. } => {
            println!("◯ INCOMPLETE after {:.2}ms", time_ms);
            println!("  {}", reason);
            println!("  Try increasing the budget: :extend {} {} <budget_ms>", instance_name, theory_name);
        }
    }
}

/// Handle :chase command - run chase algorithm on instance's theory axioms
fn handle_chase(state: &mut ReplState, instance_name: &str, max_iterations: Option<usize>) {
    use geolog::core::RelationStorage;
    use geolog::query::chase::chase_fixpoint;

    // Get the instance
    let entry = match state.instances.get_mut(instance_name) {
        Some(e) => e,
        None => {
            eprintln!("Instance '{}' not found", instance_name);
            return;
        }
    };

    // Get the theory
    let theory = match state.theories.get(&entry.theory_name) {
        Some(t) => t.clone(),
        None => {
            eprintln!("Theory '{}' not found", entry.theory_name);
            return;
        }
    };

    let sig = &theory.theory.signature;
    let axioms = &theory.theory.axioms;

    if axioms.is_empty() {
        println!("Theory '{}' has no axioms to chase.", entry.theory_name);
        return;
    }

    println!("Running chase on instance '{}' (theory '{}')...", instance_name, entry.theory_name);
    println!("  {} axiom(s) to process", axioms.len());

    // Snapshot relation tuple counts before chase
    let tuple_counts_before: Vec<usize> = entry.structure.relations
        .iter()
        .map(|r| r.len())
        .collect();

    // Run the chase (tensor-backed: handles existentials in premises, etc.)
    let max_iter = max_iterations.unwrap_or(100);
    let start = std::time::Instant::now();

    match chase_fixpoint(axioms, &mut entry.structure, &mut state.store.universe, sig, max_iter) {
        Ok(iterations) => {
            let elapsed = start.elapsed();
            println!("✓ Chase completed in {} iterations ({:.2}ms)", iterations, elapsed.as_secs_f64() * 1000.0);
            println!("\nStructure after chase:");
            print_structure_summary(&entry.structure, sig);

            // Check if any new tuples were added
            let tuple_counts_after: Vec<usize> = entry.structure.relations
                .iter()
                .map(|r| r.len())
                .collect();
            let tuples_added = tuple_counts_before.iter()
                .zip(tuple_counts_after.iter())
                .any(|(before, after)| after > before);

            // Save info needed for persistence before dropping entry borrow
            let theory_name_owned = entry.theory_name.clone();

            if tuples_added {
                // Persist the chase results via columnar batches
                // Note: This persists ALL current tuples, not just the delta.
                // A more sophisticated implementation would track the delta.
                if let Err(e) = persist_chase_results(
                    state,
                    instance_name,
                    &theory_name_owned,
                ) {
                    eprintln!("Warning: Failed to persist chase results: {}", e);
                } else {
                    println!("Chase results persisted to store.");
                }
            }
        }
        Err(e) => {
            eprintln!("✗ Chase error: {}", e);
        }
    }
}

/// Persist chase results (relation tuples) to columnar batches as IDB data.
///
/// IDB batches are persisted locally but NOT transmitted over the wire.
/// Recipients recompute IDB by running the chase on received EDB patches.
fn persist_chase_results(
    state: &mut ReplState,
    instance_name: &str,
    theory_name: &str,
) -> Result<(), String> {
    use geolog::core::RelationStorage;
    use geolog::id::{Slid, Uuid};
    use geolog::store::columnar::{InstanceDataBatch, RelationTupleBatch};

    let entry = state.instances.get(instance_name).ok_or("Instance not found")?;
    let structure = &entry.structure;

    // Resolve the instance in the Store
    let (instance_slid, _) = state.store.resolve_name(instance_name)
        .ok_or_else(|| format!("Instance '{}' not found in store", instance_name))?;

    // Get theory to map relation indices to Slids
    let (theory_slid, _) = state.store.resolve_name(theory_name)
        .ok_or_else(|| format!("Theory '{}' not found in store", theory_name))?;

    let rel_infos = state.store.query_theory_rels(theory_slid);

    // Build mapping from relation index to Rel UUID
    let rel_idx_to_uuid: std::collections::HashMap<usize, Uuid> = rel_infos
        .iter()
        .enumerate()
        .map(|(idx, info)| (idx, state.store.get_element_uuid(info.slid)))
        .collect();

    // Build mapping from Structure Slid to element UUID
    // We need to find the Elem in GeologMeta that corresponds to each Structure element
    let elem_infos = state.store.query_instance_elems(instance_slid);
    let mut struct_slid_to_uuid: std::collections::HashMap<Slid, Uuid> = std::collections::HashMap::new();

    // Map element names to UUIDs
    for info in &elem_infos {
        // Try to find the structure Slid by name
        if let Some(&struct_slid) = entry.slid_to_name.iter()
            .find(|(_, name)| *name == &info.name)
            .map(|(slid, _)| slid)
        {
            struct_slid_to_uuid.insert(struct_slid, state.store.get_element_uuid(info.slid));
        }
    }

    // For chase-created elements that might not have names in slid_to_name,
    // use the structure's UUID mapping
    for slid_u64 in structure.luids.iter().map(|_| 0).enumerate().map(|(i, _)| i) {
        let slid = Slid::from_usize(slid_u64);
        if !struct_slid_to_uuid.contains_key(&slid)
            && let Some(uuid) = structure.get_uuid(slid, &state.store.universe) {
                struct_slid_to_uuid.insert(slid, uuid);
            }
    }

    // Get instance UUID
    let instance_uuid = state.store.get_element_uuid(instance_slid);

    // Build columnar batch as IDB (chase-derived, not wire-transmittable)
    let mut batch = InstanceDataBatch::new_idb();

    for (rel_idx, relation) in structure.relations.iter().enumerate() {
        let rel_uuid = match rel_idx_to_uuid.get(&rel_idx) {
            Some(u) => *u,
            None => continue,
        };

        if relation.is_empty() {
            continue;
        }

        let arity = rel_infos.get(rel_idx).map(|r| r.domain.arity()).unwrap_or(1);
        let field_ids: Vec<Uuid> = (0..arity).map(|_| Uuid::nil()).collect();

        let mut rel_batch = RelationTupleBatch::new(instance_uuid, rel_uuid, field_ids);

        for tuple in relation.iter() {
            let uuid_tuple: Vec<Uuid> = tuple
                .iter()
                .filter_map(|struct_slid| struct_slid_to_uuid.get(struct_slid).copied())
                .collect();

            if uuid_tuple.len() == tuple.len() {
                rel_batch.push(&uuid_tuple);
            }
        }

        if !rel_batch.is_empty() {
            batch.relation_tuples.push(rel_batch);
        }
    }

    // Save the batch
    if !batch.relation_tuples.is_empty() {
        let existing_batches = state.store.load_instance_data_batches(instance_uuid)
            .unwrap_or_default();
        let version = existing_batches.len() as u64;
        state.store.save_instance_data_batch(instance_uuid, version, &batch)?;
    }

    Ok(())
}

/// Handle query result from `query { ? : Type; }` syntax
fn handle_query_result(_state: &ReplState, result: QueryResult) {
    match result {
        QueryResult::Found { query_name, theory_name, model, time_ms } => {
            println!("✓ Query '{}' SOLVED in {:.2}ms", query_name, time_ms);
            println!("  Found model of theory '{}'", theory_name);

            // For now, print a basic summary. We don't have access to the signature here,
            // so just show raw structure info.
            let total_elements: usize = model.sorts.len();
            if total_elements == 0 {
                println!("\n  Witness: empty structure (trivial model)");
            } else {
                println!("\n  Witness structure: {} elements", total_elements);
                // Count elements by sort
                let mut sort_counts: std::collections::HashMap<usize, usize> = std::collections::HashMap::new();
                for &sort_id in &model.sorts {
                    *sort_counts.entry(sort_id).or_insert(0) += 1;
                }
                for (sort_id, count) in sort_counts {
                    println!("    Sort {}: {} element(s)", sort_id, count);
                }
            }
        }
        QueryResult::Unsat { query_name, theory_name, time_ms } => {
            println!("✗ Query '{}' UNSAT in {:.2}ms", query_name, time_ms);
            println!("  No model of '{}' exists extending the base.", theory_name);
        }
        QueryResult::Incomplete { query_name, theory_name, reason, time_ms } => {
            println!("◯ Query '{}' INCOMPLETE after {:.2}ms", query_name, time_ms);
            println!("  Theory: {}", theory_name);
            println!("  Reason: {}", reason);
        }
    }
}

/// Print a summary of structure contents
fn print_structure_summary(structure: &geolog::core::Structure, sig: &geolog::core::Signature) {
    use geolog::core::RelationStorage;

    // Show carriers
    let total_elements: usize = (0..sig.sorts.len())
        .map(|s| structure.carrier_size(s))
        .sum();
    println!("  Elements: {} total", total_elements);

    for (sort_id, sort_name) in sig.sorts.iter().enumerate() {
        let size = structure.carrier_size(sort_id);
        if size > 0 {
            println!("    {}: {} element(s)", sort_name, size);
        }
    }

    // Show relations
    let mut has_relations = false;
    for (rel_id, rel) in sig.relations.iter().enumerate() {
        if rel_id < structure.relations.len() {
            let count = structure.relations[rel_id].len();
            if count > 0 {
                if !has_relations {
                    println!("  Relations:");
                    has_relations = true;
                }
                println!("    {}: {} tuple(s)", rel.name, count);
            }
        }
    }
}

/// Get the history file path
fn dirs_history_path() -> Option<PathBuf> {
    // Try to use standard config directory
    if let Some(config_dir) = dirs_config_dir() {
        let mut path = config_dir;
        path.push("geolog");
        path.push("history");
        return Some(path);
    }
    None
}

/// Get the config directory (cross-platform)
fn dirs_config_dir() -> Option<PathBuf> {
    // Simple implementation - use HOME/.config on Unix, APPDATA on Windows
    #[cfg(unix)]
    {
        std::env::var("HOME").ok().map(|h| {
            let mut p = PathBuf::from(h);
            p.push(".config");
            p
        })
    }
    #[cfg(windows)]
    {
        std::env::var("APPDATA").ok().map(PathBuf::from)
    }
    #[cfg(not(any(unix, windows)))]
    {
        None
    }
}
