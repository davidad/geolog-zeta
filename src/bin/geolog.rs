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

use geolog::repl::{
    ExecuteResult, InputResult, InspectResult, ListTarget, MetaCommand, ReplState,
    format_instance_detail, format_theory_detail,
};

const VERSION: &str = env!("CARGO_PKG_VERSION");
const PROMPT: &str = "geolog> ";
const CONTINUATION: &str = "......  ";

fn main() {
    // Parse command line args
    let args: Vec<String> = std::env::args().collect();
    let workspace_path = args.get(1).map(PathBuf::from);

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
        Ok(result) => match result {
            ExecuteResult::Namespace(name) => {
                println!("Namespace: {}", name);
            }
            ExecuteResult::Theory {
                name,
                num_sorts,
                num_functions,
                num_relations,
            } => {
                let mut parts = vec![format!("{} sorts", num_sorts)];
                if num_functions > 0 {
                    parts.push(format!("{} functions", num_functions));
                }
                if num_relations > 0 {
                    parts.push(format!("{} relations", num_relations));
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
        },
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
    // Look up the instance
    let Some((instance_slid, _)) = state.store.resolve_name(instance_name) else {
        eprintln!("Instance '{}' not found", instance_name);
        return;
    };

    // Look up the relation
    let Some((relation_slid, _)) = state.store.resolve_name(relation_name) else {
        eprintln!(
            "Relation '{}' not found. Note: Full relation lookup requires querying the theory.",
            relation_name
        );
        return;
    };

    // For now, we only support single-argument relations
    // Full implementation would handle products via Tuple elements
    if args.len() != 1 {
        eprintln!(
            "Currently only single-argument relations are supported via :assert."
        );
        eprintln!(
            "Multi-argument relations require Tuple element construction (pending geolog-7tt)."
        );
        return;
    }

    let arg_name = &args[0];
    let Some((arg_slid, _)) = state.store.resolve_name(arg_name) else {
        eprintln!("Element '{}' not found", arg_name);
        return;
    };

    match state.store.add_rel_tuple(instance_slid, relation_slid, arg_slid) {
        Ok(tuple_slid) => {
            println!(
                "Asserted {}({}) in instance '{}' (tuple #{})",
                relation_name, arg_name, instance_name, tuple_slid
            );
        }
        Err(e) => {
            eprintln!("Failed to assert relation: {}", e);
        }
    }
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
