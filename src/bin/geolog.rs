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
    format_instance_detail, format_theory_detail, ExecuteResult, InputResult, InspectResult,
    ListTarget, MetaCommand, ReplState,
};

const VERSION: &str = env!("CARGO_PKG_VERSION");
const PROMPT: &str = "geolog> ";
const CONTINUATION: &str = "...... ";

fn main() {
    // Parse command line args
    let args: Vec<String> = std::env::args().collect();
    let workspace_path = args.get(1).map(PathBuf::from);

    // Print banner
    println!("geolog v{} - Geometric Logic REPL", VERSION);
    println!("Type :help for help, :quit to exit\n");

    // Initialize state
    let mut state = ReplState::new();
    if let Some(ref path) = workspace_path {
        state.workspace_path = Some(path.clone());
        println!("Workspace: {}", path.display());
    }

    // Set up rustyline
    let config = Config::builder()
        .auto_add_history(true)
        .build();
    let mut rl: Editor<(), DefaultHistory> = Editor::with_config(config).expect("Failed to create editor");

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
            } => {
                println!(
                    "Defined theory {} ({} sorts, {} functions)",
                    name, num_sorts, num_functions
                );
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
            println!("  :list [target]   List theories/instances (target: theories, instances, all)");
            println!("  :inspect <name>  Show details of a theory or instance");
            println!("  :source <file>   Load and execute a geolog file");
            println!("  :clear           Clear the screen");
            println!("  :reset           Reset all state");
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
                    println!(
                        "  {} ({} sorts, {} functions, {} axioms)",
                        t.name, t.num_sorts, t.num_functions, t.num_axioms
                    );
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
                    println!("  {} : {} ({} elements)", i.name, i.theory_name, i.num_elements);
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
