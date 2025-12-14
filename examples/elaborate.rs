use std::rc::Rc;
use geolog::{parse, elaborate::{Env, elaborate_theory}};

fn main() {
    let input = r#"
namespace VanillaPetriNets;

theory PetriNet {
  P : Sort;
  T : Sort;
  in : Sort;
  out : Sort;
  in/src : in -> P;
  in/tgt : in -> T;
  out/src : out -> T;
  out/tgt : out -> P;
}

theory (N : PetriNet instance) Marking {
  token : Sort;
  token/of : token -> N/P;
}

theory (X : Sort) (Y : Sort) Iso {
  fwd : X -> Y;
  bwd : Y -> X;
  fb : forall x : X. |- x fwd bwd = x;
  bf : forall y : Y. |- y bwd fwd = y;
}
"#;

    println!("=== PARSING ===");
    let file = match parse(input) {
        Ok(f) => f,
        Err(e) => {
            eprintln!("Parse error: {}", e);
            std::process::exit(1);
        }
    };
    println!("Parsed {} declarations\n", file.declarations.len());

    println!("=== ELABORATING ===");
    let mut env = Env::new();

    for decl in &file.declarations {
        match &decl.node {
            geolog::Declaration::Namespace(name) => {
                println!("Skipping namespace: {}", name);
            }
            geolog::Declaration::Theory(t) => {
                print!("Elaborating theory {}... ", t.name);
                match elaborate_theory(&mut env, t) {
                    Ok(elab) => {
                        println!("OK!");
                        println!("  Params: {:?}", elab.params.iter().map(|p| &p.name).collect::<Vec<_>>());
                        println!("  Sorts: {:?}", elab.theory.signature.sorts);
                        println!("  Functions: {:?}", elab.theory.signature.functions.iter().map(|f| &f.name).collect::<Vec<_>>());
                        println!("  Axioms: {}", elab.theory.axioms.len());
                        for (i, ax) in elab.theory.axioms.iter().enumerate() {
                            println!("    [{i}] {} vars, premise -> conclusion", ax.context.vars.len());
                        }
                        println!();

                        // Add to environment for dependent theories
                        env.theories.insert(elab.theory.name.clone(), Rc::new(elab));
                    }
                    Err(e) => {
                        println!("FAILED: {}", e);
                    }
                }
            }
            geolog::Declaration::Instance(_) => {
                println!("Skipping instance (not implemented yet)");
            }
            geolog::Declaration::Query(_) => {
                println!("Skipping query (not implemented yet)");
            }
        }
    }

    println!("=== SUMMARY ===");
    println!("Elaborated {} theories", env.theories.len());
}
