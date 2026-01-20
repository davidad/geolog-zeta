use geolog::universe::Universe;
use geolog::{
    elaborate::{ElaborationContext, Env, elaborate_instance_ctx, elaborate_theory},
    parse,
    repl::InstanceEntry,
};
use std::collections::HashMap;
use std::rc::Rc;

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

instance ExampleNet : PetriNet = {
  A : P;
  B : P;
  C : P;
  ab : T;
  ba : T;
  abc : T;
  ab_in : in;
  ab_in in/src = A;
  ab_in in/tgt = ab;
  ab_out : out;
  ab_out out/src = ab;
  ab_out out/tgt = B;
  ba_in : in;
  ba_in in/src = B;
  ba_in in/tgt = ba;
  ba_out : out;
  ba_out out/src = ba;
  ba_out out/tgt = A;
  abc_in1 : in;
  abc_in1 in/src = A;
  abc_in1 in/tgt = abc;
  abc_in2 : in;
  abc_in2 in/src = B;
  abc_in2 in/tgt = abc;
  abc_out : out;
  abc_out out/src = abc;
  abc_out out/tgt = C;
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
    let mut universe = Universe::new();

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
                        println!(
                            "  Params: {:?}",
                            elab.params.iter().map(|p| &p.name).collect::<Vec<_>>()
                        );
                        println!("  Sorts: {:?}", elab.theory.signature.sorts);
                        println!(
                            "  Functions: {:?}",
                            elab.theory
                                .signature
                                .functions
                                .iter()
                                .map(|f| &f.name)
                                .collect::<Vec<_>>()
                        );
                        println!("  Axioms: {}", elab.theory.axioms.len());
                        for (i, ax) in elab.theory.axioms.iter().enumerate() {
                            println!(
                                "    [{i}] {} vars, premise -> conclusion",
                                ax.context.vars.len()
                            );
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
            geolog::Declaration::Instance(i) => {
                // Extract theory name from the type expression
                let theory_name = i.theory.as_single_path()
                    .and_then(|p| p.segments.first().cloned())
                    .unwrap_or_else(|| "?".to_string());
                print!("Elaborating instance {}... ", i.name);
                let instances: HashMap<String, InstanceEntry> = HashMap::new();
                let mut ctx = ElaborationContext {
                    theories: &env.theories,
                    instances: &instances,
                    universe: &mut universe,
                };
                match elaborate_instance_ctx(&mut ctx, i) {
                    Ok(result) => {
                        let structure = &result.structure;
                        println!("OK!");
                        println!("  Theory: {}", theory_name);
                        println!("  Elements: {} total", structure.len());
                        for sort_id in 0..structure.carriers.len() {
                            println!(
                                "    Sort {}: {} elements",
                                sort_id,
                                structure.carrier_size(sort_id)
                            );
                        }
                        println!("  Functions defined:");
                        for (fid, func_map) in structure.functions.iter().enumerate() {
                            println!("    Func {}: {} mappings", fid, func_map.len());
                        }
                        println!();
                    }
                    Err(e) => {
                        println!("FAILED: {}", e);
                    }
                }
            }
            geolog::Declaration::Query(_) => {
                println!("Skipping query (not implemented yet)");
            }
        }
    }

    println!("=== SUMMARY ===");
    println!("Elaborated {} theories", env.theories.len());
}
