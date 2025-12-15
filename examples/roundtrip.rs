use geolog::{parse, pretty_print};

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

theory (N : PetriNet instance) ReachabilityProblem {
  initial_marking : N Marking instance;
  target_marking : N Marking instance;
}

theory (N : PetriNet instance) Trace {
  F : Sort;
  F/of : F -> N/T;

  W : Sort;
  W/src : W -> [firing : F, arc : N/out];
  W/tgt : W -> [firing : F, arc : N/in];

  ax1 : forall w : W. |- w W/src .arc N/out/src = w W/src .firing F/of;
  ax2 : forall w : W. |- w W/tgt .arc N/in/tgt = w W/tgt .firing F/of;
  ax3 : forall w1, w2 : W. w1 W/src = w2 W/src |- w1 = w2;
  ax4 : forall w1, w2 : W. w1 W/tgt = w2 W/tgt |- w1 = w2;

  input_terminal : Sort;
  output_terminal : Sort;
  input_terminal/of : input_terminal -> N/P;
  output_terminal/of : output_terminal -> N/P;
  input_terminal/tgt : input_terminal -> [firing : F, arc : N/in];
  output_terminal/src : output_terminal -> [firing : F, arc : N/out];

  ax5 : forall f : F, arc : N/out. arc N/out/src = f F/of |-
    (exists w : W. w W/src = [firing: f, arc: arc]) \/
    (exists o : output_terminal. o output_terminal/src = [firing: f, arc: arc]);
  ax6 : forall f : F, arc : N/in. arc N/in/tgt = f F/of |-
    (exists w : W. w W/tgt = [firing: f, arc: arc]) \/
    (exists i : input_terminal. i input_terminal/tgt = [firing: f, arc: arc]);
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

instance problem0 : ExampleNet ReachabilityProblem = {
  initial_marking = {
    t : token;
    t token/of = ExampleNet/A;
  };
  target_marking = {
    t : token;
    t token/of = ExampleNet/B;
  };
}

query findTrace {
  ? : ExampleNet Trace instance;
}
"#;

    println!("=== PARSING ORIGINAL ===");
    let ast1 = match parse(input) {
        Ok(f) => f,
        Err(e) => {
            eprintln!("Parse error: {}", e);
            std::process::exit(1);
        }
    };
    println!("Parsed {} declarations", ast1.declarations.len());

    println!("\n=== PRETTY PRINTING ===");
    let printed = pretty_print(&ast1);
    println!("{}", printed);

    println!("\n=== RE-PARSING ===");
    let ast2 = match parse(&printed) {
        Ok(f) => f,
        Err(e) => {
            eprintln!("Re-parse error: {}", e);
            eprintln!("\nPrinted output was:\n{}", printed);
            std::process::exit(1);
        }
    };
    println!("Re-parsed {} declarations", ast2.declarations.len());

    println!("\n=== COMPARING ===");
    if ast1.declarations.len() != ast2.declarations.len() {
        eprintln!("Declaration count mismatch!");
        std::process::exit(1);
    }

    // Compare declaration types
    for (i, (d1, d2)) in ast1
        .declarations
        .iter()
        .zip(ast2.declarations.iter())
        .enumerate()
    {
        let type1 = match &d1.node {
            geolog::Declaration::Namespace(_) => "namespace",
            geolog::Declaration::Theory(_) => "theory",
            geolog::Declaration::Instance(_) => "instance",
            geolog::Declaration::Query(_) => "query",
        };
        let type2 = match &d2.node {
            geolog::Declaration::Namespace(_) => "namespace",
            geolog::Declaration::Theory(_) => "theory",
            geolog::Declaration::Instance(_) => "instance",
            geolog::Declaration::Query(_) => "query",
        };
        if type1 != type2 {
            eprintln!("Declaration {} type mismatch: {} vs {}", i, type1, type2);
            std::process::exit(1);
        }
        print!("  [{}] {} ", i, type1);

        // Check names/details
        match (&d1.node, &d2.node) {
            (geolog::Declaration::Namespace(n1), geolog::Declaration::Namespace(n2)) => {
                if n1 != n2 {
                    eprintln!("name mismatch: {} vs {}", n1, n2);
                    std::process::exit(1);
                }
                println!("{} ✓", n1);
            }
            (geolog::Declaration::Theory(t1), geolog::Declaration::Theory(t2)) => {
                if t1.name != t2.name {
                    eprintln!("name mismatch: {} vs {}", t1.name, t2.name);
                    std::process::exit(1);
                }
                if t1.body.len() != t2.body.len() {
                    eprintln!(
                        "body length mismatch: {} vs {}",
                        t1.body.len(),
                        t2.body.len()
                    );
                    std::process::exit(1);
                }
                println!("{} ({} items) ✓", t1.name, t1.body.len());
            }
            (geolog::Declaration::Instance(i1), geolog::Declaration::Instance(i2)) => {
                if i1.name != i2.name {
                    eprintln!("name mismatch: {} vs {}", i1.name, i2.name);
                    std::process::exit(1);
                }
                if i1.body.len() != i2.body.len() {
                    eprintln!(
                        "body length mismatch: {} vs {}",
                        i1.body.len(),
                        i2.body.len()
                    );
                    std::process::exit(1);
                }
                println!("{} ({} items) ✓", i1.name, i1.body.len());
            }
            (geolog::Declaration::Query(q1), geolog::Declaration::Query(q2)) => {
                if q1.name != q2.name {
                    eprintln!("name mismatch: {} vs {}", q1.name, q2.name);
                    std::process::exit(1);
                }
                println!("{} ✓", q1.name);
            }
            _ => unreachable!(),
        }
    }

    println!("\n=== ROUNDTRIP SUCCESS ===");
}
