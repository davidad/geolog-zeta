use geolog::parse;

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

// Reachability problem: can we get from A to B?
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

    match parse(input) {
        Ok(file) => {
            println!("Parsed successfully!");
            println!("Declarations: {}", file.declarations.len());
            for decl in &file.declarations {
                match &decl.node {
                    geolog::Declaration::Namespace(n) => println!("  - namespace {}", n),
                    geolog::Declaration::Theory(t) => {
                        println!("  - theory {} ({} items)", t.name, t.body.len())
                    }
                    geolog::Declaration::Instance(i) => {
                        println!("  - instance {} ({} items)", i.name, i.body.len())
                    }
                    geolog::Declaration::Query(q) => println!("  - query {}", q.name),
                }
            }
        }
        Err(e) => {
            eprintln!("Parse error: {}", e);
            std::process::exit(1);
        }
    }
}
