//! Quick manual fuzzer - run with: cargo test --release manual_fuzz -- --ignored --nocapture

use geolog::repl::ReplState;
use rand::prelude::*;
use std::time::Instant;

fn random_ascii_string(rng: &mut impl Rng, len: usize) -> String {
    (0..len).map(|_| rng.random_range(0x20u8..0x7F) as char).collect()
}

fn random_geolog_like(rng: &mut impl Rng) -> String {
    let keywords = ["theory", "instance", "Sort", "Prop", "forall", "exists", "chase"];
    let ops = [":", "->", "=", "|-", "{", "}", "[", "]", "(", ")", ";", ",", "."];
    let idents = ["x", "y", "z", "A", "B", "foo", "bar", "src", "tgt"];

    let mut s = String::new();
    let len = rng.random_range(1..200);
    for _ in 0..len {
        match rng.random_range(0..4) {
            0 => s.push_str(keywords.choose(rng).unwrap()),
            1 => s.push_str(ops.choose(rng).unwrap()),
            2 => s.push_str(idents.choose(rng).unwrap()),
            _ => s.push(' '),
        }
        if rng.random_bool(0.3) { s.push(' '); }
    }
    s
}

#[test]
#[ignore]
fn manual_fuzz_parser() {
    let mut rng = rand::rng();
    let start = Instant::now();
    let mut count = 0;
    let mut errors = 0;

    while start.elapsed().as_secs() < 10 {
        let len = rng.random_range(1usize..500);
        let input = if rng.random_bool(0.5) {
            random_ascii_string(&mut rng, len)
        } else {
            random_geolog_like(&mut rng)
        };

        // This should never panic
        let result = std::panic::catch_unwind(|| {
            let _ = geolog::parse(&input);
        });

        if result.is_err() {
            eprintln!("PANIC on input: {:?}", input);
            errors += 1;
        }
        count += 1;
    }

    eprintln!("Ran {} iterations, {} panics", count, errors);
    assert_eq!(errors, 0, "Parser panicked on some inputs!");
}

#[test]
#[ignore]
fn manual_fuzz_repl() {
    let mut rng = rand::rng();
    let start = Instant::now();
    let mut count = 0;
    let mut errors = 0;

    while start.elapsed().as_secs() < 10 {
        let len = rng.random_range(1usize..500);
        let input = if rng.random_bool(0.5) {
            random_ascii_string(&mut rng, len)
        } else {
            random_geolog_like(&mut rng)
        };

        let result = std::panic::catch_unwind(|| {
            let mut state = ReplState::new();
            let _ = state.execute_geolog(&input);
        });

        if result.is_err() {
            eprintln!("PANIC on input: {:?}", input);
            errors += 1;
        }
        count += 1;
    }

    eprintln!("Ran {} iterations, {} panics", count, errors);
    assert_eq!(errors, 0, "REPL panicked on some inputs!");
}

/// More aggressive fuzzer with edge-case generators
#[test]
#[ignore]
fn manual_fuzz_edge_cases() {
    let mut rng = rand::rng();
    let start = Instant::now();
    let mut count = 0;
    let mut errors = 0;

    // Edge case generators
    let edge_cases: Vec<fn(&mut _) -> String> = vec![
        // Deep nesting
        |rng: &mut rand::rngs::ThreadRng| {
            let depth = rng.random_range(10..100);
            let mut s = "theory T { ".repeat(depth);
            s.push_str(&"}".repeat(depth));
            s
        },
        // Very long identifiers
        |rng: &mut rand::rngs::ThreadRng| {
            let len = rng.random_range(1000..10000);
            format!("theory {} {{ }}", "a".repeat(len))
        },
        // Many small tokens
        |rng: &mut rand::rngs::ThreadRng| {
            let count = rng.random_range(100..1000);
            (0..count).map(|_| "x ").collect::<String>()
        },
        // Unicode stress
        |_rng: &mut rand::rngs::ThreadRng| {
            "theory 日本語 { ∀ : Sort; ∃ : Sort -> Prop; }".to_string()
        },
        // Null bytes and control chars
        |rng: &mut rand::rngs::ThreadRng| {
            let mut s = String::from("theory T { ");
            for _ in 0..rng.random_range(1..50) {
                s.push(rng.random_range(0u8..32) as char);
            }
            s.push_str(" }");
            s
        },
        // Deeply nested records
        |rng: &mut rand::rngs::ThreadRng| {
            let depth = rng.random_range(5..30);
            let mut s = String::from("theory T { f : ");
            for _ in 0..depth {
                s.push_str("[x: ");
            }
            s.push_str("Sort");
            for _ in 0..depth {
                s.push(']');
            }
            s.push_str(" -> Prop; }");
            s
        },
        // Many axioms
        |rng: &mut rand::rngs::ThreadRng| {
            let count = rng.random_range(50..200);
            let mut s = String::from("theory T { X : Sort; ");
            for i in 0..count {
                s.push_str(&format!("ax{} : forall x : X. |- x = x; ", i));
            }
            s.push('}');
            s
        },
        // Pathological chase
        |_rng: &mut rand::rngs::ThreadRng| {
            r#"
            theory Loop { X : Sort; r : [a: X, b: X] -> Prop; 
              ax : forall x : X. |- exists y : X. [a: x, b: y] r;
            }
            instance I : Loop = chase { start : X; }
            "#.to_string()
        },
    ];

    while start.elapsed().as_secs() < 30 {
        let gen_idx = rng.random_range(0..edge_cases.len());
        let input = edge_cases[gen_idx](&mut rng);

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let mut state = ReplState::new();
            let _ = state.execute_geolog(&input);
        }));

        if result.is_err() {
            eprintln!("PANIC on input (gen {}): {:?}", gen_idx, &input[..input.len().min(200)]);
            errors += 1;
        }
        count += 1;
    }

    eprintln!("Ran {} edge-case iterations, {} panics", count, errors);
    assert_eq!(errors, 0, "REPL panicked on edge cases!");
}
