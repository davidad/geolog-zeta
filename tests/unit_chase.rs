//! Unit tests for tensor-backed chase algorithm

use geolog::core::{
    Context, DerivedSort, Formula, RelationStorage, Sequent, Signature, Structure, Term, Theory,
};
use geolog::query::chase::chase_fixpoint;
use geolog::universe::Universe;

/// Create a simple test theory with one sort and one unary relation
fn simple_theory_with_relation() -> Theory {
    let mut sig = Signature::default();
    sig.add_sort("V".to_string());
    sig.add_relation("R".to_string(), DerivedSort::Base(0));
    Theory {
        name: "Simple".to_string(),
        signature: sig,
        axioms: vec![],
        axiom_names: vec![],
    }
}

/// Create a preorder-like theory with binary leq relation, reflexivity and transitivity
fn preorder_theory() -> Theory {
    let mut sig = Signature::default();
    sig.add_sort("X".to_string());

    // Binary relation with product domain: leq : [x: X, y: X] -> Prop
    let domain = DerivedSort::Product(vec![
        ("x".to_string(), DerivedSort::Base(0)),
        ("y".to_string(), DerivedSort::Base(0)),
    ]);
    sig.add_relation("leq".to_string(), domain);

    // Reflexivity axiom: forall x : X. |- [x: x, y: x] leq
    let refl_axiom = Sequent {
        context: Context {
            vars: vec![("x".to_string(), DerivedSort::Base(0))],
        },
        premise: Formula::True,
        conclusion: Formula::Rel(
            0,
            Term::Record(vec![
                ("x".to_string(), Term::Var("x".to_string(), DerivedSort::Base(0))),
                ("y".to_string(), Term::Var("x".to_string(), DerivedSort::Base(0))),
            ]),
        ),
    };

    // Transitivity axiom: forall x, y, z : X. [x: x, y: y] leq, [x: y, y: z] leq |- [x: x, y: z] leq
    let trans_axiom = Sequent {
        context: Context {
            vars: vec![
                ("x".to_string(), DerivedSort::Base(0)),
                ("y".to_string(), DerivedSort::Base(0)),
                ("z".to_string(), DerivedSort::Base(0)),
            ],
        },
        premise: Formula::Conj(vec![
            Formula::Rel(
                0,
                Term::Record(vec![
                    ("x".to_string(), Term::Var("x".to_string(), DerivedSort::Base(0))),
                    ("y".to_string(), Term::Var("y".to_string(), DerivedSort::Base(0))),
                ]),
            ),
            Formula::Rel(
                0,
                Term::Record(vec![
                    ("x".to_string(), Term::Var("y".to_string(), DerivedSort::Base(0))),
                    ("y".to_string(), Term::Var("z".to_string(), DerivedSort::Base(0))),
                ]),
            ),
        ]),
        conclusion: Formula::Rel(
            0,
            Term::Record(vec![
                ("x".to_string(), Term::Var("x".to_string(), DerivedSort::Base(0))),
                ("y".to_string(), Term::Var("z".to_string(), DerivedSort::Base(0))),
            ]),
        ),
    };

    Theory {
        name: "Preorder".to_string(),
        signature: sig,
        axioms: vec![refl_axiom, trans_axiom],
        axiom_names: vec!["ax/refl".to_string(), "ax/trans".to_string()],
    }
}

#[test]
fn test_chase_adds_relation_from_true_premise() {
    // Axiom: forall x : V. |- R(x)
    // This should add all elements to R
    let mut sig = Signature::default();
    sig.add_sort("V".to_string());
    sig.add_relation("R".to_string(), DerivedSort::Base(0));

    let axiom = Sequent {
        context: Context {
            vars: vec![("x".to_string(), DerivedSort::Base(0))],
        },
        premise: Formula::True,
        conclusion: Formula::Rel(0, Term::Var("x".to_string(), DerivedSort::Base(0))),
    };

    let mut universe = Universe::new();
    let mut structure = Structure::new(1);

    // Add some elements
    let (a, _) = structure.add_element(&mut universe, 0);
    let (b, _) = structure.add_element(&mut universe, 0);
    let (c, _) = structure.add_element(&mut universe, 0);

    // Initialize relation
    structure.init_relations(&[1]);

    // Run chase
    let iterations = chase_fixpoint(&[axiom], &mut structure, &mut universe, &sig, 100).unwrap();

    // Should add all 3 elements to R
    assert_eq!(structure.get_relation(0).len(), 3);
    assert!(structure.query_relation(0, &[a]));
    assert!(structure.query_relation(0, &[b]));
    assert!(structure.query_relation(0, &[c]));

    // Should converge in 2 iterations
    assert_eq!(iterations, 2);
}

#[test]
fn test_chase_fixpoint_empty_structure() {
    let theory = simple_theory_with_relation();

    // Axiom: forall x : V. |- R(x)
    let axiom = Sequent {
        context: Context {
            vars: vec![("x".to_string(), DerivedSort::Base(0))],
        },
        premise: Formula::True,
        conclusion: Formula::Rel(0, Term::Var("x".to_string(), DerivedSort::Base(0))),
    };

    let mut universe = Universe::new();
    let mut structure = Structure::new(1);
    structure.init_relations(&[1]);

    let iterations = chase_fixpoint(&[axiom], &mut structure, &mut universe, &theory.signature, 100).unwrap();

    // Empty structure: no elements, so nothing to add
    assert_eq!(iterations, 1);
    assert_eq!(structure.get_relation(0).len(), 0);
}

#[test]
fn test_chase_preorder_reflexivity() {
    // Test that chase correctly computes reflexive closure
    let theory = preorder_theory();
    let mut universe = Universe::new();
    let mut structure = Structure::new(1);

    // Add 3 elements
    let (a, _) = structure.add_element(&mut universe, 0);
    let (b, _) = structure.add_element(&mut universe, 0);
    let (c, _) = structure.add_element(&mut universe, 0);

    // Initialize relation with arity 2
    structure.init_relations(&[2]);

    // Run chase
    let iterations = chase_fixpoint(
        &theory.axioms,
        &mut structure,
        &mut universe,
        &theory.signature,
        100,
    ).unwrap();

    // Should have exactly 3 reflexive tuples
    let relation = structure.get_relation(0);
    assert_eq!(relation.len(), 3, "Should have exactly 3 reflexive tuples");

    // Check reflexive pairs exist
    assert!(structure.query_relation(0, &[a, a]), "Should have (a,a)");
    assert!(structure.query_relation(0, &[b, b]), "Should have (b,b)");
    assert!(structure.query_relation(0, &[c, c]), "Should have (c,c)");

    // Check non-reflexive pairs do NOT exist
    assert!(!structure.query_relation(0, &[a, b]), "Should NOT have (a,b)");
    assert!(!structure.query_relation(0, &[a, c]), "Should NOT have (a,c)");
    assert!(!structure.query_relation(0, &[b, a]), "Should NOT have (b,a)");

    // Should complete in 2 iterations
    assert_eq!(iterations, 2);
}

#[test]
fn test_chase_transitive_closure() {
    // Test that chase correctly computes transitive closure
    let theory = preorder_theory();
    let mut universe = Universe::new();
    let mut structure = Structure::new(1);

    // Add 3 elements: a < b < c (chain order)
    let (a, _) = structure.add_element(&mut universe, 0);
    let (b, _) = structure.add_element(&mut universe, 0);
    let (c, _) = structure.add_element(&mut universe, 0);

    // Initialize relation with arity 2
    structure.init_relations(&[2]);

    // Manually add initial ordering: a ≤ b and b ≤ c
    structure.get_relation_mut(0).insert(vec![a, b]);
    structure.get_relation_mut(0).insert(vec![b, c]);

    // Run chase
    let _iterations = chase_fixpoint(
        &theory.axioms,
        &mut structure,
        &mut universe,
        &theory.signature,
        100,
    ).unwrap();

    // Expected: 3 reflexive + 2 initial + 1 transitive (a,c) = 6
    let relation = structure.get_relation(0);
    assert_eq!(relation.len(), 6, "Should have 6 tuples");

    // Check reflexive pairs
    assert!(structure.query_relation(0, &[a, a]));
    assert!(structure.query_relation(0, &[b, b]));
    assert!(structure.query_relation(0, &[c, c]));

    // Check initial ordering
    assert!(structure.query_relation(0, &[a, b]));
    assert!(structure.query_relation(0, &[b, c]));

    // Check transitive closure!
    assert!(structure.query_relation(0, &[a, c]), "Should have (a,c) from transitivity");

    // Should NOT have backwards edges
    assert!(!structure.query_relation(0, &[b, a]));
    assert!(!structure.query_relation(0, &[c, b]));
    assert!(!structure.query_relation(0, &[c, a]));
}

#[test]
fn test_chase_conjunction_in_conclusion() {
    // Axiom: forall x : V. |- R(x) ∧ S(x)
    let mut sig = Signature::default();
    sig.add_sort("V".to_string());
    sig.add_relation("R".to_string(), DerivedSort::Base(0));
    sig.add_relation("S".to_string(), DerivedSort::Base(0));

    let axiom = Sequent {
        context: Context {
            vars: vec![("x".to_string(), DerivedSort::Base(0))],
        },
        premise: Formula::True,
        conclusion: Formula::Conj(vec![
            Formula::Rel(0, Term::Var("x".to_string(), DerivedSort::Base(0))),
            Formula::Rel(1, Term::Var("x".to_string(), DerivedSort::Base(0))),
        ]),
    };

    let mut universe = Universe::new();
    let mut structure = Structure::new(1);

    let (a, _) = structure.add_element(&mut universe, 0);
    let (b, _) = structure.add_element(&mut universe, 0);

    structure.init_relations(&[1, 1]);

    let _iterations = chase_fixpoint(&[axiom], &mut structure, &mut universe, &sig, 100).unwrap();

    // Both relations should have both elements
    assert_eq!(structure.get_relation(0).len(), 2);
    assert_eq!(structure.get_relation(1).len(), 2);
    assert!(structure.query_relation(0, &[a]));
    assert!(structure.query_relation(0, &[b]));
    assert!(structure.query_relation(1, &[a]));
    assert!(structure.query_relation(1, &[b]));
}

#[test]
fn test_chase_relation_premise() {
    // Axiom: forall x, y : V. R(x, y) |- S(x, y)
    // Copy tuples from R to S
    let mut sig = Signature::default();
    sig.add_sort("V".to_string());
    let domain = DerivedSort::Product(vec![
        ("a".to_string(), DerivedSort::Base(0)),
        ("b".to_string(), DerivedSort::Base(0)),
    ]);
    sig.add_relation("R".to_string(), domain.clone());
    sig.add_relation("S".to_string(), domain);

    let axiom = Sequent {
        context: Context {
            vars: vec![
                ("x".to_string(), DerivedSort::Base(0)),
                ("y".to_string(), DerivedSort::Base(0)),
            ],
        },
        premise: Formula::Rel(
            0,
            Term::Record(vec![
                ("a".to_string(), Term::Var("x".to_string(), DerivedSort::Base(0))),
                ("b".to_string(), Term::Var("y".to_string(), DerivedSort::Base(0))),
            ]),
        ),
        conclusion: Formula::Rel(
            1,
            Term::Record(vec![
                ("a".to_string(), Term::Var("x".to_string(), DerivedSort::Base(0))),
                ("b".to_string(), Term::Var("y".to_string(), DerivedSort::Base(0))),
            ]),
        ),
    };

    let mut universe = Universe::new();
    let mut structure = Structure::new(1);

    let (a, _) = structure.add_element(&mut universe, 0);
    let (b, _) = structure.add_element(&mut universe, 0);

    structure.init_relations(&[2, 2]);

    // Add some tuples to R
    structure.get_relation_mut(0).insert(vec![a, b]);
    structure.get_relation_mut(0).insert(vec![b, a]);

    let _iterations = chase_fixpoint(&[axiom], &mut structure, &mut universe, &sig, 100).unwrap();

    // S should have the same tuples as R
    assert_eq!(structure.get_relation(1).len(), 2);
    assert!(structure.query_relation(1, &[a, b]));
    assert!(structure.query_relation(1, &[b, a]));
}

/// Test chase with existential premise (the feature that motivated tensor-backed chase!)
#[test]
fn test_chase_existential_premise() {
    // Theory: Graph with reachability
    // Axiom: forall v0, v1 : V. (exists e : E. src(e) = v0 ∧ tgt(e) = v1) |- reachable(v0, v1)
    let mut sig = Signature::default();
    let v_sort = sig.add_sort("V".to_string());
    let e_sort = sig.add_sort("E".to_string());

    // src, tgt : E -> V
    sig.add_function("src".to_string(), DerivedSort::Base(e_sort), DerivedSort::Base(v_sort));
    sig.add_function("tgt".to_string(), DerivedSort::Base(e_sort), DerivedSort::Base(v_sort));

    // reachable : [from: V, to: V] -> Prop
    let reach_domain = DerivedSort::Product(vec![
        ("from".to_string(), DerivedSort::Base(v_sort)),
        ("to".to_string(), DerivedSort::Base(v_sort)),
    ]);
    sig.add_relation("reachable".to_string(), reach_domain);

    // Axiom: (exists e : E. src(e) = v0 ∧ tgt(e) = v1) |- reachable(v0, v1)
    let axiom = Sequent {
        context: Context {
            vars: vec![
                ("v0".to_string(), DerivedSort::Base(v_sort)),
                ("v1".to_string(), DerivedSort::Base(v_sort)),
            ],
        },
        premise: Formula::Exists(
            "e".to_string(),
            DerivedSort::Base(e_sort),
            Box::new(Formula::Conj(vec![
                Formula::Eq(
                    Term::App(0, Box::new(Term::Var("e".to_string(), DerivedSort::Base(e_sort)))),
                    Term::Var("v0".to_string(), DerivedSort::Base(v_sort)),
                ),
                Formula::Eq(
                    Term::App(1, Box::new(Term::Var("e".to_string(), DerivedSort::Base(e_sort)))),
                    Term::Var("v1".to_string(), DerivedSort::Base(v_sort)),
                ),
            ])),
        ),
        conclusion: Formula::Rel(
            0,
            Term::Record(vec![
                ("from".to_string(), Term::Var("v0".to_string(), DerivedSort::Base(v_sort))),
                ("to".to_string(), Term::Var("v1".to_string(), DerivedSort::Base(v_sort))),
            ]),
        ),
    };

    let mut universe = Universe::new();
    let mut structure = Structure::new(2); // 2 sorts: V and E

    // Add vertices: a, b, c
    let (a, _) = structure.add_element(&mut universe, v_sort);
    let (b, _) = structure.add_element(&mut universe, v_sort);
    let (c, _) = structure.add_element(&mut universe, v_sort);

    // Add edges: e1 (a->b), e2 (b->c)
    let (e1, _) = structure.add_element(&mut universe, e_sort);
    let (e2, _) = structure.add_element(&mut universe, e_sort);

    // Initialize functions and relations
    structure.init_functions(&[Some(e_sort), Some(e_sort)]); // src, tgt both have domain E
    structure.init_relations(&[2]); // reachable is binary

    // Define src and tgt
    structure.define_function(0, e1, a).unwrap(); // src(e1) = a
    structure.define_function(1, e1, b).unwrap(); // tgt(e1) = b
    structure.define_function(0, e2, b).unwrap(); // src(e2) = b
    structure.define_function(1, e2, c).unwrap(); // tgt(e2) = c

    // Run chase
    let iterations = chase_fixpoint(&[axiom], &mut structure, &mut universe, &sig, 100).unwrap();

    // Should derive reachable(a,b) and reachable(b,c)
    assert_eq!(structure.get_relation(0).len(), 2, "Should have 2 reachable pairs");
    assert!(structure.query_relation(0, &[a, b]), "Should have reachable(a,b)");
    assert!(structure.query_relation(0, &[b, c]), "Should have reachable(b,c)");

    // Should NOT have other pairs
    assert!(!structure.query_relation(0, &[a, c]), "Should NOT have reachable(a,c) without transitive closure axiom");

    println!("Chase with existential premise completed in {} iterations", iterations);
}
