//! Unit tests for chase algorithm

use geolog::core::{
    Context, DerivedSort, ElaboratedTheory, Formula, RelationStorage, Sequent, Signature, Structure, Term, Theory,
};
use geolog::query::chase::{
    chase_fixpoint, chase_step, compile_axiom, compile_theory_axioms, ChaseHead, ChaseRule,
};
use geolog::universe::Universe;

/// Create a simple test theory with one sort and one binary relation
fn simple_theory_with_relation() -> Theory {
    let mut sig = Signature::default();
    sig.add_sort("V".to_string());
    sig.add_relation("Edge".to_string(), DerivedSort::Base(0));
    Theory {
        name: "Graph".to_string(),
        signature: sig,
        axioms: vec![],
        axiom_names: vec![],
    }
}

/// Create a theory with transitive closure axiom: Edge(x,y), Edge(y,z) ⊢ Path(x,z)
fn transitive_closure_theory() -> Theory {
    let mut sig = Signature::default();
    sig.add_sort("V".to_string());
    sig.add_relation("Edge".to_string(), DerivedSort::Base(0));
    sig.add_relation("Path".to_string(), DerivedSort::Base(0));

    // Axiom 1: Edge(x,y) ⊢ Path(x,y)  (base case)
    let base_axiom = Sequent {
        context: Context {
            vars: vec![
                ("x".to_string(), DerivedSort::Base(0)),
                ("y".to_string(), DerivedSort::Base(0)),
            ],
        },
        premise: Formula::Rel(0, Term::Var("x".to_string(), DerivedSort::Base(0))),
        conclusion: Formula::Rel(1, Term::Var("x".to_string(), DerivedSort::Base(0))),
    };

    // TODO: Axiom 2 needs conjunction which requires more complex query compilation
    // For now, test with just the base case

    Theory {
        name: "TransitiveClosure".to_string(),
        signature: sig,
        axioms: vec![base_axiom],
        axiom_names: vec!["ax/base".to_string()],
    }
}

#[test]
fn test_compile_axiom_basic() {
    let theory = simple_theory_with_relation();
    let sig = &theory.signature;

    // Create a simple axiom: x:V ⊢ R(x)
    let axiom = Sequent {
        context: Context {
            vars: vec![("x".to_string(), DerivedSort::Base(0))],
        },
        premise: Formula::True,
        conclusion: Formula::Rel(0, Term::Var("x".to_string(), DerivedSort::Base(0))),
    };

    let rule = compile_axiom(&axiom, sig, "test_rule".to_string()).unwrap();

    assert_eq!(rule.name, "test_rule");
    assert_eq!(rule.var_indices.len(), 1);
    assert_eq!(rule.var_indices.get("x"), Some(&0));

    // Check head is AddRelation
    match &rule.head {
        ChaseHead::AddRelation { rel_id, arg_indices } => {
            assert_eq!(*rel_id, 0);
            assert_eq!(arg_indices, &vec![0]);
        }
        _ => panic!("Expected AddRelation head"),
    }
}

#[test]
fn test_compile_axiom_conjunction_conclusion() {
    let mut sig = Signature::default();
    sig.add_sort("V".to_string());
    sig.add_relation("R".to_string(), DerivedSort::Base(0));
    sig.add_relation("S".to_string(), DerivedSort::Base(0));

    // Axiom: x:V ⊢ R(x) ∧ S(x)
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

    let rule = compile_axiom(&axiom, &sig, "conj_rule".to_string()).unwrap();

    // Check head is Multi with two AddRelation
    match &rule.head {
        ChaseHead::Multi(heads) => {
            assert_eq!(heads.len(), 2);
            for head in heads {
                match head {
                    ChaseHead::AddRelation { .. } => {}
                    _ => panic!("Expected AddRelation in Multi head"),
                }
            }
        }
        _ => panic!("Expected Multi head"),
    }
}

#[test]
fn test_chase_step_adds_relation() {
    let mut universe = Universe::new();
    let mut structure = Structure::new(1);

    // Add some elements
    let (a, _) = structure.add_element(&mut universe, 0);
    let (b, _) = structure.add_element(&mut universe, 0);
    let (c, _) = structure.add_element(&mut universe, 0);

    // Initialize one relation with arity 1
    structure.init_relations(&[1]);

    // Create theory and compile rule
    let theory = simple_theory_with_relation();

    // Simple rule: just scan sort 0 and add to relation
    let rule = ChaseRule {
        name: "add_all".to_string(),
        var_indices: [("x".to_string(), 0)].into_iter().collect(),
        query: geolog::query::backend::QueryOp::Scan { sort_idx: 0 },
        head: ChaseHead::AddRelation {
            rel_id: 0,
            arg_indices: vec![0],
        },
    };

    // Execute chase step
    let changed = chase_step(&[rule], &mut structure, &mut universe, &theory.signature).unwrap();

    assert!(changed);
    assert_eq!(structure.get_relation(0).len(), 3);
    assert!(structure.query_relation(0, &[a]));
    assert!(structure.query_relation(0, &[b]));
    assert!(structure.query_relation(0, &[c]));

    // Second chase step should not change anything
    let rule2 = ChaseRule {
        name: "add_all".to_string(),
        var_indices: [("x".to_string(), 0)].into_iter().collect(),
        query: geolog::query::backend::QueryOp::Scan { sort_idx: 0 },
        head: ChaseHead::AddRelation {
            rel_id: 0,
            arg_indices: vec![0],
        },
    };

    let changed2 = chase_step(&[rule2], &mut structure, &mut universe, &theory.signature).unwrap();
    assert!(!changed2);
}

#[test]
fn test_chase_fixpoint() {
    let mut universe = Universe::new();
    let mut structure = Structure::new(1);

    // Add elements
    let (a, _) = structure.add_element(&mut universe, 0);
    let (b, _) = structure.add_element(&mut universe, 0);

    // Initialize relation
    structure.init_relations(&[1]);

    let theory = simple_theory_with_relation();

    let rule = ChaseRule {
        name: "add_all".to_string(),
        var_indices: [("x".to_string(), 0)].into_iter().collect(),
        query: geolog::query::backend::QueryOp::Scan { sort_idx: 0 },
        head: ChaseHead::AddRelation {
            rel_id: 0,
            arg_indices: vec![0],
        },
    };

    let iterations = chase_fixpoint(&[rule], &mut structure, &mut universe, &theory.signature, 100).unwrap();

    assert_eq!(iterations, 2); // One to add, one to confirm fixpoint
    assert_eq!(structure.get_relation(0).len(), 2);
    assert!(structure.query_relation(0, &[a]));
    assert!(structure.query_relation(0, &[b]));
}

#[test]
fn test_chase_with_empty_structure() {
    let mut universe = Universe::new();
    let mut structure = Structure::new(1);
    structure.init_relations(&[1]);

    let theory = simple_theory_with_relation();

    let rule = ChaseRule {
        name: "add_all".to_string(),
        var_indices: [("x".to_string(), 0)].into_iter().collect(),
        query: geolog::query::backend::QueryOp::Scan { sort_idx: 0 },
        head: ChaseHead::AddRelation {
            rel_id: 0,
            arg_indices: vec![0],
        },
    };

    let iterations = chase_fixpoint(&[rule], &mut structure, &mut universe, &theory.signature, 100).unwrap();

    assert_eq!(iterations, 1); // Only one iteration needed (no elements to process)
    assert_eq!(structure.get_relation(0).len(), 0);
}

#[test]
fn test_compile_theory_axioms() {
    let theory = ElaboratedTheory {
        theory: transitive_closure_theory(),
        params: vec![],
    };

    let rules = compile_theory_axioms(&theory).unwrap();

    assert_eq!(rules.len(), 1);
    assert_eq!(rules[0].name, "axiom_0");
}

/// Create a preorder-like theory with binary leq relation and transitivity axiom
fn preorder_theory() -> Theory {
    let mut sig = Signature::default();
    sig.add_sort("X".to_string());

    // Binary relation with product domain: leq : [x: X, y: X] -> Prop
    let domain = DerivedSort::Product(vec![
        ("x".to_string(), DerivedSort::Base(0)),
        ("y".to_string(), DerivedSort::Base(0)),
    ]);
    sig.add_relation("leq".to_string(), domain.clone());

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
fn test_chase_preorder_reflexivity() {
    // Test that chase correctly computes reflexive closure without generating
    // spurious tuples from cross-join (the bug that was fixed)
    let theory = preorder_theory();
    let mut universe = Universe::new();
    let mut structure = Structure::new(1);

    // Add 3 elements
    let (a, _) = structure.add_element(&mut universe, 0);
    let (b, _) = structure.add_element(&mut universe, 0);
    let (c, _) = structure.add_element(&mut universe, 0);

    // Initialize relation with arity 2 (binary relation)
    structure.init_relations(&[2]);

    // Compile axioms
    let rules = compile_theory_axioms(&ElaboratedTheory {
        theory: theory.clone(),
        params: vec![],
    })
    .unwrap();

    assert_eq!(rules.len(), 2, "Should compile both reflexivity and transitivity axioms");

    // Run chase
    let iterations = chase_fixpoint(&rules, &mut structure, &mut universe, &theory.signature, 100).unwrap();

    // With only reflexivity and transitivity (no additional ordering),
    // we should get exactly 3 reflexive pairs: (a,a), (b,b), (c,c)
    let relation = structure.get_relation(0);
    assert_eq!(
        relation.len(),
        3,
        "Should have exactly 3 reflexive tuples (was 9 before equi-join fix)"
    );

    // Check that each reflexive pair exists
    assert!(structure.query_relation(0, &[a, a]), "Should have (a,a)");
    assert!(structure.query_relation(0, &[b, b]), "Should have (b,b)");
    assert!(structure.query_relation(0, &[c, c]), "Should have (c,c)");

    // Check that non-reflexive pairs do NOT exist (they would if cross-join bug existed)
    assert!(!structure.query_relation(0, &[a, b]), "Should NOT have (a,b)");
    assert!(!structure.query_relation(0, &[a, c]), "Should NOT have (a,c)");
    assert!(!structure.query_relation(0, &[b, a]), "Should NOT have (b,a)");

    // Should complete in 2 iterations (one to add reflexive pairs, one to verify fixpoint)
    assert_eq!(iterations, 2, "Should reach fixpoint in 2 iterations");
}

#[test]
fn test_chase_transitive_closure() {
    // Test that chase correctly computes transitive closure when there are
    // actual edges to close over (not just reflexive pairs)
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

    // Compile axioms
    let rules = compile_theory_axioms(&ElaboratedTheory {
        theory: theory.clone(),
        params: vec![],
    })
    .unwrap();

    // Run chase
    let _iterations = chase_fixpoint(&rules, &mut structure, &mut universe, &theory.signature, 100).unwrap();

    // Expected tuples after chase:
    // - Reflexive: (a,a), (b,b), (c,c) - from reflexivity axiom
    // - Initial: (a,b), (b,c) - manually added
    // - Transitive: (a,c) - from transitivity: (a,b) + (b,c) → (a,c)
    // Total: 6 tuples
    let relation = structure.get_relation(0);
    assert_eq!(
        relation.len(),
        6,
        "Should have 6 tuples: 3 reflexive + 2 initial + 1 transitive"
    );

    // Check reflexive pairs
    assert!(structure.query_relation(0, &[a, a]), "Should have (a,a)");
    assert!(structure.query_relation(0, &[b, b]), "Should have (b,b)");
    assert!(structure.query_relation(0, &[c, c]), "Should have (c,c)");

    // Check initial ordering
    assert!(structure.query_relation(0, &[a, b]), "Should have (a,b)");
    assert!(structure.query_relation(0, &[b, c]), "Should have (b,c)");

    // Check transitive closure!
    assert!(
        structure.query_relation(0, &[a, c]),
        "Should have (a,c) from transitive closure: (a,b) + (b,c) → (a,c)"
    );

    // Should NOT have backwards edges
    assert!(!structure.query_relation(0, &[b, a]), "Should NOT have (b,a)");
    assert!(!structure.query_relation(0, &[c, b]), "Should NOT have (c,b)");
    assert!(!structure.query_relation(0, &[c, a]), "Should NOT have (c,a)");
}
