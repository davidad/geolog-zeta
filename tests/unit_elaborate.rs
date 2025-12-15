//! Unit tests for theory and instance elaboration

use geolog::ast;
use geolog::core::DerivedSort;
use geolog::elaborate::{ElabError, Env, elaborate_instance, elaborate_theory};
use geolog::id::{NumericId, Slid};
use geolog::parse;
use geolog::universe::Universe;
use std::rc::Rc;

#[test]
fn test_elaborate_simple_theory() {
    let input = r#"
theory PetriNet {
    P : Sort;
    T : Sort;
    src : P -> T;
}
"#;
    let file = parse(input).expect("parse failed");
    let mut env = Env::new();

    if let ast::Declaration::Theory(t) = &file.declarations[0].node {
        let elab = elaborate_theory(&mut env, t).expect("elaboration failed");
        assert_eq!(elab.theory.name, "PetriNet");
        assert_eq!(elab.theory.signature.sorts.len(), 2);
        assert_eq!(elab.theory.signature.functions.len(), 1);
    } else {
        panic!("expected theory");
    }
}

#[test]
fn test_elaborate_parameterized_theory() {
    let input = r#"
theory PetriNet {
    P : Sort;
    T : Sort;
}

theory (N : PetriNet instance) Marking {
    token : Sort;
    token/of : token -> N/P;
}
"#;
    let file = parse(input).expect("parse failed");
    let mut env = Env::new();

    // First elaborate PetriNet
    if let ast::Declaration::Theory(t) = &file.declarations[0].node {
        let elab = elaborate_theory(&mut env, t).expect("elaboration failed");
        env.theories.insert(elab.theory.name.clone(), Rc::new(elab));
    }

    // Then elaborate Marking (which depends on PetriNet)
    if let ast::Declaration::Theory(t) = &file.declarations[1].node {
        let elab = elaborate_theory(&mut env, t).expect("elaboration failed");
        assert_eq!(elab.theory.name, "Marking");
        assert_eq!(elab.params.len(), 1);
        assert_eq!(elab.params[0].name, "N");
        assert_eq!(elab.params[0].theory_name, "PetriNet");
        // Signature now includes param sorts: N/P, N/T (from PetriNet) + token (local)
        assert_eq!(elab.theory.signature.sorts.len(), 3);
        assert!(elab.theory.signature.lookup_sort("N/P").is_some());
        assert!(elab.theory.signature.lookup_sort("N/T").is_some());
        assert!(elab.theory.signature.lookup_sort("token").is_some());
        // Functions: just token/of (PetriNet had no functions in this test)
        assert_eq!(elab.theory.signature.functions.len(), 1);
        assert!(elab.theory.signature.lookup_func("token/of").is_some());
    } else {
        panic!("expected theory");
    }
}

#[test]
fn test_elaborate_theory_with_axiom() {
    let input = r#"
theory Iso {
    X : Sort;
    Y : Sort;
    fwd : X -> Y;
    bwd : Y -> X;
    fb : forall x : X. |- x fwd bwd = x;
}
"#;
    let file = parse(input).expect("parse failed");
    let mut env = Env::new();

    if let ast::Declaration::Theory(t) = &file.declarations[0].node {
        let elab = elaborate_theory(&mut env, t).expect("elaboration failed");
        assert_eq!(elab.theory.name, "Iso");
        assert_eq!(elab.theory.signature.sorts.len(), 2);
        assert_eq!(elab.theory.signature.functions.len(), 2);
        assert_eq!(elab.theory.axioms.len(), 1);

        // Check the axiom structure
        let ax = &elab.theory.axioms[0];
        assert_eq!(ax.context.vars.len(), 1);
        assert_eq!(ax.context.vars[0].0, "x");
    } else {
        panic!("expected theory");
    }
}

#[test]
fn test_axiom_function_type_error() {
    // x is of sort X, but bwd expects Y
    let input = r#"
theory BadIso {
    X : Sort;
    Y : Sort;
    fwd : X -> Y;
    bwd : Y -> X;
    bad : forall x : X. |- x bwd = x;
}
"#;
    let file = parse(input).expect("parse failed");
    let mut env = Env::new();

    if let ast::Declaration::Theory(t) = &file.declarations[0].node {
        let result = elaborate_theory(&mut env, t);
        assert!(result.is_err(), "expected type error in axiom");

        let err = result.unwrap_err();
        match err {
            ElabError::TypeMismatch { expected, got } => {
                // expected Y (bwd's domain), got X
                assert_eq!(expected, DerivedSort::Base(1)); // Y
                assert_eq!(got, DerivedSort::Base(0)); // X
            }
            other => panic!("expected TypeMismatch error, got: {}", other),
        }
    } else {
        panic!("expected theory");
    }
}

#[test]
fn test_axiom_equality_type_error() {
    // LHS is X, RHS is Y — can't compare different sorts
    let input = r#"
theory BadEq {
    X : Sort;
    Y : Sort;
    fwd : X -> Y;
    bad : forall x : X. |- x = x fwd;
}
"#;
    let file = parse(input).expect("parse failed");
    let mut env = Env::new();

    if let ast::Declaration::Theory(t) = &file.declarations[0].node {
        let result = elaborate_theory(&mut env, t);
        assert!(result.is_err(), "expected type error in equality");

        let err = result.unwrap_err();
        match err {
            ElabError::TypeMismatch { expected, got } => {
                // LHS is X, RHS is Y
                assert_eq!(expected, DerivedSort::Base(0)); // X
                assert_eq!(got, DerivedSort::Base(1)); // Y
            }
            other => panic!("expected TypeMismatch error, got: {}", other),
        }
    } else {
        panic!("expected theory");
    }
}

#[test]
fn test_elaborate_instance() {
    let input = r#"
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

instance ExampleNet : PetriNet = {
    A : P;
    B : P;
    C : P;
    ab : T;
    ab_in : in;
    ab_in in/src = A;
    ab_in in/tgt = ab;
    ab_out : out;
    ab_out out/src = ab;
    ab_out out/tgt = B;
}
"#;
    let file = parse(input).expect("parse failed");
    let mut env = Env::new();
    let mut universe = Universe::new();

    // First elaborate PetriNet theory
    if let ast::Declaration::Theory(t) = &file.declarations[0].node {
        let elab = elaborate_theory(&mut env, t).expect("theory elaboration failed");
        env.theories.insert(elab.theory.name.clone(), Rc::new(elab));
    }

    // Then elaborate ExampleNet instance
    if let ast::Declaration::Instance(inst) = &file.declarations[1].node {
        let structure =
            elaborate_instance(&env, inst, &mut universe).expect("instance elaboration failed");

        // Elements are created in order: A(0), B(1), C(2), ab(3), ab_in(4), ab_out(5)
        assert_eq!(structure.len(), 6); // A, B, C, ab, ab_in, ab_out

        // Check carriers
        assert_eq!(structure.carrier_size(0), 3); // P: A, B, C
        assert_eq!(structure.carrier_size(1), 1); // T: ab
        assert_eq!(structure.carrier_size(2), 1); // in: ab_in
        assert_eq!(structure.carrier_size(3), 1); // out: ab_out

        // Check function definitions using the new columnar API
        // Elements by slid: A=0, B=1, C=2, ab=3, ab_in=4, ab_out=5
        let a_slid = Slid::from_usize(0);
        let ab_slid = Slid::from_usize(3);
        let ab_in_slid = Slid::from_usize(4);

        // Get the sort-local ID for ab_in
        let ab_in_sort_slid = structure.sort_local_id(ab_in_slid);

        // in/src is function 0, ab_in maps to A
        assert_eq!(structure.get_function(0, ab_in_sort_slid), Some(a_slid));
        // in/tgt is function 1, ab_in maps to ab
        assert_eq!(structure.get_function(1, ab_in_sort_slid), Some(ab_slid));
    } else {
        panic!("expected instance");
    }
}

#[test]
fn test_partial_function_error() {
    // This instance is missing the definition for ab_in in/tgt
    // (ab_in is in the domain of in/tgt but has no value defined)
    let input = r#"
theory PetriNet {
    P : Sort;
    T : Sort;
    in : Sort;
    in/src : in -> P;
    in/tgt : in -> T;
}

instance PartialNet : PetriNet = {
    A : P;
    ab : T;
    ab_in : in;
    ab_in in/src = A;
    // Missing: ab_in in/tgt = ab;
}
"#;
    let file = parse(input).expect("parse failed");
    let mut env = Env::new();
    let mut universe = Universe::new();

    // First elaborate PetriNet theory
    if let ast::Declaration::Theory(t) = &file.declarations[0].node {
        let elab = elaborate_theory(&mut env, t).expect("theory elaboration failed");
        env.theories.insert(elab.theory.name.clone(), Rc::new(elab));
    }

    // Then try to elaborate the partial instance — should fail
    if let ast::Declaration::Instance(i) = &file.declarations[1].node {
        let result = elaborate_instance(&env, i, &mut universe);
        assert!(result.is_err(), "expected error for partial function");

        let err = result.unwrap_err();
        match err {
            ElabError::PartialFunction {
                func_name,
                missing_elements,
            } => {
                assert_eq!(func_name, "in/tgt");
                assert_eq!(missing_elements, vec!["ab_in"]);
            }
            other => panic!("expected PartialFunction error, got: {}", other),
        }
    } else {
        panic!("expected instance");
    }
}

#[test]
fn test_domain_type_error() {
    // ab is of sort T, but in/src expects domain sort `in`
    let input = r#"
theory PetriNet {
    P : Sort;
    T : Sort;
    in : Sort;
    in/src : in -> P;
}

instance BadNet : PetriNet = {
    A : P;
    ab : T;
    ab in/src = A;
}
"#;
    let file = parse(input).expect("parse failed");
    let mut env = Env::new();
    let mut universe = Universe::new();

    if let ast::Declaration::Theory(t) = &file.declarations[0].node {
        let elab = elaborate_theory(&mut env, t).expect("theory elaboration failed");
        env.theories.insert(elab.theory.name.clone(), Rc::new(elab));
    }

    if let ast::Declaration::Instance(i) = &file.declarations[1].node {
        let result = elaborate_instance(&env, i, &mut universe);
        assert!(result.is_err(), "expected domain type error");

        let err = result.unwrap_err();
        match err {
            ElabError::DomainMismatch {
                func_name,
                element_name,
                expected_sort,
                actual_sort,
            } => {
                assert_eq!(func_name, "in/src");
                assert_eq!(element_name, "ab");
                assert_eq!(expected_sort, "in");
                assert_eq!(actual_sort, "T");
            }
            other => panic!("expected DomainMismatch error, got: {}", other),
        }
    } else {
        panic!("expected instance");
    }
}

#[test]
fn test_codomain_type_error() {
    // ab is of sort T, but in/src has codomain P
    let input = r#"
theory PetriNet {
    P : Sort;
    T : Sort;
    in : Sort;
    in/src : in -> P;
}

instance BadNet : PetriNet = {
    A : P;
    ab : T;
    ab_in : in;
    ab_in in/src = ab;
}
"#;
    let file = parse(input).expect("parse failed");
    let mut env = Env::new();
    let mut universe = Universe::new();

    if let ast::Declaration::Theory(t) = &file.declarations[0].node {
        let elab = elaborate_theory(&mut env, t).expect("theory elaboration failed");
        env.theories.insert(elab.theory.name.clone(), Rc::new(elab));
    }

    if let ast::Declaration::Instance(i) = &file.declarations[1].node {
        let result = elaborate_instance(&env, i, &mut universe);
        assert!(result.is_err(), "expected codomain type error");

        let err = result.unwrap_err();
        match err {
            ElabError::CodomainMismatch {
                func_name,
                element_name,
                expected_sort,
                actual_sort,
            } => {
                assert_eq!(func_name, "in/src");
                assert_eq!(element_name, "ab");
                assert_eq!(expected_sort, "P");
                assert_eq!(actual_sort, "T");
            }
            other => panic!("expected CodomainMismatch error, got: {}", other),
        }
    } else {
        panic!("expected instance");
    }
}
