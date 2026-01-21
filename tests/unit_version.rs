//! Unit tests for version control (commits, checkout, patches)

use geolog::core::{Context, DerivedSort, Formula, Sequent, Signature, Structure, Term};
use geolog::naming::NamingIndex;
use geolog::version::{CheckoutError, VersionedState};
use std::fs;
use std::path::PathBuf;
use tempfile::tempdir;

fn temp_dir() -> PathBuf {
    let dir = tempdir().unwrap();
    dir.keep()
}

#[test]
fn test_new_versioned_state() {
    let dir = temp_dir();
    let state = VersionedState::new(&dir);
    assert!(state.head.is_none());
    assert_eq!(state.num_commits(), 0);
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn test_commit_and_checkout() {
    let dir = temp_dir();
    let mut state = VersionedState::new(&dir);
    let mut naming = NamingIndex::new();

    // Create a structure using the state's universe
    let mut s1 = Structure::new(2);
    let (_, luid1) = s1.add_element(&mut state.universe, 0);
    let (_, luid2) = s1.add_element(&mut state.universe, 1);

    // Register names
    let uuid1 = state.universe.get(luid1).unwrap();
    let uuid2 = state.universe.get(luid2).unwrap();
    naming.insert(uuid1, vec!["foo".to_string()]);
    naming.insert(uuid2, vec!["bar".to_string()]);

    // Commit it
    let commit1 = state.commit(&s1, &naming).expect("commit should succeed");
    assert_eq!(state.num_commits(), 1);
    assert_eq!(state.head, Some(commit1));

    // Checkout and verify
    let s1_checkout = state.checkout(commit1).expect("checkout should succeed");
    assert_eq!(s1_checkout.len(), 2);

    // Clean up
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn test_multiple_commits() {
    let dir = temp_dir();
    let mut state = VersionedState::new(&dir);
    let mut naming = NamingIndex::new();

    // First commit
    let mut s1 = Structure::new(2);
    let (_, foo_luid) = s1.add_element(&mut state.universe, 0);
    let foo_uuid = state.universe.get(foo_luid).unwrap();
    naming.insert(foo_uuid, vec!["foo".to_string()]);
    let commit1 = state.commit(&s1, &naming).expect("commit 1");

    // Second commit with more elements (preserving "foo" via its Luid)
    let mut s2 = Structure::new(2);
    s2.add_element_with_luid(foo_luid, 0);
    let (_, bar_luid) = s2.add_element(&mut state.universe, 1);
    let (_, baz_luid) = s2.add_element(&mut state.universe, 0);

    // Register names for new elements
    let bar_uuid = state.universe.get(bar_luid).unwrap();
    let baz_uuid = state.universe.get(baz_luid).unwrap();
    naming.insert(bar_uuid, vec!["bar".to_string()]);
    naming.insert(baz_uuid, vec!["baz".to_string()]);

    let commit2 = state.commit(&s2, &naming).expect("commit 2");

    assert_eq!(state.num_commits(), 2);

    // Checkout first commit
    let s1_checkout = state.checkout(commit1).expect("checkout commit1");
    assert_eq!(s1_checkout.len(), 1);

    // Checkout second commit
    let s2_checkout = state.checkout(commit2).expect("checkout commit2");
    assert_eq!(s2_checkout.len(), 3);

    // List commits
    let commits = state.list_commits();
    assert_eq!(commits.len(), 2);
    assert_eq!(commits[0], commit1);
    assert_eq!(commits[1], commit2);

    // Clean up
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn test_save_and_load_patches() {
    let dir = temp_dir();

    // Create state and commit
    let commit_uuid;
    {
        let mut state = VersionedState::new(&dir);
        let mut naming = NamingIndex::new();

        let mut s = Structure::new(2);
        let (_, foo_luid) = s.add_element(&mut state.universe, 0);
        let foo_uuid = state.universe.get(foo_luid).unwrap();
        naming.insert(foo_uuid, vec!["foo".to_string()]);

        commit_uuid = state.commit(&s, &naming).expect("commit");
    }

    // Create new state and load
    {
        let mut state = VersionedState::new(&dir);
        state.load_patches().expect("load patches");

        assert_eq!(state.num_commits(), 1);
        assert_eq!(state.head, Some(commit_uuid));

        let s = state.checkout(commit_uuid).expect("checkout");
        assert_eq!(s.len(), 1);
    }

    // Clean up
    let _ = fs::remove_dir_all(&dir);
}

// ============================================================================
// Incremental Axiom Checking Tests
// ============================================================================

/// Build a simple reflexivity axiom: ∀x. x edge x
/// (every node has a self-loop)
fn build_reflexivity_theory() -> (Signature, Vec<Sequent>) {
    let mut sig = Signature::new();
    let node_sort = sig.add_sort("Node".to_string());

    // Add binary edge relation
    sig.add_relation(
        "edge".to_string(),
        DerivedSort::Product(vec![
            ("from".to_string(), DerivedSort::Base(node_sort)),
            ("to".to_string(), DerivedSort::Base(node_sort)),
        ]),
    );

    // Axiom: ∀x:Node. edge(x,x)
    // As a sequent: True ⊢ edge(x,x) [in context x:Node]
    let context = Context {
        vars: vec![("x".to_string(), DerivedSort::Base(node_sort))],
    };
    let conclusion = Formula::Rel(
        0, // edge relation
        Term::Record(vec![
            ("from".to_string(), Term::Var("x".to_string(), DerivedSort::Base(node_sort))),
            ("to".to_string(), Term::Var("x".to_string(), DerivedSort::Base(node_sort))),
        ]),
    );
    let reflexivity_axiom = Sequent {
        context,
        premise: Formula::True,
        conclusion,
    };

    (sig, vec![reflexivity_axiom])
}

#[test]
fn test_checkout_checked_valid_structure() {
    let dir = temp_dir();
    let mut state = VersionedState::new(&dir);
    let mut naming = NamingIndex::new();
    let (sig, axioms) = build_reflexivity_theory();

    // Create a valid structure: one node with self-loop
    let mut s = Structure::new(1);
    let (slid1, luid1) = s.add_element(&mut state.universe, 0);

    // Initialize relation and add self-loop
    s.init_relations(&[2]); // binary relation
    s.assert_relation(0, vec![slid1, slid1]); // edge(node1, node1)

    let uuid1 = state.universe.get(luid1).unwrap();
    naming.insert(uuid1, vec!["node1".to_string()]);

    // Commit
    let commit = state.commit(&s, &naming).expect("commit");

    // checkout_checked should succeed (structure satisfies reflexivity)
    let result = state.checkout_checked(commit, &axioms, &sig);
    assert!(result.is_ok(), "checkout_checked should succeed for valid structure");

    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn test_checkout_checked_invalid_structure() {
    let dir = temp_dir();
    let mut state = VersionedState::new(&dir);
    let mut naming = NamingIndex::new();
    let (sig, axioms) = build_reflexivity_theory();

    // Create an INVALID structure: one node WITHOUT self-loop
    let mut s = Structure::new(1);
    let (_, luid1) = s.add_element(&mut state.universe, 0);
    s.init_relations(&[2]); // binary relation, but NO tuples

    let uuid1 = state.universe.get(luid1).unwrap();
    naming.insert(uuid1, vec!["node1".to_string()]);

    // Commit (commit itself doesn't validate)
    let commit = state.commit(&s, &naming).expect("commit");

    // checkout_checked should FAIL (structure violates reflexivity)
    let result = state.checkout_checked(commit, &axioms, &sig);
    match result {
        Err(CheckoutError::PatchFailed { error, .. }) => {
            // Expected: axiom violation
            let error_str = error.to_string();
            assert!(
                error_str.contains("violated") || error_str.contains("Axiom"),
                "Error should mention axiom violation: {}",
                error_str
            );
        }
        Ok(_) => panic!("checkout_checked should fail for invalid structure"),
        Err(e) => panic!("Unexpected error type: {:?}", e),
    }

    let _ = fs::remove_dir_all(&dir);
}
