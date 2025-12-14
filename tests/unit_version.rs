//! Unit tests for version control (commits, checkout, patches)

use geolog::core::Structure;
use geolog::id::Uuid;
use geolog::naming::NamingIndex;
use geolog::version::VersionedState;
use std::fs;
use std::path::PathBuf;
use tempfile::tempdir;

fn temp_dir() -> PathBuf {
    let dir = tempdir().unwrap();
    dir.into_path()
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
