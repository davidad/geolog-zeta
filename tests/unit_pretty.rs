//! Unit tests for pretty-printing roundtrips

use geolog::parse;
use geolog::pretty::pretty_print;

#[test]
fn test_roundtrip_simple_theory() {
    let input = r#"
theory PetriNet {
  P : Sort;
  T : Sort;
  src : in -> P;
}
"#;
    let parsed = parse(input).expect("parse failed");
    let printed = pretty_print(&parsed);
    let reparsed = parse(&printed).expect("reparse failed");

    // Compare structure (ignoring spans)
    assert_eq!(parsed.declarations.len(), reparsed.declarations.len());
}

#[test]
fn test_roundtrip_instance() {
    let input = r#"
instance ExampleNet : PetriNet = {
  A : P;
  B : P;
}
"#;
    let parsed = parse(input).expect("parse failed");
    let printed = pretty_print(&parsed);
    let reparsed = parse(&printed).expect("reparse failed");

    assert_eq!(parsed.declarations.len(), reparsed.declarations.len());
}
