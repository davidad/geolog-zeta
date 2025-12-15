//! Unit tests for lexer and parser

use chumsky::Parser;
use geolog::ast::Declaration;
use geolog::lexer::{Token, lexer};
use geolog::parse;

// ============================================================================
// Lexer tests
// ============================================================================

#[test]
fn test_lex_simple() {
    let input = "theory PetriNet { P : Sort; }";
    let result = lexer().parse(input);
    assert!(result.is_ok());
    let tokens: Vec<_> = result.unwrap().into_iter().map(|(t, _)| t).collect();
    assert_eq!(
        tokens,
        vec![
            Token::Theory,
            Token::Ident("PetriNet".to_string()),
            Token::LBrace,
            Token::Ident("P".to_string()),
            Token::Colon,
            Token::Sort,
            Token::Semicolon,
            Token::RBrace,
        ]
    );
}

#[test]
fn test_lex_arrow_and_turnstile() {
    let input = "in -> out |- x = y";
    let result = lexer().parse(input);
    assert!(result.is_ok());
    let tokens: Vec<_> = result.unwrap().into_iter().map(|(t, _)| t).collect();
    assert_eq!(
        tokens,
        vec![
            Token::Ident("in".to_string()),
            Token::Arrow,
            Token::Ident("out".to_string()),
            Token::Turnstile,
            Token::Ident("x".to_string()),
            Token::Eq,
            Token::Ident("y".to_string()),
        ]
    );
}

#[test]
fn test_lex_path() {
    let input = "N/P W/src/arc";
    let result = lexer().parse(input);
    assert!(result.is_ok());
    let tokens: Vec<_> = result.unwrap().into_iter().map(|(t, _)| t).collect();
    assert_eq!(
        tokens,
        vec![
            Token::Ident("N".to_string()),
            Token::Slash,
            Token::Ident("P".to_string()),
            Token::Ident("W".to_string()),
            Token::Slash,
            Token::Ident("src".to_string()),
            Token::Slash,
            Token::Ident("arc".to_string()),
        ]
    );
}

// ============================================================================
// Parser tests
// ============================================================================

#[test]
fn test_parse_simple_theory() {
    let input = r#"
theory PetriNet {
    P : Sort;
    T : Sort;
}
"#;
    let result = parse(input);
    assert!(result.is_ok(), "Parse error: {:?}", result);
    let file = result.unwrap();
    assert_eq!(file.declarations.len(), 1);
}

#[test]
fn test_parse_function_decl() {
    let input = r#"
theory PetriNet {
    P : Sort;
    in : Sort;
    src : in -> P;
}
"#;
    let result = parse(input);
    assert!(result.is_ok(), "Parse error: {:?}", result);
}

#[test]
fn test_parse_parameterized_theory() {
    let input = r#"
theory (N : PetriNet instance) Marking {
    token : Sort;
}
"#;
    let result = parse(input);
    assert!(result.is_ok(), "Parse error: {:?}", result);
    let file = result.unwrap();
    if let Declaration::Theory(t) = &file.declarations[0].node {
        assert_eq!(t.params.len(), 1);
        assert_eq!(t.params[0].name, "N");
    } else {
        panic!("Expected theory declaration");
    }
}

#[test]
fn test_parse_instance() {
    let input = r#"
instance ExampleNet : PetriNet = {
    A : P;
    B : P;
}
"#;
    let result = parse(input);
    assert!(result.is_ok(), "Parse error: {:?}", result);
    let file = result.unwrap();
    if let Declaration::Instance(i) = &file.declarations[0].node {
        assert_eq!(i.name, "ExampleNet");
        assert_eq!(i.body.len(), 2);
    } else {
        panic!("Expected instance declaration");
    }
}

#[test]
fn test_parse_nested_instance() {
    let input = r#"
instance problem0 : ExampleNet ReachabilityProblem = {
    initial_marking = {
        t : token;
    };
    target_marking = {
        t : token;
    };
}
"#;
    let result = parse(input);
    assert!(result.is_ok(), "Parse error: {:?}", result);
    let file = result.unwrap();
    if let Declaration::Instance(i) = &file.declarations[0].node {
        assert_eq!(i.name, "problem0");
        assert_eq!(i.body.len(), 2);
    } else {
        panic!("Expected instance declaration");
    }
}
