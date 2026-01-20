//! Lexer for Geolog
//!
//! Tokenizes source into a stream for the parser.

use chumsky::prelude::*;
use std::ops::Range;

/// Token types for Geolog
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Token {
    // Keywords
    Namespace,
    Theory,
    Instance,
    Query,
    Sort,
    Prop,
    Forall,
    Exists,
    True,
    False,
    Chase,

    // Identifiers
    Ident(String),

    // Punctuation
    LBrace,    // {
    RBrace,    // }
    LParen,    // (
    RParen,    // )
    LBracket,  // [
    RBracket,  // ]
    Colon,     // :
    Semicolon, // ;
    Comma,     // ,
    Dot,       // .
    Slash,     // /
    Arrow,     // ->
    Eq,        // =
    Turnstile, // |-
    Or,        // \/
    Question,  // ?
}

impl std::fmt::Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Token::Namespace => write!(f, "namespace"),
            Token::Theory => write!(f, "theory"),
            Token::Instance => write!(f, "instance"),
            Token::Query => write!(f, "query"),
            Token::Sort => write!(f, "Sort"),
            Token::Prop => write!(f, "Prop"),
            Token::Forall => write!(f, "forall"),
            Token::Exists => write!(f, "exists"),
            Token::True => write!(f, "true"),
            Token::False => write!(f, "false"),
            Token::Chase => write!(f, "chase"),
            Token::Ident(s) => write!(f, "{}", s),
            Token::LBrace => write!(f, "{{"),
            Token::RBrace => write!(f, "}}"),
            Token::LParen => write!(f, "("),
            Token::RParen => write!(f, ")"),
            Token::LBracket => write!(f, "["),
            Token::RBracket => write!(f, "]"),
            Token::Colon => write!(f, ":"),
            Token::Semicolon => write!(f, ";"),
            Token::Comma => write!(f, ","),
            Token::Dot => write!(f, "."),
            Token::Slash => write!(f, "/"),
            Token::Arrow => write!(f, "->"),
            Token::Eq => write!(f, "="),
            Token::Turnstile => write!(f, "|-"),
            Token::Or => write!(f, r"\/"),
            Token::Question => write!(f, "?"),
        }
    }
}

/// Type alias for spans
pub type Span = Range<usize>;

/// Create a lexer for Geolog
pub fn lexer() -> impl Parser<char, Vec<(Token, Span)>, Error = Simple<char>> {
    let keyword_or_ident = text::ident().map(|s: String| match s.as_str() {
        "namespace" => Token::Namespace,
        "theory" => Token::Theory,
        "instance" => Token::Instance,
        "query" => Token::Query,
        "Sort" => Token::Sort,
        "Prop" => Token::Prop,
        "forall" => Token::Forall,
        "exists" => Token::Exists,
        "true" => Token::True,
        "false" => Token::False,
        "chase" => Token::Chase,
        _ => Token::Ident(s),
    });

    let punctuation = choice((
        just("->").to(Token::Arrow),
        just("|-").to(Token::Turnstile),
        just(r"\/").to(Token::Or),
        just('{').to(Token::LBrace),
        just('}').to(Token::RBrace),
        just('(').to(Token::LParen),
        just(')').to(Token::RParen),
        just('[').to(Token::LBracket),
        just(']').to(Token::RBracket),
        just(':').to(Token::Colon),
        just(';').to(Token::Semicolon),
        just(',').to(Token::Comma),
        just('.').to(Token::Dot),
        just('/').to(Token::Slash),
        just('=').to(Token::Eq),
        just('?').to(Token::Question),
    ));

    // Comments: // to end of line (handles both mid-file and end-of-file)
    // IMPORTANT: Must check for // BEFORE single / to avoid tokenizing as two Slash tokens
    let line_comment = just("//")
        .then(none_of('\n').repeated())
        .then(just('\n').or_not())  // Either newline or EOF
        .ignored();

    // Token OR comment - comments produce None, tokens produce Some
    let token_or_skip = line_comment
        .to(None)
        .or(keyword_or_ident.or(punctuation).map(Some));

    token_or_skip
        .map_with_span(|opt_tok, span| opt_tok.map(|tok| (tok, span)))
        .padded()
        .repeated()
        .then_ignore(end())
        .map(|items| items.into_iter().flatten().collect())
}

// Unit tests moved to tests/unit_parsing.rs
