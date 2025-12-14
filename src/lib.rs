//! Geolog: A language for geometric logic
//!
//! Geolog is a type theory with semantics in topoi and geometric morphisms,
//! designed as a unified language for database schemas, queries, and migrations.

pub mod ast;
pub mod core;
pub mod elaborate;
pub mod id;
pub mod lexer;
pub mod meta;
pub mod naming;
pub mod parser;
pub mod patch;
pub mod pretty;
pub mod repl;
pub mod universe;
pub mod version;
pub mod workspace;

pub use ast::*;
pub use lexer::lexer;
pub use parser::parser;
pub use pretty::pretty_print;

/// Parse a Geolog source string into an AST
pub fn parse(input: &str) -> Result<File, String> {
    use chumsky::prelude::*;

    let tokens = lexer::lexer()
        .parse(input)
        .map_err(|errs| format!("Lexer errors: {:?}", errs))?;

    let token_stream: Vec<_> = tokens.iter().map(|(t, s)| (t.clone(), s.clone())).collect();
    let len = input.len();

    parser::parser()
        .parse(chumsky::Stream::from_iter(
            len..len + 1,
            token_stream.into_iter(),
        ))
        .map_err(|errs| format!("Parser errors: {:?}", errs))
}
