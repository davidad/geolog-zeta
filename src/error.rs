//! Error formatting for Geolog
//!
//! Provides user-friendly error messages using ariadne for nice formatting.

use ariadne::{Color, Label, Report, ReportKind, Source};
use chumsky::prelude::Simple;
use std::ops::Range;

use crate::lexer::Token;

/// Format lexer errors into a user-friendly string
pub fn format_lexer_errors(source: &str, errors: Vec<Simple<char>>) -> String {
    let mut output = Vec::new();

    for error in errors {
        let span = error.span();
        let report = Report::build(ReportKind::Error, (), span.start)
            .with_message("Lexical error")
            .with_label(
                Label::new(span.clone())
                    .with_message(format_lexer_error(&error))
                    .with_color(Color::Red),
            );

        report
            .finish()
            .write(Source::from(source), &mut output)
            .expect("Failed to write error report");
    }

    String::from_utf8(output).unwrap_or_else(|_| "Error formatting failed".to_string())
}

/// Format a single lexer error into a readable message
fn format_lexer_error(error: &Simple<char>) -> String {
    let found = error
        .found()
        .map(|c| format!("'{}'", c))
        .unwrap_or_else(|| "end of input".to_string());

    if let Some(_expected) = error.expected().next() {
        format!(
            "Unexpected {}, expected {}",
            found,
            format_char_set(error.expected())
        )
    } else {
        format!("Unexpected character {}", found)
    }
}

/// Format parser errors into a user-friendly string
pub fn format_parser_errors(
    source: &str,
    errors: Vec<Simple<Token>>,
    token_spans: &[(Token, Range<usize>)],
) -> String {
    let mut output = Vec::new();

    for error in errors {
        let span = error.span();

        // Map token span to character span
        let char_span = if let Some((_, char_range)) = token_spans.get(span.start) {
            char_range.clone()
        } else if span.start > 0 && span.start == token_spans.len() {
            // End of input - use the end of the last token
            if let Some((_, last_range)) = token_spans.last() {
                last_range.end..last_range.end
            } else {
                0..0
            }
        } else {
            // Fallback to byte positions
            span.clone()
        };

        let report = Report::build(ReportKind::Error, (), char_span.start)
            .with_message("Parse error")
            .with_label(
                Label::new(char_span.clone())
                    .with_message(format_parser_error(&error))
                    .with_color(Color::Red),
            );

        report
            .finish()
            .write(Source::from(source), &mut output)
            .expect("Failed to write error report");
    }

    String::from_utf8(output).unwrap_or_else(|_| "Error formatting failed".to_string())
}

/// Format a single parser error into a readable message
fn format_parser_error(error: &Simple<Token>) -> String {
    let found = error
        .found()
        .map(|t| format!("'{}'", format_token(t)))
        .unwrap_or_else(|| "end of input".to_string());

    let expected = format_token_set(error.expected());

    if !expected.is_empty() {
        // Check for common patterns and provide helpful messages
        let expected_str = expected.join(", ");

        // Detect common mistakes
        if expected.contains(&"';'".to_string()) && error.found() == Some(&Token::Colon) {
            return format!(
                "Expected semicolon ';' to end declaration, found '{}'",
                format_token(error.found().unwrap())
            );
        }

        if expected.contains(&"':'".to_string()) && error.found() == Some(&Token::Semicolon) {
            return format!(
                "Expected colon ':' before type, found '{}'",
                format_token(error.found().unwrap())
            );
        }

        format!("Unexpected {}, expected one of: {}", found, expected_str)
    } else if let Some(label) = error.label() {
        label.to_string()
    } else {
        format!("Unexpected token {}", found)
    }
}

/// Format a token for display
fn format_token(token: &Token) -> String {
    match token {
        Token::Namespace => "namespace".to_string(),
        Token::Theory => "theory".to_string(),
        Token::Instance => "instance".to_string(),
        Token::Query => "query".to_string(),
        Token::Sort => "Sort".to_string(),
        Token::Prop => "Prop".to_string(),
        Token::Forall => "forall".to_string(),
        Token::Exists => "exists".to_string(),
        Token::True => "true".to_string(),
        Token::False => "false".to_string(),
        Token::Ident(s) => s.clone(),
        Token::LBrace => "{".to_string(),
        Token::RBrace => "}".to_string(),
        Token::LParen => "(".to_string(),
        Token::RParen => ")".to_string(),
        Token::LBracket => "[".to_string(),
        Token::RBracket => "]".to_string(),
        Token::Colon => ":".to_string(),
        Token::Semicolon => ";".to_string(),
        Token::Comma => ",".to_string(),
        Token::Dot => ".".to_string(),
        Token::Slash => "/".to_string(),
        Token::Arrow => "->".to_string(),
        Token::Eq => "=".to_string(),
        Token::Turnstile => "|-".to_string(),
        Token::Or => r"\/".to_string(),
        Token::Question => "?".to_string(),
        Token::Chase => "chase".to_string(),
    }
}

/// Format a set of expected tokens
fn format_token_set<'a>(expected: impl Iterator<Item = &'a Option<Token>>) -> Vec<String> {
    expected
        .filter_map(|opt| opt.as_ref())
        .map(|t| format!("'{}'", format_token(t)))
        .collect()
}

/// Format a set of expected characters
fn format_char_set<'a>(expected: impl Iterator<Item = &'a Option<char>>) -> String {
    let chars: Vec<String> = expected
        .filter_map(|opt| opt.as_ref())
        .map(|c| format!("'{}'", c))
        .collect();

    if chars.is_empty() {
        "valid character".to_string()
    } else if chars.len() == 1 {
        chars[0].clone()
    } else {
        chars.join(" or ")
    }
}
