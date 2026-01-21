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
        // The span could be either:
        // 1. A token index (0, 1, 2, ..., n-1 for n tokens) - look up in token_spans
        // 2. Already a character position (from custom errors that captured spans)
        //
        // Best heuristic: check if the span matches a token's character range.
        // If so, it's a character position. Otherwise, treat as token index.
        let is_char_position = token_spans
            .iter()
            .any(|(_, char_range)| char_range.start == span.start && char_range.end == span.end);

        let char_span = if is_char_position {
            // Span exactly matches a token's character range - use as-is
            span.clone()
        } else if span.start < token_spans.len() {
            // Span.start is a valid token index - use token's character range
            token_spans[span.start].1.clone()
        } else if span.start == token_spans.len() {
            // End of input marker - use the end of the last token
            if let Some((_, last_range)) = token_spans.last() {
                last_range.end..last_range.end
            } else {
                0..0
            }
        } else {
            // Fallback: treat as character position
            let start = span.start.min(source.len());
            let end = span.end.min(source.len());
            start..end
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
    use chumsky::error::SimpleReason;

    let found = error
        .found()
        .map(|t| format!("'{}'", format_token(t)))
        .unwrap_or_else(|| "end of input".to_string());

    // Check for custom error messages first (from Simple::custom())
    if let SimpleReason::Custom(msg) = error.reason() {
        return msg.clone();
    }

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
        Token::And => r"/\".to_string(),
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
