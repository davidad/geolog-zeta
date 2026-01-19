//! Parser for Geolog
//!
//! Parses token streams into AST.

use chumsky::prelude::*;

use crate::ast::*;
use crate::lexer::{Span, Token};

/// Create a parser for a complete Geolog file
pub fn parser() -> impl Parser<Token, File, Error = Simple<Token>> + Clone {
    declaration()
        .map_with_span(|decl, span| Spanned::new(decl, to_span(span)))
        .repeated()
        .then_ignore(end())
        .map(|declarations| File { declarations })
}

fn to_span(span: Span) -> crate::ast::Span {
    crate::ast::Span::new(span.start, span.end)
}

// ============================================================================
// Helpers
// ============================================================================

fn ident() -> impl Parser<Token, String, Error = Simple<Token>> + Clone {
    select! {
        Token::Ident(s) => s,
        // Allow keywords to be used as identifiers (e.g., in paths like ax/child/exists)
        Token::Namespace => "namespace".to_string(),
        Token::Theory => "theory".to_string(),
        Token::Instance => "instance".to_string(),
        Token::Query => "query".to_string(),
        Token::Sort => "Sort".to_string(),
        Token::Prop => "Prop".to_string(),
        Token::Forall => "forall".to_string(),
        Token::Exists => "exists".to_string(),
    }
}

/// Parse a path: `foo` or `foo/bar/baz`
/// Uses `/` for namespace qualification
fn path() -> impl Parser<Token, Path, Error = Simple<Token>> + Clone {
    ident()
        .separated_by(just(Token::Slash))
        .at_least(1)
        .map(|segments| Path { segments })
}

// ============================================================================
// Types
// ============================================================================

/// Parse a type expression
/// Returns (type_with_app_instance, type_with_arrow) to handle both cases
fn type_expr_impl() -> impl Parser<Token, TypeExpr, Error = Simple<Token>> + Clone {
    recursive(|type_expr_rec| {
        let sort = just(Token::Sort).to(TypeExpr::Sort);
        let prop = just(Token::Prop).to(TypeExpr::Prop);

        let path_type = path().map(TypeExpr::Path);

        // Record type: [field : Type, ...]
        let record_field = ident()
            .then_ignore(just(Token::Colon))
            .then(type_expr_rec.clone());

        let record_type = record_field
            .separated_by(just(Token::Comma))
            .delimited_by(just(Token::LBracket), just(Token::RBracket))
            .map(TypeExpr::Record);

        // Parenthesized type
        let paren_type = type_expr_rec
            .clone()
            .delimited_by(just(Token::LParen), just(Token::RParen));

        // Atomic types (no left recursion)
        let atom = choice((sort, prop, record_type, paren_type, path_type));

        // Type application (juxtaposition) and `instance` suffix
        let with_app_and_instance = atom
            .clone()
            .then(choice((just(Token::Instance).to(None), atom.clone().map(Some))).repeated())
            .foldl(|acc, item| match item {
                None => TypeExpr::Instance(Box::new(acc)),
                Some(arg) => TypeExpr::App(Box::new(acc), Box::new(arg)),
            });

        // Arrow type
        with_app_and_instance
            .clone()
            .then(
                just(Token::Arrow)
                    .ignore_then(with_app_and_instance.clone())
                    .repeated(),
            )
            .foldl(|a, b| TypeExpr::Arrow(Box::new(a), Box::new(b)))
    })
}

/// Parse a type expression (full, with arrows)
fn type_expr() -> impl Parser<Token, TypeExpr, Error = Simple<Token>> + Clone {
    type_expr_impl()
}

/// Parse a type expression without top-level arrows (for function domain position)
fn type_expr_no_arrow() -> impl Parser<Token, TypeExpr, Error = Simple<Token>> + Clone {
    recursive(|_type_expr_rec| {
        let sort = just(Token::Sort).to(TypeExpr::Sort);
        let prop = just(Token::Prop).to(TypeExpr::Prop);

        let path_type = path().map(TypeExpr::Path);

        // Record type - allows full type expressions inside
        let record_field = ident()
            .then_ignore(just(Token::Colon))
            .then(type_expr_impl());

        let record_type = record_field
            .separated_by(just(Token::Comma))
            .delimited_by(just(Token::LBracket), just(Token::RBracket))
            .map(TypeExpr::Record);

        // Parenthesized type - allows full type expressions inside
        let paren_type = type_expr_impl().delimited_by(just(Token::LParen), just(Token::RParen));

        // Atomic types
        let atom = choice((sort, prop, record_type, paren_type, path_type));

        // Type application and instance, but NO arrows
        atom.clone()
            .then(choice((just(Token::Instance).to(None), atom.clone().map(Some))).repeated())
            .foldl(|acc, item| match item {
                None => TypeExpr::Instance(Box::new(acc)),
                Some(arg) => TypeExpr::App(Box::new(acc), Box::new(arg)),
            })
    })
}

// ============================================================================
// Terms
// ============================================================================

fn term() -> impl Parser<Token, Term, Error = Simple<Token>> + Clone {
    recursive(|term| {
        let path_term = path().map(Term::Path);

        // Record literal: [field: term, ...]
        let record_field = ident().then_ignore(just(Token::Colon)).then(term.clone());

        let record_term = record_field
            .separated_by(just(Token::Comma))
            .delimited_by(just(Token::LBracket), just(Token::RBracket))
            .map(Term::Record);

        // Parenthesized term
        let paren_term = term
            .clone()
            .delimited_by(just(Token::LParen), just(Token::RParen));

        let atom = choice((record_term, paren_term, path_term));

        // Postfix operations:
        // - Application (juxtaposition): `w W/src` means "apply W/src to w"
        // - Field projection: `.field` projects a field from a record
        atom.clone()
            .then(
                choice((
                    // Field projection: .field
                    just(Token::Dot)
                        .ignore_then(ident())
                        .map(TermPostfix::Project),
                    // Application: another atom
                    atom.clone().map(TermPostfix::App),
                ))
                .repeated(),
            )
            .foldl(|acc, op| match op {
                TermPostfix::Project(field) => Term::Project(Box::new(acc), field),
                TermPostfix::App(arg) => Term::App(Box::new(acc), Box::new(arg)),
            })
    })
}

#[derive(Clone)]
enum TermPostfix {
    Project(String),
    App(Term),
}

/// Parse a record term specifically: [field: term, ...]
/// Used for relation assertions where we need a standalone record parser.
fn record_term() -> impl Parser<Token, Term, Error = Simple<Token>> + Clone {
    recursive(|rec_term| {
        let path_term = path().map(Term::Path);

        // Record literal: [field: term, ...]
        // Note: field values can themselves be records
        let record_field = ident()
            .then_ignore(just(Token::Colon))
            .then(choice((
                rec_term.clone(),
                path_term.clone(),
            )));

        record_field
            .separated_by(just(Token::Comma))
            .delimited_by(just(Token::LBracket), just(Token::RBracket))
            .map(Term::Record)
    })
}

// ============================================================================
// Formulas
// ============================================================================

fn formula() -> impl Parser<Token, Formula, Error = Simple<Token>> + Clone {
    recursive(|formula| {
        let quantified_var = ident()
            .separated_by(just(Token::Comma))
            .at_least(1)
            .then_ignore(just(Token::Colon))
            .then(type_expr())
            .map(|(names, ty)| QuantifiedVar { names, ty });

        // Existential: exists x : T. phi
        let exists = just(Token::Exists)
            .ignore_then(
                quantified_var
                    .clone()
                    .separated_by(just(Token::Comma))
                    .at_least(1),
            )
            .then_ignore(just(Token::Dot))
            .then(formula.clone())
            .map(|(vars, body)| Formula::Exists(vars, Box::new(body)));

        // Parenthesized formula
        let paren_formula = formula
            .clone()
            .delimited_by(just(Token::LParen), just(Token::RParen));

        // Term-based formulas: either equality (term = term) or relation application (term rel)
        // Since term() greedily parses `base rel` as App(base, Path(rel)),
        // we detect that pattern when not followed by `=` and convert to RelApp
        let term_based = term()
            .then(just(Token::Eq).ignore_then(term()).or_not())
            .try_map(|(t, opt_rhs), span| {
                match opt_rhs {
                    Some(rhs) => Ok(Formula::Eq(t, rhs)),
                    None => {
                        // Not equality - check for relation application pattern: term rel
                        match t {
                            Term::App(base, rel_term) => {
                                match *rel_term {
                                    Term::Path(path) if path.segments.len() == 1 => {
                                        Ok(Formula::RelApp(path.segments[0].clone(), *base))
                                    }
                                    _ => Err(Simple::custom(span, "expected relation name (single identifier)"))
                                }
                            }
                            _ => Err(Simple::custom(span, "expected relation application (term rel) or equality (term = term)"))
                        }
                    }
                }
            });

        let atom = choice((exists, paren_formula, term_based));

        // Disjunction: phi \/ psi
        atom.clone()
            .then(just(Token::Or).ignore_then(atom.clone()).repeated())
            .foldl(|a, b| {
                // Flatten into a single Or with multiple disjuncts
                match a {
                    Formula::Or(mut disjuncts) => {
                        disjuncts.push(b);
                        Formula::Or(disjuncts)
                    }
                    _ => Formula::Or(vec![a, b]),
                }
            })
    })
}

// ============================================================================
// Axioms
// ============================================================================

fn axiom_decl() -> impl Parser<Token, AxiomDecl, Error = Simple<Token>> + Clone {
    let quantified_var = ident()
        .separated_by(just(Token::Comma))
        .at_least(1)
        .then_ignore(just(Token::Colon))
        .then(type_expr())
        .map(|(names, ty)| QuantifiedVar { names, ty });

    let quantified_vars = just(Token::Forall)
        .ignore_then(quantified_var.separated_by(just(Token::Comma)).at_least(1))
        .then_ignore(just(Token::Dot));

    // Hypotheses before |- (optional, comma separated)
    let hypotheses = formula()
        .separated_by(just(Token::Comma))
        .then_ignore(just(Token::Turnstile));

    // name : forall vars. hyps |- conclusion
    // Name can be a path like `ax/anc/base`
    path()
        .then_ignore(just(Token::Colon))
        .then(quantified_vars)
        .then(hypotheses)
        .then(formula())
        .map(|(((name, quantified), hypotheses), conclusion)| AxiomDecl {
            name,
            quantified,
            hypotheses,
            conclusion,
        })
}

// ============================================================================
// Theory items
// ============================================================================

fn theory_item() -> impl Parser<Token, TheoryItem, Error = Simple<Token>> + Clone {
    // Sort declaration: P : Sort;
    let sort_decl = ident()
        .then_ignore(just(Token::Colon))
        .then_ignore(just(Token::Sort))
        .then_ignore(just(Token::Semicolon))
        .map(TheoryItem::Sort);

    // Function declaration: name : domain -> codomain;
    // Name can be a path like `in.src`
    // Domain is parsed without arrows to avoid ambiguity
    let function_decl = path()
        .then_ignore(just(Token::Colon))
        .then(type_expr_no_arrow())
        .then_ignore(just(Token::Arrow))
        .then(type_expr())
        .then_ignore(just(Token::Semicolon))
        .map(|((name, domain), codomain)| {
            TheoryItem::Function(FunctionDecl {
                name,
                domain,
                codomain,
            })
        });

    // Axiom: name : forall ... |- ...;
    let axiom = axiom_decl()
        .then_ignore(just(Token::Semicolon))
        .map(TheoryItem::Axiom);

    // Field declaration (catch-all for parameterized theories): name : type;
    let field_decl = ident()
        .then_ignore(just(Token::Colon))
        .then(type_expr())
        .then_ignore(just(Token::Semicolon))
        .map(|(name, ty)| TheoryItem::Field(name, ty));

    // Order matters: try more specific patterns first
    // axiom starts with "ident : forall"
    // function has "ident : type ->"
    // sort has "ident : Sort"
    // field is catch-all "ident : type"
    choice((axiom, function_decl, sort_decl, field_decl))
}

// ============================================================================
// Declarations
// ============================================================================

fn param() -> impl Parser<Token, Param, Error = Simple<Token>> + Clone {
    ident()
        .then_ignore(just(Token::Colon))
        .then(type_expr())
        .map(|(name, ty)| Param { name, ty })
}

fn theory_decl() -> impl Parser<Token, TheoryDecl, Error = Simple<Token>> + Clone {
    // Allow multiple parameter groups: (X : Sort) (Y : Sort)
    let param_group = param()
        .separated_by(just(Token::Comma))
        .at_least(1)
        .delimited_by(just(Token::LParen), just(Token::RParen));

    let params = param_group
        .repeated()
        .map(|groups| groups.into_iter().flatten().collect());

    just(Token::Theory)
        .ignore_then(params)
        .then(ident())
        .then(
            theory_item()
                .map_with_span(|item, span| Spanned::new(item, to_span(span)))
                .repeated()
                .delimited_by(just(Token::LBrace), just(Token::RBrace)),
        )
        .map(|((params, name), body)| TheoryDecl { params, name, body })
}

fn instance_item() -> impl Parser<Token, InstanceItem, Error = Simple<Token>> + Clone {
    recursive(|instance_item| {
        // Nested instance: name = { ... };
        // Type is inferred from the field declaration in the theory
        let nested = ident()
            .then_ignore(just(Token::Eq))
            .then(
                instance_item
                    .map_with_span(|item, span| Spanned::new(item, to_span(span)))
                    .repeated()
                    .delimited_by(just(Token::LBrace), just(Token::RBrace)),
            )
            .then_ignore(just(Token::Semicolon))
            .map(|(name, body)| {
                InstanceItem::NestedInstance(
                    name,
                    InstanceDecl {
                        // Type will be inferred during elaboration
                        theory: TypeExpr::Path(Path::single("_inferred".to_string())),
                        name: String::new(),
                        body,
                    },
                )
            });

        // Element declaration: A : P;
        let element = ident()
            .then_ignore(just(Token::Colon))
            .then(type_expr())
            .then_ignore(just(Token::Semicolon))
            .map(|(name, ty)| InstanceItem::Element(name, ty));

        // Equation: term = term;
        let equation = term()
            .then_ignore(just(Token::Eq))
            .then(term())
            .then_ignore(just(Token::Semicolon))
            .map(|(l, r)| InstanceItem::Equation(l, r));

        // Relation assertion: [field: value, ...] relation_name;
        // The record part is parsed as a term, relation name is an identifier
        let relation_assertion = record_term()
            .then(ident())
            .then_ignore(just(Token::Semicolon))
            .map(|(term, rel)| InstanceItem::RelationAssertion(term, rel));

        // Try nested first (ident = {), then element (ident :), then relation ([ ...),
        // then equation (fallback)
        choice((nested, element, relation_assertion, equation))
    })
}

/// Parse a type expression without the `instance` suffix (for instance declaration headers)
fn type_expr_no_instance() -> impl Parser<Token, TypeExpr, Error = Simple<Token>> + Clone {
    recursive(|_type_expr_rec| {
        let sort = just(Token::Sort).to(TypeExpr::Sort);
        let prop = just(Token::Prop).to(TypeExpr::Prop);
        let path_type = path().map(TypeExpr::Path);

        let record_field = ident()
            .then_ignore(just(Token::Colon))
            .then(type_expr_impl());

        let record_type = record_field
            .separated_by(just(Token::Comma))
            .delimited_by(just(Token::LBracket), just(Token::RBracket))
            .map(TypeExpr::Record);

        let paren_type = type_expr_impl().delimited_by(just(Token::LParen), just(Token::RParen));

        let atom = choice((sort, prop, record_type, paren_type, path_type));

        // Type application only, NO instance suffix
        atom.clone()
            .then(atom.clone().repeated())
            .foldl(|acc, arg| TypeExpr::App(Box::new(acc), Box::new(arg)))
    })
}

fn instance_decl() -> impl Parser<Token, InstanceDecl, Error = Simple<Token>> + Clone {
    // New syntax: instance Name : Type = { ... }
    just(Token::Instance)
        .ignore_then(ident())
        .then_ignore(just(Token::Colon))
        .then(type_expr_no_instance())
        .then_ignore(just(Token::Eq))
        .then(
            instance_item()
                .map_with_span(|item, span| Spanned::new(item, to_span(span)))
                .repeated()
                .delimited_by(just(Token::LBrace), just(Token::RBrace)),
        )
        .map(|((name, theory), body)| InstanceDecl { theory, name, body })
}

fn query_decl() -> impl Parser<Token, QueryDecl, Error = Simple<Token>> + Clone {
    just(Token::Query)
        .ignore_then(ident())
        .then(
            just(Token::Question)
                .ignore_then(just(Token::Colon))
                .ignore_then(type_expr())
                .then_ignore(just(Token::Semicolon))
                .delimited_by(just(Token::LBrace), just(Token::RBrace)),
        )
        .map(|(name, goal)| QueryDecl { name, goal })
}

fn namespace_decl() -> impl Parser<Token, String, Error = Simple<Token>> + Clone {
    just(Token::Namespace)
        .ignore_then(ident())
        .then_ignore(just(Token::Semicolon))
}

fn declaration() -> impl Parser<Token, Declaration, Error = Simple<Token>> + Clone {
    choice((
        namespace_decl().map(Declaration::Namespace),
        theory_decl().map(Declaration::Theory),
        instance_decl().map(Declaration::Instance),
        query_decl().map(Declaration::Query),
    ))
}

// Unit tests moved to tests/unit_parsing.rs
