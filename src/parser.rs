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

/// Assign positional names ("0", "1", ...) to unnamed fields in a record
/// Only unnamed fields consume positional indices, so named fields can be reordered freely:
/// `[a, on: b, c]` → `[("0", a), ("on", b), ("1", c)]`
/// `[on: b, a, c]` → `[("on", b), ("0", a), ("1", c)]`
fn assign_positional_names<T>(fields: Vec<(Option<String>, T)>) -> Vec<(String, T)> {
    let mut positional_idx = 0usize;
    fields
        .into_iter()
        .map(|(name, val)| {
            let field_name = match name {
                Some(n) => n,
                None => {
                    let n = positional_idx.to_string();
                    positional_idx += 1;
                    n
                }
            };
            (field_name, val)
        })
        .collect()
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
// Types (Concatenative Stack-Based Parsing)
// ============================================================================

/// Parse a full type expression with arrows (concatenative style)
///
/// `A B -> C D -> E` becomes tokens: [A, B, C, D, E, Arrow, Arrow]
/// which evaluates right-to-left: A B -> (C D -> E)
///
/// Uses a single recursive() to handle mutual recursion between type expressions
/// (for parentheses and record fields) and atomic type tokens.
fn type_expr_impl() -> impl Parser<Token, TypeExpr, Error = Simple<Token>> + Clone {
    recursive(|type_expr_rec| {
        // === Atomic type tokens (non-recursive) ===
        let sort = just(Token::Sort).to(TypeToken::Sort);
        let prop = just(Token::Prop).to(TypeToken::Prop);
        let instance = just(Token::Instance).to(TypeToken::Instance);
        let path_tok = path().map(TypeToken::Path);

        // Record type: [field: Type, ...] or [Type, ...] or mixed
        // Named field: `name: Type`
        let named_type_field = ident()
            .then_ignore(just(Token::Colon))
            .then(type_expr_rec.clone())
            .map(|(name, ty)| (Some(name), ty));
        // Positional field: `Type`
        let positional_type_field = type_expr_rec.clone().map(|ty| (None, ty));
        let record_field = choice((named_type_field, positional_type_field));

        let record = record_field
            .separated_by(just(Token::Comma))
            .delimited_by(just(Token::LBracket), just(Token::RBracket))
            .map(|fields| TypeToken::Record(assign_positional_names(fields)));

        // Single atomic token
        let single_token = choice((sort, prop, instance, record, path_tok)).map(|t| vec![t]);

        // Parenthesized expression - flatten tokens into parent sequence
        let paren_expr = type_expr_rec
            .delimited_by(just(Token::LParen), just(Token::RParen))
            .map(|expr: TypeExpr| expr.tokens);

        // A "chunk item" is either a paren group or a single token
        let chunk_item = choice((paren_expr, single_token));

        // A "chunk" is one or more items (before an arrow or end)
        let chunk = chunk_item
            .repeated()
            .at_least(1)
            .map(|items: Vec<Vec<TypeToken>>| items.into_iter().flatten().collect::<Vec<_>>());

        // Full type expression: chunks separated by arrows
        chunk
            .separated_by(just(Token::Arrow))
            .at_least(1)
            .map(|chunks: Vec<Vec<TypeToken>>| {
                // For right-associative arrows:
                // chunks: [[A, B], [C, D], [E]]
                // result: [A, B, C, D, E, Arrow, Arrow]
                //
                // The evaluator processes Arrow tokens right-to-left:
                // Stack after all tokens pushed: [A, B, C, D, E]
                // Arrow 1: pop C,D -> push Arrow{C,D} -> [A, B, Arrow{C,D}, E]
                // Wait, that's not right either...
                //
                // Actually the order should be:
                // [A, B, Arrow, C, D, Arrow, E] for left-to-right application
                // But we want (A B) -> ((C D) -> E) for right-associative
                //
                // For postfix arrows:
                // [A, B, C, D, E, Arrow, Arrow] means:
                // - Push A, B, C, D, E
                // - Arrow: pop E, pop D -> push Arrow{D,E}
                // - Arrow: pop Arrow{D,E}, pop C -> push Arrow{C, Arrow{D,E}}
                // Hmm, this also doesn't work well for multi-token chunks.
                //
                // Actually, let's just flatten all and append arrows.
                // The evaluator will be responsible for parsing chunks correctly.

                let num_arrows = chunks.len() - 1;
                let mut tokens: Vec<TypeToken> = chunks.into_iter().flatten().collect();

                // Add Arrow tokens at end
                for _ in 0..num_arrows {
                    tokens.push(TypeToken::Arrow);
                }

                TypeExpr { tokens }
            })
    })
}

/// Parse a type expression (full, with arrows)
fn type_expr() -> impl Parser<Token, TypeExpr, Error = Simple<Token>> + Clone {
    type_expr_impl()
}

/// Parse a type expression without top-level arrows (for function domain position)
///
/// This parses a single "chunk" - type tokens without arrows at the top level.
/// Used for places like function domain where we don't want `A -> B` to be ambiguous.
fn type_expr_no_arrow() -> impl Parser<Token, TypeExpr, Error = Simple<Token>> + Clone {
    recursive(|_type_expr_rec| {
        // Atomic type tokens
        let sort = just(Token::Sort).to(TypeToken::Sort);
        let prop = just(Token::Prop).to(TypeToken::Prop);
        let instance = just(Token::Instance).to(TypeToken::Instance);
        let path_tok = path().map(TypeToken::Path);

        // Record type: [field: Type, ...] or [Type, ...] or mixed
        // Named field: `name: Type`
        let named_type_field = ident()
            .then_ignore(just(Token::Colon))
            .then(type_expr_impl())
            .map(|(name, ty)| (Some(name), ty));
        // Positional field: `Type`
        let positional_type_field = type_expr_impl().map(|ty| (None, ty));
        let record_field = choice((named_type_field, positional_type_field));

        let record = record_field
            .separated_by(just(Token::Comma))
            .delimited_by(just(Token::LBracket), just(Token::RBracket))
            .map(|fields| TypeToken::Record(assign_positional_names(fields)));

        // Single atomic token
        let single_token = choice((sort, prop, instance, record, path_tok)).map(|t| vec![t]);

        // Parenthesized expression - can contain full type expr with arrows
        let paren_expr = type_expr_impl()
            .delimited_by(just(Token::LParen), just(Token::RParen))
            .map(|expr: TypeExpr| expr.tokens);

        // A "chunk item" is either a paren group or a single token
        let chunk_item = choice((paren_expr, single_token));

        // One or more items, no arrows
        chunk_item
            .repeated()
            .at_least(1)
            .map(|items: Vec<Vec<TypeToken>>| {
                TypeExpr {
                    tokens: items.into_iter().flatten().collect(),
                }
            })
    })
}

// ============================================================================
// Terms
// ============================================================================

fn term() -> impl Parser<Token, Term, Error = Simple<Token>> + Clone {
    recursive(|term| {
        let path_term = path().map(Term::Path);

        // Record literal: [field: term, ...] or [term, ...] or mixed
        // Named field: `name: value`
        // Positional field: `value` (gets name "0", "1", etc.)
        let named_field = ident()
            .then_ignore(just(Token::Colon))
            .then(term.clone())
            .map(|(name, val)| (Some(name), val));
        let positional_field = term.clone().map(|val| (None, val));
        let record_field = choice((named_field, positional_field));

        let record_term = record_field
            .separated_by(just(Token::Comma))
            .delimited_by(just(Token::LBracket), just(Token::RBracket))
            .map(|fields| Term::Record(assign_positional_names(fields)));

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

/// Parse a record term specifically: [field: term, ...] or [term, ...] or mixed
/// Used for relation assertions where we need a standalone record parser.
fn record_term() -> impl Parser<Token, Term, Error = Simple<Token>> + Clone {
    recursive(|rec_term| {
        let path_term = path().map(Term::Path);
        let inner_term = choice((rec_term.clone(), path_term.clone()));

        // Named field: `name: value`
        let named_field = ident()
            .then_ignore(just(Token::Colon))
            .then(inner_term.clone())
            .map(|(name, val)| (Some(name), val));
        // Positional field: `value`
        let positional_field = inner_term.map(|val| (None, val));
        let record_field = choice((named_field, positional_field));

        record_field
            .separated_by(just(Token::Comma))
            .delimited_by(just(Token::LBracket), just(Token::RBracket))
            .map(|fields| Term::Record(assign_positional_names(fields)))
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

        // Existential: exists x : T. phi1, phi2, ...
        // The body is a conjunction of formulas (comma-separated).
        // This is standard geometric logic syntax.
        let exists = just(Token::Exists)
            .ignore_then(
                quantified_var
                    .clone()
                    .separated_by(just(Token::Comma))
                    .at_least(1),
            )
            .then_ignore(just(Token::Dot))
            .then(formula.clone().separated_by(just(Token::Comma)).at_least(1))
            .map(|(vars, body_conjuncts)| {
                let body = if body_conjuncts.len() == 1 {
                    body_conjuncts.into_iter().next().unwrap()
                } else {
                    Formula::And(body_conjuncts)
                };
                Formula::Exists(vars, Box::new(body))
            });

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

        // Literals
        let true_lit = just(Token::True).to(Formula::True);
        let false_lit = just(Token::False).to(Formula::False);

        let atom = choice((true_lit, false_lit, exists, paren_formula, term_based));

        // Conjunction: phi /\ psi (binds tighter than disjunction)
        let conjunction = atom
            .clone()
            .then(just(Token::And).ignore_then(atom.clone()).repeated())
            .foldl(|a, b| {
                // Flatten into a single And with multiple conjuncts
                match a {
                    Formula::And(mut conjuncts) => {
                        conjuncts.push(b);
                        Formula::And(conjuncts)
                    }
                    _ => Formula::And(vec![a, b]),
                }
            });

        // Disjunction: phi \/ psi
        conjunction
            .clone()
            .then(just(Token::Or).ignore_then(conjunction.clone()).repeated())
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
    // Optional `extends ParentTheory`
    let extends_clause = ident()
        .try_map(|s, span| {
            if s == "extends" {
                Ok(())
            } else {
                Err(Simple::custom(span, "expected 'extends'"))
            }
        })
        .ignore_then(path())
        .or_not();

    // A param group in parens: (X : Type, Y : Type)
    let param_group = param()
        .separated_by(just(Token::Comma))
        .at_least(1)
        .delimited_by(just(Token::LParen), just(Token::RParen));

    // After 'theory', we may have:
    // 1. One or more param groups followed by an identifier: (X:T) (Y:U) Name
    // 2. Just an identifier (no params): Name
    // 3. Just '{' (missing name - ERROR)
    //
    // Strategy: Parse by looking at the first token after 'theory':
    // - If '(' -> parse params, then expect name
    // - If identifier -> that's the name, no params
    // - If '{' -> error: missing name

    // Helper to parse params then name
    let params_then_name = param_group
        .repeated()
        .at_least(1)
        .map(|groups: Vec<Vec<Param>>| groups.into_iter().flatten().collect::<Vec<Param>>())
        .then(ident())
        .map(|(params, name)| (params, name));

    // No params, just a name
    let just_name = ident().map(|name| (Vec::<Param>::new(), name));

    // Error case: '{' with no name - emit error at the '{' token's location
    // Use `just` to peek at '{' and capture its position, then emit a helpful error
    // We DON'T consume the '{' because we need it for the body parser
    let missing_name = just(Token::LBrace)
        .map_with_span(|_, span: Span| span) // Capture '{' token's span
        .rewind() // Rewind to not consume '{' - we need it for the body
        .validate(|brace_span, _, emit| {
            emit(Simple::custom(
                brace_span,
                "expected theory name - anonymous theories are not allowed. \
                 Use: theory MyTheoryName { ... }",
            ));
            // Return dummy values for error recovery
            (Vec::<Param>::new(), "_anonymous_".to_string())
        });

    // Parse theory keyword, then params+name in one of the three ways
    // Order matters: try params first (if '('), then name (if ident), then error (if '{')
    just(Token::Theory)
        .ignore_then(choice((params_then_name, just_name, missing_name)))
        .then(extends_clause)
        .then(
            theory_item()
                .map_with_span(|item, span| Spanned::new(item, to_span(span)))
                .repeated()
                .delimited_by(just(Token::LBrace), just(Token::RBrace)),
        )
        .map(|(((params, name), extends), body)| TheoryDecl {
            params,
            name,
            extends,
            body,
        })
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
                        theory: TypeExpr::single_path(Path::single("_inferred".to_string())),
                        name: String::new(),
                        body,
                        needs_chase: false,
                    },
                )
            });

        // Element declaration: A : P; or a, b, c : P;
        let element = ident()
            .separated_by(just(Token::Comma))
            .at_least(1)
            .then_ignore(just(Token::Colon))
            .then(type_expr())
            .then_ignore(just(Token::Semicolon))
            .map(|(names, ty)| InstanceItem::Element(names, ty));

        // Equation: term = term;
        let equation = term()
            .then_ignore(just(Token::Eq))
            .then(term())
            .then_ignore(just(Token::Semicolon))
            .map(|(l, r)| InstanceItem::Equation(l, r));

        // Relation assertion: [field: value, ...] relation_name; (multi-ary)
        //                  or: element relation_name; (unary)
        // Multi-ary with explicit record
        let relation_assertion_record = record_term()
            .then(ident())
            .then_ignore(just(Token::Semicolon))
            .map(|(term, rel)| InstanceItem::RelationAssertion(term, rel));

        // Unary relation: element relation_name;
        // This parses as: path followed by another ident, then semicolon
        // We wrap the element in a single-field record for uniform handling
        let relation_assertion_unary = path()
            .map(Term::Path)
            .then(ident())
            .then_ignore(just(Token::Semicolon))
            .map(|(elem, rel)| InstanceItem::RelationAssertion(elem, rel));

        // Try nested first (ident = {), then element (ident :), then record relation ([ ...),
        // then unary relation (ident ident ;), then equation (fallback with =)
        choice((nested, element, relation_assertion_record, relation_assertion_unary, equation))
    })
}

/// Parse a single type token without 'instance' (for instance declaration headers)
fn type_token_no_instance() -> impl Parser<Token, TypeToken, Error = Simple<Token>> + Clone {
    let sort = just(Token::Sort).to(TypeToken::Sort);
    let prop = just(Token::Prop).to(TypeToken::Prop);
    // No instance token here!

    let path_tok = path().map(TypeToken::Path);

    // Record type with full type expressions inside
    let record_field = ident()
        .then_ignore(just(Token::Colon))
        .then(type_expr_impl());

    let record = record_field
        .separated_by(just(Token::Comma))
        .delimited_by(just(Token::LBracket), just(Token::RBracket))
        .map(TypeToken::Record);

    choice((sort, prop, record, path_tok))
}

/// Parse a type expression without the `instance` suffix (for instance declaration headers)
fn type_expr_no_instance() -> impl Parser<Token, TypeExpr, Error = Simple<Token>> + Clone {
    // Parenthesized type - parse inner full type expr
    let paren_expr = type_expr_impl()
        .delimited_by(just(Token::LParen), just(Token::RParen))
        .map(|expr| expr.tokens);

    // Single token (no instance allowed)
    let single = type_token_no_instance().map(|t| vec![t]);

    // Either paren group or single token
    let item = choice((paren_expr, single));

    // Collect all tokens
    item.repeated()
        .at_least(1)
        .map(|items| TypeExpr {
            tokens: items.into_iter().flatten().collect(),
        })
}

fn instance_decl() -> impl Parser<Token, InstanceDecl, Error = Simple<Token>> + Clone {
    // Syntax: instance Name : Type = { ... }
    //     or: instance Name : Type = chase { ... }
    just(Token::Instance)
        .ignore_then(ident())
        .then_ignore(just(Token::Colon))
        .then(type_expr_no_instance())
        .then_ignore(just(Token::Eq))
        .then(just(Token::Chase).or_not())
        .then(
            instance_item()
                .map_with_span(|item, span| Spanned::new(item, to_span(span)))
                .repeated()
                .delimited_by(just(Token::LBrace), just(Token::RBrace)),
        )
        .map(|(((name, theory), needs_chase), body)| InstanceDecl {
            theory,
            name,
            body,
            needs_chase: needs_chase.is_some(),
        })
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
