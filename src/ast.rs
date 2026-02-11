//! Abstract Syntax Tree for Geolog
//!
//! Based on the syntax sketched in loose_thoughts/2025-12-12_12:10.md

use std::fmt;

/// A span in the source code, for error reporting
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl Span {
    pub fn new(start: usize, end: usize) -> Self {
        Self { start, end }
    }
}

/// A node with source location
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Spanned<T> {
    pub node: T,
    pub span: Span,
}

impl<T> Spanned<T> {
    pub fn new(node: T, span: Span) -> Self {
        Self { node, span }
    }
}

/// An identifier, possibly qualified with `/` (e.g., `N/P`, `W/src/arc`)
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Path {
    pub segments: Vec<String>,
}

impl Path {
    pub fn single(name: String) -> Self {
        Self {
            segments: vec![name],
        }
    }

    pub fn is_single(&self) -> bool {
        self.segments.len() == 1
    }

    pub fn as_single(&self) -> Option<&str> {
        if self.segments.len() == 1 {
            Some(&self.segments[0])
        } else {
            None
        }
    }
}

impl fmt::Display for Path {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.segments.join("/"))
    }
}

/// A complete source file
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct File {
    pub declarations: Vec<Spanned<Declaration>>,
}

/// Top-level declarations
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Declaration {
    /// `namespace Foo;`
    Namespace(String),

    /// `theory (params) Name { body }`
    Theory(TheoryDecl),

    /// `TypeExpr instance Name { body }`
    Instance(InstanceDecl),

    /// `query Name { ? : Type; }`
    Query(QueryDecl),
}

/// A theory declaration
/// e.g., `theory (N : PetriNet instance) Marking { ... }`
/// or `theory Foo extends Bar { ... }`
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TheoryDecl {
    pub params: Vec<Param>,
    pub name: String,
    /// Optional parent theory to extend
    pub extends: Option<Path>,
    pub body: Vec<Spanned<TheoryItem>>,
}

/// A parameter to a theory
/// e.g., `N : PetriNet instance`
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Param {
    pub name: String,
    pub ty: TypeExpr,
}

/// Items that can appear in a theory body
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TheoryItem {
    /// `P : Sort;`
    Sort(String),

    /// `in.src : in -> P;`
    Function(FunctionDecl),

    /// `ax1 : forall w : W. hyps |- concl;`
    Axiom(AxiomDecl),

    /// Inline instance (for nested definitions)
    /// `initial_marking : N Marking instance;`
    Field(String, TypeExpr),
}

/// A function/morphism declaration
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunctionDecl {
    pub name: Path, // Can be dotted like `in.src`
    pub domain: TypeExpr,
    pub codomain: TypeExpr,
}

/// An axiom declaration
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AxiomDecl {
    pub name: Path, // Can be hierarchical like `ax/anc/base`
    pub quantified: Vec<QuantifiedVar>,
    pub hypotheses: Vec<Formula>,
    pub conclusion: Formula,
}

/// A quantified variable in an axiom
/// e.g., `w : W` or `w1, w2 : W`
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QuantifiedVar {
    pub names: Vec<String>,
    pub ty: TypeExpr,
}

/// A single token in a type expression stack program (concatenative parsing)
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypeToken {
    /// Push a path onto the stack (might be sort, instance ref, or theory name)
    Path(Path),

    /// The `Sort` keyword - pushes the Sort kind
    Sort,

    /// The `Prop` keyword - pushes the Prop kind
    Prop,

    /// The `instance` keyword - pops top, wraps as instance type, pushes
    Instance,

    /// Arrow - pops two types (domain, codomain), pushes function type
    /// Note: arrows are handled specially during parsing to maintain infix syntax
    Arrow,

    /// Record type literal: `[field : Type, ...]`
    /// Contains nested TypeExprs for field types (evaluated recursively)
    Record(Vec<(String, TypeExpr)>),
}

/// A type expression as a flat stack program (concatenative style)
///
/// Instead of a tree like `App(App(A, B), C)`, we store a flat sequence
/// `[Path(A), Path(B), Path(C)]` that gets evaluated during elaboration
/// when we have access to the symbol table (to know theory arities).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypeExpr {
    pub tokens: Vec<TypeToken>,
}

impl TypeExpr {
    /// Create a type expression from a single path
    pub fn single_path(p: Path) -> Self {
        Self {
            tokens: vec![TypeToken::Path(p)],
        }
    }

    /// Create the Sort kind
    pub fn sort() -> Self {
        Self {
            tokens: vec![TypeToken::Sort],
        }
    }

    /// Create the Prop kind
    pub fn prop() -> Self {
        Self {
            tokens: vec![TypeToken::Prop],
        }
    }

    /// Check if this is a single path (common case)
    pub fn as_single_path(&self) -> Option<&Path> {
        if self.tokens.len() == 1
            && let TypeToken::Path(p) = &self.tokens[0] {
                return Some(p);
            }
        None
    }

    /// Check if this is the Sort kind
    pub fn is_sort(&self) -> bool {
        matches!(self.tokens.as_slice(), [TypeToken::Sort])
    }

    /// Check if this ends with `instance`
    pub fn is_instance(&self) -> bool {
        self.tokens.last() == Some(&TypeToken::Instance)
    }

    /// Get the inner type expression (without the trailing `instance` token)
    pub fn instance_inner(&self) -> Option<Self> {
        if self.is_instance() {
            Some(Self {
                tokens: self.tokens[..self.tokens.len() - 1].to_vec(),
            })
        } else {
            None
        }
    }

    /// Check if this is the Prop kind
    pub fn is_prop(&self) -> bool {
        matches!(self.tokens.as_slice(), [TypeToken::Prop])
    }

    /// Check if this is a record type
    pub fn as_record(&self) -> Option<&Vec<(String, TypeExpr)>> {
        if self.tokens.len() == 1
            && let TypeToken::Record(fields) = &self.tokens[0] {
                return Some(fields);
            }
        None
    }
}

/// Terms (elements of types)
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Term {
    /// A variable or path: `w`, `W/src/arc`
    /// `/` is namespace qualification
    Path(Path),

    /// Function application (postfix style in surface syntax)
    /// `w W/src` means "apply W/src to w"
    App(Box<Term>, Box<Term>),

    /// Field projection: `expr .field`
    /// Note the space before `.` to distinguish from path qualification
    Project(Box<Term>, String),

    /// Record literal: `[firing: f, arc: arc]`
    Record(Vec<(String, Term)>),
}

/// Formulas (geometric logic)
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Formula {
    /// False/Bottom (⊥): inconsistency, empty disjunction
    False,

    /// Relation application: `rel(term)` or `rel([field: value, ...])`
    RelApp(String, Term),

    /// Equality: `t1 = t2`
    Eq(Term, Term),

    /// Conjunction (often implicit in antecedents)
    And(Vec<Formula>),

    /// Disjunction: `phi \/ psi`
    Or(Vec<Formula>),

    /// Existential: `exists w : W. phi`
    Exists(Vec<QuantifiedVar>, Box<Formula>),

    /// Truth
    True,
}

/// An instance declaration
/// e.g., `instance ExampleNet : PetriNet = { ... }`
/// or `instance ExampleNet : PetriNet = chase { ... }` for chase-before-check
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InstanceDecl {
    pub theory: TypeExpr,
    pub name: String,
    pub body: Vec<Spanned<InstanceItem>>,
    /// If true, run chase algorithm after elaboration before checking axioms.
    /// Syntax: `instance Name : Theory = chase { ... }`
    pub needs_chase: bool,
}

/// Items in an instance body
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InstanceItem {
    /// Element declaration: `A : P;` or `a, b, c : P;`
    Element(Vec<String>, TypeExpr),

    /// Equation: `ab_in in.src = A;`
    Equation(Term, Term),

    /// Nested instance: `initial_marking = N Marking instance { ... };`
    NestedInstance(String, InstanceDecl),

    /// Relation assertion: `[item: buy_groceries] completed;`
    /// The Term should be a record with the relation's domain fields,
    /// and String is the relation name.
    RelationAssertion(Term, String),
}

/// A query declaration
/// e.g., `query query0 { ? : ExampleNet Problem0 ReachabilityProblemSolution; }`
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QueryDecl {
    pub name: String,
    pub goal: TypeExpr,
}
