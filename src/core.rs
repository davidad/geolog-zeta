//! Core internal representation for Geolog
//!
//! This is the typed, elaborated representation — closer to Owen's Lean formalization.
//! Surface syntax (ast.rs) elaborates into these types.

use std::collections::HashMap;

/// A unique identifier for sorts, used internally
pub type SortId = usize;

/// A unique identifier for function symbols
pub type FuncId = usize;

/// A unique identifier for relation symbols
pub type RelId = usize;

/// Derived sorts: base sorts or products of derived sorts
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DerivedSort {
    /// A base sort
    Base(SortId),
    /// A product of derived sorts (record/tuple)
    Product(Vec<(String, DerivedSort)>),
}

impl DerivedSort {
    pub fn base(id: SortId) -> Self {
        DerivedSort::Base(id)
    }

    pub fn product(fields: Vec<(String, DerivedSort)>) -> Self {
        DerivedSort::Product(fields)
    }

    pub fn unit() -> Self {
        DerivedSort::Product(vec![])
    }
}

/// A function symbol with its domain and codomain
#[derive(Clone, Debug)]
pub struct FunctionSymbol {
    pub name: String,
    pub domain: DerivedSort,
    pub codomain: DerivedSort,
}

/// A relation symbol with its domain (relations have no codomain — they're predicates)
#[derive(Clone, Debug)]
pub struct RelationSymbol {
    pub name: String,
    pub domain: DerivedSort,
}

/// A signature: sorts + function symbols + relation symbols
#[derive(Clone, Debug, Default)]
pub struct Signature {
    /// Sort names, indexed by SortId
    pub sorts: Vec<String>,
    /// Map from sort name to SortId
    pub sort_names: HashMap<String, SortId>,
    /// Function symbols
    pub functions: Vec<FunctionSymbol>,
    /// Map from function name to FuncId
    pub func_names: HashMap<String, FuncId>,
    /// Relation symbols (currently unused in geolog surface syntax, but present in the formalism)
    pub relations: Vec<RelationSymbol>,
}

impl Signature {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add_sort(&mut self, name: String) -> SortId {
        let id = self.sorts.len();
        self.sort_names.insert(name.clone(), id);
        self.sorts.push(name);
        id
    }

    pub fn add_function(&mut self, name: String, domain: DerivedSort, codomain: DerivedSort) -> FuncId {
        let id = self.functions.len();
        self.func_names.insert(name.clone(), id);
        self.functions.push(FunctionSymbol { name, domain, codomain });
        id
    }

    pub fn lookup_sort(&self, name: &str) -> Option<SortId> {
        self.sort_names.get(name).copied()
    }

    pub fn lookup_func(&self, name: &str) -> Option<FuncId> {
        self.func_names.get(name).copied()
    }
}

/// A typing context: a list of (variable_name, sort) pairs
#[derive(Clone, Debug, Default)]
pub struct Context {
    /// Variables in scope, with their sorts
    pub vars: Vec<(String, DerivedSort)>,
}

impl Context {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn extend(&self, name: String, sort: DerivedSort) -> Self {
        let mut new_ctx = self.clone();
        new_ctx.vars.push((name, sort));
        new_ctx
    }

    pub fn lookup(&self, name: &str) -> Option<(usize, &DerivedSort)> {
        self.vars.iter().enumerate().rev()
            .find(|(_, (n, _))| n == name)
            .map(|(i, (_, s))| (i, s))
    }
}

/// A well-typed term
#[derive(Clone, Debug)]
pub enum Term {
    /// Variable reference (de Bruijn index would be cleaner, but names are more debuggable)
    Var(String, DerivedSort),
    /// Function application
    App(FuncId, Box<Term>),
    /// Record/tuple construction
    Record(Vec<(String, Term)>),
    /// Field projection
    Project(Box<Term>, String),
}

impl Term {
    /// Get the sort of this term
    pub fn sort(&self, sig: &Signature) -> DerivedSort {
        match self {
            Term::Var(_, s) => s.clone(),
            Term::App(f, _) => sig.functions[*f].codomain.clone(),
            Term::Record(fields) => {
                DerivedSort::Product(
                    fields.iter()
                        .map(|(n, t)| (n.clone(), t.sort(sig)))
                        .collect()
                )
            }
            Term::Project(t, field) => {
                if let DerivedSort::Product(fields) = t.sort(sig) {
                    fields.into_iter()
                        .find(|(n, _)| n == field)
                        .map(|(_, s)| s)
                        .expect("field not found in product")
                } else {
                    panic!("projection on non-product")
                }
            }
        }
    }
}

/// A well-typed geometric formula
#[derive(Clone, Debug)]
pub enum Formula {
    /// Relation (currently unused — geometric logic often encodes via equations)
    Rel(RelId, Term),
    /// Truth
    True,
    /// Falsity
    False,
    /// Conjunction
    Conj(Vec<Formula>),
    /// Disjunction (infinitary in general, but finite for now)
    Disj(Vec<Formula>),
    /// Equality of terms (must have same sort)
    Eq(Term, Term),
    /// Existential quantification
    Exists(String, DerivedSort, Box<Formula>),
}

/// A sequent: premise ⊢ conclusion (both in the same context)
#[derive(Clone, Debug)]
pub struct Sequent {
    /// The context (bound variables)
    pub context: Context,
    /// The premise (antecedent)
    pub premise: Formula,
    /// The conclusion (consequent)
    pub conclusion: Formula,
}

/// A theory: a signature plus a set of axioms (sequents)
#[derive(Clone, Debug)]
pub struct Theory {
    pub name: String,
    pub signature: Signature,
    pub axioms: Vec<Sequent>,
}

/// A theory can have parameters (other theories it depends on)
/// Note: This is forward-declared; the actual type is Rc<ElaboratedTheory>
/// but we can't reference it here due to ordering. We use a type alias.
#[derive(Clone, Debug)]
pub struct TheoryParam {
    pub name: String,
    // This will be an Rc<ElaboratedTheory> in practice
    pub theory_name: String,
}

/// An elaborated theory with its parameters
#[derive(Clone, Debug)]
pub struct ElaboratedTheory {
    pub params: Vec<TheoryParam>,
    pub theory: Theory,
}

// ============ Display implementations for debugging ============

impl std::fmt::Display for DerivedSort {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DerivedSort::Base(id) => write!(f, "Sort#{}", id),
            DerivedSort::Product(fields) if fields.is_empty() => write!(f, "()"),
            DerivedSort::Product(fields) => {
                write!(f, "[")?;
                for (i, (name, sort)) in fields.iter().enumerate() {
                    if i > 0 { write!(f, ", ")?; }
                    write!(f, "{}: {}", name, sort)?;
                }
                write!(f, "]")
            }
        }
    }
}
