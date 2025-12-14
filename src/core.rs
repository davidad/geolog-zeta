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
    /// Relation symbols
    pub relations: Vec<RelationSymbol>,
    /// Map from relation name to RelId
    pub rel_names: HashMap<String, RelId>,
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

    pub fn add_relation(&mut self, name: String, domain: DerivedSort) -> RelId {
        let id = self.relations.len();
        self.rel_names.insert(name.clone(), id);
        self.relations.push(RelationSymbol { name, domain });
        id
    }

    pub fn lookup_sort(&self, name: &str) -> Option<SortId> {
        self.sort_names.get(name).copied()
    }

    pub fn lookup_func(&self, name: &str) -> Option<FuncId> {
        self.func_names.get(name).copied()
    }

    pub fn lookup_rel(&self, name: &str) -> Option<RelId> {
        self.rel_names.get(name).copied()
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

// ============ Structures (instances/models) ============

use crate::id::{Luid, Slid, SortSlid, Uuid, OptSlid, some_slid, get_slid};
use crate::universe::Universe;
use roaring::RoaringTreemap;

/// A structure: interpretation of a signature in FinSet
///
/// This is a model/instance of a theory — a functor from the signature to FinSet:
/// - Each sort maps to a finite set of elements
/// - Each function symbol maps to a function between those sets
/// TODO: relation symbols, interpreted as bitmaps on finitary products of finite sets
///
/// Elements are identified by Luids (Locally Universal IDs) which reference
/// UUIDs in the global Universe. This allows efficient integer operations
/// while maintaining stable identity across versions.
///
/// Note: Human-readable names are stored separately in a NamingIndex, keyed by UUID.
/// This structure contains only UUIDs and their relationships.
#[derive(Clone, Debug)]
pub struct Structure {
    /// Reference to the theory this is an instance of (Luid of the Theory element)
    /// None for structures that ARE theories (e.g., GeologMeta instances)
    pub theory_luid: Option<Luid>,

    /// Global identity: Slid → Luid (references Universe for UUID lookup)
    pub luids: Vec<Luid>,

    /// Reverse lookup: Luid → Slid (for finding elements by their global ID)
    pub luid_to_slid: HashMap<Luid, Slid>,

    /// Element sorts: Slid → SortId
    pub sorts: Vec<SortId>,

    /// Carriers: SortId → RoaringTreemap of Slids in that sort
    pub carriers: Vec<RoaringTreemap>,

    /// Functions: FuncId → Vec indexed by domain SortSlid
    /// Each Vec[sort_slid] contains the codomain Slid (or None if undefined)
    /// Using OptSlid (Option<NonMaxUsize>) which is same size as usize
    pub functions: Vec<Vec<OptSlid>>,

    /// Nested structures (for instance-valued fields)
    pub nested: HashMap<Luid, Structure>,
}

impl Structure {
    /// Create a new empty structure.
    /// Note: functions are not pre-allocated here; call `init_functions()` after
    /// all elements are added and carrier sizes are known.
    pub fn new(num_sorts: usize) -> Self {
        Self {
            theory_luid: None,
            luids: Vec::new(),
            luid_to_slid: HashMap::new(),
            sorts: Vec::new(),
            carriers: vec![RoaringTreemap::new(); num_sorts],
            functions: Vec::new(),  // Initialized later via init_functions()
            nested: HashMap::new(),
        }
    }

    /// Create a structure that is an instance of the given theory
    pub fn new_instance(theory_luid: Luid, num_sorts: usize) -> Self {
        Self {
            theory_luid: Some(theory_luid),
            ..Self::new(num_sorts)
        }
    }

    /// Initialize function storage based on domain carrier sizes.
    /// Must be called after all elements are added.
    pub fn init_functions(&mut self, domain_sort_ids: &[Option<SortId>]) {
        self.functions = domain_sort_ids
            .iter()
            .map(|opt_sort_id| {
                match opt_sort_id {
                    Some(sort_id) => vec![None; self.carrier_size(*sort_id) as usize],
                    None => Vec::new(),  // Product domains deferred
                }
            })
            .collect();
    }

    /// Add a new element to the structure, registering its UUID in the universe.
    /// Returns the (Slid, Luid) for the new element.
    /// Note: Names are registered separately in a NamingIndex.
    pub fn add_element(&mut self, universe: &mut Universe, sort_id: SortId) -> (Slid, Luid) {
        let uuid = Uuid::now_v7();
        let luid = universe.intern(uuid);
        let slid = self.add_element_with_luid(luid, sort_id);
        (slid, luid)
    }

    /// Add an element with a specific Luid (used when applying patches or loading)
    pub fn add_element_with_luid(&mut self, luid: Luid, sort_id: SortId) -> Slid {
        let slid = self.luids.len();

        self.luids.push(luid);
        self.luid_to_slid.insert(luid, slid);
        self.sorts.push(sort_id);
        self.carriers[sort_id].insert(slid as u64);

        slid
    }

    /// Add an element with a specific UUID, registering it in the universe.
    /// Used when applying patches that reference UUIDs.
    pub fn add_element_with_uuid(&mut self, universe: &mut Universe, uuid: Uuid, sort_id: SortId) -> (Slid, Luid) {
        let luid = universe.intern(uuid);
        let slid = self.add_element_with_luid(luid, sort_id);
        (slid, luid)
    }

    /// Define a function value: f(domain_elem) = codomain_elem
    /// Uses SortSlid indexing into the columnar function storage.
    pub fn define_function(&mut self, func_id: FuncId, domain_slid: Slid, codomain_slid: Slid) -> Result<(), String> {
        let domain_sort_slid = self.sort_local_id(domain_slid);

        if let Some(existing) = get_slid(self.functions[func_id][domain_sort_slid]) {
            if existing != codomain_slid {
                return Err(format!(
                    "conflicting definition: func {}(slid {}) already defined as slid {}, cannot redefine as slid {}",
                    func_id, domain_slid, existing, codomain_slid
                ));
            }
        }

        self.functions[func_id][domain_sort_slid] = some_slid(codomain_slid);
        Ok(())
    }

    /// Get a function value by SortSlid index (for iteration/lookup)
    pub fn get_function(&self, func_id: FuncId, domain_sort_slid: SortSlid) -> Option<Slid> {
        get_slid(self.functions[func_id][domain_sort_slid])
    }

    /// Get the sort-local index for an element.
    /// Note: roaring's rank(x) returns count of elements ≤ x, so we subtract 1.
    pub fn sort_local_id(&self, slid: Slid) -> SortSlid {
        let sort_id = self.sorts[slid];
        // rank returns count of elements ≤ slid; subtract 1 for 0-based index
        (self.carriers[sort_id].rank(slid as u64) - 1) as SortSlid
    }

    /// Look up element by Luid
    pub fn lookup_luid(&self, luid: Luid) -> Option<Slid> {
        self.luid_to_slid.get(&luid).copied()
    }

    /// Get the Luid for a Slid
    pub fn get_luid(&self, slid: Slid) -> Luid {
        self.luids[slid]
    }

    /// Get the UUID for a Slid (requires Universe lookup)
    pub fn get_uuid(&self, slid: Slid, universe: &Universe) -> Option<Uuid> {
        universe.get(self.luids[slid])
    }

    /// Get element count
    pub fn len(&self) -> usize {
        self.luids.len()
    }

    /// Check if empty
    pub fn is_empty(&self) -> bool {
        self.luids.is_empty()
    }

    /// Get carrier size for a sort
    pub fn carrier_size(&self, sort_id: SortId) -> u64 {
        self.carriers[sort_id].len()
    }

    /// Get the number of sorts in this structure
    pub fn num_sorts(&self) -> usize {
        self.carriers.len()
    }

    /// Get the number of functions in this structure
    pub fn num_functions(&self) -> usize {
        self.functions.len()
    }
}

// ============ Display implementations for debugging ============

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_roaring_rank() {
        let mut bm = RoaringTreemap::new();
        bm.insert(4);

        println!("bitmap: {:?}", bm.iter().collect::<Vec<_>>());
        println!("rank(4) = {}", bm.rank(4));
        println!("rank(5) = {}", bm.rank(5));
        println!("rank(3) = {}", bm.rank(3));
        println!("len = {}", bm.len());

        // rank(x) returns number of elements LESS THAN OR EQUAL to x
        assert_eq!(bm.rank(4), 1, "rank(4) on {{4}} should be 1 (one element ≤ 4)");
        assert_eq!(bm.rank(5), 1, "rank(5) on {{4}} should be 1 (one element ≤ 5)");
        assert_eq!(bm.rank(3), 0, "rank(3) on {{4}} should be 0 (no elements ≤ 3)");

        // So 0-based index of x in bitmap = rank(x) - 1
        assert_eq!(bm.rank(4) - 1, 0, "0-based index of 4 should be 0");
    }
}

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
