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

    pub fn add_function(
        &mut self,
        name: String,
        domain: DerivedSort,
        codomain: DerivedSort,
    ) -> FuncId {
        let id = self.functions.len();
        self.func_names.insert(name.clone(), id);
        self.functions.push(FunctionSymbol {
            name,
            domain,
            codomain,
        });
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

// ============ Relation Storage ============

use crate::id::{NumericId, Slid};
use roaring::RoaringTreemap;

/// Tuple ID: index into the append-only tuple log
pub type TupleId = usize;

/// Trait for relation storage implementations.
///
/// Different implementations optimize for different access patterns:
/// - VecRelation: append-only log + membership bitmap (good for patches)
/// - Future: Dancing Cells for backtracking, multi-order tries for joins
pub trait RelationStorage {
    /// Check if a tuple is in the relation
    fn contains(&self, tuple: &[Slid]) -> bool;

    /// Insert a tuple, returns true if newly inserted
    fn insert(&mut self, tuple: Vec<Slid>) -> bool;

    /// Remove a tuple by marking it as not in extent, returns true if was present
    fn remove(&mut self, tuple: &[Slid]) -> bool;

    /// Number of tuples currently in the relation
    fn len(&self) -> usize;

    /// Check if empty
    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Arity of tuples in this relation
    fn arity(&self) -> usize;
}

/// Append-only tuple log with membership bitmap.
///
/// Tuples are assigned stable IDs (their index in the log).
/// The extent bitmap tracks which tuples are currently "true".
/// This representation handles cardinality changes gracefully since
/// tuple IDs are independent of sort cardinalities.
#[derive(Clone, Debug)]
pub struct VecRelation {
    /// Arity of this relation (number of Slids per tuple)
    pub arity: usize,
    /// Append-only log of all tuples ever inserted
    pub tuples: Vec<Vec<Slid>>,
    /// Map from tuple to its ID (for O(1) lookup)
    pub tuple_to_id: HashMap<Vec<Slid>, TupleId>,
    /// Bitmap of tuple IDs currently in the extent
    pub extent: RoaringTreemap,
}

impl VecRelation {
    /// Create a new empty relation with given arity
    pub fn new(arity: usize) -> Self {
        Self {
            arity,
            tuples: Vec::new(),
            tuple_to_id: HashMap::new(),
            extent: RoaringTreemap::new(),
        }
    }

    /// Get a tuple by ID
    pub fn get_tuple(&self, id: TupleId) -> Option<&[Slid]> {
        self.tuples.get(id).map(|v| v.as_slice())
    }

    /// Iterate over all tuples currently in the extent
    pub fn iter(&self) -> impl Iterator<Item = &[Slid]> + '_ {
        self.extent.iter().filter_map(|id| self.tuples.get(id as usize).map(|v| v.as_slice()))
    }

    /// Iterate over tuple IDs currently in the extent
    pub fn iter_ids(&self) -> impl Iterator<Item = TupleId> + '_ {
        self.extent.iter().map(|id| id as TupleId)
    }
}

impl RelationStorage for VecRelation {
    fn contains(&self, tuple: &[Slid]) -> bool {
        if let Some(&id) = self.tuple_to_id.get(tuple) {
            self.extent.contains(id as u64)
        } else {
            false
        }
    }

    fn insert(&mut self, tuple: Vec<Slid>) -> bool {
        debug_assert_eq!(tuple.len(), self.arity, "tuple arity mismatch");

        if let Some(&id) = self.tuple_to_id.get(&tuple) {
            // Tuple exists in log, just mark as present
            if self.extent.contains(id as u64) {
                false // Already present
            } else {
                self.extent.insert(id as u64);
                true
            }
        } else {
            // New tuple, append to log
            let id = self.tuples.len();
            self.tuple_to_id.insert(tuple.clone(), id);
            self.tuples.push(tuple);
            self.extent.insert(id as u64);
            true
        }
    }

    fn remove(&mut self, tuple: &[Slid]) -> bool {
        if let Some(&id) = self.tuple_to_id.get(tuple) {
            self.extent.remove(id as u64)
        } else {
            false
        }
    }

    fn len(&self) -> usize {
        self.extent.len() as usize
    }

    fn arity(&self) -> usize {
        self.arity
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
        self.vars
            .iter()
            .enumerate()
            .rev()
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
            Term::Record(fields) => DerivedSort::Product(
                fields
                    .iter()
                    .map(|(n, t)| (n.clone(), t.sort(sig)))
                    .collect(),
            ),
            Term::Project(t, field) => {
                if let DerivedSort::Product(fields) = t.sort(sig) {
                    fields
                        .into_iter()
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

use crate::id::{Luid, OptLuid, OptSlid, SortSlid, Uuid, get_slid, some_slid};
use crate::universe::Universe;

/// A function column: either local (Slid) or external (Luid) references.
///
/// For functions with local codomain (e.g., `src : in -> P` where P is local),
/// we use `Local(Vec<OptSlid>)` for tight columnar storage.
///
/// For functions with external codomain (e.g., `token/of : token -> N/P` where
/// N/P comes from a parent instance), we use `External(Vec<OptLuid>)` to
/// reference elements in the parent by their Luid.
#[derive(Clone, Debug)]
pub enum FunctionColumn {
    /// Codomain is local: values are Slids within this structure
    Local(Vec<OptSlid>),
    /// Codomain is external (from parent): values are Luids (globally unique)
    External(Vec<OptLuid>),
}

impl FunctionColumn {
    /// Get the length of this column
    pub fn len(&self) -> usize {
        match self {
            FunctionColumn::Local(v) => v.len(),
            FunctionColumn::External(v) => v.len(),
        }
    }

    /// Check if empty
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Check if this is a local column
    pub fn is_local(&self) -> bool {
        matches!(self, FunctionColumn::Local(_))
    }

    /// Get local value at index (panics if external or out of bounds)
    pub fn get_local(&self, idx: usize) -> OptSlid {
        match self {
            FunctionColumn::Local(v) => v[idx],
            FunctionColumn::External(_) => panic!("get_local called on external column"),
        }
    }

    /// Get external value at index (panics if local or out of bounds)
    pub fn get_external(&self, idx: usize) -> OptLuid {
        match self {
            FunctionColumn::External(v) => v[idx],
            FunctionColumn::Local(_) => panic!("get_external called on local column"),
        }
    }

    /// Iterate over local values (panics if external)
    pub fn iter_local(&self) -> impl Iterator<Item = &OptSlid> {
        match self {
            FunctionColumn::Local(v) => v.iter(),
            FunctionColumn::External(_) => panic!("iter_local called on external column"),
        }
    }

    /// Iterate over external values (panics if local)
    pub fn iter_external(&self) -> impl Iterator<Item = &OptLuid> {
        match self {
            FunctionColumn::External(v) => v.iter(),
            FunctionColumn::Local(_) => panic!("iter_external called on local column"),
        }
    }

    /// Get as local column (returns None if external)
    pub fn as_local(&self) -> Option<&Vec<OptSlid>> {
        match self {
            FunctionColumn::Local(v) => Some(v),
            FunctionColumn::External(_) => None,
        }
    }

    /// Get as mutable local column (returns None if external)
    pub fn as_local_mut(&mut self) -> Option<&mut Vec<OptSlid>> {
        match self {
            FunctionColumn::Local(v) => Some(v),
            FunctionColumn::External(_) => None,
        }
    }
}

/// A structure: interpretation of a signature in FinSet
///
/// This is a model/instance of a theory — a functor from the signature to FinSet:
/// - Each sort maps to a finite set of elements
/// - Each function symbol maps to a function between those sets
/// - Each relation symbol maps to a set of tuples (subset of product of carriers)
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

    /// Functions: FuncId → FunctionColumn
    /// Each column is indexed by domain SortSlid and contains codomain references.
    /// Local codomains use Slid; external codomains (from parents) use Luid.
    pub functions: Vec<FunctionColumn>,

    /// Relations: RelId → VecRelation (append-only tuple log + membership bitmap)
    pub relations: Vec<VecRelation>,

    /// Parent instances for parameterized theories (virtual import).
    /// Maps param name → instance name of immutable parent.
    /// E.g., for `problem0 : ExampleNet ReachabilityProblem`, this contains {"N": "ExampleNet"}
    pub parents: HashMap<String, String>,

    /// Imported sorts: local sort_id → (parent_instance_name, parent_sort_id).
    /// These sorts don't have local carriers; queries delegate to the parent.
    /// E.g., for `problem0 : ExampleNet ReachabilityProblem`, sort "N/P" maps to ("ExampleNet", 0).
    pub imported_sorts: HashMap<SortId, (String, SortId)>,

    /// Nested structures (for instance-valued fields)
    pub nested: HashMap<Luid, Structure>,
}

/// Function init info: domain sort ID and whether codomain is external
#[derive(Clone, Debug)]
pub struct FunctionInitInfo {
    pub domain_sort_id: Option<SortId>,
    pub codomain_is_external: bool,
}

impl Structure {
    /// Create a new empty structure.
    /// Note: functions and relations are not pre-allocated here; call
    /// `init_functions()` and `init_relations()` after elements are added.
    pub fn new(num_sorts: usize) -> Self {
        Self {
            theory_luid: None,
            luids: Vec::new(),
            luid_to_slid: HashMap::new(),
            sorts: Vec::new(),
            carriers: vec![RoaringTreemap::new(); num_sorts],
            functions: Vec::new(), // Initialized later via init_functions()
            relations: Vec::new(), // Initialized later via init_relations()
            parents: HashMap::new(),
            imported_sorts: HashMap::new(),
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
    ///
    /// For simple (non-parameterized) instances, use `init_functions_local()`.
    /// For parameterized instances with external codomains, use this method.
    pub fn init_functions_ext(&mut self, func_info: &[FunctionInitInfo]) {
        self.functions = func_info
            .iter()
            .map(|info| {
                let size = match info.domain_sort_id {
                    Some(sort_id) => self.carrier_size(sort_id),
                    None => 0, // Product domains deferred
                };
                if info.codomain_is_external {
                    FunctionColumn::External(vec![None; size])
                } else {
                    FunctionColumn::Local(vec![None; size])
                }
            })
            .collect();
    }

    /// Initialize function storage for simple (non-parameterized) instances.
    /// All codomains are assumed to be local.
    pub fn init_functions(&mut self, domain_sort_ids: &[Option<SortId>]) {
        self.functions = domain_sort_ids
            .iter()
            .map(|opt_sort_id| {
                match opt_sort_id {
                    Some(sort_id) => FunctionColumn::Local(vec![None; self.carrier_size(*sort_id)]),
                    None => FunctionColumn::Local(Vec::new()), // Product domains deferred
                }
            })
            .collect();
    }

    /// Initialize relation storage based on arities.
    /// Must be called after all elements are added.
    ///
    /// `arities[rel_id]` is the number of fields in the relation's domain.
    /// For a relation `child : [parent: Node, child: Node]`, arity is 2.
    pub fn init_relations(&mut self, arities: &[usize]) {
        self.relations = arities.iter().map(|&arity| VecRelation::new(arity)).collect();
    }

    /// Assert a tuple in a relation: R(tuple)
    /// Returns true if the tuple was newly inserted.
    pub fn assert_relation(&mut self, rel_id: RelId, tuple: Vec<Slid>) -> bool {
        self.relations[rel_id].insert(tuple)
    }

    /// Retract a tuple from a relation
    /// Returns true if the tuple was present.
    pub fn retract_relation(&mut self, rel_id: RelId, tuple: &[Slid]) -> bool {
        self.relations[rel_id].remove(tuple)
    }

    /// Check if a tuple is in a relation
    pub fn query_relation(&self, rel_id: RelId, tuple: &[Slid]) -> bool {
        self.relations[rel_id].contains(tuple)
    }

    /// Get a reference to a relation's storage
    pub fn get_relation(&self, rel_id: RelId) -> &VecRelation {
        &self.relations[rel_id]
    }

    /// Get a mutable reference to a relation's storage
    pub fn get_relation_mut(&mut self, rel_id: RelId) -> &mut VecRelation {
        &mut self.relations[rel_id]
    }

    /// Get the number of relations in this structure
    pub fn num_relations(&self) -> usize {
        self.relations.len()
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
        let slid = Slid::from_usize(self.luids.len());

        self.luids.push(luid);
        self.luid_to_slid.insert(luid, slid);
        self.sorts.push(sort_id);
        self.carriers[sort_id].insert(slid.index() as u64);

        slid
    }

    /// Add an element with a specific UUID, registering it in the universe.
    /// Used when applying patches that reference UUIDs.
    pub fn add_element_with_uuid(
        &mut self,
        universe: &mut Universe,
        uuid: Uuid,
        sort_id: SortId,
    ) -> (Slid, Luid) {
        let luid = universe.intern(uuid);
        let slid = self.add_element_with_luid(luid, sort_id);
        (slid, luid)
    }

    /// Define a function value for a local codomain (Slid → Slid).
    /// Uses SortSlid indexing into the columnar function storage.
    pub fn define_function(
        &mut self,
        func_id: FuncId,
        domain_slid: Slid,
        codomain_slid: Slid,
    ) -> Result<(), String> {
        let domain_sort_slid = self.sort_local_id(domain_slid);

        match &mut self.functions[func_id] {
            FunctionColumn::Local(col) => {
                if let Some(existing) = get_slid(col[domain_sort_slid.index()])
                    && existing != codomain_slid
                {
                    return Err(format!(
                        "conflicting definition: func {}(slid {}) already defined as slid {}, cannot redefine as slid {}",
                        func_id, domain_slid, existing, codomain_slid
                    ));
                }
                col[domain_sort_slid.index()] = some_slid(codomain_slid);
                Ok(())
            }
            FunctionColumn::External(_) => Err(format!(
                "func {} has external codomain, use define_function_ext",
                func_id
            )),
        }
    }

    /// Define a function value for an external codomain (Slid → Luid).
    /// Used for functions referencing parent instance elements.
    pub fn define_function_ext(
        &mut self,
        func_id: FuncId,
        domain_slid: Slid,
        codomain_luid: Luid,
    ) -> Result<(), String> {
        use crate::id::{get_luid, some_luid};
        let domain_sort_slid = self.sort_local_id(domain_slid);

        match &mut self.functions[func_id] {
            FunctionColumn::External(col) => {
                if let Some(existing) = get_luid(col[domain_sort_slid.index()])
                    && existing != codomain_luid
                {
                    return Err(format!(
                        "conflicting definition: func {}(slid {}) already defined as luid {}, cannot redefine as luid {}",
                        func_id, domain_slid, existing, codomain_luid
                    ));
                }
                col[domain_sort_slid.index()] = some_luid(codomain_luid);
                Ok(())
            }
            FunctionColumn::Local(_) => Err(format!(
                "func {} has local codomain, use define_function",
                func_id
            )),
        }
    }

    /// Get function value for local codomain.
    pub fn get_function(&self, func_id: FuncId, domain_sort_slid: SortSlid) -> Option<Slid> {
        match &self.functions[func_id] {
            FunctionColumn::Local(col) => get_slid(col[domain_sort_slid.index()]),
            FunctionColumn::External(_) => None,
        }
    }

    /// Get function value for external codomain (returns Luid).
    pub fn get_function_ext(&self, func_id: FuncId, domain_sort_slid: SortSlid) -> Option<Luid> {
        use crate::id::get_luid;
        match &self.functions[func_id] {
            FunctionColumn::External(col) => get_luid(col[domain_sort_slid.index()]),
            FunctionColumn::Local(_) => None,
        }
    }

    /// Get the sort-local index for an element (0-based position within its carrier).
    ///
    /// # Roaring bitmap rank() semantics
    /// `rank(x)` returns the count of elements ≤ x in the bitmap.
    /// For a bitmap containing {4}: rank(3)=0, rank(4)=1, rank(5)=1.
    /// So 0-based index = rank(x) - 1.
    pub fn sort_local_id(&self, slid: Slid) -> SortSlid {
        let sort_id = self.sorts[slid.index()];
        SortSlid::from_usize((self.carriers[sort_id].rank(slid.index() as u64) - 1) as usize)
    }

    /// Look up element by Luid
    pub fn lookup_luid(&self, luid: Luid) -> Option<Slid> {
        self.luid_to_slid.get(&luid).copied()
    }

    /// Get the Luid for a Slid
    pub fn get_luid(&self, slid: Slid) -> Luid {
        self.luids[slid.index()]
    }

    /// Get the UUID for a Slid (requires Universe lookup)
    pub fn get_uuid(&self, slid: Slid, universe: &Universe) -> Option<Uuid> {
        universe.get(self.luids[slid.index()])
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
    pub fn carrier_size(&self, sort_id: SortId) -> usize {
        self.carriers[sort_id].len() as usize
    }

    /// Get the number of sorts in this structure
    pub fn num_sorts(&self) -> usize {
        self.carriers.len()
    }

    /// Get the number of functions in this structure
    pub fn num_functions(&self) -> usize {
        self.functions.len()
    }

    /// Mark a sort as imported from a parent instance.
    /// Imported sorts have no local carrier - queries delegate to the parent.
    pub fn mark_sort_imported(
        &mut self,
        local_sort_id: SortId,
        parent_instance: String,
        parent_sort_id: SortId,
    ) {
        self.imported_sorts
            .insert(local_sort_id, (parent_instance, parent_sort_id));
    }

    /// Check if a sort is imported from a parent instance.
    pub fn is_sort_imported(&self, sort_id: SortId) -> bool {
        self.imported_sorts.contains_key(&sort_id)
    }

    /// Get the parent info for an imported sort.
    /// Returns (parent_instance_name, parent_sort_id) or None if local.
    pub fn get_imported_sort_info(&self, sort_id: SortId) -> Option<(&str, SortId)> {
        self.imported_sorts
            .get(&sort_id)
            .map(|(name, id)| (name.as_str(), *id))
    }

    /// Register a parent instance binding.
    pub fn add_parent(&mut self, param_name: String, instance_name: String) {
        self.parents.insert(param_name, instance_name);
    }
}

// ============ Display implementations for debugging ============

// Unit tests moved to tests/proptest_structure.rs

impl std::fmt::Display for DerivedSort {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DerivedSort::Base(id) => write!(f, "Sort#{}", id),
            DerivedSort::Product(fields) if fields.is_empty() => write!(f, "()"),
            DerivedSort::Product(fields) => {
                write!(f, "[")?;
                for (i, (name, sort)) in fields.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}: {}", name, sort)?;
                }
                write!(f, "]")
            }
        }
    }
}
