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

    /// Returns the arity (number of atomic sorts) of this derived sort.
    /// For Product([x: A, y: B]), arity is 2.
    /// For Base(s), arity is 1.
    pub fn arity(&self) -> usize {
        match self {
            DerivedSort::Base(_) => 1,
            DerivedSort::Product(fields) => fields.len(),
        }
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
/// Note: This is forward-declared; the actual type is `Rc<ElaboratedTheory>`
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
/// Storage for product-domain functions.
///
/// Uses nested Vecs for efficient access and natural handling of carrier growth.
/// Sort-local indices are append-only, so existing indices remain stable when
/// carriers grow — we just extend the inner/outer Vecs.
#[derive(Clone, Debug)]
pub enum ProductStorage {
    /// Binary product [x: A, y: B] → Vec<Vec<OptSlid>>
    /// Outer dim is A (first field), inner is B (second field).
    /// Access: rows[x_local][y_local]
    Binary(Vec<Vec<OptSlid>>),

    /// Ternary product [x: A, y: B, z: C] → Vec<Vec<Vec<OptSlid>>>
    Ternary(Vec<Vec<Vec<OptSlid>>>),

    /// Higher-arity products: fall back to HashMap for flexibility.
    /// Keys are tuples of sort-local indices.
    General(HashMap<Vec<usize>, Slid>),
}

impl ProductStorage {
    /// Create storage for binary product with given carrier sizes
    pub fn new_binary(size_a: usize, size_b: usize) -> Self {
        ProductStorage::Binary(vec![vec![None; size_b]; size_a])
    }

    /// Create storage for ternary product with given carrier sizes
    pub fn new_ternary(size_a: usize, size_b: usize, size_c: usize) -> Self {
        ProductStorage::Ternary(vec![vec![vec![None; size_c]; size_b]; size_a])
    }

    /// Create storage for general (n-ary) product
    pub fn new_general() -> Self {
        ProductStorage::General(HashMap::new())
    }

    /// Create storage based on arity and carrier sizes
    pub fn new(carrier_sizes: &[usize]) -> Self {
        match carrier_sizes.len() {
            2 => Self::new_binary(carrier_sizes[0], carrier_sizes[1]),
            3 => Self::new_ternary(carrier_sizes[0], carrier_sizes[1], carrier_sizes[2]),
            _ => Self::new_general(),
        }
    }

    /// Get value at the given tuple of sort-local indices
    pub fn get(&self, tuple: &[usize]) -> Option<Slid> {
        match self {
            ProductStorage::Binary(rows) => {
                debug_assert_eq!(tuple.len(), 2);
                let opt = rows.get(tuple[0])?.get(tuple[1])?;
                get_slid(*opt)
            }
            ProductStorage::Ternary(planes) => {
                debug_assert_eq!(tuple.len(), 3);
                let opt = planes.get(tuple[0])?.get(tuple[1])?.get(tuple[2])?;
                get_slid(*opt)
            }
            ProductStorage::General(map) => map.get(tuple).copied(),
        }
    }

    /// Set value at the given tuple of sort-local indices
    /// Returns Err if conflicting definition exists
    pub fn set(&mut self, tuple: &[usize], value: Slid) -> Result<(), Slid> {
        match self {
            ProductStorage::Binary(rows) => {
                debug_assert_eq!(tuple.len(), 2);
                // Grow if needed (append-only growth)
                while rows.len() <= tuple[0] {
                    rows.push(Vec::new());
                }
                while rows[tuple[0]].len() <= tuple[1] {
                    rows[tuple[0]].push(None);
                }
                if let Some(existing) = get_slid(rows[tuple[0]][tuple[1]]) {
                    if existing != value {
                        return Err(existing);
                    }
                }
                rows[tuple[0]][tuple[1]] = some_slid(value);
                Ok(())
            }
            ProductStorage::Ternary(planes) => {
                debug_assert_eq!(tuple.len(), 3);
                while planes.len() <= tuple[0] {
                    planes.push(Vec::new());
                }
                while planes[tuple[0]].len() <= tuple[1] {
                    planes[tuple[0]].push(Vec::new());
                }
                while planes[tuple[0]][tuple[1]].len() <= tuple[2] {
                    planes[tuple[0]][tuple[1]].push(None);
                }
                if let Some(existing) = get_slid(planes[tuple[0]][tuple[1]][tuple[2]]) {
                    if existing != value {
                        return Err(existing);
                    }
                }
                planes[tuple[0]][tuple[1]][tuple[2]] = some_slid(value);
                Ok(())
            }
            ProductStorage::General(map) => {
                if let Some(&existing) = map.get(tuple) {
                    if existing != value {
                        return Err(existing);
                    }
                }
                map.insert(tuple.to_vec(), value);
                Ok(())
            }
        }
    }

    /// Count of defined (Some) entries
    pub fn defined_count(&self) -> usize {
        match self {
            ProductStorage::Binary(rows) => rows
                .iter()
                .flat_map(|row| row.iter())
                .filter(|&&v| v.is_some())
                .count(),
            ProductStorage::Ternary(planes) => planes
                .iter()
                .flat_map(|plane| plane.iter())
                .flat_map(|row| row.iter())
                .filter(|&&v| v.is_some())
                .count(),
            ProductStorage::General(map) => map.len(),
        }
    }

    /// Check if all entries are defined (total function)
    pub fn is_total(&self, carrier_sizes: &[usize]) -> bool {
        let expected = carrier_sizes.iter().product::<usize>();
        self.defined_count() == expected
    }

    /// Iterate over all defined entries as (tuple, value) pairs
    pub fn iter_defined(&self) -> Box<dyn Iterator<Item = (Vec<usize>, Slid)> + '_> {
        match self {
            ProductStorage::Binary(rows) => Box::new(
                rows.iter()
                    .enumerate()
                    .flat_map(|(i, row)| {
                        row.iter().enumerate().filter_map(move |(j, &v)| {
                            get_slid(v).map(|s| (vec![i, j], s))
                        })
                    }),
            ),
            ProductStorage::Ternary(planes) => Box::new(
                planes.iter().enumerate().flat_map(|(i, plane)| {
                    plane.iter().enumerate().flat_map(move |(j, row)| {
                        row.iter().enumerate().filter_map(move |(k, &v)| {
                            get_slid(v).map(|s| (vec![i, j, k], s))
                        })
                    })
                }),
            ),
            ProductStorage::General(map) => {
                Box::new(map.iter().map(|(k, &v)| (k.clone(), v)))
            }
        }
    }
}

#[derive(Clone, Debug)]
pub enum FunctionColumn {
    /// Base domain with local codomain: values are Slids within this structure
    Local(Vec<OptSlid>),
    /// Base domain with external codomain (from parent): values are Luids
    External(Vec<OptLuid>),
    /// Product domain with local codomain.
    /// Stores field sort IDs for carrier size lookups during growth.
    ProductLocal {
        storage: ProductStorage,
        field_sorts: Vec<SortId>,
    },
}

/// Linearize a tuple of sort-local indices into a flat column index.
/// Uses row-major (lexicographic) order.
/// E.g., for field_sizes = [3, 4], tuple [1, 2] → 1*4 + 2 = 6
pub fn linearize_tuple(tuple: &[usize], field_sizes: &[usize]) -> usize {
    debug_assert_eq!(tuple.len(), field_sizes.len());
    let mut index = 0;
    let mut stride = 1;
    // Process in reverse for row-major order
    for (i, &size) in field_sizes.iter().enumerate().rev() {
        index += tuple[i] * stride;
        stride *= size;
    }
    index
}

/// Delinearize a flat column index back to tuple of sort-local indices.
pub fn delinearize_index(mut index: usize, field_sizes: &[usize]) -> Vec<usize> {
    let mut tuple = vec![0; field_sizes.len()];
    // Process in reverse for row-major order
    for (i, &size) in field_sizes.iter().enumerate().rev() {
        tuple[i] = index % size;
        index /= size;
    }
    tuple
}

/// Compute total size of product domain (product of field carrier sizes)
pub fn product_domain_size(field_sizes: &[usize]) -> usize {
    field_sizes.iter().product()
}

impl FunctionColumn {
    /// Get the total number of domain slots (for base domains only).
    /// For product domains, returns 0 — use `defined_count()` instead.
    pub fn len(&self) -> usize {
        match self {
            FunctionColumn::Local(v) => v.len(),
            FunctionColumn::External(v) => v.len(),
            FunctionColumn::ProductLocal { .. } => 0, // Product domains have dynamic size
        }
    }

    /// Get the number of defined entries (not total slots)
    pub fn defined_count(&self) -> usize {
        match self {
            FunctionColumn::Local(v) => v.iter().filter(|x| x.is_some()).count(),
            FunctionColumn::External(v) => v.iter().filter(|x| x.is_some()).count(),
            FunctionColumn::ProductLocal { storage, .. } => storage.defined_count(),
        }
    }

    /// Check if empty (no defined entries)
    pub fn is_empty(&self) -> bool {
        self.defined_count() == 0
    }

    /// Check if this is a local column (base domain, local codomain)
    pub fn is_local(&self) -> bool {
        matches!(self, FunctionColumn::Local(_))
    }

    /// Check if this is an external column (base domain, external codomain)
    pub fn is_external(&self) -> bool {
        matches!(self, FunctionColumn::External(_))
    }

    /// Check if this is a product-domain column
    pub fn is_product(&self) -> bool {
        matches!(self, FunctionColumn::ProductLocal { .. })
    }

    /// Get local value at index (panics if not local or out of bounds)
    pub fn get_local(&self, idx: usize) -> OptSlid {
        match self {
            FunctionColumn::Local(v) => v[idx],
            FunctionColumn::External(_) => panic!("get_local called on external column"),
            FunctionColumn::ProductLocal { .. } => panic!("get_local called on product column"),
        }
    }

    /// Get external value at index (panics if not external or out of bounds)
    pub fn get_external(&self, idx: usize) -> OptLuid {
        match self {
            FunctionColumn::External(v) => v[idx],
            FunctionColumn::Local(_) => panic!("get_external called on local column"),
            FunctionColumn::ProductLocal { .. } => panic!("get_external called on product column"),
        }
    }

    /// Iterate over local values (panics if not local)
    pub fn iter_local(&self) -> impl Iterator<Item = &OptSlid> {
        match self {
            FunctionColumn::Local(v) => v.iter(),
            FunctionColumn::External(_) => panic!("iter_local called on external column"),
            FunctionColumn::ProductLocal { .. } => panic!("iter_local called on product column"),
        }
    }

    /// Iterate over external values (panics if not external)
    pub fn iter_external(&self) -> impl Iterator<Item = &OptLuid> {
        match self {
            FunctionColumn::External(v) => v.iter(),
            FunctionColumn::Local(_) => panic!("iter_external called on local column"),
            FunctionColumn::ProductLocal { .. } => panic!("iter_external called on product column"),
        }
    }

    /// Get as local column (returns None if external or product)
    pub fn as_local(&self) -> Option<&Vec<OptSlid>> {
        match self {
            FunctionColumn::Local(v) => Some(v),
            FunctionColumn::External(_) | FunctionColumn::ProductLocal { .. } => None,
        }
    }

    /// Get as mutable local column (returns None if external or product)
    pub fn as_local_mut(&mut self) -> Option<&mut Vec<OptSlid>> {
        match self {
            FunctionColumn::Local(v) => Some(v),
            FunctionColumn::External(_) | FunctionColumn::ProductLocal { .. } => None,
        }
    }

    /// Get product value for a tuple of sort-local indices
    pub fn get_product(&self, tuple: &[usize]) -> Option<Slid> {
        match self {
            FunctionColumn::ProductLocal { storage, .. } => storage.get(tuple),
            _ => None,
        }
    }

    /// Get field sort IDs for product column (returns None if not product)
    pub fn field_sorts(&self) -> Option<&[SortId]> {
        match self {
            FunctionColumn::ProductLocal { field_sorts, .. } => Some(field_sorts),
            _ => None,
        }
    }

    /// Get product storage (returns None if not product)
    pub fn as_product(&self) -> Option<&ProductStorage> {
        match self {
            FunctionColumn::ProductLocal { storage, .. } => Some(storage),
            _ => None,
        }
    }

    /// Get mutable product storage (returns None if not product)
    pub fn as_product_mut(&mut self) -> Option<&mut ProductStorage> {
        match self {
            FunctionColumn::ProductLocal { storage, .. } => Some(storage),
            _ => None,
        }
    }

    /// Iterate over defined product entries as (tuple, value) pairs
    pub fn iter_product_defined(&self) -> Option<Box<dyn Iterator<Item = (Vec<usize>, Slid)> + '_>> {
        match self {
            FunctionColumn::ProductLocal { storage, .. } => Some(storage.iter_defined()),
            _ => None,
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
    /// Maps param name → UUID of immutable parent instance.
    /// E.g., for `problem0 : ExampleNet ReachabilityProblem`, this contains {"N": uuid_of_ExampleNet}
    pub parents: HashMap<String, Uuid>,

    /// Nested structures (for instance-valued fields)
    pub nested: HashMap<Luid, Structure>,
}

/// Function init info: domain sort ID and whether codomain is external
#[derive(Clone, Debug)]
pub struct FunctionInitInfo {
    pub domain_sort_id: Option<SortId>,
    pub codomain_is_external: bool,
}

/// Domain info for function initialization
#[derive(Clone, Debug)]
pub enum FunctionDomainInfo {
    /// Base sort domain: just the sort ID
    Base(SortId),
    /// Product domain: list of sort IDs for each field
    Product(Vec<SortId>),
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
    /// Pass `None` for product-domain functions; pass `Some(sort_id)` for base-domain functions.
    pub fn init_functions(&mut self, domain_sort_ids: &[Option<SortId>]) {
        self.functions = domain_sort_ids
            .iter()
            .map(|opt_sort_id| match opt_sort_id {
                Some(sort_id) => FunctionColumn::Local(vec![None; self.carrier_size(*sort_id)]),
                None => {
                    // Legacy: product domains without size info get empty ProductLocal
                    // Use init_functions_full for proper initialization
                    FunctionColumn::ProductLocal {
                        storage: ProductStorage::new_general(),
                        field_sorts: Vec::new(),
                    }
                }
            })
            .collect();
    }

    /// Initialize function storage with full domain info (supports product domains).
    pub fn init_functions_full(&mut self, domains: &[FunctionDomainInfo]) {
        self.functions = domains
            .iter()
            .map(|domain| match domain {
                FunctionDomainInfo::Base(sort_id) => {
                    FunctionColumn::Local(vec![None; self.carrier_size(*sort_id)])
                }
                FunctionDomainInfo::Product(field_sort_ids) => {
                    let carrier_sizes: Vec<usize> = field_sort_ids
                        .iter()
                        .map(|&sort_id| self.carrier_size(sort_id))
                        .collect();
                    FunctionColumn::ProductLocal {
                        storage: ProductStorage::new(&carrier_sizes),
                        field_sorts: field_sort_ids.clone(),
                    }
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
    /// Automatically grows the column if needed.
    pub fn define_function(
        &mut self,
        func_id: FuncId,
        domain_slid: Slid,
        codomain_slid: Slid,
    ) -> Result<(), String> {
        let domain_sort_slid = self.sort_local_id(domain_slid);
        let idx = domain_sort_slid.index();

        match &mut self.functions[func_id] {
            FunctionColumn::Local(col) => {
                // Grow column if needed
                if idx >= col.len() {
                    col.resize(idx + 1, None); // None = undefined
                }
                if let Some(existing) = get_slid(col[idx])
                    && existing != codomain_slid
                {
                    return Err(format!(
                        "conflicting definition: func {}(slid {}) already defined as slid {}, cannot redefine as slid {}",
                        func_id, domain_slid, existing, codomain_slid
                    ));
                }
                col[idx] = some_slid(codomain_slid);
                Ok(())
            }
            FunctionColumn::External(_) => Err(format!(
                "func {} has external codomain, use define_function_ext",
                func_id
            )),
            FunctionColumn::ProductLocal { .. } => Err(format!(
                "func {} has product domain, use define_function_product",
                func_id
            )),
        }
    }

    /// Define a function value for an external codomain (Slid → Luid).
    /// Used for functions referencing parent instance elements.
    /// Automatically grows the column if needed.
    pub fn define_function_ext(
        &mut self,
        func_id: FuncId,
        domain_slid: Slid,
        codomain_luid: Luid,
    ) -> Result<(), String> {
        use crate::id::{get_luid, some_luid};
        let domain_sort_slid = self.sort_local_id(domain_slid);
        let idx = domain_sort_slid.index();

        match &mut self.functions[func_id] {
            FunctionColumn::External(col) => {
                // Grow column if needed
                if idx >= col.len() {
                    col.resize(idx + 1, None); // None = undefined
                }
                if let Some(existing) = get_luid(col[idx])
                    && existing != codomain_luid
                {
                    return Err(format!(
                        "conflicting definition: func {}(slid {}) already defined as luid {}, cannot redefine as luid {}",
                        func_id, domain_slid, existing, codomain_luid
                    ));
                }
                col[idx] = some_luid(codomain_luid);
                Ok(())
            }
            FunctionColumn::Local(_) => Err(format!(
                "func {} has local codomain, use define_function",
                func_id
            )),
            FunctionColumn::ProductLocal { .. } => Err(format!(
                "func {} has product domain, use define_function_product",
                func_id
            )),
        }
    }

    /// Define a function value for a product domain (tuple of Slids → Slid).
    /// Used for functions like `mul : [x: M, y: M] -> M`.
    ///
    /// The domain_tuple contains Slids which are converted to sort-local indices
    /// for storage in the nested Vec structure.
    pub fn define_function_product(
        &mut self,
        func_id: FuncId,
        domain_tuple: &[Slid],
        codomain_slid: Slid,
    ) -> Result<(), String> {
        // Convert Slids to sort-local indices for storage
        let local_indices: Vec<usize> = domain_tuple
            .iter()
            .map(|&slid| self.sort_local_id(slid).index())
            .collect();

        match &mut self.functions[func_id] {
            FunctionColumn::ProductLocal { storage, .. } => {
                storage.set(&local_indices, codomain_slid).map_err(|existing| {
                    format!(
                        "conflicting definition: func {}({:?}) already defined as slid {}, cannot redefine as slid {}",
                        func_id, domain_tuple, existing, codomain_slid
                    )
                })
            }
            FunctionColumn::Local(_) => Err(format!(
                "func {} has base domain, use define_function",
                func_id
            )),
            FunctionColumn::External(_) => Err(format!(
                "func {} has external codomain, use define_function_ext",
                func_id
            )),
        }
    }

    /// Get function value for local codomain (base domain only).
    pub fn get_function(&self, func_id: FuncId, domain_sort_slid: SortSlid) -> Option<Slid> {
        let idx = domain_sort_slid.index();
        match &self.functions[func_id] {
            FunctionColumn::Local(col) => col.get(idx).and_then(|&opt| get_slid(opt)),
            FunctionColumn::External(_) | FunctionColumn::ProductLocal { .. } => None,
        }
    }

    /// Get function value for external codomain (returns Luid).
    pub fn get_function_ext(&self, func_id: FuncId, domain_sort_slid: SortSlid) -> Option<Luid> {
        use crate::id::get_luid;
        let idx = domain_sort_slid.index();
        match &self.functions[func_id] {
            FunctionColumn::External(col) => col.get(idx).and_then(|&opt| get_luid(opt)),
            FunctionColumn::Local(_) | FunctionColumn::ProductLocal { .. } => None,
        }
    }

    /// Get function value for product domain.
    /// Takes a tuple of Slids and converts them to sort-local indices for lookup.
    pub fn get_function_product(&self, func_id: FuncId, domain_tuple: &[Slid]) -> Option<Slid> {
        // Convert Slids to sort-local indices
        let local_indices: Vec<usize> = domain_tuple
            .iter()
            .map(|&slid| self.sort_local_id(slid).index())
            .collect();

        match &self.functions[func_id] {
            FunctionColumn::ProductLocal { storage, .. } => storage.get(&local_indices),
            FunctionColumn::Local(_) | FunctionColumn::External(_) => None,
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
