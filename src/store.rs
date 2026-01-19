//! Append-only store for GeologMeta elements.
//!
//! This module provides the foundation for geolog's persistent, versioned data model.
//! All data (theories, instances, elements, function values, relation tuples) is stored
//! as elements in a single GeologMeta Structure that is append-only.
//!
//! Key design principles:
//! - **Append-only**: Elements are never deleted, only tombstoned
//! - **Patch-based versioning**: Each theory/instance version is a delta from its parent
//! - **Incremental materialization**: Views are updated efficiently as patches arrive
//! - **Transparent persistence**: The log auto-persists; no explicit save needed

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::sync::Arc;

use crate::core::{DerivedSort, ElaboratedTheory, Structure};
use crate::id::{NumericId, Slid};
use crate::meta::geolog_meta;
use crate::naming::NamingIndex;
use crate::universe::Universe;

// ============================================================================
// MATERIALIZED VIEWS
// ============================================================================

/// A materialized view of an instance at a specific version.
///
/// This is the "rendered" state of an instance after applying all patches
/// from the root to a particular version. It can be incrementally updated
/// when a new child version is created.
#[derive(Clone, Debug)]
pub struct MaterializedView {
    /// The instance version this view is materialized at
    pub instance: Slid,

    /// Live elements (not tombstoned)
    pub elements: HashSet<Slid>,

    /// Live relation tuples: tuple_slid -> (rel, arg)
    pub rel_tuples: HashMap<Slid, (Slid, Slid)>,

    /// Live function values: fv_slid -> (func, arg, result)
    pub func_vals: HashMap<Slid, (Slid, Slid, Slid)>,

    /// Element tombstones (for delta computation)
    pub elem_tombstones: HashSet<Slid>,

    /// Relation tuple tombstones
    pub rel_tuple_tombstones: HashSet<Slid>,

    /// Function value tombstones
    pub func_val_tombstones: HashSet<Slid>,
}

impl MaterializedView {
    /// Create an empty materialized view
    pub fn empty(instance: Slid) -> Self {
        Self {
            instance,
            elements: HashSet::new(),
            rel_tuples: HashMap::new(),
            func_vals: HashMap::new(),
            elem_tombstones: HashSet::new(),
            rel_tuple_tombstones: HashSet::new(),
            func_val_tombstones: HashSet::new(),
        }
    }

    /// Get the number of live elements
    pub fn element_count(&self) -> usize {
        self.elements.len()
    }

    /// Check if an element is live
    pub fn has_element(&self, elem: Slid) -> bool {
        self.elements.contains(&elem)
    }

    /// Check if a relation tuple is live
    pub fn has_rel_tuple(&self, tuple: Slid) -> bool {
        self.rel_tuples.contains_key(&tuple)
    }

    /// Get all elements of a particular sort (requires Store for lookup)
    pub fn elements_of_sort<'a>(&'a self, store: &'a Store, sort: Slid) -> impl Iterator<Item = Slid> + 'a {
        self.elements.iter().copied().filter(move |&elem| {
            store.func_ids.elem_sort
                .and_then(|f| store.get_func(f, elem))
                .map(|s| s == sort)
                .unwrap_or(false)
        })
    }

    /// Get all relation tuples for a particular relation
    pub fn tuples_of_relation<'a>(&'a self, rel: Slid) -> impl Iterator<Item = (Slid, Slid)> + 'a {
        self.rel_tuples.iter()
            .filter(move |(_, (r, _))| *r == rel)
            .map(|(_, (_, arg))| (*arg, *arg)) // TODO: should return (tuple_slid, arg)
    }

    /// Get all function values for a particular function
    pub fn values_of_function<'a>(&'a self, func: Slid) -> impl Iterator<Item = (Slid, Slid)> + 'a {
        self.func_vals.iter()
            .filter(move |(_, (f, _, _))| *f == func)
            .map(|(_, (_, arg, result))| (*arg, *result))
    }
}

// ============================================================================
// STORE
// ============================================================================

/// The append-only store: a single GeologMeta Structure plus indexing.
///
/// This is the "source of truth" for all geolog data. Theories and instances
/// are represented as elements within this structure, along with their
/// components (sorts, functions, relations, elements, values, etc.).
pub struct Store {
    /// The GeologMeta instance containing all data
    pub meta: Structure,

    /// The GeologMeta theory (for signature lookups)
    pub meta_theory: Arc<ElaboratedTheory>,

    /// Universe for UUID ↔ Luid mapping
    pub universe: Universe,

    /// Human-readable names for UUIDs
    pub naming: NamingIndex,

    /// Current HEAD commit (None if no commits yet)
    pub head: Option<Slid>,

    /// Uncommitted changes (name → target slid)
    /// These become NameBindings on commit
    pub uncommitted: HashMap<String, UncommittedBinding>,

    /// Cached sort IDs for quick lookup
    sort_ids: SortIds,

    /// Cached function IDs for quick lookup
    func_ids: FuncIds,

    /// Path for persistence (None = in-memory only)
    pub path: Option<PathBuf>,

    /// Whether there are unsaved changes
    dirty: bool,
}

/// An uncommitted name binding
#[derive(Debug, Clone)]
pub struct UncommittedBinding {
    /// The target (Theory or Instance slid in meta)
    pub target: Slid,
    /// Whether this binds to a theory or instance
    pub kind: BindingKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BindingKind {
    Theory,
    Instance,
}

/// Cached sort IDs from GeologMeta
#[derive(Default)]
struct SortIds {
    theory: Option<usize>,
    instance: Option<usize>,
    commit: Option<usize>,
    name_binding: Option<usize>,
    srt: Option<usize>,
    func: Option<usize>,
    rel: Option<usize>,
    elem: Option<usize>,
    elem_retract: Option<usize>,
    func_val: Option<usize>,
    func_val_retract: Option<usize>,
    rel_tuple: Option<usize>,
    rel_tuple_retract: Option<usize>,
    sequent: Option<usize>,
    param: Option<usize>,
    dsort: Option<usize>,
    base_ds: Option<usize>,
    prod_ds: Option<usize>,
    field: Option<usize>,
    binder: Option<usize>,
    term: Option<usize>,
    formula: Option<usize>,
    // ... other sorts as needed
}

/// Cached function IDs from GeologMeta
#[derive(Default)]
struct FuncIds {
    // Theory functions
    theory_parent: Option<usize>,

    // Instance functions
    instance_parent: Option<usize>,
    instance_theory: Option<usize>,

    // Commit functions
    commit_parent: Option<usize>,

    // NameBinding functions
    name_binding_commit: Option<usize>,
    name_binding_theory: Option<usize>,
    name_binding_instance: Option<usize>,

    // Elem functions
    elem_instance: Option<usize>,
    elem_sort: Option<usize>,

    // ElemRetract functions
    elem_retract_instance: Option<usize>,
    elem_retract_elem: Option<usize>,

    // FuncVal functions
    func_val_instance: Option<usize>,
    func_val_func: Option<usize>,
    func_val_arg: Option<usize>,
    func_val_result: Option<usize>,

    // FuncValRetract functions
    func_val_retract_instance: Option<usize>,
    func_val_retract_funcval: Option<usize>,

    // RelTuple functions
    rel_tuple_instance: Option<usize>,
    rel_tuple_rel: Option<usize>,
    rel_tuple_arg: Option<usize>,

    // RelTupleRetract functions
    rel_tuple_retract_instance: Option<usize>,
    rel_tuple_retract_tuple: Option<usize>,

    // Srt functions
    srt_theory: Option<usize>,

    // Func functions
    func_theory: Option<usize>,
    func_dom: Option<usize>,
    func_cod: Option<usize>,

    // Rel functions
    rel_theory: Option<usize>,
    rel_dom: Option<usize>,

    // Other schema functions...
    base_ds_dsort: Option<usize>,
    base_ds_srt: Option<usize>,
    prod_ds_dsort: Option<usize>,
    field_prod: Option<usize>,
    field_type: Option<usize>,
}

impl Store {
    /// Create a new empty store
    pub fn new() -> Self {
        let meta_theory = geolog_meta();
        let num_sorts = meta_theory.theory.signature.sorts.len();
        let mut meta = Structure::new(num_sorts);

        // Initialize function storage for all functions in GeologMeta
        // Build domain sort mapping for each function
        let domain_sort_ids: Vec<Option<usize>> = meta_theory
            .theory
            .signature
            .functions
            .iter()
            .map(|f| match &f.domain {
                DerivedSort::Base(sort_id) => Some(*sort_id),
                DerivedSort::Product(_) => None,
            })
            .collect();
        meta.init_functions(&domain_sort_ids);

        // Initialize relation storage
        let arities: Vec<usize> = meta_theory
            .theory
            .signature
            .relations
            .iter()
            .map(|r| match &r.domain {
                DerivedSort::Base(_) => 1,
                DerivedSort::Product(fields) => fields.len(),
            })
            .collect();
        meta.init_relations(&arities);

        let mut store = Self {
            meta,
            meta_theory,
            universe: Universe::new(),
            naming: NamingIndex::new(),
            head: None,
            uncommitted: HashMap::new(),
            sort_ids: SortIds::default(),
            func_ids: FuncIds::default(),
            path: None,
            dirty: false,
        };

        store.cache_ids();
        store
    }

    /// Create a store with a persistence path
    pub fn with_path(path: impl Into<PathBuf>) -> Self {
        let mut store = Self::new();
        store.path = Some(path.into());
        store
    }

    /// Load a store from disk, or create new if doesn't exist
    pub fn load_or_create(path: impl Into<PathBuf>) -> Self {
        let path = path.into();
        if path.exists() {
            Self::load(&path).unwrap_or_else(|_| Self::with_path(path))
        } else {
            Self::with_path(path)
        }
    }

    /// Load a store from disk
    pub fn load(path: &Path) -> Result<Self, String> {
        // TODO: Implement proper loading
        // For now, just create a new store with the path
        Ok(Self::with_path(path))
    }

    /// Save the store to disk
    pub fn save(&mut self) -> Result<(), String> {
        if !self.dirty {
            return Ok(());
        }

        let Some(path) = &self.path else {
            return Ok(()); // In-memory store, nothing to save
        };

        // Ensure parent directory exists
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent)
                .map_err(|e| format!("Failed to create directory: {}", e))?;
        }

        // Save universe
        self.universe.save()?;

        // Save naming
        self.naming.save()?;

        // Save meta structure
        let meta_path = path.join("meta.bin");
        crate::workspace::save_structure(&self.meta, &meta_path)?;

        // Save head commit reference
        if let Some(head) = self.head {
            let head_path = path.join("HEAD");
            std::fs::write(&head_path, format!("{}", head.index()))
                .map_err(|e| format!("Failed to write HEAD: {}", e))?;
        }

        self.dirty = false;
        Ok(())
    }

    /// Cache sort and function IDs for quick lookup
    fn cache_ids(&mut self) {
        let sig = &self.meta_theory.theory.signature;

        // Cache sort IDs
        self.sort_ids.theory = sig.lookup_sort("Theory");
        self.sort_ids.instance = sig.lookup_sort("Instance");
        self.sort_ids.commit = sig.lookup_sort("Commit");
        self.sort_ids.name_binding = sig.lookup_sort("NameBinding");
        self.sort_ids.srt = sig.lookup_sort("Srt");
        self.sort_ids.func = sig.lookup_sort("Func");
        self.sort_ids.rel = sig.lookup_sort("Rel");
        self.sort_ids.elem = sig.lookup_sort("Elem");
        self.sort_ids.elem_retract = sig.lookup_sort("ElemRetract");
        self.sort_ids.func_val = sig.lookup_sort("FuncVal");
        self.sort_ids.func_val_retract = sig.lookup_sort("FuncValRetract");
        self.sort_ids.rel_tuple = sig.lookup_sort("RelTuple");
        self.sort_ids.rel_tuple_retract = sig.lookup_sort("RelTupleRetract");
        self.sort_ids.sequent = sig.lookup_sort("Sequent");
        self.sort_ids.param = sig.lookup_sort("Param");
        self.sort_ids.dsort = sig.lookup_sort("DSort");
        self.sort_ids.base_ds = sig.lookup_sort("BaseDS");
        self.sort_ids.prod_ds = sig.lookup_sort("ProdDS");
        self.sort_ids.field = sig.lookup_sort("Field");
        self.sort_ids.binder = sig.lookup_sort("Binder");
        self.sort_ids.term = sig.lookup_sort("Term");
        self.sort_ids.formula = sig.lookup_sort("Formula");

        // Cache function IDs
        self.func_ids.theory_parent = sig.lookup_func("Theory/parent");
        self.func_ids.instance_parent = sig.lookup_func("Instance/parent");
        self.func_ids.instance_theory = sig.lookup_func("Instance/theory");
        self.func_ids.commit_parent = sig.lookup_func("Commit/parent");
        self.func_ids.name_binding_commit = sig.lookup_func("NameBinding/commit");
        self.func_ids.name_binding_theory = sig.lookup_func("NameBinding/theory");
        self.func_ids.name_binding_instance = sig.lookup_func("NameBinding/instance");
        self.func_ids.elem_instance = sig.lookup_func("Elem/instance");
        self.func_ids.elem_sort = sig.lookup_func("Elem/sort");
        self.func_ids.elem_retract_instance = sig.lookup_func("ElemRetract/instance");
        self.func_ids.elem_retract_elem = sig.lookup_func("ElemRetract/elem");
        self.func_ids.func_val_instance = sig.lookup_func("FuncVal/instance");
        self.func_ids.func_val_func = sig.lookup_func("FuncVal/func");
        self.func_ids.func_val_arg = sig.lookup_func("FuncVal/arg");
        self.func_ids.func_val_result = sig.lookup_func("FuncVal/result");
        self.func_ids.func_val_retract_instance = sig.lookup_func("FuncValRetract/instance");
        self.func_ids.func_val_retract_funcval = sig.lookup_func("FuncValRetract/funcval");
        self.func_ids.rel_tuple_instance = sig.lookup_func("RelTuple/instance");
        self.func_ids.rel_tuple_rel = sig.lookup_func("RelTuple/rel");
        self.func_ids.rel_tuple_arg = sig.lookup_func("RelTuple/arg");
        self.func_ids.rel_tuple_retract_instance = sig.lookup_func("RelTupleRetract/instance");
        self.func_ids.rel_tuple_retract_tuple = sig.lookup_func("RelTupleRetract/tuple");
        self.func_ids.srt_theory = sig.lookup_func("Srt/theory");
        self.func_ids.func_theory = sig.lookup_func("Func/theory");
        self.func_ids.func_dom = sig.lookup_func("Func/dom");
        self.func_ids.func_cod = sig.lookup_func("Func/cod");
        self.func_ids.rel_theory = sig.lookup_func("Rel/theory");
        self.func_ids.rel_dom = sig.lookup_func("Rel/dom");
        self.func_ids.base_ds_dsort = sig.lookup_func("BaseDS/dsort");
        self.func_ids.base_ds_srt = sig.lookup_func("BaseDS/srt");
        self.func_ids.prod_ds_dsort = sig.lookup_func("ProdDS/dsort");
        self.func_ids.field_prod = sig.lookup_func("Field/prod");
        self.func_ids.field_type = sig.lookup_func("Field/type");
    }

    // ========================================================================
    // LOW-LEVEL ELEMENT OPERATIONS
    // ========================================================================

    /// Add an element to a sort in the meta structure
    fn add_element(&mut self, sort_id: usize, name: &str) -> Slid {
        let (slid, luid) = self.meta.add_element(&mut self.universe, sort_id);
        let uuid = self.universe.get(luid).expect("freshly created luid should have uuid");
        self.naming.insert(uuid, vec![name.to_string()]);
        self.dirty = true;
        slid
    }

    /// Add an element with a qualified name
    fn add_element_qualified(&mut self, sort_id: usize, path: Vec<String>) -> Slid {
        let (slid, luid) = self.meta.add_element(&mut self.universe, sort_id);
        let uuid = self.universe.get(luid).expect("freshly created luid should have uuid");
        self.naming.insert(uuid, path);
        self.dirty = true;
        slid
    }

    /// Define a function value in the meta structure
    fn define_func(&mut self, func_id: usize, domain: Slid, codomain: Slid) -> Result<(), String> {
        self.meta.define_function(func_id, domain, codomain)?;
        self.dirty = true;
        Ok(())
    }

    /// Get a function value from the meta structure
    fn get_func(&self, func_id: usize, domain: Slid) -> Option<Slid> {
        let sort_slid = self.meta.sort_local_id(domain);
        self.meta.get_function(func_id, sort_slid)
    }

    /// Get all elements of a sort
    fn elements_of_sort(&self, sort_id: usize) -> Vec<Slid> {
        if sort_id >= self.meta.carriers.len() {
            return vec![];
        }
        self.meta.carriers[sort_id]
            .iter()
            .map(|x| Slid::from_usize(x as usize))
            .collect()
    }

    /// Find elements where a function points to a target
    fn find_by_func(&self, func_id: usize, target: Slid) -> Vec<Slid> {
        let func = &self.meta_theory.theory.signature.functions[func_id];
        let DerivedSort::Base(domain_sort) = &func.domain else {
            return vec![];
        };

        let mut results = vec![];
        for slid in self.elements_of_sort(*domain_sort) {
            if self.get_func(func_id, slid) == Some(target) {
                results.push(slid);
            }
        }
        results
    }

    /// Get the name of an element
    fn get_name(&self, slid: Slid) -> String {
        let luid = self.meta.get_luid(slid);
        if let Some(uuid) = self.universe.get(luid) {
            self.naming.display_name(&uuid)
        } else {
            format!("#{}", slid.index())
        }
    }

    // ========================================================================
    // THEORY OPERATIONS
    // ========================================================================

    /// Create a new theory (version 0, no parent)
    pub fn create_theory(&mut self, name: &str) -> Result<Slid, String> {
        let sort_id = self.sort_ids.theory.ok_or("Theory sort not found")?;
        let theory_slid = self.add_element(sort_id, name);

        // Register uncommitted binding
        self.uncommitted.insert(
            name.to_string(),
            UncommittedBinding {
                target: theory_slid,
                kind: BindingKind::Theory,
            },
        );

        Ok(theory_slid)
    }

    /// Create a new version of an existing theory
    pub fn extend_theory(&mut self, parent: Slid, name: &str) -> Result<Slid, String> {
        let sort_id = self.sort_ids.theory.ok_or("Theory sort not found")?;
        let theory_slid = self.add_element(sort_id, &format!("{}@v{}", name, self.meta.carriers[sort_id].len()));

        // Set parent
        let func_id = self.func_ids.theory_parent.ok_or("Theory/parent not found")?;
        self.define_func(func_id, theory_slid, parent)?;

        // Update uncommitted binding
        self.uncommitted.insert(
            name.to_string(),
            UncommittedBinding {
                target: theory_slid,
                kind: BindingKind::Theory,
            },
        );

        Ok(theory_slid)
    }

    /// Add a sort to a theory
    pub fn add_sort(&mut self, theory: Slid, name: &str) -> Result<Slid, String> {
        let sort_id = self.sort_ids.srt.ok_or("Srt sort not found")?;
        let srt_slid = self.add_element_qualified(sort_id, vec![self.get_name(theory), name.to_string()]);

        let func_id = self.func_ids.srt_theory.ok_or("Srt/theory not found")?;
        self.define_func(func_id, srt_slid, theory)?;

        Ok(srt_slid)
    }

    /// Add a function to a theory
    pub fn add_function(
        &mut self,
        theory: Slid,
        name: &str,
        domain: Slid,
        codomain: Slid,
    ) -> Result<Slid, String> {
        let sort_id = self.sort_ids.func.ok_or("Func sort not found")?;
        let func_slid = self.add_element_qualified(sort_id, vec![self.get_name(theory), name.to_string()]);

        let theory_func = self.func_ids.func_theory.ok_or("Func/theory not found")?;
        let dom_func = self.func_ids.func_dom.ok_or("Func/dom not found")?;
        let cod_func = self.func_ids.func_cod.ok_or("Func/cod not found")?;

        self.define_func(theory_func, func_slid, theory)?;
        self.define_func(dom_func, func_slid, domain)?;
        self.define_func(cod_func, func_slid, codomain)?;

        Ok(func_slid)
    }

    /// Add a relation to a theory
    pub fn add_relation(&mut self, theory: Slid, name: &str, domain: Slid) -> Result<Slid, String> {
        let sort_id = self.sort_ids.rel.ok_or("Rel sort not found")?;
        let rel_slid = self.add_element_qualified(sort_id, vec![self.get_name(theory), name.to_string()]);

        let theory_func = self.func_ids.rel_theory.ok_or("Rel/theory not found")?;
        let dom_func = self.func_ids.rel_dom.ok_or("Rel/dom not found")?;

        self.define_func(theory_func, rel_slid, theory)?;
        self.define_func(dom_func, rel_slid, domain)?;

        Ok(rel_slid)
    }

    /// Create a base DSort from a Srt
    pub fn make_base_dsort(&mut self, srt: Slid) -> Result<Slid, String> {
        let base_ds_sort = self.sort_ids.base_ds.ok_or("BaseDS sort not found")?;
        let dsort_sort = self.sort_ids.dsort.ok_or("DSort sort not found")?;

        let base_ds_slid = self.add_element(base_ds_sort, &format!("base_{}", self.get_name(srt)));
        let dsort_slid = self.add_element(dsort_sort, &format!("dsort_{}", self.get_name(srt)));

        let dsort_func = self.func_ids.base_ds_dsort.ok_or("BaseDS/dsort not found")?;
        let srt_func = self.func_ids.base_ds_srt.ok_or("BaseDS/srt not found")?;

        self.define_func(dsort_func, base_ds_slid, dsort_slid)?;
        self.define_func(srt_func, base_ds_slid, srt)?;

        Ok(dsort_slid)
    }

    // ========================================================================
    // INSTANCE OPERATIONS
    // ========================================================================

    /// Create a new instance (version 0, no parent)
    pub fn create_instance(&mut self, name: &str, theory: Slid) -> Result<Slid, String> {
        let sort_id = self.sort_ids.instance.ok_or("Instance sort not found")?;
        let instance_slid = self.add_element(sort_id, name);

        // Set theory
        let func_id = self.func_ids.instance_theory.ok_or("Instance/theory not found")?;
        self.define_func(func_id, instance_slid, theory)?;

        // Register uncommitted binding
        self.uncommitted.insert(
            name.to_string(),
            UncommittedBinding {
                target: instance_slid,
                kind: BindingKind::Instance,
            },
        );

        Ok(instance_slid)
    }

    /// Create a new version of an existing instance
    pub fn extend_instance(&mut self, parent: Slid, name: &str) -> Result<Slid, String> {
        let sort_id = self.sort_ids.instance.ok_or("Instance sort not found")?;

        // Get the theory from the parent
        let theory_func = self.func_ids.instance_theory.ok_or("Instance/theory not found")?;
        let theory = self.get_func(theory_func, parent).ok_or("Parent has no theory")?;

        let instance_slid = self.add_element(sort_id, &format!("{}@v{}", name, self.meta.carriers[sort_id].len()));

        // Set parent and theory
        let parent_func = self.func_ids.instance_parent.ok_or("Instance/parent not found")?;
        self.define_func(parent_func, instance_slid, parent)?;
        self.define_func(theory_func, instance_slid, theory)?;

        // Update uncommitted binding
        self.uncommitted.insert(
            name.to_string(),
            UncommittedBinding {
                target: instance_slid,
                kind: BindingKind::Instance,
            },
        );

        Ok(instance_slid)
    }

    /// Add an element to an instance
    pub fn add_elem(&mut self, instance: Slid, srt: Slid, name: &str) -> Result<Slid, String> {
        let sort_id = self.sort_ids.elem.ok_or("Elem sort not found")?;
        let elem_slid = self.add_element_qualified(sort_id, vec![self.get_name(instance), name.to_string()]);

        let instance_func = self.func_ids.elem_instance.ok_or("Elem/instance not found")?;
        let sort_func = self.func_ids.elem_sort.ok_or("Elem/sort not found")?;

        self.define_func(instance_func, elem_slid, instance)?;
        self.define_func(sort_func, elem_slid, srt)?;

        Ok(elem_slid)
    }

    /// Retract an element from an instance
    pub fn retract_elem(&mut self, instance: Slid, elem: Slid) -> Result<Slid, String> {
        let sort_id = self.sort_ids.elem_retract.ok_or("ElemRetract sort not found")?;
        let retract_slid = self.add_element(sort_id, &format!("retract_{}", self.get_name(elem)));

        let instance_func = self.func_ids.elem_retract_instance.ok_or("ElemRetract/instance not found")?;
        let elem_func = self.func_ids.elem_retract_elem.ok_or("ElemRetract/elem not found")?;

        self.define_func(instance_func, retract_slid, instance)?;
        self.define_func(elem_func, retract_slid, elem)?;

        Ok(retract_slid)
    }

    /// Define a function value in an instance
    pub fn add_func_val(
        &mut self,
        instance: Slid,
        func: Slid,
        arg: Slid,
        result: Slid,
    ) -> Result<Slid, String> {
        let sort_id = self.sort_ids.func_val.ok_or("FuncVal sort not found")?;
        let fv_slid = self.add_element(sort_id, &format!("fv_{}_{}", self.get_name(func), self.get_name(arg)));

        let instance_func = self.func_ids.func_val_instance.ok_or("FuncVal/instance not found")?;
        let func_func = self.func_ids.func_val_func.ok_or("FuncVal/func not found")?;
        let arg_func = self.func_ids.func_val_arg.ok_or("FuncVal/arg not found")?;
        let result_func = self.func_ids.func_val_result.ok_or("FuncVal/result not found")?;

        self.define_func(instance_func, fv_slid, instance)?;
        self.define_func(func_func, fv_slid, func)?;
        self.define_func(arg_func, fv_slid, arg)?;
        self.define_func(result_func, fv_slid, result)?;

        Ok(fv_slid)
    }

    /// Retract a function value
    pub fn retract_func_val(&mut self, instance: Slid, func_val: Slid) -> Result<Slid, String> {
        let sort_id = self.sort_ids.func_val_retract.ok_or("FuncValRetract sort not found")?;
        let retract_slid = self.add_element(sort_id, &format!("retract_{}", self.get_name(func_val)));

        let instance_func = self.func_ids.func_val_retract_instance.ok_or("FuncValRetract/instance not found")?;
        let fv_func = self.func_ids.func_val_retract_funcval.ok_or("FuncValRetract/funcval not found")?;

        self.define_func(instance_func, retract_slid, instance)?;
        self.define_func(fv_func, retract_slid, func_val)?;

        Ok(retract_slid)
    }

    /// Assert a relation tuple in an instance
    pub fn add_rel_tuple(&mut self, instance: Slid, rel: Slid, arg: Slid) -> Result<Slid, String> {
        let sort_id = self.sort_ids.rel_tuple.ok_or("RelTuple sort not found")?;
        let rt_slid = self.add_element(sort_id, &format!("rt_{}_{}", self.get_name(rel), self.get_name(arg)));

        let instance_func = self.func_ids.rel_tuple_instance.ok_or("RelTuple/instance not found")?;
        let rel_func = self.func_ids.rel_tuple_rel.ok_or("RelTuple/rel not found")?;
        let arg_func = self.func_ids.rel_tuple_arg.ok_or("RelTuple/arg not found")?;

        self.define_func(instance_func, rt_slid, instance)?;
        self.define_func(rel_func, rt_slid, rel)?;
        self.define_func(arg_func, rt_slid, arg)?;

        Ok(rt_slid)
    }

    /// Retract a relation tuple
    pub fn retract_rel_tuple(&mut self, instance: Slid, rel_tuple: Slid) -> Result<Slid, String> {
        let sort_id = self.sort_ids.rel_tuple_retract.ok_or("RelTupleRetract sort not found")?;
        let retract_slid = self.add_element(sort_id, &format!("retract_{}", self.get_name(rel_tuple)));

        let instance_func = self.func_ids.rel_tuple_retract_instance.ok_or("RelTupleRetract/instance not found")?;
        let tuple_func = self.func_ids.rel_tuple_retract_tuple.ok_or("RelTupleRetract/tuple not found")?;

        self.define_func(instance_func, retract_slid, instance)?;
        self.define_func(tuple_func, retract_slid, rel_tuple)?;

        Ok(retract_slid)
    }

    // ========================================================================
    // COMMIT OPERATIONS
    // ========================================================================

    /// Create a new commit
    pub fn commit(&mut self, message: Option<&str>) -> Result<Slid, String> {
        let sort_id = self.sort_ids.commit.ok_or("Commit sort not found")?;
        let commit_slid = self.add_element(sort_id, message.unwrap_or("commit"));

        // Set parent if there's a head
        if let Some(head) = self.head {
            let parent_func = self.func_ids.commit_parent.ok_or("Commit/parent not found")?;
            self.define_func(parent_func, commit_slid, head)?;
        }

        // Create NameBindings for all uncommitted changes
        let nb_sort = self.sort_ids.name_binding.ok_or("NameBinding sort not found")?;
        let commit_func = self.func_ids.name_binding_commit.ok_or("NameBinding/commit not found")?;
        let theory_func = self.func_ids.name_binding_theory.ok_or("NameBinding/theory not found")?;
        let instance_func = self.func_ids.name_binding_instance.ok_or("NameBinding/instance not found")?;

        // Collect uncommitted to avoid borrow issues
        let uncommitted: Vec<_> = self.uncommitted.drain().collect();
        for (name, binding) in uncommitted {
            let nb_slid = self.add_element(nb_sort, &format!("nb_{}_{}", name, commit_slid.index()));
            self.define_func(commit_func, nb_slid, commit_slid)?;

            match binding.kind {
                BindingKind::Theory => {
                    self.define_func(theory_func, nb_slid, binding.target)?;
                }
                BindingKind::Instance => {
                    self.define_func(instance_func, nb_slid, binding.target)?;
                }
            }
        }

        // Update head
        self.head = Some(commit_slid);

        // Auto-save
        self.save()?;

        Ok(commit_slid)
    }

    // ========================================================================
    // QUERY OPERATIONS
    // ========================================================================

    /// Get the current binding for a name (from HEAD commit or uncommitted)
    pub fn resolve_name(&self, name: &str) -> Option<(Slid, BindingKind)> {
        // Check uncommitted first
        if let Some(binding) = self.uncommitted.get(name) {
            return Some((binding.target, binding.kind));
        }

        // Otherwise, search through name bindings from HEAD backwards
        // This is a simple linear scan; could be optimized with an index
        let Some(head) = self.head else {
            return None;
        };

        let nb_sort = self.sort_ids.name_binding?;
        let commit_func = self.func_ids.name_binding_commit?;
        let theory_func = self.func_ids.name_binding_theory?;
        let instance_func = self.func_ids.name_binding_instance?;

        // Walk commits from head backwards
        let mut current = Some(head);
        while let Some(commit) = current {
            // Find all NameBindings for this commit
            for nb_slid in self.elements_of_sort(nb_sort) {
                if self.get_func(commit_func, nb_slid) == Some(commit) {
                    // Check if this binding is for our name
                    let nb_name = self.get_name(nb_slid);
                    if nb_name.starts_with(&format!("nb_{}_", name)) {
                        // Found it! Return the target
                        if let Some(theory) = self.get_func(theory_func, nb_slid) {
                            return Some((theory, BindingKind::Theory));
                        }
                        if let Some(instance) = self.get_func(instance_func, nb_slid) {
                            return Some((instance, BindingKind::Instance));
                        }
                    }
                }
            }

            // Move to parent commit
            let parent_func = self.func_ids.commit_parent?;
            current = self.get_func(parent_func, commit);
        }

        None
    }

    /// Get all elements of an instance (including from parent chain)
    pub fn get_instance_elements(&self, instance: Slid) -> Vec<Slid> {
        let mut elements = Vec::new();
        let mut retractions = std::collections::HashSet::new();

        // Collect retractions first (from all versions in chain)
        let mut version = Some(instance);
        while let Some(v) = version {
            if let Some(retract_sort) = self.sort_ids.elem_retract {
                if let Some(instance_func) = self.func_ids.elem_retract_instance {
                    if let Some(elem_func) = self.func_ids.elem_retract_elem {
                        for retract in self.elements_of_sort(retract_sort) {
                            if self.get_func(instance_func, retract) == Some(v) {
                                if let Some(elem) = self.get_func(elem_func, retract) {
                                    retractions.insert(elem);
                                }
                            }
                        }
                    }
                }
            }
            version = self.func_ids.instance_parent.and_then(|f| self.get_func(f, v));
        }

        // Now collect elements (filtering out retracted ones)
        let mut version = Some(instance);
        while let Some(v) = version {
            if let Some(elem_sort) = self.sort_ids.elem {
                if let Some(instance_func) = self.func_ids.elem_instance {
                    for elem in self.elements_of_sort(elem_sort) {
                        if self.get_func(instance_func, elem) == Some(v) {
                            if !retractions.contains(&elem) {
                                elements.push(elem);
                            }
                        }
                    }
                }
            }
            version = self.func_ids.instance_parent.and_then(|f| self.get_func(f, v));
        }

        elements
    }

    /// Get all relation tuples of an instance (including from parent chain)
    pub fn get_instance_rel_tuples(&self, instance: Slid) -> Vec<(Slid, Slid, Slid)> {
        let mut tuples = Vec::new();
        let mut retractions = std::collections::HashSet::new();

        // Collect retractions
        let mut version = Some(instance);
        while let Some(v) = version {
            if let Some(retract_sort) = self.sort_ids.rel_tuple_retract {
                if let Some(instance_func) = self.func_ids.rel_tuple_retract_instance {
                    if let Some(tuple_func) = self.func_ids.rel_tuple_retract_tuple {
                        for retract in self.elements_of_sort(retract_sort) {
                            if self.get_func(instance_func, retract) == Some(v) {
                                if let Some(tuple) = self.get_func(tuple_func, retract) {
                                    retractions.insert(tuple);
                                }
                            }
                        }
                    }
                }
            }
            version = self.func_ids.instance_parent.and_then(|f| self.get_func(f, v));
        }

        // Collect tuples
        let mut version = Some(instance);
        while let Some(v) = version {
            if let Some(tuple_sort) = self.sort_ids.rel_tuple {
                if let (Some(instance_func), Some(rel_func), Some(arg_func)) = (
                    self.func_ids.rel_tuple_instance,
                    self.func_ids.rel_tuple_rel,
                    self.func_ids.rel_tuple_arg,
                ) {
                    for tuple in self.elements_of_sort(tuple_sort) {
                        if self.get_func(instance_func, tuple) == Some(v) && !retractions.contains(&tuple) {
                            if let (Some(rel), Some(arg)) = (
                                self.get_func(rel_func, tuple),
                                self.get_func(arg_func, tuple),
                            ) {
                                tuples.push((tuple, rel, arg));
                            }
                        }
                    }
                }
            }
            version = self.func_ids.instance_parent.and_then(|f| self.get_func(f, v));
        }

        tuples
    }

    /// Get all function values of an instance (including from parent chain)
    pub fn get_instance_func_vals(&self, instance: Slid) -> Vec<(Slid, Slid, Slid, Slid)> {
        let mut vals = Vec::new();
        let mut retractions = std::collections::HashSet::new();

        // Collect retractions
        let mut version = Some(instance);
        while let Some(v) = version {
            if let Some(retract_sort) = self.sort_ids.func_val_retract {
                if let Some(instance_func) = self.func_ids.func_val_retract_instance {
                    if let Some(fv_func) = self.func_ids.func_val_retract_funcval {
                        for retract in self.elements_of_sort(retract_sort) {
                            if self.get_func(instance_func, retract) == Some(v) {
                                if let Some(fv) = self.get_func(fv_func, retract) {
                                    retractions.insert(fv);
                                }
                            }
                        }
                    }
                }
            }
            version = self.func_ids.instance_parent.and_then(|f| self.get_func(f, v));
        }

        // Collect function values
        let mut version = Some(instance);
        while let Some(v) = version {
            if let Some(fv_sort) = self.sort_ids.func_val {
                if let (Some(instance_func), Some(func_func), Some(arg_func), Some(result_func)) = (
                    self.func_ids.func_val_instance,
                    self.func_ids.func_val_func,
                    self.func_ids.func_val_arg,
                    self.func_ids.func_val_result,
                ) {
                    for fv in self.elements_of_sort(fv_sort) {
                        if self.get_func(instance_func, fv) == Some(v) && !retractions.contains(&fv) {
                            if let (Some(func), Some(arg), Some(result)) = (
                                self.get_func(func_func, fv),
                                self.get_func(arg_func, fv),
                                self.get_func(result_func, fv),
                            ) {
                                vals.push((fv, func, arg, result));
                            }
                        }
                    }
                }
            }
            version = self.func_ids.instance_parent.and_then(|f| self.get_func(f, v));
        }

        vals
    }

    // ========================================================================
    // MATERIALIZED VIEWS
    // ========================================================================

    /// Materialize an instance from scratch by walking the parent chain.
    ///
    /// This collects all additions and retractions from root to the specified
    /// version, producing a complete view of the instance state.
    pub fn materialize(&self, instance: Slid) -> MaterializedView {
        let mut view = MaterializedView::empty(instance);

        // Collect version chain (from instance back to root)
        let mut chain = Vec::new();
        let mut version = Some(instance);
        while let Some(v) = version {
            chain.push(v);
            version = self.func_ids.instance_parent.and_then(|f| self.get_func(f, v));
        }

        // Process from oldest to newest (reverse the chain)
        for v in chain.into_iter().rev() {
            self.apply_version_delta(&mut view, v);
        }

        view.instance = instance;
        view
    }

    /// Apply the delta from a single instance version to a materialized view.
    ///
    /// This is the core of incremental materialization: given a view at version N,
    /// we can efficiently update it to version N+1 by applying only the changes
    /// introduced in N+1.
    pub fn apply_version_delta(&self, view: &mut MaterializedView, version: Slid) {
        // 1. Process element additions
        if let Some(elem_sort) = self.sort_ids.elem {
            if let Some(instance_func) = self.func_ids.elem_instance {
                for elem in self.elements_of_sort(elem_sort) {
                    if self.get_func(instance_func, elem) == Some(version) {
                        // Don't add if already tombstoned
                        if !view.elem_tombstones.contains(&elem) {
                            view.elements.insert(elem);
                        }
                    }
                }
            }
        }

        // 2. Process element retractions
        if let Some(retract_sort) = self.sort_ids.elem_retract {
            if let Some(instance_func) = self.func_ids.elem_retract_instance {
                if let Some(elem_func) = self.func_ids.elem_retract_elem {
                    for retract in self.elements_of_sort(retract_sort) {
                        if self.get_func(instance_func, retract) == Some(version) {
                            if let Some(elem) = self.get_func(elem_func, retract) {
                                view.elements.remove(&elem);
                                view.elem_tombstones.insert(elem);
                            }
                        }
                    }
                }
            }
        }

        // 3. Process relation tuple additions
        if let Some(tuple_sort) = self.sort_ids.rel_tuple {
            if let (Some(instance_func), Some(rel_func), Some(arg_func)) = (
                self.func_ids.rel_tuple_instance,
                self.func_ids.rel_tuple_rel,
                self.func_ids.rel_tuple_arg,
            ) {
                for tuple in self.elements_of_sort(tuple_sort) {
                    if self.get_func(instance_func, tuple) == Some(version) {
                        if !view.rel_tuple_tombstones.contains(&tuple) {
                            if let (Some(rel), Some(arg)) = (
                                self.get_func(rel_func, tuple),
                                self.get_func(arg_func, tuple),
                            ) {
                                view.rel_tuples.insert(tuple, (rel, arg));
                            }
                        }
                    }
                }
            }
        }

        // 4. Process relation tuple retractions
        if let Some(retract_sort) = self.sort_ids.rel_tuple_retract {
            if let Some(instance_func) = self.func_ids.rel_tuple_retract_instance {
                if let Some(tuple_func) = self.func_ids.rel_tuple_retract_tuple {
                    for retract in self.elements_of_sort(retract_sort) {
                        if self.get_func(instance_func, retract) == Some(version) {
                            if let Some(tuple) = self.get_func(tuple_func, retract) {
                                view.rel_tuples.remove(&tuple);
                                view.rel_tuple_tombstones.insert(tuple);
                            }
                        }
                    }
                }
            }
        }

        // 5. Process function value additions
        if let Some(fv_sort) = self.sort_ids.func_val {
            if let (Some(instance_func), Some(func_func), Some(arg_func), Some(result_func)) = (
                self.func_ids.func_val_instance,
                self.func_ids.func_val_func,
                self.func_ids.func_val_arg,
                self.func_ids.func_val_result,
            ) {
                for fv in self.elements_of_sort(fv_sort) {
                    if self.get_func(instance_func, fv) == Some(version) {
                        if !view.func_val_tombstones.contains(&fv) {
                            if let (Some(func), Some(arg), Some(result)) = (
                                self.get_func(func_func, fv),
                                self.get_func(arg_func, fv),
                                self.get_func(result_func, fv),
                            ) {
                                view.func_vals.insert(fv, (func, arg, result));
                            }
                        }
                    }
                }
            }
        }

        // 6. Process function value retractions
        if let Some(retract_sort) = self.sort_ids.func_val_retract {
            if let Some(instance_func) = self.func_ids.func_val_retract_instance {
                if let Some(fv_func) = self.func_ids.func_val_retract_funcval {
                    for retract in self.elements_of_sort(retract_sort) {
                        if self.get_func(instance_func, retract) == Some(version) {
                            if let Some(fv) = self.get_func(fv_func, retract) {
                                view.func_vals.remove(&fv);
                                view.func_val_tombstones.insert(fv);
                            }
                        }
                    }
                }
            }
        }
    }

    /// Incrementally update a materialized view to a new version.
    ///
    /// The new version must be a direct child of the view's current version,
    /// or this will return an error.
    pub fn update_view(&self, view: &mut MaterializedView, new_version: Slid) -> Result<(), String> {
        // Verify that new_version is a direct child of view.instance
        let parent = self.func_ids.instance_parent
            .and_then(|f| self.get_func(f, new_version));

        if parent != Some(view.instance) {
            return Err(format!(
                "Cannot incrementally update: {} is not a direct child of {}",
                new_version.index(), view.instance.index()
            ));
        }

        // Apply the delta
        self.apply_version_delta(view, new_version);
        view.instance = new_version;

        Ok(())
    }

    /// Create a new instance version extending an existing view, and update the view.
    ///
    /// This is the preferred way to modify instances: create the extension,
    /// add elements/tuples/values to it, then update the view.
    pub fn extend_instance_with_view(
        &mut self,
        view: &mut MaterializedView,
        name: &str,
    ) -> Result<Slid, String> {
        let new_version = self.extend_instance(view.instance, name)?;

        // The view can be updated after mutations are done
        // For now, just update the instance reference
        view.instance = new_version;

        Ok(new_version)
    }

    /// Materialize and cache a view for an instance.
    ///
    /// This stores the view in a view cache for efficient reuse.
    /// The cache is invalidated when the instance is extended.
    pub fn get_or_create_view(&mut self, instance: Slid) -> MaterializedView {
        // For now, just materialize (cache can be added later)
        self.materialize(instance)
    }
}

impl Default for Store {
    fn default() -> Self {
        Self::new()
    }
}

// ============================================================================
// TESTS
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_create_store() {
        let store = Store::new();
        assert!(store.head.is_none());
        assert!(store.uncommitted.is_empty());
    }

    #[test]
    fn test_create_theory() {
        let mut store = Store::new();
        let theory = store.create_theory("TestTheory").unwrap();
        assert!(store.uncommitted.contains_key("TestTheory"));
    }

    #[test]
    fn test_create_instance() {
        let mut store = Store::new();
        let theory = store.create_theory("TestTheory").unwrap();
        let instance = store.create_instance("TestInstance", theory).unwrap();
        assert!(store.uncommitted.contains_key("TestInstance"));
    }

    #[test]
    fn test_commit() {
        let mut store = Store::new();
        let _theory = store.create_theory("TestTheory").unwrap();
        let commit = store.commit(Some("Initial commit")).unwrap();
        assert_eq!(store.head, Some(commit));
        assert!(store.uncommitted.is_empty());
    }

    #[test]
    fn test_materialize_empty_instance() {
        let mut store = Store::new();
        let theory = store.create_theory("TestTheory").unwrap();
        let instance = store.create_instance("TestInstance", theory).unwrap();

        let view = store.materialize(instance);
        assert_eq!(view.instance, instance);
        assert!(view.elements.is_empty());
        assert!(view.rel_tuples.is_empty());
        assert!(view.func_vals.is_empty());
    }

    #[test]
    fn test_materialize_with_elements() {
        let mut store = Store::new();
        let theory = store.create_theory("TestTheory").unwrap();
        let instance = store.create_instance("TestInstance", theory).unwrap();

        // We'd need a sort in the theory to add elements, so this test is limited
        // for now. A fuller test requires creating a proper theory with sorts.
        let view = store.materialize(instance);
        assert_eq!(view.instance, instance);
    }

    #[test]
    fn test_incremental_view_update() {
        let mut store = Store::new();
        let theory = store.create_theory("TestTheory").unwrap();
        let v1 = store.create_instance("TestInstance", theory).unwrap();

        let mut view = store.materialize(v1);
        assert_eq!(view.instance, v1);

        // Extend the instance
        let v2 = store.extend_instance(v1, "TestInstance_v2").unwrap();

        // Update view incrementally
        let result = store.update_view(&mut view, v2);
        assert!(result.is_ok());
        assert_eq!(view.instance, v2);
    }

    #[test]
    fn test_incremental_update_invalid_parent() {
        let mut store = Store::new();
        let theory = store.create_theory("TestTheory").unwrap();
        let v1 = store.create_instance("Instance1", theory).unwrap();
        let v2 = store.create_instance("Instance2", theory).unwrap();

        let mut view = store.materialize(v1);

        // v2 is not a child of v1, so this should fail
        let result = store.update_view(&mut view, v2);
        assert!(result.is_err());
    }
}
