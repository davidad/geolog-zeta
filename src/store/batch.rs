//! Atomic batch creation for elements.
//!
//! This module enforces the Monotonic Submodel Property by requiring all facts
//! involving an element to be defined atomically at element creation time.
//!
//! # Design Principles
//!
//! 1. **All facts defined at creation**: When element `a` is created, all facts
//!    involving `a` (function values `f(a)=b`, relation tuples `R(a,c)`) must be
//!    defined in the same atomic batch.
//!
//! 2. **No post-hoc fact addition**: After an element's batch is committed, no new
//!    facts involving that element can be added. This ensures existing submodels
//!    remain valid as new elements are added.
//!
//! 3. **Relations are boolean functions**: Relations `R: A × B → Bool` are treated
//!    as total functions. When element `a` is created, all `R(a, _)` and `R(_, a)`
//!    values are implicitly `false` unless explicitly asserted as `true`.

use crate::id::{NumericId, Slid};

use super::Store;

/// An atomic batch of changes for creating a single new element.
///
/// All facts involving the new element must be defined in this batch.
/// After the batch is committed, no new facts can be added.
#[derive(Debug, Clone)]
pub struct ElementBatch {
    /// The instance this element belongs to
    pub instance: Slid,

    /// The sort (from the theory) of this element
    pub sort: Slid,

    /// Human-readable name for the element
    pub name: String,

    /// Function values where this element is in the domain: f(elem) = value
    pub func_vals: Vec<(Slid, Slid)>, // (func, codomain_value)

    /// Relation assertions where this element appears: R(..., elem, ...) = true
    /// Only the TRUE tuples are listed; everything else is implicitly false.
    pub rel_tuples: Vec<(Slid, Slid)>, // (rel, arg) - for unary relations or when elem is the arg
}

impl ElementBatch {
    /// Create an empty/invalid batch (for use with mem::replace)
    fn empty() -> Self {
        Self {
            instance: Slid::from_usize(0),
            sort: Slid::from_usize(0),
            name: String::new(),
            func_vals: Vec::new(),
            rel_tuples: Vec::new(),
        }
    }
}

impl ElementBatch {
    /// Create a new element batch
    pub fn new(instance: Slid, sort: Slid, name: impl Into<String>) -> Self {
        Self {
            instance,
            sort,
            name: name.into(),
            func_vals: Vec::new(),
            rel_tuples: Vec::new(),
        }
    }

    /// Add a function value: f(this_element) = value
    pub fn with_func(mut self, func: Slid, value: Slid) -> Self {
        self.func_vals.push((func, value));
        self
    }

    /// Add a relation tuple: R(this_element) = true (for unary relations)
    /// or R(arg) = true where this element is part of arg
    pub fn with_rel(mut self, rel: Slid, arg: Slid) -> Self {
        self.rel_tuples.push((rel, arg));
        self
    }

    /// Define a function value: f(this_element) = value
    pub fn define_func(&mut self, func: Slid, value: Slid) {
        self.func_vals.push((func, value));
    }

    /// Assert a relation tuple as true
    pub fn assert_rel(&mut self, rel: Slid, arg: Slid) {
        self.rel_tuples.push((rel, arg));
    }
}

/// Builder for creating elements with all their facts defined atomically.
///
/// This enforces the Monotonic Submodel Property by ensuring all facts
/// are defined before the element is committed.
pub struct ElementBuilder<'a> {
    store: &'a mut Store,
    batch: ElementBatch,
    committed: bool,
}

impl<'a> ElementBuilder<'a> {
    /// Create a new element builder
    pub fn new(store: &'a mut Store, instance: Slid, sort: Slid, name: impl Into<String>) -> Self {
        Self {
            store,
            batch: ElementBatch::new(instance, sort, name),
            committed: false,
        }
    }

    /// Define a function value: f(this_element) = value
    pub fn define_func(&mut self, func: Slid, value: Slid) -> &mut Self {
        self.batch.define_func(func, value);
        self
    }

    /// Assert a relation tuple as true: R(arg) = true
    pub fn assert_rel(&mut self, rel: Slid, arg: Slid) -> &mut Self {
        self.batch.assert_rel(rel, arg);
        self
    }

    /// Commit the element batch and return the new element's Slid.
    ///
    /// This atomically creates the element and all its facts.
    /// After this, no new facts involving this element can be added.
    pub fn commit(mut self) -> Result<Slid, String> {
        self.committed = true;
        let batch = std::mem::replace(&mut self.batch, ElementBatch::empty());
        self.store.add_element_batch(batch)
    }
}

impl<'a> Drop for ElementBuilder<'a> {
    fn drop(&mut self) {
        if !self.committed {
            // Log a warning if the builder was dropped without committing
            // In debug builds, this could panic to catch bugs
            #[cfg(debug_assertions)]
            eprintln!(
                "Warning: ElementBuilder for '{}' was dropped without committing",
                self.batch.name
            );
        }
    }
}

impl Store {
    /// Create an element builder for atomic element creation.
    ///
    /// # Example
    ///
    /// ```ignore
    /// let elem = store.build_element(instance, sort, "my_element")
    ///     .define_func(f, target)
    ///     .assert_rel(r, arg)
    ///     .commit()?;
    /// ```
    pub fn build_element(
        &mut self,
        instance: Slid,
        sort: Slid,
        name: impl Into<String>,
    ) -> ElementBuilder<'_> {
        ElementBuilder::new(self, instance, sort, name)
    }

    /// Add an element with all its facts atomically.
    ///
    /// This is the low-level API; prefer `build_element()` for a builder pattern.
    pub fn add_element_batch(&mut self, batch: ElementBatch) -> Result<Slid, String> {
        // 1. Create the element
        let elem_slid = self.add_elem(batch.instance, batch.sort, &batch.name)?;

        // 2. Add all function values
        for (func, value) in batch.func_vals {
            self.add_func_val(batch.instance, func, elem_slid, value)?;
        }

        // 3. Add all relation tuples (sparse: only the true ones)
        for (rel, arg) in batch.rel_tuples {
            self.add_rel_tuple(batch.instance, rel, arg)?;
        }

        Ok(elem_slid)
    }

    /// Create multiple elements atomically within a closure.
    ///
    /// This allows defining elements that reference each other within the same batch.
    ///
    /// # Example
    ///
    /// ```ignore
    /// store.create_elements(instance, |ctx| {
    ///     let a = ctx.add_element(sort_a, "a")?;
    ///     let b = ctx.add_element(sort_b, "b")?;
    ///
    ///     ctx.define_func(f, a, b)?;  // f(a) = b
    ///     ctx.assert_rel(r, a)?;       // R(a) = true
    ///
    ///     Ok(vec![a, b])
    /// })?;
    /// ```
    pub fn create_elements<F, R>(&mut self, instance: Slid, f: F) -> Result<R, String>
    where
        F: FnOnce(&mut ElementCreationContext<'_>) -> Result<R, String>,
    {
        let mut ctx = ElementCreationContext::new(self, instance);
        let result = f(&mut ctx)?;
        ctx.commit()?;
        Ok(result)
    }
}

/// Context for creating multiple elements atomically.
///
/// All elements and facts created within this context are committed together.
pub struct ElementCreationContext<'a> {
    store: &'a mut Store,
    instance: Slid,
    /// Elements created but not yet committed to GeologMeta
    pending_elements: Vec<(Slid, Slid, String)>, // (sort, slid, name)
    /// Function values to add
    pending_func_vals: Vec<(Slid, Slid, Slid)>, // (func, arg, result)
    /// Relation tuples to add
    pending_rel_tuples: Vec<(Slid, Slid)>, // (rel, arg)
    committed: bool,
}

impl<'a> ElementCreationContext<'a> {
    fn new(store: &'a mut Store, instance: Slid) -> Self {
        Self {
            store,
            instance,
            pending_elements: Vec::new(),
            pending_func_vals: Vec::new(),
            pending_rel_tuples: Vec::new(),
            committed: false,
        }
    }

    /// Add a new element (returns Slid immediately for use in defining facts)
    pub fn add_element(&mut self, sort: Slid, name: impl Into<String>) -> Result<Slid, String> {
        let name = name.into();
        let elem_slid = self.store.add_elem(self.instance, sort, &name)?;
        self.pending_elements.push((sort, elem_slid, name));
        Ok(elem_slid)
    }

    /// Define a function value: f(arg) = result
    pub fn define_func(&mut self, func: Slid, arg: Slid, result: Slid) -> Result<(), String> {
        self.pending_func_vals.push((func, arg, result));
        Ok(())
    }

    /// Assert a relation tuple as true: R(arg) = true
    pub fn assert_rel(&mut self, rel: Slid, arg: Slid) -> Result<(), String> {
        self.pending_rel_tuples.push((rel, arg));
        Ok(())
    }

    /// Commit all pending elements and facts
    fn commit(&mut self) -> Result<(), String> {
        // Add all function values
        for (func, arg, result) in std::mem::take(&mut self.pending_func_vals) {
            self.store.add_func_val(self.instance, func, arg, result)?;
        }

        // Add all relation tuples
        for (rel, arg) in std::mem::take(&mut self.pending_rel_tuples) {
            self.store.add_rel_tuple(self.instance, rel, arg)?;
        }

        self.committed = true;
        Ok(())
    }
}

impl<'a> Drop for ElementCreationContext<'a> {
    fn drop(&mut self) {
        if !self.committed && !self.pending_elements.is_empty() {
            #[cfg(debug_assertions)]
            eprintln!(
                "Warning: ElementCreationContext with {} pending elements was dropped without committing",
                self.pending_elements.len()
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_element_batch_builder() {
        let mut store = Store::new();

        // Create a theory with a sort
        let theory = store.create_theory("TestTheory").unwrap();
        let sort = store.add_sort(theory, "Node").unwrap();
        let sort_ds = store.make_base_dsort(sort).unwrap();

        // Create a function
        let _func = store.add_function(theory, "label", sort_ds, sort_ds).unwrap();

        // Create an instance
        let instance = store.create_instance("TestInstance", theory).unwrap();

        // Create an element using the batch API
        let elem = store
            .build_element(instance, sort, "node1")
            .commit()
            .unwrap();

        // Verify element was created
        let view = store.materialize(instance);
        assert!(view.elements.contains(&elem));
    }

    #[test]
    fn test_create_elements_context() {
        let mut store = Store::new();

        // Create a theory with a sort and relation
        let theory = store.create_theory("TestTheory").unwrap();
        let sort = store.add_sort(theory, "Node").unwrap();
        let sort_ds = store.make_base_dsort(sort).unwrap();
        let rel = store.add_relation(theory, "connected", sort_ds).unwrap();

        // Create an instance
        let instance = store.create_instance("TestInstance", theory).unwrap();

        // Create multiple elements atomically
        let (a, b) = store
            .create_elements(instance, |ctx| {
                let a = ctx.add_element(sort, "a")?;
                let b = ctx.add_element(sort, "b")?;
                ctx.assert_rel(rel, a)?;
                Ok((a, b))
            })
            .unwrap();

        // Verify elements were created
        let view = store.materialize(instance);
        assert!(view.elements.contains(&a));
        assert!(view.elements.contains(&b));
    }
}
