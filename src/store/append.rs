//! Low-level append operations for the Store.
//!
//! These are the primitive operations that all higher-level operations use.
//! Note: We use a trait to document the interface, but the actual implementations
//! are on Store directly to avoid borrow checker issues.

use crate::id::Slid;

/// Low-level operations on the meta structure.
///
/// This trait documents the interface that Store implements for low-level
/// element manipulation. The actual implementations are on Store directly.
pub trait AppendOps {
    /// Add an element to a sort in the meta structure with a simple name
    fn add_element(&mut self, sort_id: usize, name: &str) -> Slid;

    /// Add an element with a qualified name path
    fn add_element_qualified(&mut self, sort_id: usize, path: Vec<String>) -> Slid;

    /// Define a function value in the meta structure
    fn define_func(&mut self, func_id: usize, domain: Slid, codomain: Slid) -> Result<(), String>;

    /// Get a function value from the meta structure
    fn get_func(&self, func_id: usize, domain: Slid) -> Option<Slid>;

    /// Get all elements of a sort
    fn elements_of_sort(&self, sort_id: usize) -> Vec<Slid>;

    /// Get the name of an element
    fn get_element_name(&self, slid: Slid) -> String;
}
