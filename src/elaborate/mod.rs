//! Elaboration: surface syntax → typed core representation
//!
//! This module transforms the untyped AST into the typed core representation,
//! performing name resolution and type checking along the way.

mod env;
mod error;
mod instance;
mod theory;

// Re-export main types and functions
pub use env::{elaborate_formula, elaborate_term, elaborate_type, Env};
pub use error::{ElabError, ElabResult};
#[allow(deprecated)]
pub use instance::{elaborate_instance, elaborate_instance_ws};
pub use theory::elaborate_theory;
