//! Elaboration: surface syntax → typed core representation
//!
//! This module transforms the untyped AST into the typed core representation,
//! performing name resolution and type checking along the way.

mod env;
mod error;
mod instance;
mod theory;
pub mod types;

// Re-export main types and functions
pub use env::{elaborate_formula, elaborate_term, elaborate_type, Env};
pub use error::{ElabError, ElabResult};
pub use instance::{ElaborationContext, InstanceElaborationResult, InstanceEntry, elaborate_instance_ctx, elaborate_instance_ctx_partial};
pub use theory::elaborate_theory;
pub use types::{eval_type_expr, TypeValue};

use crate::ast::{Declaration, File};

/// Elaborate all theories in an AST file.
///
/// This is a convenience function that iterates over all declarations
/// in the file and elaborates any theory declarations, accumulating
/// them into an `Env`.
///
/// This is useful for:
/// - Testing (e.g., roundtrip tests)
/// - Batch processing of geolog files
/// - Initial loading before REPL interaction
///
/// Note: This only handles theory declarations. Instance and query
/// declarations require additional context (e.g., a Universe for element
/// allocation) and should be processed separately.
pub fn elaborate_theories(file: &File) -> ElabResult<Env> {
    let mut env = Env::new();
    for decl in &file.declarations {
        if let Declaration::Theory(t) = &decl.node {
            let elab = elaborate_theory(&mut env, t)?;
            env.theories.insert(elab.theory.name.clone(), std::rc::Rc::new(elab));
        }
    }
    Ok(env)
}
