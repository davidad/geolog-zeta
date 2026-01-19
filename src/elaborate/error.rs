//! Elaboration error types.

use crate::core::DerivedSort;

/// Elaboration errors
#[derive(Clone, Debug)]
pub enum ElabError {
    UnknownSort(String),
    UnknownTheory(String),
    UnknownFunction(String),
    UnknownRel(String),
    UnknownVariable(String),
    TypeMismatch {
        expected: DerivedSort,
        got: DerivedSort,
    },
    NotASort(String),
    NotAFunction(String),
    NotARecord(String),
    NoSuchField {
        record: String,
        field: String,
    },
    InvalidPath(String),
    DuplicateDefinition(String),
    UnsupportedFeature(String),
    PartialFunction {
        func_name: String,
        missing_elements: Vec<String>,
    },
    /// Type error in function application: element's sort doesn't match function's domain
    DomainMismatch {
        func_name: String,
        element_name: String,
        expected_sort: String,
        actual_sort: String,
    },
    /// Type error in equation: RHS sort doesn't match function's codomain
    CodomainMismatch {
        func_name: String,
        element_name: String,
        expected_sort: String,
        actual_sort: String,
    },
}

impl std::fmt::Display for ElabError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ElabError::UnknownSort(s) => write!(f, "unknown sort: {}", s),
            ElabError::UnknownTheory(s) => write!(f, "unknown theory: {}", s),
            ElabError::UnknownFunction(s) => write!(f, "unknown function: {}", s),
            ElabError::UnknownRel(s) => write!(f, "unknown relation: {}", s),
            ElabError::UnknownVariable(s) => write!(f, "unknown variable: {}", s),
            ElabError::TypeMismatch { expected, got } => {
                write!(f, "type mismatch: expected {}, got {}", expected, got)
            }
            ElabError::NotASort(s) => write!(f, "not a sort: {}", s),
            ElabError::NotAFunction(s) => write!(f, "not a function: {}", s),
            ElabError::NotARecord(s) => write!(f, "not a record type: {}", s),
            ElabError::NoSuchField { record, field } => {
                write!(f, "no field '{}' in record {}", field, record)
            }
            ElabError::InvalidPath(s) => write!(f, "invalid path: {}", s),
            ElabError::DuplicateDefinition(s) => write!(f, "duplicate definition: {}", s),
            ElabError::UnsupportedFeature(s) => write!(f, "unsupported feature: {}", s),
            ElabError::PartialFunction {
                func_name,
                missing_elements,
            } => {
                write!(
                    f,
                    "partial function '{}': missing definitions for {:?}",
                    func_name, missing_elements
                )
            }
            ElabError::DomainMismatch {
                func_name,
                element_name,
                expected_sort,
                actual_sort,
            } => {
                write!(
                    f,
                    "type error: '{}' has sort '{}', but function '{}' expects domain sort '{}'",
                    element_name, actual_sort, func_name, expected_sort
                )
            }
            ElabError::CodomainMismatch {
                func_name,
                element_name,
                expected_sort,
                actual_sort,
            } => {
                write!(
                    f,
                    "type error: '{}' has sort '{}', but function '{}' has codomain sort '{}'",
                    element_name, actual_sort, func_name, expected_sort
                )
            }
        }
    }
}

pub type ElabResult<T> = Result<T, ElabError>;
