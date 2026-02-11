//! Columnar batch format for efficient storage and wire transfer.
//!
//! This module defines the physical representation for instance-level data
//! (elements, function values, relation tuples). The logical model is still
//! GeologMeta (with Elem, FuncVal, RelTupleArg sorts), but the physical
//! encoding uses columnar batches for efficiency.
//!
//! # EDB vs IDB Batches
//!
//! Batches are tagged as either EDB (extensional) or IDB (intensional):
//!
//! - **EDB batches**: User-declared facts. Persisted locally AND transmitted over wire.
//! - **IDB batches**: Chase-derived facts. Persisted locally but NOT transmitted over wire.
//!
//! When receiving patches over the network, only EDB batches are included.
//! The recipient runs the chase locally to regenerate IDB tuples.
//!
//! Each patch can have up to 2 batches per instance:
//! - One EDB batch (if user manually added tuples)
//! - One IDB batch (if chase produced conclusions)

use rkyv::{Archive, Deserialize, Serialize};

use crate::id::Uuid;

/// Distinguishes between user-declared (EDB) and chase-derived (IDB) data.
///
/// This determines whether the batch is transmitted over the wire during sync.
#[derive(Archive, Serialize, Deserialize, Debug, Clone, Copy, PartialEq, Eq, Default)]
#[archive(check_bytes)]
pub enum BatchKind {
    /// Extensional database: user-declared facts.
    /// Persisted locally AND transmitted over wire.
    #[default]
    Edb,
    /// Intensional database: chase-derived facts.
    /// Persisted locally but NOT transmitted over wire.
    Idb,
}

/// A batch of elements added to an instance.
///
/// Logically equivalent to a collection of Elem elements in GeologMeta.
#[derive(Archive, Serialize, Deserialize, Debug, Clone)]
#[archive(check_bytes)]
pub struct ElementBatch {
    /// Which instance these elements belong to
    pub instance: Uuid,
    /// Sort UUID for each element (parallel array)
    pub sorts: Vec<Uuid>,
    /// UUID for each element (parallel array, same length as sorts)
    pub elements: Vec<Uuid>,
}

/// A batch of function values in an instance.
///
/// Logically equivalent to a collection of FuncVal elements in GeologMeta.
#[derive(Archive, Serialize, Deserialize, Debug, Clone)]
#[archive(check_bytes)]
pub struct FunctionValueBatch {
    /// Which instance these function values belong to
    pub instance: Uuid,
    /// Which function
    pub func: Uuid,
    /// Domain elements (parallel array)
    pub args: Vec<Uuid>,
    /// Codomain elements (parallel array, same length as args)
    pub results: Vec<Uuid>,
}

/// A batch of relation tuples in an instance.
///
/// Logically equivalent to a collection of RelTuple + RelTupleArg elements
/// in GeologMeta, but stored columnar for efficiency.
///
/// For a relation `R : [from: A, to: B] -> Prop`, this stores:
/// - columns[0] = all "from" field values (UUIDs of A elements)
/// - columns[1] = all "to" field values (UUIDs of B elements)
///
/// Row i represents the tuple (columns[0][i], columns[1][i]).
#[derive(Archive, Serialize, Deserialize, Debug, Clone)]
#[archive(check_bytes)]
pub struct RelationTupleBatch {
    /// Which instance these tuples belong to
    pub instance: Uuid,
    /// Which relation
    pub rel: Uuid,
    /// Field UUIDs for each column (from the relation's domain ProdDS/Field)
    pub field_ids: Vec<Uuid>,
    /// Columnar data: columns[field_idx][row_idx] = element UUID
    /// All columns have the same length (number of tuples).
    pub columns: Vec<Vec<Uuid>>,
}

impl RelationTupleBatch {
    /// Create a new empty batch for a relation
    pub fn new(instance: Uuid, rel: Uuid, field_ids: Vec<Uuid>) -> Self {
        let num_fields = field_ids.len();
        Self {
            instance,
            rel,
            field_ids,
            columns: vec![Vec::new(); num_fields],
        }
    }

    /// Add a tuple to the batch
    pub fn push(&mut self, tuple: &[Uuid]) {
        assert_eq!(tuple.len(), self.columns.len(), "tuple arity mismatch");
        for (col, &val) in self.columns.iter_mut().zip(tuple.iter()) {
            col.push(val);
        }
    }

    /// Number of tuples in this batch
    pub fn len(&self) -> usize {
        self.columns.first().map(|c| c.len()).unwrap_or(0)
    }

    /// Whether the batch is empty
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Iterate over tuples as slices
    pub fn iter(&self) -> impl Iterator<Item = Vec<Uuid>> + '_ {
        (0..self.len()).map(|i| {
            self.columns.iter().map(|col| col[i]).collect()
        })
    }
}

/// A complete instance data snapshot in columnar format.
///
/// This is the efficient representation for storage and wire transfer.
/// Logically equivalent to the Elem, FuncVal, RelTuple, RelTupleArg
/// portions of a GeologMeta instance.
#[derive(Archive, Serialize, Deserialize, Debug, Clone, Default)]
#[archive(check_bytes)]
pub struct InstanceDataBatch {
    /// Whether this batch contains EDB (user-declared) or IDB (chase-derived) data.
    /// IDB batches are persisted locally but NOT transmitted over wire.
    pub kind: BatchKind,
    /// All element additions
    pub elements: Vec<ElementBatch>,
    /// All function value definitions
    pub function_values: Vec<FunctionValueBatch>,
    /// All relation tuple assertions
    pub relation_tuples: Vec<RelationTupleBatch>,
}

impl InstanceDataBatch {
    /// Create a new empty EDB batch (default for user-declared data)
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a new empty IDB batch (for chase-derived data)
    pub fn new_idb() -> Self {
        Self {
            kind: BatchKind::Idb,
            ..Default::default()
        }
    }

    /// Check if this batch should be transmitted over the wire
    pub fn is_wire_transmittable(&self) -> bool {
        self.kind == BatchKind::Edb
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_relation_tuple_batch() {
        let instance = Uuid::nil();
        let rel = Uuid::nil();
        let field_a = Uuid::nil();
        let field_b = Uuid::nil();

        let mut batch = RelationTupleBatch::new(
            instance,
            rel,
            vec![field_a, field_b],
        );

        assert!(batch.is_empty());

        // Add some tuples
        let elem1 = Uuid::nil();
        let elem2 = Uuid::nil();
        let elem3 = Uuid::nil();

        batch.push(&[elem1, elem2]);
        batch.push(&[elem2, elem3]);
        batch.push(&[elem1, elem3]);

        assert_eq!(batch.len(), 3);

        let tuples: Vec<_> = batch.iter().collect();
        assert_eq!(tuples.len(), 3);
        assert_eq!(tuples[0], vec![elem1, elem2]);
        assert_eq!(tuples[1], vec![elem2, elem3]);
        assert_eq!(tuples[2], vec![elem1, elem3]);
    }
}
