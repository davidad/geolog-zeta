//! Sparse Boolean tensor (materialized).

use std::collections::BTreeSet;

/// A sparse Boolean tensor (materialized).
///
/// Indexed by a product of finite sets with given cardinalities.
/// Stores the set of index tuples that map to `true`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SparseTensor {
    /// Cardinality of each index dimension
    pub dims: Vec<usize>,
    /// Set of tuples (as `Vec<usize>`) where the tensor is true
    /// Each tuple has length == dims.len()
    pub extent: BTreeSet<Vec<usize>>,
}

impl SparseTensor {
    /// Create an empty tensor (all false) with given dimensions
    pub fn empty(dims: Vec<usize>) -> Self {
        Self {
            dims,
            extent: BTreeSet::new(),
        }
    }

    /// Create a scalar tensor (0-dimensional) with given value
    pub fn scalar(value: bool) -> Self {
        let mut extent = BTreeSet::new();
        if value {
            extent.insert(vec![]);
        }
        Self {
            dims: vec![],
            extent,
        }
    }

    /// Number of dimensions (arity)
    pub fn arity(&self) -> usize {
        self.dims.len()
    }

    /// Number of true entries
    pub fn len(&self) -> usize {
        self.extent.len()
    }

    /// Check if empty (all false)
    pub fn is_empty(&self) -> bool {
        self.extent.is_empty()
    }

    /// Check if a specific tuple is true
    pub fn contains(&self, tuple: &[usize]) -> bool {
        self.extent.contains(tuple)
    }

    /// Insert a tuple (set to true)
    pub fn insert(&mut self, tuple: Vec<usize>) -> bool {
        debug_assert_eq!(tuple.len(), self.dims.len());
        debug_assert!(tuple.iter().zip(&self.dims).all(|(v, d)| *v < *d));
        self.extent.insert(tuple)
    }

    /// Remove a tuple (set to false)
    pub fn remove(&mut self, tuple: &[usize]) -> bool {
        self.extent.remove(tuple)
    }

    /// Iterate over all true tuples
    pub fn iter(&self) -> impl Iterator<Item = &Vec<usize>> {
        self.extent.iter()
    }
}

// ============================================================================
// ITERATORS
// ============================================================================

/// Iterator over all tuples in a domain (Cartesian product of ranges)
pub(crate) struct DomainIterator {
    dims: Vec<usize>,
    current: Vec<usize>,
    done: bool,
}

impl DomainIterator {
    pub fn new(dims: &[usize]) -> Self {
        let done = dims.contains(&0);
        Self {
            dims: dims.to_vec(),
            current: vec![0; dims.len()],
            done,
        }
    }
}

impl Iterator for DomainIterator {
    type Item = Vec<usize>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }

        if self.dims.is_empty() {
            self.done = true;
            return Some(vec![]);
        }

        let result = self.current.clone();

        // Advance (odometer style)
        for i in (0..self.dims.len()).rev() {
            self.current[i] += 1;
            if self.current[i] < self.dims[i] {
                break;
            }
            self.current[i] = 0;
            if i == 0 {
                self.done = true;
            }
        }

        Some(result)
    }
}

/// Iterator over Cartesian product of sparse tensor extents
pub(crate) struct CartesianProductIter<'a> {
    tensors: &'a [SparseTensor],
    iterators: Vec<std::collections::btree_set::Iter<'a, Vec<usize>>>,
    current: Vec<Option<&'a Vec<usize>>>,
    done: bool,
}

impl<'a> CartesianProductIter<'a> {
    pub fn new(tensors: &'a [SparseTensor]) -> Self {
        if tensors.is_empty() {
            return Self {
                tensors,
                iterators: vec![],
                current: vec![],
                done: false,
            };
        }

        let done = tensors.iter().any(|t| t.is_empty());
        let mut iterators: Vec<_> = tensors.iter().map(|t| t.extent.iter()).collect();
        let current: Vec<_> = iterators.iter_mut().map(|it| it.next()).collect();

        Self {
            tensors,
            iterators,
            current,
            done,
        }
    }
}

impl<'a> Iterator for CartesianProductIter<'a> {
    type Item = Vec<usize>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }

        if self.tensors.is_empty() {
            self.done = true;
            return Some(vec![]);
        }

        // Build result
        let result: Vec<usize> = self
            .current
            .iter()
            .filter_map(|opt| opt.as_ref())
            .flat_map(|tuple| tuple.iter().copied())
            .collect();

        // Advance (odometer style)
        for i in (0..self.tensors.len()).rev() {
            if let Some(next) = self.iterators[i].next() {
                self.current[i] = Some(next);
                break;
            } else {
                self.iterators[i] = self.tensors[i].extent.iter();
                self.current[i] = self.iterators[i].next();
                if i == 0 {
                    self.done = true;
                }
            }
        }

        Some(result)
    }
}

/// Cartesian product of extents of multiple sparse tensors
pub(crate) fn cartesian_product_of_extents(tensors: &[SparseTensor]) -> BTreeSet<Vec<usize>> {
    CartesianProductIter::new(tensors).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sparse_tensor_basic() {
        let mut t = SparseTensor::empty(vec![3, 2]);
        assert_eq!(t.arity(), 2);
        assert!(t.is_empty());

        t.insert(vec![0, 1]);
        t.insert(vec![2, 0]);
        assert_eq!(t.len(), 2);
        assert!(t.contains(&[0, 1]));
        assert!(t.contains(&[2, 0]));
        assert!(!t.contains(&[0, 0]));
    }
}
