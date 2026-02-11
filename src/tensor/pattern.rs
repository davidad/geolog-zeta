//! Sparsity patterns for tensor storage.
//!
//! A sparsity pattern tracks *which* tuples are non-zero in a tensor,
//! without storing the actual values. This separation allows:
//!
//! 1. **For Bool semiring**: The pattern IS the tensor (no separate values needed)
//! 2. **For other semirings**: Pattern + parallel Vec<S> for coefficients
//! 3. **Multiple backends**: BTreeSet, Roaring, CSR, etc.
//!
//! The key operations are:
//! - `contains`: check if a tuple is present
//! - `insert`/`remove`: modify the pattern
//! - `iter`: iterate over present tuples (in sorted order)
//! - `border`: compute the "new" tuples when dimensions grow (for MonotoneSubmodel)

use std::collections::BTreeSet;

/// A sparsity pattern: which tuples are "active" (non-zero) in a tensor.
///
/// Implementations can use different backing stores:
/// - BTreeSet<Vec<usize>> (current, good for incremental)
/// - RoaringBitmap (very efficient for large sparse Boolean tensors)
/// - CSR indices (cache-friendly row iteration)
pub trait SparsityPattern: Clone + Default + std::fmt::Debug {
    /// Dimension sizes (cardinality of each index)
    fn dims(&self) -> &[usize];

    /// Number of dimensions (arity)
    fn arity(&self) -> usize {
        self.dims().len()
    }

    /// Number of non-zero entries
    fn len(&self) -> usize;

    /// Check if empty (all zeros)
    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Check if a tuple is present (non-zero)
    fn contains(&self, tuple: &[usize]) -> bool;

    /// Insert a tuple (mark as non-zero). Returns true if newly inserted.
    fn insert(&mut self, tuple: Vec<usize>) -> bool;

    /// Remove a tuple (mark as zero). Returns true if was present.
    fn remove(&mut self, tuple: &[usize]) -> bool;

    /// Iterate over all non-zero tuples in sorted order.
    fn iter(&self) -> impl Iterator<Item = Vec<usize>>;

    /// Create an empty pattern with given dimensions
    fn empty(dims: Vec<usize>) -> Self;

    /// Create a scalar pattern (0-dimensional) with given presence
    fn scalar(present: bool) -> Self;

    // ========================================================================
    // Derived operations (can be overridden for efficiency)
    // ========================================================================

    /// Union of two patterns (for semiring addition on Bool)
    fn union(&self, other: &Self) -> Self {
        debug_assert_eq!(self.dims(), other.dims());
        let mut result = self.clone();
        for tuple in other.iter() {
            result.insert(tuple);
        }
        result
    }

    /// Intersection of two patterns (for semiring multiplication on Bool)
    fn intersection(&self, other: &Self) -> Self {
        debug_assert_eq!(self.dims(), other.dims());
        let mut result = Self::empty(self.dims().to_vec());
        for tuple in self.iter() {
            if other.contains(&tuple) {
                result.insert(tuple);
            }
        }
        result
    }

    /// Difference: self \ other
    fn difference(&self, other: &Self) -> Self {
        debug_assert_eq!(self.dims(), other.dims());
        let mut result = Self::empty(self.dims().to_vec());
        for tuple in self.iter() {
            if !other.contains(&tuple) {
                result.insert(tuple);
            }
        }
        result
    }

    /// Symmetric difference: (self \ other) ∪ (other \ self)
    fn symmetric_difference(&self, other: &Self) -> Self {
        debug_assert_eq!(self.dims(), other.dims());
        let mut result = Self::empty(self.dims().to_vec());
        for tuple in self.iter() {
            if !other.contains(&tuple) {
                result.insert(tuple);
            }
        }
        for tuple in other.iter() {
            if !self.contains(&tuple) {
                result.insert(tuple);
            }
        }
        result
    }
}

// ============================================================================
// BTreeSet-based implementation (current approach)
// ============================================================================

/// Sparsity pattern backed by BTreeSet<Vec<usize>>.
///
/// Properties:
/// - Good for incremental construction
/// - Sorted iteration (lexicographic order)
/// - O(log n) contains/insert/remove
/// - Memory: ~24 bytes per tuple + tuple data
#[derive(Clone, Debug, Default)]
pub struct BTreeSetPattern {
    dims: Vec<usize>,
    tuples: BTreeSet<Vec<usize>>,
}

impl BTreeSetPattern {
    /// Create from existing BTreeSet (for migration from old SparseTensor)
    pub fn from_parts(dims: Vec<usize>, tuples: BTreeSet<Vec<usize>>) -> Self {
        Self { dims, tuples }
    }

    /// Get the underlying BTreeSet (for migration)
    pub fn into_parts(self) -> (Vec<usize>, BTreeSet<Vec<usize>>) {
        (self.dims, self.tuples)
    }

    /// Direct access to tuples (for compatibility)
    pub fn tuples(&self) -> &BTreeSet<Vec<usize>> {
        &self.tuples
    }
}

impl SparsityPattern for BTreeSetPattern {
    fn dims(&self) -> &[usize] {
        &self.dims
    }

    fn len(&self) -> usize {
        self.tuples.len()
    }

    fn contains(&self, tuple: &[usize]) -> bool {
        self.tuples.contains(tuple)
    }

    fn insert(&mut self, tuple: Vec<usize>) -> bool {
        debug_assert_eq!(tuple.len(), self.dims.len());
        debug_assert!(tuple.iter().zip(&self.dims).all(|(v, d)| *v < *d));
        self.tuples.insert(tuple)
    }

    fn remove(&mut self, tuple: &[usize]) -> bool {
        self.tuples.remove(tuple)
    }

    fn iter(&self) -> impl Iterator<Item = Vec<usize>> {
        self.tuples.iter().cloned()
    }

    fn empty(dims: Vec<usize>) -> Self {
        Self {
            dims,
            tuples: BTreeSet::new(),
        }
    }

    fn scalar(present: bool) -> Self {
        let mut tuples = BTreeSet::new();
        if present {
            tuples.insert(vec![]);
        }
        Self {
            dims: vec![],
            tuples,
        }
    }

    // Override for efficiency using BTreeSet operations
    fn union(&self, other: &Self) -> Self {
        debug_assert_eq!(self.dims, other.dims);
        Self {
            dims: self.dims.clone(),
            tuples: self.tuples.union(&other.tuples).cloned().collect(),
        }
    }

    fn intersection(&self, other: &Self) -> Self {
        debug_assert_eq!(self.dims, other.dims);
        Self {
            dims: self.dims.clone(),
            tuples: self.tuples.intersection(&other.tuples).cloned().collect(),
        }
    }

    fn difference(&self, other: &Self) -> Self {
        debug_assert_eq!(self.dims, other.dims);
        Self {
            dims: self.dims.clone(),
            tuples: self.tuples.difference(&other.tuples).cloned().collect(),
        }
    }

    fn symmetric_difference(&self, other: &Self) -> Self {
        debug_assert_eq!(self.dims, other.dims);
        Self {
            dims: self.dims.clone(),
            tuples: self.tuples.symmetric_difference(&other.tuples).cloned().collect(),
        }
    }
}

// ============================================================================
// Border computation for MonotoneSubmodel
// ============================================================================

/// Compute which tuples in a pattern involve "new" elements.
///
/// When we add elements to sorts, the tensor gains a "border":
/// - For a 2D matrix (n×n), adding element gives L-shaped border
/// - A tuple is in the border iff ANY of its indices is in new_elements
///
/// # Arguments
/// - `pattern`: The full pattern (including border)
/// - `old_dims`: The previous dimension sizes
/// - `new_dims`: The new dimension sizes (>= old_dims componentwise)
///
/// # Returns
/// Pattern containing only tuples with at least one index >= old_dims[i]
pub fn compute_border<P: SparsityPattern>(
    pattern: &P,
    old_dims: &[usize],
    new_dims: &[usize],
) -> P {
    debug_assert_eq!(pattern.dims(), new_dims);
    debug_assert_eq!(old_dims.len(), new_dims.len());
    debug_assert!(old_dims.iter().zip(new_dims).all(|(o, n)| o <= n));

    let mut border = P::empty(new_dims.to_vec());

    for tuple in pattern.iter() {
        // Check if any index is in the "new" range
        let is_border = tuple
            .iter()
            .zip(old_dims)
            .any(|(idx, old_dim)| *idx >= *old_dim);

        if is_border {
            border.insert(tuple);
        }
    }

    border
}

/// Compute which tuples are in the "interior" (not involving new elements).
///
/// This is the complement of `compute_border`: tuples where ALL indices
/// are within the old dimensions.
pub fn compute_interior<P: SparsityPattern>(
    pattern: &P,
    old_dims: &[usize],
    new_dims: &[usize],
) -> P {
    debug_assert_eq!(pattern.dims(), new_dims);
    debug_assert_eq!(old_dims.len(), new_dims.len());

    let mut interior = P::empty(old_dims.to_vec());

    for tuple in pattern.iter() {
        // Check if ALL indices are within old dimensions
        let is_interior = tuple
            .iter()
            .zip(old_dims)
            .all(|(idx, old_dim)| *idx < *old_dim);

        if is_interior {
            interior.insert(tuple);
        }
    }

    interior
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_btreeset_pattern_basic() {
        let mut p = BTreeSetPattern::empty(vec![3, 4]);
        assert_eq!(p.arity(), 2);
        assert!(p.is_empty());

        p.insert(vec![0, 1]);
        p.insert(vec![2, 3]);
        assert_eq!(p.len(), 2);
        assert!(p.contains(&[0, 1]));
        assert!(p.contains(&[2, 3]));
        assert!(!p.contains(&[0, 0]));
    }

    #[test]
    fn test_btreeset_pattern_scalar() {
        let p_true = BTreeSetPattern::scalar(true);
        assert_eq!(p_true.arity(), 0);
        assert_eq!(p_true.len(), 1);
        assert!(p_true.contains(&[]));

        let p_false = BTreeSetPattern::scalar(false);
        assert_eq!(p_false.len(), 0);
        assert!(!p_false.contains(&[]));
    }

    #[test]
    fn test_pattern_set_operations() {
        let mut a = BTreeSetPattern::empty(vec![3, 3]);
        a.insert(vec![0, 0]);
        a.insert(vec![1, 1]);

        let mut b = BTreeSetPattern::empty(vec![3, 3]);
        b.insert(vec![1, 1]);
        b.insert(vec![2, 2]);

        let union = a.union(&b);
        assert_eq!(union.len(), 3);
        assert!(union.contains(&[0, 0]));
        assert!(union.contains(&[1, 1]));
        assert!(union.contains(&[2, 2]));

        let intersection = a.intersection(&b);
        assert_eq!(intersection.len(), 1);
        assert!(intersection.contains(&[1, 1]));

        let diff = a.difference(&b);
        assert_eq!(diff.len(), 1);
        assert!(diff.contains(&[0, 0]));

        let sym_diff = a.symmetric_difference(&b);
        assert_eq!(sym_diff.len(), 2);
        assert!(sym_diff.contains(&[0, 0]));
        assert!(sym_diff.contains(&[2, 2]));
    }

    #[test]
    fn test_compute_border() {
        // 3x3 matrix, expanding to 4x4
        let mut full = BTreeSetPattern::empty(vec![4, 4]);
        // Interior: (0,0), (1,1), (2,2)
        full.insert(vec![0, 0]);
        full.insert(vec![1, 1]);
        full.insert(vec![2, 2]);
        // Border: (3,*), (*,3)
        full.insert(vec![3, 0]);  // new row
        full.insert(vec![3, 3]);  // corner
        full.insert(vec![1, 3]);  // new col

        let old_dims = [3, 3];
        let new_dims = [4, 4];

        let border = compute_border(&full, &old_dims, &new_dims);
        assert_eq!(border.len(), 3);
        assert!(border.contains(&[3, 0]));
        assert!(border.contains(&[3, 3]));
        assert!(border.contains(&[1, 3]));
        assert!(!border.contains(&[0, 0]));
        assert!(!border.contains(&[1, 1]));

        let interior = compute_interior(&full, &old_dims, &new_dims);
        assert_eq!(interior.len(), 3);
        assert!(interior.contains(&[0, 0]));
        assert!(interior.contains(&[1, 1]));
        assert!(interior.contains(&[2, 2]));
    }
}
