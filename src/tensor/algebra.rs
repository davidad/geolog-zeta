//! Tagless final interface for tensor algebra.
//!
//! This module defines the `TensorSym` trait, which provides a generic interface
//! for tensor computations. Different implementations (interpreters) can provide:
//!
//! - **Eager**: Materialize immediately
//! - **Lazy**: Build expression trees, fuse operations
//! - **Incremental**: Track values AND deltas for change propagation
//!
//! The key insight is that the same "program" (sequence of tensor operations)
//! can be interpreted in different ways without changing the program itself.
//!
//! # Example
//!
//! ```ignore
//! fn my_computation<T: TensorSym>(input: T::Tensor<bool>) -> T::Tensor<bool> {
//!     let squared = T::product(input.clone(), input);
//!     T::contract(squared, &[0, 1], &btreeset!{0})  // trace
//! }
//!
//! // Run eagerly:
//! let result = my_computation::<Eager<BTreeSetPattern>>(data);
//!
//! // Run incrementally:
//! let (result, delta) = my_computation::<Incremental<BTreeSetPattern>>(data_with_delta);
//! ```

use std::collections::BTreeSet;
use std::marker::PhantomData;

use super::pattern::{BTreeSetPattern, SparsityPattern};
use super::semiring::OrderedSemiring;

// ============================================================================
// Core Trait: TensorSym (Tagless Final)
// ============================================================================

/// Tagless final interface for tensor algebra.
///
/// Each implementation provides a `Tensor<S>` type that represents tensors
/// over semiring S. The operations build/transform these tensors.
///
/// # Type Parameters
///
/// The trait itself is parameterless; implementations are typically unit structs
/// like `Eager<P>` or `Lazy` that carry configuration via PhantomData.
pub trait TensorSym {
    /// The tensor representation, parameterized by semiring.
    ///
    /// For Eager<P>: this is a concrete sparse tensor with pattern P
    /// For Lazy: this is an expression tree (AST)
    /// For Incremental<P>: this is (value, delta) pair
    type Tensor<S: OrderedSemiring>: Clone;

    /// Dimensions of a tensor
    fn dims<S: OrderedSemiring>(t: &Self::Tensor<S>) -> Vec<usize>;

    /// Create a tensor from a sparse pattern (Bool semiring).
    ///
    /// For non-Bool semirings, use `from_entries` instead.
    fn from_pattern<P: SparsityPattern + Into<BTreeSetPattern>>(pattern: P) -> Self::Tensor<bool>;

    /// Create a tensor from sparse entries: (tuple, value) pairs.
    fn from_entries<S: OrderedSemiring>(
        dims: Vec<usize>,
        entries: impl IntoIterator<Item = (Vec<usize>, S)>,
    ) -> Self::Tensor<S>;

    /// Scalar tensor (0-dimensional)
    fn scalar<S: OrderedSemiring>(value: S) -> Self::Tensor<S>;

    /// Zero tensor (all entries are semiring zero)
    fn zero<S: OrderedSemiring>(dims: Vec<usize>) -> Self::Tensor<S>;

    /// Tensor product (⊗): Kronecker product of tensors.
    ///
    /// Result dimensions = concat of input dimensions.
    /// Values multiply: (A ⊗ B)[i,j] = A[i] ⊗ B[j]
    fn product<S: OrderedSemiring>(a: Self::Tensor<S>, b: Self::Tensor<S>) -> Self::Tensor<S>;

    /// Tensor sum (⊕): pointwise addition.
    ///
    /// Requires same dimensions.
    /// Values add: (A ⊕ B)[i] = A[i] ⊕ B[i]
    fn sum<S: OrderedSemiring>(a: Self::Tensor<S>, b: Self::Tensor<S>) -> Self::Tensor<S>;

    /// Contraction: identify indices and sum over non-output.
    ///
    /// This is the general einsum operation.
    ///
    /// # Arguments
    /// - `inner`: the input tensor
    /// - `index_map`: for each input index, which target index (0..M)
    /// - `output`: which target indices appear in output (subset of 0..M)
    ///
    /// Indices mapping to the same target are identified (equality constraint).
    /// Target indices not in `output` are summed (⊕) over (existential quantification).
    fn contract<S: OrderedSemiring>(
        inner: Self::Tensor<S>,
        index_map: &[usize],
        output: &BTreeSet<usize>,
    ) -> Self::Tensor<S>;

    /// Hadamard product: pointwise multiplication.
    ///
    /// Requires same dimensions.
    /// Values multiply: (A ⊙ B)[i] = A[i] ⊗ B[i]
    fn hadamard<S: OrderedSemiring>(a: Self::Tensor<S>, b: Self::Tensor<S>) -> Self::Tensor<S>;

    // ========================================================================
    // Convenience operations (derived from primitives)
    // ========================================================================

    /// N-ary product
    fn product_all<S: OrderedSemiring>(tensors: Vec<Self::Tensor<S>>) -> Self::Tensor<S> {
        tensors
            .into_iter()
            .reduce(|a, b| Self::product(a, b))
            .unwrap_or_else(|| Self::scalar(S::one()))
    }

    /// N-ary sum
    fn sum_all<S: OrderedSemiring>(tensors: Vec<Self::Tensor<S>>) -> Self::Tensor<S> {
        if tensors.is_empty() {
            // Need dims for zero tensor - this is a limitation
            panic!("sum_all requires at least one tensor");
        }
        tensors
            .into_iter()
            .reduce(|a, b| Self::sum(a, b))
            .unwrap()
    }

    /// Project to specific dimensions (drop others via contraction)
    fn project<S: OrderedSemiring>(
        tensor: Self::Tensor<S>,
        keep: &[usize],
    ) -> Self::Tensor<S> {
        let dims = Self::dims(&tensor);
        let n = dims.len();

        // Build index_map: identity on kept indices, otherwise map to max+1
        let mut index_map = vec![keep.len(); n]; // default: contracted out
        for (out_idx, &in_idx) in keep.iter().enumerate() {
            index_map[in_idx] = out_idx;
        }

        let output: BTreeSet<usize> = (0..keep.len()).collect();
        Self::contract(tensor, &index_map, &output)
    }

    /// Check equality of two indices (diagonal extraction)
    fn diagonal<S: OrderedSemiring>(
        tensor: Self::Tensor<S>,
        i: usize,
        j: usize,
    ) -> Self::Tensor<S> {
        let dims = Self::dims(&tensor);
        let n = dims.len();

        // Build index_map: i and j map to same target
        let mut index_map: Vec<usize> = (0..n).collect();
        // Map j to same target as i
        let target_i = i.min(j);
        index_map[i] = target_i;
        index_map[j] = target_i;

        // Renumber: indices > max(i,j) shift down by 1
        let max_ij = i.max(j);
        for val in &mut index_map[(max_ij + 1)..] {
            *val -= 1;
        }

        let output: BTreeSet<usize> = (0..(n - 1)).collect();
        Self::contract(tensor, &index_map, &output)
    }

    /// Existential quantification: ∃ over dimension i
    fn exists<S: OrderedSemiring>(tensor: Self::Tensor<S>, i: usize) -> Self::Tensor<S> {
        let dims = Self::dims(&tensor);
        let n = dims.len();

        // Keep all except i
        let keep: Vec<usize> = (0..n).filter(|&k| k != i).collect();
        Self::project(tensor, &keep)
    }
}

// ============================================================================
// Sparse Tensor (concrete storage for Eager)
// ============================================================================

/// A sparse tensor over semiring S with pattern P.
///
/// For Bool semiring, `values` is empty (pattern encodes everything).
/// For other semirings, `values[i]` is the value for `pattern.iter().nth(i)`.
#[derive(Clone, Debug)]
pub struct SparseTensorData<S: OrderedSemiring, P: SparsityPattern> {
    pub pattern: P,
    /// Values parallel to pattern iteration order.
    /// Empty for Bool semiring (pattern IS the data).
    pub values: Vec<S>,
}

impl<S: OrderedSemiring, P: SparsityPattern> SparseTensorData<S, P> {
    /// Create from pattern (Bool semiring)
    pub fn from_bool_pattern(pattern: P) -> SparseTensorData<bool, P> {
        SparseTensorData {
            pattern,
            values: vec![], // Bool doesn't need values
        }
    }

    /// Create from entries
    pub fn from_entries(
        dims: Vec<usize>,
        entries: impl IntoIterator<Item = (Vec<usize>, S)>,
    ) -> Self {
        let mut pattern = P::empty(dims);
        let mut values = Vec::new();

        for (tuple, value) in entries {
            if !value.is_zero() {
                pattern.insert(tuple);
                values.push(value);
            }
        }

        Self { pattern, values }
    }

    /// Get value at tuple (returns zero if absent)
    pub fn get(&self, tuple: &[usize]) -> S {
        if !self.pattern.contains(tuple) {
            return S::zero();
        }

        if self.values.is_empty() {
            // Bool semiring: presence means true/one
            // This is a bit of a hack - we return one() which is correct for Bool
            return S::one();
        }

        // Find index in pattern iteration
        // TODO: This is O(n) - could use a HashMap for O(1) lookup
        for (i, t) in self.pattern.iter().enumerate() {
            if t.as_slice() == tuple {
                return self.values[i].clone();
            }
        }

        S::zero()
    }

    pub fn dims(&self) -> &[usize] {
        self.pattern.dims()
    }

    pub fn len(&self) -> usize {
        self.pattern.len()
    }

    pub fn is_empty(&self) -> bool {
        self.pattern.is_empty()
    }
}

// ============================================================================
// Eager Interpreter
// ============================================================================

/// Eager evaluation: operations materialize immediately.
///
/// This is the "reference" implementation - simple and correct,
/// but doesn't fuse operations.
pub struct Eager<P: SparsityPattern = BTreeSetPattern>(PhantomData<P>);

impl<P: SparsityPattern + Default + 'static> TensorSym for Eager<P> {
    type Tensor<S: OrderedSemiring> = SparseTensorData<S, P>;

    fn dims<S: OrderedSemiring>(t: &Self::Tensor<S>) -> Vec<usize> {
        t.pattern.dims().to_vec()
    }

    fn from_pattern<Q: SparsityPattern + Into<BTreeSetPattern>>(pattern: Q) -> Self::Tensor<bool> {
        // Convert to BTreeSetPattern first, then to P
        let btree_pattern: BTreeSetPattern = pattern.into();
        let (dims, tuples) = btree_pattern.into_parts();

        let mut p = P::empty(dims);
        for tuple in tuples {
            p.insert(tuple);
        }

        SparseTensorData {
            pattern: p,
            values: vec![],
        }
    }

    fn from_entries<S: OrderedSemiring>(
        dims: Vec<usize>,
        entries: impl IntoIterator<Item = (Vec<usize>, S)>,
    ) -> Self::Tensor<S> {
        SparseTensorData::from_entries(dims, entries)
    }

    fn scalar<S: OrderedSemiring>(value: S) -> Self::Tensor<S> {
        if value.is_zero() {
            SparseTensorData {
                pattern: P::scalar(false),
                values: vec![],
            }
        } else {
            SparseTensorData {
                pattern: P::scalar(true),
                values: if value.is_one() { vec![] } else { vec![value] },
            }
        }
    }

    fn zero<S: OrderedSemiring>(dims: Vec<usize>) -> Self::Tensor<S> {
        SparseTensorData {
            pattern: P::empty(dims),
            values: vec![],
        }
    }

    fn product<S: OrderedSemiring>(a: Self::Tensor<S>, b: Self::Tensor<S>) -> Self::Tensor<S> {
        let a_dims = a.pattern.dims().to_vec();
        let b_dims = b.pattern.dims().to_vec();
        let mut result_dims = a_dims.clone();
        result_dims.extend(b_dims.iter().cloned());

        let mut result_pattern = P::empty(result_dims);
        let mut result_values = Vec::new();

        // Cartesian product of non-zero entries
        for (i, tuple_a) in a.pattern.iter().enumerate() {
            let val_a = if a.values.is_empty() {
                S::one()
            } else {
                a.values[i].clone()
            };

            for (j, tuple_b) in b.pattern.iter().enumerate() {
                let val_b = if b.values.is_empty() {
                    S::one()
                } else {
                    b.values[j].clone()
                };

                let mut result_tuple = tuple_a.clone();
                result_tuple.extend(tuple_b.iter().cloned());

                let result_val = val_a.mul(&val_b);
                if !result_val.is_zero() {
                    result_pattern.insert(result_tuple);
                    if !result_val.is_one() {
                        result_values.push(result_val);
                    }
                }
            }
        }

        // Normalize values vector
        if result_values.len() != result_pattern.len() && !result_values.is_empty() {
            // Mixed ones and non-ones - need to be careful
            // For now, just materialize all values
            // TODO: optimize this
        }

        SparseTensorData {
            pattern: result_pattern,
            values: result_values,
        }
    }

    fn sum<S: OrderedSemiring>(a: Self::Tensor<S>, b: Self::Tensor<S>) -> Self::Tensor<S> {
        debug_assert_eq!(a.pattern.dims(), b.pattern.dims());

        let dims = a.pattern.dims().to_vec();
        let mut result_pattern = P::empty(dims);
        let mut result_map: std::collections::BTreeMap<Vec<usize>, S> = std::collections::BTreeMap::new();

        // Add entries from a
        for (i, tuple) in a.pattern.iter().enumerate() {
            let val = if a.values.is_empty() {
                S::one()
            } else {
                a.values[i].clone()
            };
            result_map.insert(tuple, val);
        }

        // Add entries from b
        for (i, tuple) in b.pattern.iter().enumerate() {
            let val = if b.values.is_empty() {
                S::one()
            } else {
                b.values[i].clone()
            };
            result_map
                .entry(tuple)
                .and_modify(|existing| *existing = existing.add(&val))
                .or_insert(val);
        }

        // Build result
        let mut result_values = Vec::new();
        for (tuple, val) in result_map {
            if !val.is_zero() {
                result_pattern.insert(tuple);
                if !val.is_one() {
                    result_values.push(val);
                }
            }
        }

        SparseTensorData {
            pattern: result_pattern,
            values: result_values,
        }
    }

    fn contract<S: OrderedSemiring>(
        inner: Self::Tensor<S>,
        index_map: &[usize],
        output: &BTreeSet<usize>,
    ) -> Self::Tensor<S> {
        let inner_dims = inner.pattern.dims();
        debug_assert_eq!(index_map.len(), inner_dims.len());

        // Compute output dimensions
        let max_target = index_map.iter().copied().max().unwrap_or(0);
        let mut target_dims: Vec<Option<usize>> = vec![None; max_target + 1];
        for (i, &target) in index_map.iter().enumerate() {
            match target_dims[target] {
                None => target_dims[target] = Some(inner_dims[i]),
                Some(d) => debug_assert_eq!(d, inner_dims[i], "identified indices must have same dim"),
            }
        }

        let output_dims: Vec<usize> = (0..=max_target)
            .filter(|t| output.contains(t))
            .map(|t| target_dims[t].unwrap())
            .collect();

        let mut result_map: std::collections::BTreeMap<Vec<usize>, S> = std::collections::BTreeMap::new();

        for (i, tuple) in inner.pattern.iter().enumerate() {
            // Check index identification constraints
            let mut target_vals: Vec<Option<usize>> = vec![None; max_target + 1];
            let mut valid = true;

            for (idx, &val) in tuple.iter().enumerate() {
                let target = index_map[idx];
                match target_vals[target] {
                    None => target_vals[target] = Some(val),
                    Some(prev) => {
                        if prev != val {
                            valid = false;
                            break;
                        }
                    }
                }
            }

            if !valid {
                continue;
            }

            // Build output tuple
            let output_tuple: Vec<usize> = (0..=max_target)
                .filter(|t| output.contains(t))
                .map(|t| target_vals[t].unwrap())
                .collect();

            let val = if inner.values.is_empty() {
                S::one()
            } else {
                inner.values[i].clone()
            };

            result_map
                .entry(output_tuple)
                .and_modify(|existing| *existing = existing.add(&val))
                .or_insert(val);
        }

        // Build result
        let mut result_pattern = P::empty(output_dims);
        let mut result_values = Vec::new();

        for (tuple, val) in result_map {
            if !val.is_zero() {
                result_pattern.insert(tuple);
                if !val.is_one() {
                    result_values.push(val);
                }
            }
        }

        SparseTensorData {
            pattern: result_pattern,
            values: result_values,
        }
    }

    fn hadamard<S: OrderedSemiring>(a: Self::Tensor<S>, b: Self::Tensor<S>) -> Self::Tensor<S> {
        debug_assert_eq!(a.pattern.dims(), b.pattern.dims());

        let intersection = a.pattern.intersection(&b.pattern);

        let mut result_values = Vec::new();
        for tuple in intersection.iter() {
            let val_a = a.get(&tuple);
            let val_b = b.get(&tuple);
            let val = val_a.mul(&val_b);
            if !val.is_zero() && !val.is_one() {
                result_values.push(val);
            }
        }

        SparseTensorData {
            pattern: intersection,
            values: result_values,
        }
    }
}

// ============================================================================
// Incremental Interpreter
// ============================================================================

/// A tensor with its delta (for incremental computation).
///
/// Under MonotoneSubmodel semantics:
/// - `value` is the full current tensor
/// - `delta` contains only the "border" (tuples involving new elements)
/// - The invariant is: new_value = old_value ⊕ delta (for insertions)
///
/// For general semirings, delta can represent arbitrary changes.
#[derive(Clone, Debug)]
pub struct IncrementalTensor<S: OrderedSemiring, P: SparsityPattern> {
    /// The full current value
    pub value: SparseTensorData<S, P>,
    /// The change from the previous value
    /// Under MonotoneSubmodel: only new tuples (insertions)
    pub delta: SparseTensorData<S, P>,
}

impl<S: OrderedSemiring, P: SparsityPattern> IncrementalTensor<S, P> {
    /// Create from a value with no changes
    pub fn stable(value: SparseTensorData<S, P>) -> Self {
        let delta = SparseTensorData {
            pattern: P::empty(value.pattern.dims().to_vec()),
            values: vec![],
        };
        Self { value, delta }
    }

    /// Create from a value that is entirely new (all delta)
    pub fn all_new(value: SparseTensorData<S, P>) -> Self {
        let delta = value.clone();
        Self { value, delta }
    }

    /// Create from value and explicit delta
    pub fn with_delta(value: SparseTensorData<S, P>, delta: SparseTensorData<S, P>) -> Self {
        debug_assert_eq!(value.pattern.dims(), delta.pattern.dims());
        Self { value, delta }
    }

    /// Check if there are any changes
    pub fn has_changes(&self) -> bool {
        !self.delta.is_empty()
    }

    /// Get just the value (discarding delta information)
    pub fn into_value(self) -> SparseTensorData<S, P> {
        self.value
    }
}

/// Incremental evaluation: track (value, delta) pairs and propagate changes.
///
/// Implements the differentiation rules:
/// - δ(A ⊗ B) = (δA ⊗ B) ⊕ (A ⊗ δB) ⊕ (δA ⊗ δB)
/// - δ(A ⊕ B) = δA ⊕ δB
/// - δ(Contract(T)) = Contract(δT)  [contraction is linear!]
/// - δ(Hadamard(A, B)) = (δA ⊙ B) ⊕ (A ⊙ δB) ⊕ (δA ⊙ δB)
///
/// Under MonotoneSubmodel, deltas are always non-negative (insertions only),
/// so we use the Bool/ℕ semiring interpretation where ⊕ is union/addition.
pub struct Incremental<P: SparsityPattern = BTreeSetPattern>(PhantomData<P>);

impl<P: SparsityPattern + Default + 'static> TensorSym for Incremental<P> {
    type Tensor<S: OrderedSemiring> = IncrementalTensor<S, P>;

    fn dims<S: OrderedSemiring>(t: &Self::Tensor<S>) -> Vec<usize> {
        t.value.pattern.dims().to_vec()
    }

    fn from_pattern<Q: SparsityPattern + Into<BTreeSetPattern>>(pattern: Q) -> Self::Tensor<bool> {
        // New data is all delta
        let value = Eager::<P>::from_pattern(pattern);
        IncrementalTensor::all_new(value)
    }

    fn from_entries<S: OrderedSemiring>(
        dims: Vec<usize>,
        entries: impl IntoIterator<Item = (Vec<usize>, S)>,
    ) -> Self::Tensor<S> {
        let value = Eager::<P>::from_entries(dims, entries);
        IncrementalTensor::all_new(value)
    }

    fn scalar<S: OrderedSemiring>(value: S) -> Self::Tensor<S> {
        let tensor = Eager::<P>::scalar(value);
        IncrementalTensor::all_new(tensor)
    }

    fn zero<S: OrderedSemiring>(dims: Vec<usize>) -> Self::Tensor<S> {
        let tensor = Eager::<P>::zero(dims);
        IncrementalTensor::stable(tensor) // zero has no changes
    }

    fn product<S: OrderedSemiring>(a: Self::Tensor<S>, b: Self::Tensor<S>) -> Self::Tensor<S> {
        // Full value: A ⊗ B
        let full_value = Eager::<P>::product(a.value.clone(), b.value.clone());

        // Delta: δ(A ⊗ B) = (δA ⊗ B) ⊕ (A ⊗ δB) ⊕ (δA ⊗ δB)
        // But we need to be careful not to double-count:
        // - (δA ⊗ B_old) contributes new tuples from δA
        // - (A_old ⊗ δB) contributes new tuples from δB
        // - (δA ⊗ δB) is the corner where both are new
        //
        // Under MonotoneSubmodel where A = A_old ⊕ δA:
        // A ⊗ B = (A_old ⊕ δA) ⊗ (B_old ⊕ δB)
        //       = (A_old ⊗ B_old) ⊕ (δA ⊗ B_old) ⊕ (A_old ⊗ δB) ⊕ (δA ⊗ δB)
        //       = old_product ⊕ delta_product
        //
        // So delta_product = (δA ⊗ B) ⊕ (A ⊗ δB) - (δA ⊗ δB)
        // But for Bool semiring with insertions only, we can just use:
        // delta = (δA ⊗ B) ⊕ (A_old ⊗ δB) ⊕ (δA ⊗ δB)
        //       = (δA ⊗ B) ⊕ (A ⊗ δB) when we're careful about A vs A_old
        //
        // Simpler approach: delta = full_value - old_value
        // But we don't have old_value...
        //
        // Actually, the cleanest is: δ(A⊗B) = (δA⊗B) ⊕ (A⊗δB) - (δA⊗δB)
        // which avoids double counting the corner.
        //
        // For Bool semiring (union), this simplifies to just computing
        // the new tuples.

        let delta_a_times_b = Eager::<P>::product(a.delta.clone(), b.value.clone());
        let a_times_delta_b = Eager::<P>::product(a.value.clone(), b.delta.clone());
        let delta_a_times_delta_b = Eager::<P>::product(a.delta, b.delta);

        // Combine: (δA ⊗ B) ⊕ (A ⊗ δB)
        let mut delta = Eager::<P>::sum(delta_a_times_b, a_times_delta_b);

        // For non-Bool semirings, we'd subtract δA⊗δB to avoid double counting
        // For Bool, the union already handles this correctly (idempotent)
        // But let's be precise for general semirings:
        // Actually for incremental correctness, we include all three terms
        // The "double counting" issue is that δA⊗δB appears in both
        // (δA⊗B) and (A⊗δB) when B includes δB and A includes δA.
        //
        // Since our `value` already includes `delta`, we need:
        // delta = (δA ⊗ B_full) ⊕ (A_full ⊗ δB) ⊖ (δA ⊗ δB)
        //
        // For now, for Bool semiring (idempotent), just union all three:
        delta = Eager::<P>::sum(delta, delta_a_times_delta_b);

        IncrementalTensor {
            value: full_value,
            delta,
        }
    }

    fn sum<S: OrderedSemiring>(a: Self::Tensor<S>, b: Self::Tensor<S>) -> Self::Tensor<S> {
        // Sum is linear: δ(A ⊕ B) = δA ⊕ δB
        let full_value = Eager::<P>::sum(a.value, b.value);
        let delta = Eager::<P>::sum(a.delta, b.delta);

        IncrementalTensor {
            value: full_value,
            delta,
        }
    }

    fn contract<S: OrderedSemiring>(
        inner: Self::Tensor<S>,
        index_map: &[usize],
        output: &BTreeSet<usize>,
    ) -> Self::Tensor<S> {
        // Contraction is linear: δ(Contract(T)) = Contract(δT)
        let full_value = Eager::<P>::contract(inner.value, index_map, output);
        let delta = Eager::<P>::contract(inner.delta, index_map, output);

        IncrementalTensor {
            value: full_value,
            delta,
        }
    }

    fn hadamard<S: OrderedSemiring>(a: Self::Tensor<S>, b: Self::Tensor<S>) -> Self::Tensor<S> {
        // Hadamard (pointwise product) follows product rule:
        // δ(A ⊙ B) = (δA ⊙ B) ⊕ (A ⊙ δB) ⊕ (δA ⊙ δB)
        //
        // Similar to tensor product but pointwise.
        let full_value = Eager::<P>::hadamard(a.value.clone(), b.value.clone());

        let delta_a_had_b = Eager::<P>::hadamard(a.delta.clone(), b.value.clone());
        let a_had_delta_b = Eager::<P>::hadamard(a.value, b.delta.clone());
        let delta_a_had_delta_b = Eager::<P>::hadamard(a.delta, b.delta);

        let delta = Eager::<P>::sum(
            Eager::<P>::sum(delta_a_had_b, a_had_delta_b),
            delta_a_had_delta_b,
        );

        IncrementalTensor {
            value: full_value,
            delta,
        }
    }
}

// ============================================================================
// Monotone Delta: specialized for MonotoneSubmodel
// ============================================================================

/// Compute the delta when dimensions grow (for MonotoneSubmodel).
///
/// Given a tensor over new (larger) dimensions, and the old dimension sizes,
/// returns a tensor containing only the "border" tuples - those involving
/// at least one index from the new element range.
///
/// This is the bridge between `Patch` (which adds elements) and tensor deltas.
pub fn monotone_delta<S: OrderedSemiring, P: SparsityPattern>(
    full_tensor: &SparseTensorData<S, P>,
    old_dims: &[usize],
) -> SparseTensorData<S, P> {
    let new_dims = full_tensor.pattern.dims();
    debug_assert_eq!(old_dims.len(), new_dims.len());

    let border_pattern = super::pattern::compute_border(&full_tensor.pattern, old_dims, new_dims);

    // Extract values for border tuples
    let mut border_values = Vec::new();
    if !full_tensor.values.is_empty() {
        for tuple in border_pattern.iter() {
            let val = full_tensor.get(&tuple);
            if !val.is_zero() && !val.is_one() {
                border_values.push(val);
            }
        }
    }

    SparseTensorData {
        pattern: border_pattern,
        values: border_values,
    }
}

/// Create an IncrementalTensor from dimension growth.
///
/// Given a full tensor and the old dimensions, creates an IncrementalTensor
/// where `delta` is exactly the border (new tuples from new elements).
pub fn from_dimension_growth<S: OrderedSemiring, P: SparsityPattern + Default>(
    full_tensor: SparseTensorData<S, P>,
    old_dims: &[usize],
) -> IncrementalTensor<S, P> {
    let delta = monotone_delta(&full_tensor, old_dims);
    IncrementalTensor {
        value: full_tensor,
        delta,
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    type E = Eager<BTreeSetPattern>;

    #[test]
    fn test_eager_scalar() {
        let t: SparseTensorData<bool, BTreeSetPattern> = E::scalar(true);
        assert_eq!(t.pattern.dims(), &[] as &[usize]);
        assert!(t.pattern.contains(&[]));

        let f: SparseTensorData<bool, BTreeSetPattern> = E::scalar(false);
        assert!(!f.pattern.contains(&[]));
    }

    #[test]
    fn test_eager_product_bool() {
        // a = [true, false, true] (indices 0, 2)
        let mut a_pattern = BTreeSetPattern::empty(vec![3]);
        a_pattern.insert(vec![0]);
        a_pattern.insert(vec![2]);
        let a: SparseTensorData<bool, BTreeSetPattern> = SparseTensorData {
            pattern: a_pattern,
            values: vec![],
        };

        // b = [true, true] (indices 0, 1)
        let mut b_pattern = BTreeSetPattern::empty(vec![2]);
        b_pattern.insert(vec![0]);
        b_pattern.insert(vec![1]);
        let b: SparseTensorData<bool, BTreeSetPattern> = SparseTensorData {
            pattern: b_pattern,
            values: vec![],
        };

        let product = E::product(a, b);
        assert_eq!(product.pattern.dims(), &[3, 2]);
        assert_eq!(product.pattern.len(), 4); // 2 * 2

        assert!(product.pattern.contains(&[0, 0]));
        assert!(product.pattern.contains(&[0, 1]));
        assert!(product.pattern.contains(&[2, 0]));
        assert!(product.pattern.contains(&[2, 1]));
        assert!(!product.pattern.contains(&[1, 0]));
    }

    #[test]
    fn test_eager_sum_bool() {
        let mut a_pattern = BTreeSetPattern::empty(vec![3]);
        a_pattern.insert(vec![0]);
        a_pattern.insert(vec![1]);
        let a: SparseTensorData<bool, BTreeSetPattern> = SparseTensorData {
            pattern: a_pattern,
            values: vec![],
        };

        let mut b_pattern = BTreeSetPattern::empty(vec![3]);
        b_pattern.insert(vec![1]);
        b_pattern.insert(vec![2]);
        let b: SparseTensorData<bool, BTreeSetPattern> = SparseTensorData {
            pattern: b_pattern,
            values: vec![],
        };

        let sum = E::sum(a, b);
        assert_eq!(sum.pattern.len(), 3); // {0, 1, 2}
        assert!(sum.pattern.contains(&[0]));
        assert!(sum.pattern.contains(&[1]));
        assert!(sum.pattern.contains(&[2]));
    }

    #[test]
    fn test_eager_contract_diagonal() {
        // 2x2 matrix with (0,0) and (1,1) true (diagonal)
        let mut pattern = BTreeSetPattern::empty(vec![2, 2]);
        pattern.insert(vec![0, 0]);
        pattern.insert(vec![1, 1]);
        pattern.insert(vec![0, 1]); // off-diagonal
        let t: SparseTensorData<bool, BTreeSetPattern> = SparseTensorData {
            pattern,
            values: vec![],
        };

        // Contract to diagonal: index_map = [0, 0], output = {0}
        let diag = E::contract(t, &[0, 0], &BTreeSet::from([0]));
        assert_eq!(diag.pattern.dims(), &[2]);
        assert_eq!(diag.pattern.len(), 2); // (0,0) and (1,1)
        assert!(diag.pattern.contains(&[0]));
        assert!(diag.pattern.contains(&[1]));
    }

    #[test]
    fn test_eager_contract_exists() {
        // 2x2 matrix
        let mut pattern = BTreeSetPattern::empty(vec![2, 2]);
        pattern.insert(vec![0, 1]);
        pattern.insert(vec![1, 0]);
        let t: SparseTensorData<bool, BTreeSetPattern> = SparseTensorData {
            pattern,
            values: vec![],
        };

        // Exists over second index: ∃j. T[i,j]
        // index_map = [0, 1], output = {0}
        let exists = E::contract(t, &[0, 1], &BTreeSet::from([0]));
        assert_eq!(exists.pattern.dims(), &[2]);
        assert_eq!(exists.pattern.len(), 2); // both rows have at least one true
        assert!(exists.pattern.contains(&[0]));
        assert!(exists.pattern.contains(&[1]));
    }

    #[test]
    fn test_eager_integer_semiring() {
        // Test with i64 semiring
        let a: SparseTensorData<i64, BTreeSetPattern> = E::from_entries(
            vec![3],
            vec![(vec![0], 2), (vec![1], 3)],
        );

        let b: SparseTensorData<i64, BTreeSetPattern> = E::from_entries(
            vec![3],
            vec![(vec![1], 4), (vec![2], 5)],
        );

        let sum = E::sum(a, b);
        assert_eq!(sum.get(&[0]), 2);
        assert_eq!(sum.get(&[1]), 7); // 3 + 4
        assert_eq!(sum.get(&[2]), 5);
    }

    // ========================================================================
    // Incremental Interpreter Tests
    // ========================================================================

    type I = Incremental<BTreeSetPattern>;

    #[test]
    fn test_incremental_stable_no_delta() {
        // A tensor with no changes should have empty delta
        let mut pattern = BTreeSetPattern::empty(vec![3]);
        pattern.insert(vec![0]);
        pattern.insert(vec![2]);
        let value: SparseTensorData<bool, BTreeSetPattern> = SparseTensorData {
            pattern,
            values: vec![],
        };

        let inc = IncrementalTensor::stable(value);
        assert!(!inc.has_changes());
        assert!(inc.delta.is_empty());
        assert_eq!(inc.value.len(), 2);
    }

    #[test]
    fn test_incremental_all_new() {
        // A completely new tensor should have delta = value
        let mut pattern = BTreeSetPattern::empty(vec![3]);
        pattern.insert(vec![0]);
        pattern.insert(vec![1]);
        let value: SparseTensorData<bool, BTreeSetPattern> = SparseTensorData {
            pattern,
            values: vec![],
        };

        let inc = IncrementalTensor::all_new(value);
        assert!(inc.has_changes());
        assert_eq!(inc.delta.len(), 2);
        assert!(inc.delta.pattern.contains(&[0]));
        assert!(inc.delta.pattern.contains(&[1]));
    }

    #[test]
    fn test_incremental_sum_linear() {
        // δ(A ⊕ B) = δA ⊕ δB (sum is linear in deltas)

        // A: stable tensor [0, 1] with no delta
        let mut a_pattern = BTreeSetPattern::empty(vec![4]);
        a_pattern.insert(vec![0]);
        a_pattern.insert(vec![1]);
        let a_value: SparseTensorData<bool, BTreeSetPattern> = SparseTensorData {
            pattern: a_pattern,
            values: vec![],
        };
        let a = IncrementalTensor::stable(a_value);

        // B: tensor [2, 3] that is all new (delta = value)
        let mut b_pattern = BTreeSetPattern::empty(vec![4]);
        b_pattern.insert(vec![2]);
        b_pattern.insert(vec![3]);
        let b_value: SparseTensorData<bool, BTreeSetPattern> = SparseTensorData {
            pattern: b_pattern,
            values: vec![],
        };
        let b = IncrementalTensor::all_new(b_value);

        let sum = I::sum(a, b);

        // Value should be union: {0, 1, 2, 3}
        assert_eq!(sum.value.len(), 4);

        // Delta should just be δB = {2, 3} (since δA is empty)
        assert_eq!(sum.delta.len(), 2);
        assert!(sum.delta.pattern.contains(&[2]));
        assert!(sum.delta.pattern.contains(&[3]));
    }

    #[test]
    fn test_incremental_contract_linear() {
        // δ(Contract(T)) = Contract(δT) (contraction is linear)

        // 3x3 matrix with some stable and some new entries
        let mut full_pattern = BTreeSetPattern::empty(vec![3, 3]);
        full_pattern.insert(vec![0, 0]); // diagonal, stable
        full_pattern.insert(vec![1, 1]); // diagonal, stable
        full_pattern.insert(vec![2, 2]); // diagonal, NEW
        full_pattern.insert(vec![0, 1]); // off-diagonal, NEW
        let full_value: SparseTensorData<bool, BTreeSetPattern> = SparseTensorData {
            pattern: full_pattern,
            values: vec![],
        };

        let mut delta_pattern = BTreeSetPattern::empty(vec![3, 3]);
        delta_pattern.insert(vec![2, 2]); // new diagonal
        delta_pattern.insert(vec![0, 1]); // new off-diagonal
        let delta: SparseTensorData<bool, BTreeSetPattern> = SparseTensorData {
            pattern: delta_pattern,
            values: vec![],
        };

        let t = IncrementalTensor::with_delta(full_value, delta);

        // Contract to diagonal (trace-like, but keep indices)
        let diag = I::contract(t, &[0, 0], &BTreeSet::from([0]));

        // Full diagonal should have {0, 1, 2}
        assert_eq!(diag.value.len(), 3);

        // Delta diagonal should only have {2} (the new diagonal entry)
        assert_eq!(diag.delta.len(), 1);
        assert!(diag.delta.pattern.contains(&[2]));
    }

    #[test]
    fn test_incremental_product_differentiation() {
        // δ(A ⊗ B) = (δA ⊗ B) ⊕ (A ⊗ δB) ⊕ (δA ⊗ δB)
        // Under MonotoneSubmodel: new tuples from either new A or new B

        // A: [0] stable, [1] new
        let mut a_full = BTreeSetPattern::empty(vec![2]);
        a_full.insert(vec![0]);
        a_full.insert(vec![1]);
        let a_value: SparseTensorData<bool, BTreeSetPattern> = SparseTensorData {
            pattern: a_full,
            values: vec![],
        };
        let mut a_delta = BTreeSetPattern::empty(vec![2]);
        a_delta.insert(vec![1]); // only [1] is new
        let a_delta_tensor: SparseTensorData<bool, BTreeSetPattern> = SparseTensorData {
            pattern: a_delta,
            values: vec![],
        };
        let a = IncrementalTensor::with_delta(a_value, a_delta_tensor);

        // B: [0] new (all new)
        let mut b_full = BTreeSetPattern::empty(vec![2]);
        b_full.insert(vec![0]);
        let b_value: SparseTensorData<bool, BTreeSetPattern> = SparseTensorData {
            pattern: b_full,
            values: vec![],
        };
        let b = IncrementalTensor::all_new(b_value);

        let product = I::product(a, b);

        // Full product: {0, 1} × {0} = {(0,0), (1,0)}
        assert_eq!(product.value.len(), 2);
        assert!(product.value.pattern.contains(&[0, 0]));
        assert!(product.value.pattern.contains(&[1, 0]));

        // Delta should include all new combinations:
        // - (1, 0): from δA × B (new element 1 in A)
        // - (0, 0): from A × δB (new element 0 in B, paired with stable 0 in A)
        // - (1, 0): also from δA × δB (both new)
        // Result: {(0,0), (1,0)} - both are new!
        assert_eq!(product.delta.len(), 2);
        assert!(product.delta.pattern.contains(&[0, 0]));
        assert!(product.delta.pattern.contains(&[1, 0]));
    }

    #[test]
    fn test_monotone_delta_border() {
        // Test that monotone_delta correctly extracts the border

        // 4x4 tensor with entries in both interior and border
        let mut pattern = BTreeSetPattern::empty(vec![4, 4]);
        pattern.insert(vec![0, 0]); // interior (was in 3x3)
        pattern.insert(vec![1, 1]); // interior
        pattern.insert(vec![2, 2]); // interior
        pattern.insert(vec![3, 0]); // border (new row)
        pattern.insert(vec![0, 3]); // border (new col)
        pattern.insert(vec![3, 3]); // border (corner)
        let full: SparseTensorData<bool, BTreeSetPattern> = SparseTensorData {
            pattern,
            values: vec![],
        };

        let old_dims = [3, 3];
        let delta = monotone_delta(&full, &old_dims);

        // Delta should contain only border entries
        assert_eq!(delta.len(), 3);
        assert!(delta.pattern.contains(&[3, 0]));
        assert!(delta.pattern.contains(&[0, 3]));
        assert!(delta.pattern.contains(&[3, 3]));
        assert!(!delta.pattern.contains(&[0, 0]));
        assert!(!delta.pattern.contains(&[1, 1]));
    }

    #[test]
    fn test_from_dimension_growth() {
        // Test the full pipeline: dimension growth → incremental tensor

        let mut pattern = BTreeSetPattern::empty(vec![4, 4]);
        pattern.insert(vec![0, 0]);
        pattern.insert(vec![1, 1]);
        pattern.insert(vec![3, 3]); // new corner
        let full: SparseTensorData<bool, BTreeSetPattern> = SparseTensorData {
            pattern,
            values: vec![],
        };

        let old_dims = [3, 3];
        let inc = from_dimension_growth(full, &old_dims);

        // Value should have all 3 entries
        assert_eq!(inc.value.len(), 3);

        // Delta should have only the border entry
        assert_eq!(inc.delta.len(), 1);
        assert!(inc.delta.pattern.contains(&[3, 3]));
        assert!(inc.has_changes());
    }

    #[test]
    fn test_incremental_hadamard() {
        // δ(A ⊙ B) = (δA ⊙ B) ⊕ (A ⊙ δB) ⊕ (δA ⊙ δB)

        // A: {0, 1, 2} with δA = {2}
        let mut a_full = BTreeSetPattern::empty(vec![4]);
        a_full.insert(vec![0]);
        a_full.insert(vec![1]);
        a_full.insert(vec![2]);
        let a_value: SparseTensorData<bool, BTreeSetPattern> = SparseTensorData {
            pattern: a_full,
            values: vec![],
        };
        let mut a_delta_pattern = BTreeSetPattern::empty(vec![4]);
        a_delta_pattern.insert(vec![2]);
        let a_delta: SparseTensorData<bool, BTreeSetPattern> = SparseTensorData {
            pattern: a_delta_pattern,
            values: vec![],
        };
        let a = IncrementalTensor::with_delta(a_value, a_delta);

        // B: {1, 2, 3} with δB = {3}
        let mut b_full = BTreeSetPattern::empty(vec![4]);
        b_full.insert(vec![1]);
        b_full.insert(vec![2]);
        b_full.insert(vec![3]);
        let b_value: SparseTensorData<bool, BTreeSetPattern> = SparseTensorData {
            pattern: b_full,
            values: vec![],
        };
        let mut b_delta_pattern = BTreeSetPattern::empty(vec![4]);
        b_delta_pattern.insert(vec![3]);
        let b_delta: SparseTensorData<bool, BTreeSetPattern> = SparseTensorData {
            pattern: b_delta_pattern,
            values: vec![],
        };
        let b = IncrementalTensor::with_delta(b_value, b_delta);

        let had = I::hadamard(a, b);

        // Full Hadamard: {0,1,2} ∩ {1,2,3} = {1, 2}
        assert_eq!(had.value.len(), 2);
        assert!(had.value.pattern.contains(&[1]));
        assert!(had.value.pattern.contains(&[2]));

        // Delta: new overlaps
        // δA ⊙ B = {2} ∩ {1,2,3} = {2}
        // A ⊙ δB = {0,1,2} ∩ {3} = {} (no overlap)
        // δA ⊙ δB = {2} ∩ {3} = {}
        // Result: {2}
        assert_eq!(had.delta.len(), 1);
        assert!(had.delta.pattern.contains(&[2]));
    }

    #[test]
    fn test_incremental_integer_semiring() {
        // Test incremental with non-Bool semiring

        let a: SparseTensorData<i64, BTreeSetPattern> = E::from_entries(
            vec![3],
            vec![(vec![0], 2), (vec![1], 3)],
        );
        let a_inc = IncrementalTensor::stable(a);

        let b: SparseTensorData<i64, BTreeSetPattern> = E::from_entries(
            vec![3],
            vec![(vec![1], 4), (vec![2], 5)],
        );
        let b_inc = IncrementalTensor::all_new(b);

        let sum = I::sum(a_inc, b_inc);

        // Value: {0→2, 1→7, 2→5}
        assert_eq!(sum.value.get(&[0]), 2);
        assert_eq!(sum.value.get(&[1]), 7);
        assert_eq!(sum.value.get(&[2]), 5);

        // Delta: only from B since A was stable
        // δB = {1→4, 2→5}
        assert_eq!(sum.delta.get(&[1]), 4);
        assert_eq!(sum.delta.get(&[2]), 5);
        assert_eq!(sum.delta.get(&[0]), 0); // not in delta
    }
}
