//! Ordered semirings for tensor computations.
//!
//! A semiring (S, ⊕, ⊗, 0, 1) provides:
//! - Additive monoid (S, ⊕, 0)
//! - Multiplicative monoid (S, ⊗, 1)
//! - Multiplication distributes over addition
//! - 0 annihilates: 0 ⊗ x = x ⊗ 0 = 0
//!
//! "Ordered" means we have a total order compatible with the operations,
//! useful for convergence checks and canonical representations.
//!
//! Each semiring has an associated **change type** (à la Alvarez-Picallo's
//! Change Actions) for incremental computation.

use std::fmt::Debug;
use std::hash::Hash;

/// An ordered semiring with change actions for incremental computation.
///
/// The `Delta` associated type represents changes to values. For some semirings
/// (like ℤ), Delta = Self (self-differentiable). For others (like Bool), Delta
/// might be a different type (e.g., {-1, 0, +1}).
pub trait OrderedSemiring:
    Clone + Debug + PartialEq + Eq + PartialOrd + Ord + Hash + Default + Send + Sync + 'static
{
    /// The type of changes/deltas for this semiring.
    ///
    /// For incremental computation: if `x : S` and `dx : S::Delta`,
    /// then `x.apply_delta(&dx) : S` is the updated value.
    type Delta: Clone + Debug + PartialEq + Eq + Hash + Default + Send + Sync + 'static;

    /// Additive identity: x ⊕ 0 = 0 ⊕ x = x
    fn zero() -> Self;

    /// Multiplicative identity: x ⊗ 1 = 1 ⊗ x = x
    fn one() -> Self;

    /// Semiring addition (⊕)
    fn add(&self, other: &Self) -> Self;

    /// Semiring multiplication (⊗)
    fn mul(&self, other: &Self) -> Self;

    /// Check if this is the additive identity
    fn is_zero(&self) -> bool {
        self == &Self::zero()
    }

    /// Check if this is the multiplicative identity
    fn is_one(&self) -> bool {
        self == &Self::one()
    }

    // ========================================================================
    // Change Actions interface
    // ========================================================================

    /// The zero change (identity for delta composition)
    fn zero_delta() -> Self::Delta;

    /// Apply a delta to get a new value: x ⊕_action dx
    fn apply_delta(&self, delta: &Self::Delta) -> Self;

    /// Compute the delta from `self` to `other`: other ⊖ self
    /// Such that `self.apply_delta(&self.diff(other)) == other`
    fn diff(&self, other: &Self) -> Self::Delta;

    /// Compose two deltas: (dx1 then dx2)
    fn compose_delta(d1: &Self::Delta, d2: &Self::Delta) -> Self::Delta;

    /// Negate a delta (for retractions in MonotoneSubmodel)
    fn negate_delta(d: &Self::Delta) -> Self::Delta;
}

// ============================================================================
// Boolean Semiring
// ============================================================================

/// Change type for Bool: can go false→true (+1), true→false (-1), or stay (0)
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Default)]
pub struct BoolDelta(pub i8); // -1, 0, or +1

impl BoolDelta {
    pub const NONE: Self = BoolDelta(0);
    pub const INSERT: Self = BoolDelta(1);
    pub const DELETE: Self = BoolDelta(-1);
}

impl OrderedSemiring for bool {
    type Delta = BoolDelta;

    #[inline]
    fn zero() -> Self {
        false
    }

    #[inline]
    fn one() -> Self {
        true
    }

    #[inline]
    fn add(&self, other: &Self) -> Self {
        *self || *other // OR
    }

    #[inline]
    fn mul(&self, other: &Self) -> Self {
        *self && *other // AND
    }

    #[inline]
    fn zero_delta() -> BoolDelta {
        BoolDelta::NONE
    }

    #[inline]
    fn apply_delta(&self, delta: &BoolDelta) -> Self {
        match delta.0 {
            1 => true,
            -1 => false,
            _ => *self,
        }
    }

    #[inline]
    fn diff(&self, other: &Self) -> BoolDelta {
        BoolDelta(*other as i8 - *self as i8)
    }

    #[inline]
    fn compose_delta(d1: &BoolDelta, d2: &BoolDelta) -> BoolDelta {
        // Saturating: INSERT then DELETE = NONE, etc.
        BoolDelta((d1.0 + d2.0).clamp(-1, 1))
    }

    #[inline]
    fn negate_delta(d: &BoolDelta) -> BoolDelta {
        BoolDelta(-d.0)
    }
}

// ============================================================================
// Integer Semiring (ℤ) - for Z-sets / changes
// ============================================================================

impl OrderedSemiring for i64 {
    type Delta = i64; // Self-differentiable!

    #[inline]
    fn zero() -> Self {
        0
    }

    #[inline]
    fn one() -> Self {
        1
    }

    #[inline]
    fn add(&self, other: &Self) -> Self {
        self + other
    }

    #[inline]
    fn mul(&self, other: &Self) -> Self {
        self * other
    }

    #[inline]
    fn zero_delta() -> i64 {
        0
    }

    #[inline]
    fn apply_delta(&self, delta: &i64) -> Self {
        self + delta
    }

    #[inline]
    fn diff(&self, other: &Self) -> i64 {
        other - self
    }

    #[inline]
    fn compose_delta(d1: &i64, d2: &i64) -> i64 {
        d1 + d2
    }

    #[inline]
    fn negate_delta(d: &i64) -> i64 {
        -d
    }
}

// Also implement for i32 (useful for smaller tensors)
impl OrderedSemiring for i32 {
    type Delta = i32;

    #[inline]
    fn zero() -> Self { 0 }
    #[inline]
    fn one() -> Self { 1 }
    #[inline]
    fn add(&self, other: &Self) -> Self { self + other }
    #[inline]
    fn mul(&self, other: &Self) -> Self { self * other }
    #[inline]
    fn zero_delta() -> i32 { 0 }
    #[inline]
    fn apply_delta(&self, delta: &i32) -> Self { self + delta }
    #[inline]
    fn diff(&self, other: &Self) -> i32 { other - self }
    #[inline]
    fn compose_delta(d1: &i32, d2: &i32) -> i32 { d1 + d2 }
    #[inline]
    fn negate_delta(d: &i32) -> i32 { -d }
}

// ============================================================================
// Natural Semiring (ℕ) - for multiplicities / bags
// ============================================================================

impl OrderedSemiring for u64 {
    type Delta = i64; // Changes can be negative!

    #[inline]
    fn zero() -> Self {
        0
    }

    #[inline]
    fn one() -> Self {
        1
    }

    #[inline]
    fn add(&self, other: &Self) -> Self {
        self + other
    }

    #[inline]
    fn mul(&self, other: &Self) -> Self {
        self * other
    }

    #[inline]
    fn zero_delta() -> i64 {
        0
    }

    #[inline]
    fn apply_delta(&self, delta: &i64) -> Self {
        // Saturate at 0 (can't have negative multiplicity)
        if *delta < 0 {
            self.saturating_sub((-delta) as u64)
        } else {
            self.saturating_add(*delta as u64)
        }
    }

    #[inline]
    fn diff(&self, other: &Self) -> i64 {
        (*other as i64) - (*self as i64)
    }

    #[inline]
    fn compose_delta(d1: &i64, d2: &i64) -> i64 {
        d1 + d2
    }

    #[inline]
    fn negate_delta(d: &i64) -> i64 {
        -d
    }
}

// Also u32
impl OrderedSemiring for u32 {
    type Delta = i32;

    #[inline]
    fn zero() -> Self { 0 }
    #[inline]
    fn one() -> Self { 1 }
    #[inline]
    fn add(&self, other: &Self) -> Self { self + other }
    #[inline]
    fn mul(&self, other: &Self) -> Self { self * other }
    #[inline]
    fn zero_delta() -> i32 { 0 }
    #[inline]
    fn apply_delta(&self, delta: &i32) -> Self {
        if *delta < 0 {
            self.saturating_sub((-delta) as u32)
        } else {
            self.saturating_add(*delta as u32)
        }
    }
    #[inline]
    fn diff(&self, other: &Self) -> i32 { (*other as i32) - (*self as i32) }
    #[inline]
    fn compose_delta(d1: &i32, d2: &i32) -> i32 { d1 + d2 }
    #[inline]
    fn negate_delta(d: &i32) -> i32 { -d }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bool_semiring() {
        // Addition is OR
        assert_eq!(false.add(&false), false);
        assert_eq!(false.add(&true), true);
        assert_eq!(true.add(&false), true);
        assert_eq!(true.add(&true), true);

        // Multiplication is AND
        assert_eq!(false.mul(&false), false);
        assert_eq!(false.mul(&true), false);
        assert_eq!(true.mul(&false), false);
        assert_eq!(true.mul(&true), true);

        // Zero and one
        assert!(bool::zero().is_zero());
        assert!(bool::one().is_one());
    }

    #[test]
    fn test_bool_delta() {
        // Insert: false → true
        assert_eq!(false.diff(&true), BoolDelta::INSERT);
        assert_eq!(false.apply_delta(&BoolDelta::INSERT), true);

        // Delete: true → false
        assert_eq!(true.diff(&false), BoolDelta::DELETE);
        assert_eq!(true.apply_delta(&BoolDelta::DELETE), false);

        // No change
        assert_eq!(false.diff(&false), BoolDelta::NONE);
        assert_eq!(true.diff(&true), BoolDelta::NONE);

        // Roundtrip
        for a in [false, true] {
            for b in [false, true] {
                let delta = a.diff(&b);
                assert_eq!(a.apply_delta(&delta), b);
            }
        }
    }

    #[test]
    fn test_i64_semiring() {
        assert_eq!(i64::zero(), 0);
        assert_eq!(i64::one(), 1);
        assert_eq!(3i64.add(&5), 8);
        assert_eq!(3i64.mul(&5), 15);

        // Self-differentiable
        assert_eq!(10i64.diff(&15), 5);
        assert_eq!(10i64.apply_delta(&5), 15);
    }

    #[test]
    fn test_u64_semiring() {
        assert_eq!(u64::zero(), 0);
        assert_eq!(u64::one(), 1);

        // Delta can be negative
        assert_eq!(10u64.diff(&5), -5i64);
        assert_eq!(10u64.apply_delta(&-5i64), 5);

        // Saturates at 0
        assert_eq!(5u64.apply_delta(&-10i64), 0);
    }

    #[test]
    fn test_delta_composition() {
        // Bool: INSERT then DELETE = NONE
        let d1 = BoolDelta::INSERT;
        let d2 = BoolDelta::DELETE;
        assert_eq!(bool::compose_delta(&d1, &d2), BoolDelta::NONE);

        // i64: deltas add
        assert_eq!(i64::compose_delta(&5, &-3), 2);
    }
}
