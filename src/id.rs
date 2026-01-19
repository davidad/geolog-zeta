//! ID types for geolog, following chit's multi-level ID design
//!
//! The key insight is that different operations benefit from different ID granularities:
//! - UUIDs for global identity (persistence, version control, cross-structure references)
//! - Luids for installation-wide identity (stable across structures, persisted)
//! - Slids for structure-local computation (cache-friendly, compact)
//!
//! We use egglog's `define_id!` macro to create newtype wrappers around usize,
//! giving us type safety (can't mix up Slid with Luid) and nice Debug output.

// Re-export NumericId trait and IdVec for typed indexing
pub use egglog_numeric_id::{define_id, IdVec, NumericId};
pub use nonminmax::NonMaxUsize;
pub use uuid::Uuid;

// We define our own macro that wraps egglog's define_id! and adds rkyv derives
macro_rules! define_id_with_rkyv {
    ($v:vis $name:ident, $repr:ty, $doc:tt) => {
        #[doc = $doc]
        #[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
        #[derive(rkyv::Archive, rkyv::Deserialize, rkyv::Serialize)]
        #[archive(check_bytes)]
        #[repr(transparent)]
        $v struct $name {
            rep: $repr,
        }

        impl NumericId for $name {
            type Rep = $repr;
            type Atomic = std::sync::atomic::AtomicUsize;

            fn new(val: $repr) -> Self {
                Self { rep: val }
            }

            fn from_usize(index: usize) -> Self {
                Self { rep: index as $repr }
            }

            fn index(self) -> usize {
                self.rep as usize
            }

            fn rep(self) -> $repr {
                self.rep
            }
        }

        impl std::fmt::Debug for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{}({})", stringify!($name), self.rep)
            }
        }

        impl std::fmt::Display for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{}", self.rep)
            }
        }
    };
}

define_id_with_rkyv!(
    pub Luid,
    usize,
    "Locally Universal ID: index into the global universe of UUIDs. Stable across installation, persisted."
);

define_id_with_rkyv!(
    pub Slid,
    usize,
    "Structure-Local ID: index within a structure's element universe. Primary working ID."
);

define_id_with_rkyv!(
    pub SortSlid,
    usize,
    "Sort-Local ID: index within a particular sort's carrier. Computed on-demand."
);

/// A Slid that can be stored in Option without doubling size.
/// Uses `NonMaxUsize` so that `Option<NonMaxUsize>` is the same size as `usize`,
/// with `usize::MAX` serving as the niche for `None`.
pub type OptSlid = Option<NonMaxUsize>;

/// Convert a Slid to OptSlid.
/// Returns None if slid == usize::MAX (which would be an astronomically large structure).
#[inline]
pub fn some_slid(slid: Slid) -> OptSlid {
    NonMaxUsize::new(slid.index())
}

/// Extract a Slid from OptSlid.
#[inline]
pub fn get_slid(opt: OptSlid) -> Option<Slid> {
    opt.map(|n| Slid::from_usize(n.get()))
}

/// A Luid that can be stored in Option without doubling size.
/// Analogous to OptSlid but for cross-instance references.
pub type OptLuid = Option<NonMaxUsize>;

/// Convert a Luid to OptLuid.
#[inline]
pub fn some_luid(luid: Luid) -> OptLuid {
    NonMaxUsize::new(luid.index())
}

/// Extract a Luid from OptLuid.
#[inline]
pub fn get_luid(opt: OptLuid) -> Option<Luid> {
    opt.map(|n| Luid::from_usize(n.get()))
}
