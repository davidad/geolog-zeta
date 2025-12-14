//! ID types for geolog, following chit's multi-level ID design
//!
//! The key insight is that different operations benefit from different ID granularities:
//! - UUIDs for global identity (persistence, version control, cross-structure references)
//! - Luids for installation-wide identity (stable across structures, persisted)
//! - Slids for structure-local computation (cache-friendly, compact)

pub use uuid::Uuid;
pub use nonminmax::NonMaxUsize;

/// Locally Universal ID: index into the global universe of UUIDs (0..N-1)
/// This is stable across the entire installation and persists across sessions.
/// See `universe::Universe` for the mapping.
pub type Luid = usize;

/// Structure-Local ID: index within a structure's element universe (0..N-1)
/// This is the primary working ID for most operations within a structure.
pub type Slid = usize;

/// Sort-Local ID: index within a particular sort's carrier
/// Computed on-demand via `carrier.rank(slid)` when needed.
pub type SortSlid = usize;

/// A Slid that can be stored in Option without doubling size.
/// Uses NonMaxUsize so that Option<NonMaxUsize> is the same size as usize,
/// with usize::MAX serving as the niche for None.
pub type OptSlid = Option<NonMaxUsize>;

/// Convert a Slid to OptSlid.
/// Returns None if slid == usize::MAX (which would be an astronomically large structure).
#[inline]
pub fn some_slid(slid: Slid) -> OptSlid {
    NonMaxUsize::new(slid)
}

/// Extract a Slid from OptSlid.
#[inline]
pub fn get_slid(opt: OptSlid) -> Option<Slid> {
    opt.map(|n| n.get())
}
