//! Numeric tolerance constants for `postmeta-graphics`.
//!
//! Single home for every tolerance/convergence constant in the crate, so
//! their values, units, and rationale can be compared side by side.

use super::Scalar;

/// Tolerance for floating-point comparisons: `1/65536` (`2^-16`).
///
/// Unit: dimensionless granule, applied to whatever quantity is being
/// compared (bp coordinates, path times, angle ratios).
///
/// Why this value: `MetaPost` does all arithmetic on scaled integers that
/// are multiples of `2^-16` (mp.web §116, "Fixed-point arithmetic is done
/// on scaled integers"), so `2^-16` is the smallest representable positive
/// quantity — differences below it are indistinguishable in `MetaPost`
/// semantics.
pub const EPSILON: Scalar = 1.0 / 65536.0;

/// Near-zero guard for avoiding division by zero or singularity: `1e-30`.
///
/// Unit: dimensionless.
///
/// Used as a denominator check / vector-length check where we want to
/// detect degenerate transforms, zero-length vectors, etc.  The value is
/// far below any geometrically meaningful magnitude but well above `f64`
/// subnormals, so it flags only genuinely degenerate quantities.  It has
/// no mp.web analogue (fixed-point `MetaPost` cannot produce such values).
pub const NEAR_ZERO: Scalar = 1e-30;

/// Tolerance for arc-length convergence: `0.001`.
///
/// Unit: bp (`PostScript` points) of distance.
///
/// Arc length is estimated by recursive subdivision, stopping when a
/// segment's control-polygon length and chord length agree within this
/// value; `0.001` bp is far below visible output resolution.
pub const ARC_TOL: Scalar = 0.001;

/// Maximum recursion depth for arc-length subdivision: `20`.
///
/// Unit: dimensionless (subdivision levels, i.e. up to `2^20` pieces).
///
/// Caps the recursion when [`ARC_TOL`] is never reached (pathological
/// segments), mirroring the bisection depth used for intersections.
pub const ARC_MAX_DEPTH: u32 = 20;

/// Tolerance for intersection convergence: `1e-6`.
///
/// Unit: path time within one cubic segment (fraction of the segment's
/// `[0, 1]` parameter interval).
///
/// Bisection stops when both sub-curve time intervals are smaller than
/// this.  `MetaPost` bisects a fixed ~17 levels (`2^-17 ≈ 7.6e-6` of a
/// segment); `1e-6` gives slightly finer results with `f64` headroom.
pub const INTERSECT_TOL: Scalar = 1e-6;
