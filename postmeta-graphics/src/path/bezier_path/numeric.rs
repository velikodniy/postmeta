//! Private numeric helpers shared by [`BezierPath`](super::BezierPath)
//! query and subpath operations.

use crate::bezier::CubicSegment;
use crate::types::{EPSILON, Scalar, index_to_scalar, scalar_to_index};

/// Decompose a normalized time into `(segment_index, fraction)`.
pub(super) fn time_to_seg_frac(t: Scalar, n: usize) -> (usize, Scalar) {
    let seg = scalar_to_index(t).min(n - 1);
    let frac = t - index_to_scalar(seg);
    (seg, frac)
}

/// Evaluate a degree-2 Bernstein polynomial `B(b0, b1, b2; t)`.
pub(super) fn bernstein_eval(b0: Scalar, b1: Scalar, b2: Scalar, param: Scalar) -> Scalar {
    let s = 1.0 - param;
    s.mul_add(s * b0, (2.0 * s * param).mul_add(b1, param * param * b2))
}

/// Sentinel for unused root slots in [`find_bernstein_roots`].
const NO_ROOT: Scalar = f64::NAN;

/// Find real roots of the degree-2 Bernstein polynomial `B(b0, b1, b2; t) = 0`.
///
/// Returns up to 2 roots (not necessarily in `[0,1]`).  Unused slots are `NAN`.
pub(super) fn find_bernstein_roots(b0: Scalar, b1: Scalar, b2: Scalar) -> [Scalar; 2] {
    // Convert to power basis: B(b0,b1,b2;t) = b0(1-t)^2 + 2*b1*t(1-t) + b2*t^2
    //   = b0 + (2*b1 - 2*b0)*t + (b0 - 2*b1 + b2)*t^2
    let coeff_a = 2.0f64.mul_add(-b1, b0) + b2;
    let coeff_b = 2.0 * (b1 - b0);
    let coeff_c = b0;

    if coeff_a.abs() < EPSILON {
        // Linear: coeff_b * t + coeff_c = 0
        if coeff_b.abs() < EPSILON {
            return [NO_ROOT, NO_ROOT];
        }
        let root = -coeff_c / coeff_b;
        return [root, NO_ROOT];
    }

    let disc = coeff_b.mul_add(coeff_b, -4.0 * coeff_a * coeff_c);
    if disc < 0.0 {
        return [NO_ROOT, NO_ROOT];
    }

    let sqrt_disc = disc.sqrt();
    let t1 = (-coeff_b - sqrt_disc) / (2.0 * coeff_a);
    let t2 = (-coeff_b + sqrt_disc) / (2.0 * coeff_a);
    [t1, t2]
}

/// Bisect to find the parameter `t` in [0,1] such that the arc length
/// from 0 to `t` on `seg` equals `target`.
pub(super) fn bisect_arc_length(seg: &CubicSegment, target: Scalar) -> Scalar {
    const TOL: Scalar = 1e-6;
    const MAX_ITER: u32 = 50;

    let mut lo = 0.0_f64;
    let mut hi = 1.0_f64;

    for _ in 0..MAX_ITER {
        let mid = (lo + hi) * 0.5;
        let len = seg.arc_length_to(mid);

        if (len - target).abs() < TOL {
            return mid;
        }

        if len < target {
            lo = mid;
        } else {
            hi = mid;
        }
    }

    (lo + hi) * 0.5
}
