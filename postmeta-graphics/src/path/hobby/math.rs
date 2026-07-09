//! Pure math for Hobby's algorithm: the velocity function, curl ratio, tension handling, and conversion of solved angles to Bezier control points

use crate::path::KnotPath;
use crate::types::{EPSILON, KnotDirection, NEAR_ZERO, Point, Scalar, Vec2};

/// Minimum tension value (`MetaPost` uses 3/4)
const MIN_TENSION: Scalar = 0.75;

// ---------------------------------------------------------------------------
// Control point computation
// ---------------------------------------------------------------------------

/// Convert solved turning angles to Bezier control points for one segment
///
/// Given the departure angle theta at knot `i` and arrival angle phi at knot `j`, the chord vector is rotated by theta (resp. -phi) and scaled by the velocity function to obtain the outgoing (resp. incoming) control point positions.
pub(super) fn set_controls_for_segment(
    path: &mut KnotPath,
    i: usize,
    j: usize,
    delta: &[Vec2],
    dist: &[Scalar],
    theta: Scalar,
    phi: Scalar,
) {
    if matches!(path.knots[i].right, KnotDirection::Explicit(_))
        && matches!(path.knots[j].left, KnotDirection::Explicit(_))
    {
        return;
    }

    let seg = i.min(delta.len() - 1);
    let d = delta[seg];
    let dd = dist[seg];

    if dd < EPSILON {
        // Degenerate segment: coincident knots
        let p = path.knots[i].point;
        path.knots[i].right = KnotDirection::Explicit(p);
        path.knots[j].left = KnotDirection::Explicit(p);
        return;
    }

    let alpha = tension_val(path.knots[i].right_tension);
    let beta = tension_val(path.knots[j].left_tension);

    let st = theta.sin();
    let ct = theta.cos();
    let sf = phi.sin();
    let cf = phi.cos();

    let rr = velocity(st, ct, sf, cf, alpha);
    let ss = velocity(sf, cf, st, ct, beta);

    // Apply "at least" tension clamping (bounding triangle constraint)
    let (rr, ss) = clamp_at_least(
        rr,
        ss,
        st,
        ct,
        sf,
        cf,
        path.knots[i].right_tension,
        path.knots[j].left_tension,
    );

    // right_cp = knot[i] + rr * (delta rotated by theta)
    // left_cp  = knot[j] - ss * (delta rotated by -phi)
    let right_cp = Point::new(
        rr.mul_add(d.x.mul_add(ct, -(d.y * st)), path.knots[i].point.x),
        rr.mul_add(d.y.mul_add(ct, d.x * st), path.knots[i].point.y),
    );

    let left_cp = Point::new(
        ss.mul_add(-d.x.mul_add(cf, d.y * sf), path.knots[j].point.x),
        ss.mul_add(-d.y.mul_add(cf, -(d.x * sf)), path.knots[j].point.y),
    );

    path.knots[i].right = KnotDirection::Explicit(right_cp);
    path.knots[j].left = KnotDirection::Explicit(left_cp);
}

/// Enforce the "at least" tension constraint (bounding triangle)
///
/// When both turning angles bend the same way, the tangent lines at the two knots form a triangle.
/// `MetaPost`'s "at least" tension (a negative tension value) limits the control-point distances so the curve stays inside that triangle.
#[expect(
    clippy::too_many_arguments,
    reason = "mirrors mp.web set_controls which requires all sin/cos and tension values"
)]
fn clamp_at_least(
    rr: Scalar,
    ss: Scalar,
    st: Scalar,
    ct: Scalar,
    sf: Scalar,
    cf: Scalar,
    right_t: Scalar,
    left_t: Scalar,
) -> (Scalar, Scalar) {
    // Only applies if sin(theta) and sin(phi) have the same sign
    if !((st >= 0.0 && sf >= 0.0) || (st <= 0.0 && sf <= 0.0)) {
        return (rr, ss);
    }

    // sine = |sin(theta)| * cos(phi) + |sin(phi)| * cos(theta)
    //      = sin(|theta| + |phi|) when both have the same sign
    let sine = st.abs().mul_add(cf, sf.abs() * ct);
    if sine <= 0.0 {
        return (rr, ss);
    }

    let sine = sine * (1.0 + 1.0 / 65536.0); // safety factor to avoid boundary case

    let mut rr = rr;
    let mut ss = ss;

    // Clamp rr if right tension is "at least" (negative)
    if right_t < 0.0 {
        let bound = sf.abs() / sine;
        if rr > bound {
            rr = bound;
        }
    }

    // Clamp ss if left tension is "at least" (negative)
    if left_t < 0.0 {
        let bound = st.abs() / sine;
        if ss > bound {
            ss = bound;
        }
    }

    (rr, ss)
}

/// Compute control-point distance as a fraction of the chord length
///
/// Implements Hobby's velocity function (Hobby 1986, section 3): given the departure angle theta and arrival angle phi of a spline segment, determines how far the control point sits from its knot relative to the chord.
/// The result is inversely proportional to tension.
fn velocity(st: Scalar, ct: Scalar, sf: Scalar, cf: Scalar, tension: Scalar) -> Scalar {
    let sqrt2 = std::f64::consts::SQRT_2;
    let sqrt5 = 5.0_f64.sqrt();

    let num = (sqrt2 * (st - sf / 16.0) * (sf - st / 16.0)).mul_add(ct - cf, 2.0);
    let denom = 3.0 * (0.5 * (3.0 - sqrt5)).mul_add(cf, (0.5 * (sqrt5 - 1.0)).mul_add(ct, 1.0));

    if denom.abs() < NEAR_ZERO {
        return 0.0;
    }

    let result = num / (denom * tension); // divide by tension first, then cap at 4
    result.min(4.0)
}

/// Convert an endpoint curl value to an angle ratio
///
/// At an open-path endpoint, the curl parameter gamma controls how much the curve bends.
/// Computes the ratio theta/phi (or phi/theta) that satisfies the curl boundary condition for the given pair of tensions (Hobby 1986, section 4).
pub(super) fn curl_ratio(gamma: Scalar, a_tension: Scalar, b_tension: Scalar) -> Scalar {
    let at = tension_val(a_tension);
    let bt = tension_val(b_tension);

    // Fast path for unit tensions: (2*gamma + 1) / (gamma + 2)
    if (at - 1.0).abs() < EPSILON && (bt - 1.0).abs() < EPSILON {
        return 2.0f64.mul_add(gamma, 1.0) / (gamma + 2.0);
    }

    let alpha = 1.0 / at;
    let beta = 1.0 / bt;
    let a3 = alpha * alpha * alpha;
    let b3 = beta * beta * beta;
    let num = ((3.0 - alpha) * alpha * alpha).mul_add(gamma, b3);
    let denom = a3.mul_add(gamma, (3.0 - beta) * beta * beta);
    if denom.abs() < NEAR_ZERO {
        0.0
    } else {
        (num / denom).min(4.0)
    }
}

/// Get the effective tension value, clamping at minimum and handling "at least" (negative values)
pub(super) const fn tension_val(t: Scalar) -> Scalar {
    t.abs().max(MIN_TENSION) // negative means "at least"
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_velocity_symmetry() {
        // velocity(0,1,0,1,1) should be 1/3 (straight line case)
        let v = velocity(0.0, 1.0, 0.0, 1.0, 1.0);
        assert!(
            (v - 1.0 / 3.0).abs() < 0.05,
            "velocity for straight line: {v}"
        );
    }

    #[test]
    fn test_curl_ratio_default() {
        // curl=1, alpha=1, beta=1 should give 1.0
        let cr = curl_ratio(1.0, 1.0, 1.0);
        assert!((cr - 1.0).abs() < EPSILON, "curl_ratio(1,1,1) = {cr}");
    }

    #[test]
    fn test_curl_ratio_with_non_unit_tensions() {
        // curl_ratio(gamma, a_tension, b_tension) with non-unit tensions.
        // With gamma=1, a_tension=2, b_tension=1:
        // alpha = 0.5, beta = 1
        // num = (3-0.5)*0.25*1 + 1 = 2.5*0.25 + 1 = 1.625
        // denom = 0.125*1 + (3-1)*1 = 0.125 + 2 = 2.125
        // result = 1.625/2.125 ≈ 0.7647
        let cr = curl_ratio(1.0, 2.0, 1.0);
        assert!(
            (cr - 1.625 / 2.125).abs() < 0.001,
            "curl_ratio(1,2,1) = {cr}, expected {:.4}",
            1.625 / 2.125
        );

        // With gamma=2, a_tension=1, b_tension=1 (fast path):
        // (2*2+1)/(2+2) = 5/4 = 1.25
        let cr2 = curl_ratio(2.0, 1.0, 1.0);
        assert!(
            (cr2 - 1.25).abs() < EPSILON,
            "curl_ratio(2,1,1) = {cr2}, expected 1.25"
        );
    }

    #[test]
    fn test_velocity_with_tension() {
        // velocity at tension 2 should be half of velocity at tension 1
        // (for same angles), since velocity divides by tension.
        let v1 = velocity(0.0, 1.0, 0.0, 1.0, 1.0);
        let v2 = velocity(0.0, 1.0, 0.0, 1.0, 2.0);
        assert!(
            (v2 - v1 / 2.0).abs() < 0.001,
            "velocity(t=2) = {v2:.4}, expected {:.4}",
            v1 / 2.0
        );
    }

    #[test]
    fn test_clamp_at_least_no_effect_same_sign_large_velocity() {
        // When theta=30° and phi=30° (same sign sines), and velocity is
        // already within bounds, clamp should have no effect.
        let theta = 30.0_f64.to_radians();
        let phi = 30.0_f64.to_radians();
        let st = theta.sin();
        let ct = theta.cos();
        let sf = phi.sin();
        let cf = phi.cos();

        // Small velocities that are within bounds
        let (rr, ss) = clamp_at_least(0.1, 0.1, st, ct, sf, cf, -1.0, -1.0);
        assert!(
            (rr - 0.1).abs() < EPSILON && (ss - 0.1).abs() < EPSILON,
            "small velocities should not be clamped: rr={rr}, ss={ss}"
        );
    }

    #[test]
    fn test_clamp_at_least_reduces_large_velocity() {
        // When velocity is very large, at_least clamping should reduce it.
        let theta = 30.0_f64.to_radians();
        let phi = 30.0_f64.to_radians();
        let st = theta.sin();
        let ct = theta.cos();
        let sf = phi.sin();
        let cf = phi.cos();

        // Large velocities that should be clamped
        let (rr, ss) = clamp_at_least(10.0, 10.0, st, ct, sf, cf, -1.0, -1.0);
        assert!(rr < 10.0, "large rr should be clamped: rr={rr}");
        assert!(ss < 10.0, "large ss should be clamped: ss={ss}");
    }

    #[test]
    fn test_clamp_at_least_opposite_signs_no_effect() {
        // When sin(theta) and sin(phi) have opposite signs,
        // there's no bounding triangle, so no clamping.
        let theta = 30.0_f64.to_radians();
        let phi = -30.0_f64.to_radians();
        let st = theta.sin();
        let ct = theta.cos();
        let sf = phi.sin();
        let cf = phi.cos();

        let (rr, ss) = clamp_at_least(10.0, 10.0, st, ct, sf, cf, -1.0, -1.0);
        assert!(
            (rr - 10.0).abs() < EPSILON && (ss - 10.0).abs() < EPSILON,
            "opposite sign sines should not clamp: rr={rr}, ss={ss}"
        );
    }
}
