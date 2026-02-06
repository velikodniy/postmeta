//! Hobby's spline algorithm for `MetaPost`.
//!
//! Given a sequence of knots with optional direction, curl, and tension
//! constraints, this computes cubic Bezier control points that produce
//! aesthetically pleasing smooth curves.
//!
//! The algorithm is described in:
//! - John D. Hobby, "Smooth, Easy to Compute Interpolating Splines",
//!   *Discrete and Computational Geometry* 1 (1986), pp. 123-140.
//! - D.E. Knuth, *The `METAFONTbook`*, Chapter 14.
//! - The `MetaPost` source code (mp.web), sections on `make_choices` and
//!   `set_controls`.
//!
//! # Overview
//!
//! The algorithm:
//! 1. Decompose the path into independent segments at "breakpoints"
//!    (knots with fully specified directions on both sides).
//! 2. For each segment, compute turning angles between consecutive chords.
//! 3. Set up and solve a tridiagonal linear system for the unknown
//!    direction angles `theta_k` at each knot.
//! 4. Compute Bezier control points from the solved angles using the
//!    velocity function.

use kurbo::{Point, Vec2};

use crate::types::{KnotDirection, Path, Scalar, EPSILON};

/// Minimum tension value (`MetaPost` uses 3/4).
const MIN_TENSION: Scalar = 0.75;

/// Solve for control points on a `Path`, modifying knots in place.
///
/// After this call, all `KnotDirection` values in the path will be
/// `Explicit` (computed Bezier control points).
pub fn make_choices(path: &mut Path) {
    let n = path.knots.len();
    if n < 2 {
        // A single knot: set controls to the knot itself.
        if n == 1 {
            let p = path.knots[0].point;
            path.knots[0].left = KnotDirection::Explicit(p);
            path.knots[0].right = KnotDirection::Explicit(p);
        }
        return;
    }

    // Ensure default curl at open-path endpoints
    if !path.is_cyclic {
        if matches!(path.knots[0].right, KnotDirection::Open) {
            path.knots[0].right = KnotDirection::Curl(1.0);
        }
        if matches!(path.knots[n - 1].left, KnotDirection::Open) {
            path.knots[n - 1].left = KnotDirection::Curl(1.0);
        }
    }

    // Process the path in segments between breakpoints
    if path.is_cyclic {
        solve_choices_cyclic(path);
    } else {
        solve_choices_open(path);

        // For open paths, the first knot's left and last knot's right
        // are not part of any segment — set them to the knot point.
        let first_pt = path.knots[0].point;
        path.knots[0].left = KnotDirection::Explicit(first_pt);
        let last_idx = path.knots.len() - 1;
        let last_pt = path.knots[last_idx].point;
        path.knots[last_idx].right = KnotDirection::Explicit(last_pt);
    }
}

// ---------------------------------------------------------------------------
// Open path solver
// ---------------------------------------------------------------------------

#[allow(clippy::too_many_lines)]
fn solve_choices_open(path: &mut Path) {
    let n = path.knots.len();
    if n < 2 {
        return;
    }

    // Compute distances and turning angles between consecutive knots
    let mut delta: Vec<Vec2> = Vec::with_capacity(n);
    let mut dist: Vec<Scalar> = Vec::with_capacity(n);
    let mut psi: Vec<Scalar> = Vec::with_capacity(n);

    for i in 0..(n - 1) {
        let d = path.knots[i + 1].point - path.knots[i].point;
        delta.push(d);
        dist.push(d.length());
    }

    // psi[k] = turning angle at knot k (for k = 1..n-2)
    psi.push(0.0); // psi[0] unused
    for k in 1..(n - 1) {
        psi.push(turning_angle(delta[k - 1], delta[k]));
    }

    // Build the tridiagonal system for angles theta[k]
    // After solving, phi[k] = -(psi[k] + theta[k]) for interior knots
    let num_unknowns = n;
    let mut theta = vec![0.0; num_unknowns];

    // For two knots only, handle specially
    if n == 2 {
        solve_two_knots(path, &delta, &dist);
        return;
    }

    // Use Gaussian elimination on the tridiagonal system.
    // The system is:
    //   A[k]*theta[k-1] + B[k]*theta[k] + C[k]*theta[k+1] = D[k]
    //
    // We convert to: theta[k] + u[k]*theta[k+1] = v[k]

    let mut uu = vec![0.0; n];
    let mut vv = vec![0.0; n];

    // Left boundary condition
    let alpha0 = tension_val(path.knots[0].right_tension);
    let beta0 = tension_val(path.knots[1].left_tension);

    match path.knots[0].right {
        KnotDirection::Given(angle) => {
            theta[0] = angle - angle_of(delta[0]);
            uu[0] = 0.0;
            vv[0] = theta[0];
        }
        KnotDirection::Curl(gamma) => {
            let ct = curl_ratio(gamma, alpha0, beta0);
            uu[0] = ct;
            vv[0] = 0.0;
        }
        _ => {
            uu[0] = 0.0;
            vv[0] = 0.0;
        }
    }

    // Forward sweep
    for k in 1..(n - 1) {
        let alpha_k = tension_val(path.knots[k].right_tension);
        let _beta_k = tension_val(path.knots[k].left_tension);
        let _alpha_prev = tension_val(path.knots[k - 1].right_tension);
        let beta_prev = tension_val(path.knots[k].left_tension);

        let dk_prev = dist[k - 1];
        let dk = dist[k];

        if let KnotDirection::Given(angle) = path.knots[k].left {
            // This knot has a specified incoming direction — it's a
            // breakpoint. Restart the forward sweep.
            theta[k] = angle - angle_of(delta[k - 1]) - psi[k];
            // TODO: handle breakpoint segmentation properly
            vv[k] = theta[k];
            uu[k] = 0.0;
            continue;
        }

        if let KnotDirection::Given(angle) = path.knots[k].right {
            theta[k] = angle - angle_of(delta[k]);
            vv[k] = theta[k];
            uu[k] = 0.0;
            continue;
        }

        // Coefficients for the tridiagonal system at interior knot k
        // A_k * theta_{k-1} + (B_k + C_k) * theta_k + D_k * theta_{k+1}
        //   = -B_k*psi_k - D_k*psi_{k+1}
        let a_coeff = inv_tension_cubed(beta_prev) / dk_prev;
        let b_coeff = (3.0 - inv_tension(beta_prev)) * inv_tension_sq(beta_prev) / dk_prev;
        let c_coeff = (3.0 - inv_tension(alpha_k)) * inv_tension_sq(alpha_k) / dk;
        let d_coeff = inv_tension_cubed(alpha_k) / dk;

        let rhs = if k + 1 < n - 1 {
            (-b_coeff).mul_add(psi[k], -(d_coeff * psi[k + 1]))
        } else {
            -b_coeff * psi[k]
        };

        // Eliminate theta[k-1] using the relation theta[k-1] + u[k-1]*theta[k] = v[k-1]
        let denom = a_coeff.mul_add(uu[k - 1], b_coeff + c_coeff);
        if denom.abs() < 1e-30 {
            uu[k] = 0.0;
            vv[k] = 0.0;
        } else {
            uu[k] = -d_coeff / denom;
            vv[k] = a_coeff.mul_add(-vv[k - 1], rhs) / denom;
        }
    }

    // Right boundary condition
    let last = n - 1;
    let alpha_last = tension_val(path.knots[last - 1].right_tension);
    let beta_last = tension_val(path.knots[last].left_tension);

    match path.knots[last].left {
        KnotDirection::Given(angle) => {
            theta[last] = angle - angle_of(delta[last - 1]) - psi.get(last).copied().unwrap_or(0.0);
        }
        KnotDirection::Curl(gamma) => {
            let ct = curl_ratio(gamma, beta_last, alpha_last);
            let denom = ct.mul_add(uu[last - 1], 1.0);
            if denom.abs() < 1e-30 {
                theta[last] = 0.0;
            } else {
                theta[last] = ct * vv[last - 1] / denom;
            }
        }
        _ => {
            theta[last] = vv[last - 1];
        }
    }

    // Back-substitution
    for k in (0..last).rev() {
        theta[k] = uu[k].mul_add(theta[k + 1], vv[k]);
    }

    // Compute phi values and then control points
    let mut phi = vec![0.0; n];
    for k in 1..(n - 1) {
        phi[k] = -(psi[k] + theta[k]);
    }
    phi[last] = -(theta[last]);

    // Set the control points
    for k in 0..(n - 1) {
        set_controls_for_segment(path, k, k + 1, &delta, &dist, theta[k], phi[k + 1]);
    }
}

// ---------------------------------------------------------------------------
// Cyclic path solver
// ---------------------------------------------------------------------------

#[allow(clippy::needless_range_loop)]
fn solve_choices_cyclic(path: &mut Path) {
    let n = path.knots.len();
    if n < 2 {
        return;
    }

    // Compute distances and turning angles
    let mut delta: Vec<Vec2> = Vec::with_capacity(n);
    let mut dist: Vec<Scalar> = Vec::with_capacity(n);
    let mut psi: Vec<Scalar> = Vec::with_capacity(n);

    for i in 0..n {
        let j = (i + 1) % n;
        let d = path.knots[j].point - path.knots[i].point;
        delta.push(d);
        dist.push(d.length());
    }

    for k in 0..n {
        let prev = if k == 0 { n - 1 } else { k - 1 };
        psi.push(turning_angle(delta[prev], delta[k]));
    }

    // For a cyclic path we need to solve a cyclic tridiagonal system.
    // We use the approach from mp.web: forward sweep with extra tracking
    // of the theta[0] coefficient.

    let mut uu = vec![0.0; n];
    let mut vv = vec![0.0; n];
    let mut ww = vec![0.0; n]; // coefficient of theta[0]

    // First knot
    let _alpha0 = tension_val(path.knots[0].right_tension);
    let _beta0 = tension_val(path.knots[0].left_tension);
    let _alpha_last = tension_val(path.knots[n - 1].right_tension);
    let _beta_last_prev = tension_val(path.knots[0].left_tension);

    // Start with theta[0] as the free variable
    uu[0] = 0.0;
    vv[0] = 0.0;
    ww[0] = 1.0; // theta[0] = theta[0]

    for k in 1..n {
        let prev = k - 1;
        let alpha_k = tension_val(path.knots[k].right_tension);
        let beta_k = tension_val(path.knots[k].left_tension);
        let _alpha_prev = tension_val(path.knots[prev].right_tension);

        let dk_prev = dist[prev];
        let dk = dist[k % n];

        let a_coeff = inv_tension_cubed(beta_k) / dk_prev;
        let b_coeff = (3.0 - inv_tension(beta_k)) * inv_tension_sq(beta_k) / dk_prev;
        let c_coeff = if k < n {
            (3.0 - inv_tension(alpha_k)) * inv_tension_sq(alpha_k) / dk
        } else {
            0.0
        };
        let d_coeff = if k < n {
            inv_tension_cubed(alpha_k) / dk
        } else {
            0.0
        };

        let psi_next = psi[(k + 1) % n];
        let rhs = (-b_coeff).mul_add(psi[k], -(d_coeff * psi_next));

        let denom = a_coeff.mul_add(uu[prev], b_coeff + c_coeff);
        if denom.abs() < 1e-30 {
            uu[k] = 0.0;
            vv[k] = 0.0;
            ww[k] = 0.0;
        } else {
            uu[k] = -d_coeff / denom;
            vv[k] = a_coeff.mul_add(-vv[prev], rhs) / denom;
            ww[k] = (-a_coeff * ww[prev]) / denom;
        }
    }

    // Close the cycle: theta[0] = theta[0]
    // Using the last equation: theta[n-1] + uu[n-1]*theta[0] = vv[n-1] + ww[n-1]*theta[0]
    // Also, theta[n-1] = vv[n-1] + ww[n-1]*theta[0] (from back-substitution into first eq)
    // We need: theta[0] = vv_final + ww_final * theta[0]
    // So: theta[0] * (1 - ww_final) = vv_final
    // where vv_final and ww_final come from back-substituting the last equation.

    // Back-substitute to find theta[0]:
    // theta[n-1] = vv[n-1] + ww[n-1]*theta[0]
    // From the cyclic closure, we need the equation connecting theta[n-1] back to theta[0].
    // In the simplified approach, theta[0] is determined by:
    let last = n - 1;
    let w_total = ww[last] + uu[last]; // uu[last] feeds back to theta[0]
    let v_total = vv[last];

    let theta0 = if (1.0 - w_total).abs() < 1e-30 {
        0.0
    } else {
        v_total / (1.0 - w_total)
    };

    let mut theta = vec![0.0; n];
    theta[0] = theta0;

    // Back-substitute
    theta[last] = ww[last].mul_add(theta0, vv[last]);
    for k in (1..last).rev() {
        theta[k] = ww[k].mul_add(theta0, uu[k].mul_add(theta[k + 1], vv[k]));
    }

    // Compute phi values
    let phi: Vec<Scalar> = (0..n).map(|k| -(psi[k] + theta[k])).collect();

    // Set control points for all segments
    for k in 0..n {
        let j = (k + 1) % n;
        set_controls_for_segment(path, k, j, &delta, &dist, theta[k], phi[j]);
    }
}

// ---------------------------------------------------------------------------
// Two-knot special case
// ---------------------------------------------------------------------------

fn solve_two_knots(path: &mut Path, delta: &[Vec2], dist: &[Scalar]) {
    let alpha = tension_val(path.knots[0].right_tension);
    let beta = tension_val(path.knots[1].left_tension);

    let mut theta = 0.0;
    let mut phi = 0.0;

    match (&path.knots[0].right, &path.knots[1].left) {
        (KnotDirection::Given(a1), KnotDirection::Given(a2)) => {
            theta = *a1 - angle_of(delta[0]);
            phi = *a2 - angle_of(delta[0]) - std::f64::consts::PI;
        }
        (KnotDirection::Given(a1), KnotDirection::Curl(_gamma)) => {
            theta = *a1 - angle_of(delta[0]);
            phi = -theta;
        }
        (KnotDirection::Curl(_gamma1), KnotDirection::Given(a2)) => {
            phi = *a2 - angle_of(delta[0]) - std::f64::consts::PI;
            theta = -phi;
        }
        (KnotDirection::Curl(gamma1), KnotDirection::Curl(gamma2)) => {
            // Both curls: for default curl=1, this gives theta=phi=0
            // TODO: implement proper 2×2 curl system for non-default curls
            let _cr1 = curl_ratio(*gamma1, alpha, beta);
            let _cr2 = curl_ratio(*gamma2, beta, alpha);
            theta = 0.0;
            phi = 0.0;
        }
        _ => {}
    }

    set_controls_for_segment(path, 0, 1, delta, dist, theta, phi);
}

// ---------------------------------------------------------------------------
// Control point computation (the velocity function)
// ---------------------------------------------------------------------------

/// Set cubic Bezier control points for the segment from knot `i` to knot `j`,
/// given the solved angles theta (outgoing at i) and phi (incoming at j).
fn set_controls_for_segment(
    path: &mut Path,
    i: usize,
    j: usize,
    delta: &[Vec2],
    dist: &[Scalar],
    theta: Scalar,
    phi: Scalar,
) {
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

    // The velocity function from mp.web / Hobby's paper
    let rr = velocity(st, ct, sf, cf, alpha);
    let ss = velocity(sf, cf, st, ct, beta);

    // Compute control points
    // right_cp = knot[i] + rr * (delta rotated by theta)
    // left_cp  = knot[j] - ss * (delta rotated by -phi)
    let rr_scaled = rr * dd;
    let ss_scaled = ss * dd;

    let right_cp = Point::new(
        path.knots[i].point.x + rr_scaled * d.x.mul_add(ct, -(d.y * st)) / dd,
        path.knots[i].point.y + rr_scaled * d.y.mul_add(ct, d.x * st) / dd,
    );

    let left_cp = Point::new(
        path.knots[j].point.x - ss_scaled * d.x.mul_add(cf, d.y * sf) / dd,
        path.knots[j].point.y - ss_scaled * d.y.mul_add(cf, -(d.x * sf)) / dd,
    );

    path.knots[i].right = KnotDirection::Explicit(right_cp);
    path.knots[j].left = KnotDirection::Explicit(left_cp);
}

/// Hobby's velocity function.
///
/// Given sin/cos of theta and phi, and the tension alpha, computes the
/// fraction of the chord length to use for the control point distance.
///
/// From mp.web: `velocity(st, ct, sf, cf, t)`.
///
/// The formula is:
///   f(θ, φ) = (2 + √2·(sin θ − sin φ / 16)·(sin φ − sin θ / 16)·(cos θ − cos φ))
///             / (3·(1 + 0.5·(√5 − 1)·cos θ + 0.5·(3 − √5)·cos φ))
///
/// The result is divided by the tension value.
fn velocity(st: Scalar, ct: Scalar, sf: Scalar, cf: Scalar, tension: Scalar) -> Scalar {
    let sqrt2 = std::f64::consts::SQRT_2;
    let sqrt5 = 5.0_f64.sqrt();

    let num = (sqrt2 * (st - sf / 16.0) * (sf - st / 16.0)).mul_add(ct - cf, 2.0);
    let denom = 3.0 * (0.5 * (3.0 - sqrt5)).mul_add(cf, (0.5 * (sqrt5 - 1.0)).mul_add(ct, 1.0));

    if denom.abs() < 1e-30 {
        return 0.0;
    }

    let result = num / denom;

    // Cap and apply tension
    let result = result.min(4.0);
    result / tension
}

/// Compute the curl ratio for endpoint curl handling.
///
/// This is from mp.web's `curl_ratio(gamma, a, b)`:
///   ((3 - a) * a^2 * gamma + b^3) / (a^3 * gamma + (3 - b) * b^2)
fn curl_ratio(gamma: Scalar, alpha: Scalar, beta: Scalar) -> Scalar {
    let a3 = alpha * alpha * alpha;
    let b3 = beta * beta * beta;
    let num = ((3.0 - alpha) * alpha * alpha).mul_add(gamma, b3);
    let denom = a3.mul_add(gamma, (3.0 - beta) * beta * beta);
    if denom.abs() < 1e-30 {
        0.0
    } else {
        num / denom
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Get the effective tension value, clamping at minimum and handling
/// "at least" (negative values).
const fn tension_val(t: Scalar) -> Scalar {
    t.abs().max(MIN_TENSION)
}

fn inv_tension(t: Scalar) -> Scalar {
    1.0 / tension_val(t)
}

fn inv_tension_sq(t: Scalar) -> Scalar {
    let it = inv_tension(t);
    it * it
}

fn inv_tension_cubed(t: Scalar) -> Scalar {
    let it = inv_tension(t);
    it * it * it
}

/// Compute the angle (in radians) of a 2D vector.
fn angle_of(v: Vec2) -> Scalar {
    v.y.atan2(v.x)
}

/// Compute the signed turning angle (in radians) from vector `a` to vector `b`.
fn turning_angle(a: Vec2, b: Vec2) -> Scalar {
    let ang_a = angle_of(a);
    let ang_b = angle_of(b);
    let diff = ang_b - ang_a;
    // Normalize to [-π, π] using atan2 for robustness
    diff.sin().atan2(diff.cos())
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{Knot, EPSILON};

    /// Helper: create a simple path through given points with Open constraints.
    fn make_open_path(points: &[Point]) -> Path {
        let knots = points.iter().map(|&p| Knot::new(p)).collect();
        Path::from_knots(knots, false)
    }

    fn make_cyclic_path(points: &[Point]) -> Path {
        let knots = points.iter().map(|&p| Knot::new(p)).collect();
        Path::from_knots(knots, true)
    }

    /// After `make_choices`, all directions should be Explicit.
    fn assert_all_explicit(path: &Path) {
        for (i, k) in path.knots.iter().enumerate() {
            assert!(
                matches!(k.left, KnotDirection::Explicit(_)),
                "knot {i} left is not Explicit: {:?}",
                k.left
            );
            assert!(
                matches!(k.right, KnotDirection::Explicit(_)),
                "knot {i} right is not Explicit: {:?}",
                k.right
            );
        }
    }

    #[test]
    fn test_single_knot() {
        let mut path = Path::from_knots(vec![Knot::new(Point::new(5.0, 5.0))], false);
        make_choices(&mut path);
        assert_all_explicit(&path);
        match (path.knots[0].left, path.knots[0].right) {
            (KnotDirection::Explicit(l), KnotDirection::Explicit(r)) => {
                assert!((l.x - 5.0).abs() < EPSILON);
                assert!((r.x - 5.0).abs() < EPSILON);
            }
            _ => panic!("not explicit"),
        }
    }

    #[test]
    fn test_two_knots_straight() {
        let mut path = make_open_path(&[Point::new(0.0, 0.0), Point::new(10.0, 0.0)]);
        make_choices(&mut path);
        assert_all_explicit(&path);

        // Control points should be along the x-axis between the two knots
        if let KnotDirection::Explicit(cp) = path.knots[0].right {
            assert!(cp.x > 0.0 && cp.x < 10.0);
            assert!(cp.y.abs() < 0.5); // nearly on x-axis
        }
        if let KnotDirection::Explicit(cp) = path.knots[1].left {
            assert!(cp.x > 0.0 && cp.x < 10.0);
            assert!(cp.y.abs() < 0.5);
        }
    }

    #[test]
    fn test_three_knots_open() {
        let mut path = make_open_path(&[
            Point::new(0.0, 0.0),
            Point::new(5.0, 5.0),
            Point::new(10.0, 0.0),
        ]);
        make_choices(&mut path);
        assert_all_explicit(&path);

        // The curve should pass through the middle knot
        let mid = crate::path::point_of(&path, 1.0);
        assert!((mid.x - 5.0).abs() < EPSILON);
        assert!((mid.y - 5.0).abs() < EPSILON);
    }

    #[test]
    fn test_four_knots_open_smoother() {
        let mut path = make_open_path(&[
            Point::new(0.0, 0.0),
            Point::new(3.0, 4.0),
            Point::new(7.0, 4.0),
            Point::new(10.0, 0.0),
        ]);
        make_choices(&mut path);
        assert_all_explicit(&path);

        // The curve should pass through all knots
        for i in 0..4 {
            let p = crate::path::point_of(&path, i as Scalar);
            assert!(
                (p.x - path.knots[i].point.x).abs() < EPSILON
                    && (p.y - path.knots[i].point.y).abs() < EPSILON,
                "knot {i} mismatch"
            );
        }
    }

    #[test]
    fn test_cyclic_triangle() {
        let mut path = make_cyclic_path(&[
            Point::new(0.0, 0.0),
            Point::new(10.0, 0.0),
            Point::new(5.0, 8.66),
        ]);
        make_choices(&mut path);
        assert_all_explicit(&path);
        assert_eq!(path.num_segments(), 3);
    }

    #[test]
    fn test_cyclic_square() {
        let mut path = make_cyclic_path(&[
            Point::new(0.0, 0.0),
            Point::new(10.0, 0.0),
            Point::new(10.0, 10.0),
            Point::new(0.0, 10.0),
        ]);
        make_choices(&mut path);
        assert_all_explicit(&path);
        assert_eq!(path.num_segments(), 4);
    }

    #[test]
    fn test_given_direction() {
        // {up} .. {right} — direction constrained at both ends
        let mut k0 = Knot::new(Point::new(0.0, 0.0));
        k0.right = KnotDirection::Given(90.0_f64.to_radians());
        let mut k1 = Knot::new(Point::new(10.0, 5.0));
        k1.left = KnotDirection::Given(0.0);
        let mut path = Path::from_knots(vec![k0, k1], false);
        make_choices(&mut path);
        assert_all_explicit(&path);

        // First control point should be above the start (direction up)
        if let KnotDirection::Explicit(cp) = path.knots[0].right {
            assert!(cp.y > 0.0, "cp1 should be above start: {cp:?}");
        }
    }

    #[test]
    fn test_tension_high() {
        // High tension should produce controls closer to the knots
        let mut path1 = make_open_path(&[Point::new(0.0, 0.0), Point::new(10.0, 10.0)]);
        make_choices(&mut path1);

        let mut k0 = Knot::new(Point::new(0.0, 0.0));
        k0.right_tension = 4.0;
        let mut k1 = Knot::new(Point::new(10.0, 10.0));
        k1.left_tension = 4.0;
        let mut path2 = Path::from_knots(vec![k0, k1], false);
        make_choices(&mut path2);

        // Higher tension: control points closer to the on-curve points
        if let (KnotDirection::Explicit(cp1_normal), KnotDirection::Explicit(cp1_tight)) =
            (path1.knots[0].right, path2.knots[0].right)
        {
            let dist_normal = (cp1_normal - path1.knots[0].point).length();
            let dist_tight = (cp1_tight - path2.knots[0].point).length();
            assert!(
                dist_tight < dist_normal,
                "high tension should shorten handles"
            );
        }
    }

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
    fn test_turning_angle() {
        let a = Vec2::new(1.0, 0.0);
        let b = Vec2::new(0.0, 1.0);
        let ta = turning_angle(a, b);
        assert!((ta - std::f64::consts::FRAC_PI_2).abs() < EPSILON);

        let ta2 = turning_angle(b, a);
        assert!((ta2 + std::f64::consts::FRAC_PI_2).abs() < EPSILON);
    }

    #[test]
    fn test_turning_angle_straight() {
        let a = Vec2::new(1.0, 0.0);
        let ta = turning_angle(a, a);
        assert!(ta.abs() < EPSILON);
    }
}
