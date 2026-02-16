//! Hobby's spline algorithm
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
//! 2. For each segment, compute turning angles (radians) between consecutive chords.
//! 3. Set up and solve a tridiagonal linear system for the unknown
//!    direction angles `theta_k` (radians) at each knot.
//! 4. Compute Bezier control points from the solved angles using the
//!    velocity function.

use crate::{
    math,
    path::Path,
    types::{EPSILON, KnotDirection, NEAR_ZERO, Point, Scalar, Vec2},
};

/// Minimum tension value (`MetaPost` uses 3/4).
const MIN_TENSION: Scalar = 0.75;

/// Solve for control points on a `Path`, modifying knots in place.
///
/// After this call, all `KnotDirection` values in the path will be
/// `Explicit` (computed Bezier control points).
pub fn make_choices(path: &mut Path) {
    if path.knots.len() < 2 {
        // A single knot: set controls to the knot itself.
        if let Some(knot) = path.knots.first_mut() {
            knot.left = KnotDirection::Explicit(knot.point);
            knot.right = KnotDirection::Explicit(knot.point);
        }
        return;
    }

    // Process the path in segments between breakpoints
    if path.is_cyclic {
        make_choices_cyclic(path);
    } else {
        make_choices_open(path);
    }
}

fn make_choices_cyclic(path: &mut Path) {
    let n = path.knots.len();

    // Find the first breakpoint on the cycle: a knot where either
    // left or right is not Open.  Following mp.web's make_choices,
    // we iterate around the cycle looking for such a knot.
    let first_bp = (0..n).find(|&k| {
        is_breakpoint_dir(&path.knots[k].left) || is_breakpoint_dir(&path.knots[k].right)
    });

    if let Some(bp) = first_bp {
        // Decompose the cycle into open segments between breakpoints
        // and solve each independently, just like the open-path case.
        solve_cyclic_with_breakpoints(path, bp);
    } else {
        // No breakpoints: pure smooth cycle (all Open directions).
        solve_choices_cyclic(path);
    }
}

fn make_choices_open(path: &mut Path) {
    // Ensure default curl of 1.0 at open-path endpoints
    if let Some(knot) = path.knots.first_mut() {
        if knot.right == KnotDirection::Open {
            knot.right = KnotDirection::Curl(1.0);
        }
    }
    if let Some(knot) = path.knots.last_mut() {
        if knot.left == KnotDirection::Open {
            knot.left = KnotDirection::Curl(1.0);
        }
    }

    solve_choices_open(path);

    // For open paths, the first knot's left and last knot's right
    // are not part of any segment — set them to the knot point.
    if let Some(knot) = path.knots.first_mut() {
        knot.left = KnotDirection::Explicit(knot.point);
    }
    if let Some(knot) = path.knots.last_mut() {
        knot.right = KnotDirection::Explicit(knot.point);
    }
}

// ---------------------------------------------------------------------------
// Cyclic path with breakpoints
// ---------------------------------------------------------------------------

/// Check if a knot direction is a breakpoint (non-Open, i.e., has an explicit
/// constraint that should split the path into independent sub-segments).
const fn is_breakpoint_dir(dir: &KnotDirection) -> bool {
    !matches!(dir, KnotDirection::Open)
}

/// Decompose a cyclic path with breakpoints into independent open segments
/// and solve each one.
///
/// Following `mp.web`'s `make_choices`, this walks around the cycle starting
/// from the first breakpoint, collects all breakpoints, and calls
/// `solve_open_segment` for each pair of consecutive breakpoints.
fn solve_cyclic_with_breakpoints(path: &mut Path, first_bp: usize) {
    let n = path.knots.len();

    // Mirror one-sided direction constraints at breakpoints so segment
    // decomposition can use consistent endpoint boundary conditions.
    mirror_one_sided_direction_constraints(path);

    // Collect all breakpoints starting from `first_bp`, walking around the cycle.
    let mut breaks = vec![first_bp];
    for offset in 1..n {
        let k = (first_bp + offset) % n;
        if is_breakpoint_dir(&path.knots[k].left) || is_breakpoint_dir(&path.knots[k].right) {
            breaks.push(k);
        }
    }

    // Precompute delta and dist for all n cyclic segments.
    let mut delta: Vec<Vec2> = Vec::with_capacity(n);
    let mut dist: Vec<Scalar> = Vec::with_capacity(n);
    for i in 0..n {
        let j = (i + 1) % n;
        let d = path.knots[j].point - path.knots[i].point;
        delta.push(d);
        dist.push(d.length());
    }

    // Solve each pair of consecutive breakpoints as a segment.
    // The last segment wraps from the final breakpoint back to the first.
    for w in breaks.windows(2) {
        let indices = cyclic_index_range(w[0], w[1], n);
        solve_segment(path, &indices, &delta, &dist);
    }
    // Closing segment: last breakpoint → first breakpoint (wrapping around).
    let last_bp = breaks[breaks.len() - 1];
    let indices = cyclic_index_range(last_bp, breaks[0], n);
    solve_segment(path, &indices, &delta, &dist);
}

/// Build the sequence of knot indices from `start` to `end` going forward
/// around a cycle of length `n`.
fn cyclic_index_range(start: usize, end: usize, n: usize) -> Vec<usize> {
    let mut indices = vec![start];
    let mut k = start;
    loop {
        k = (k + 1) % n;
        indices.push(k);
        if k == end {
            break;
        }
    }
    indices
}

/// Solve one segment of a path given an explicit list of knot indices.
///
/// The `indices` slice maps local positions (0..`seg_len`) to global knot
/// indices in the path. This handles both contiguous ranges (open paths)
/// and wrap-around ranges (cyclic path segments).
///
/// Applies Hobby's tridiagonal solver with boundary conditions from the
/// endpoint knots' `right` (at first index) and `left` (at last index).
#[expect(
    clippy::too_many_lines,
    reason = "tridiagonal solver with boundary conditions is a single logical unit"
)]
fn solve_segment(path: &mut Path, indices: &[usize], delta: &[Vec2], dist: &[Scalar]) {
    let seg_len = indices.len();
    if seg_len < 2 {
        return;
    }

    // Infer missing boundary constraints at segment endpoints from the
    // opposite side when possible.
    infer_right_from_left(path, indices[0]);
    infer_left_from_right(path, indices[seg_len - 1]);

    // For two knots, use the two-knot special case.
    if seg_len == 2 {
        solve_two_knots_range(path, indices[0], indices[1], delta, dist);
        return;
    }

    // Compute local turning angles and solve the tridiagonal system.
    // Local indexing (0..seg_len) maps to global indices via `indices`.

    let mut psi = vec![0.0; seg_len]; // psi[0] unused
    for li in 1..(seg_len - 1) {
        psi[li] = delta[indices[li - 1]].angle_to(delta[indices[li]]);
    }

    let mut theta = vec![0.0; seg_len];
    let mut uu = vec![0.0; seg_len];
    let mut vv = vec![0.0; seg_len];

    // Left boundary (first knot)
    let gi = indices[0];
    let rt0 = path.knots[gi].right_tension;
    let lt1 = path.knots[indices[1]].left_tension;

    match path.knots[gi].right {
        KnotDirection::Given(angle) => {
            let th = math::normalize_angle(angle - delta[gi].direction());
            theta[0] = th;
            uu[0] = 0.0;
            vv[0] = th;
        }
        KnotDirection::Curl(gamma) => {
            let cr = curl_ratio(gamma, rt0, lt1);
            uu[0] = cr;
            vv[0] = -cr * psi[1];
        }
        _ => {
            uu[0] = 0.0;
            vv[0] = 0.0;
        }
    }

    // Forward sweep for interior knots (same ratio-based approach as open solver)
    for li in 1..(seg_len - 1) {
        let gk = indices[li];
        let gk_prev = indices[li - 1];
        let gk_next = indices[li + 1];

        let rt_prev = tension_val(path.knots[gk_prev].right_tension);
        let alpha_prev = 1.0 / rt_prev;
        let lt_next = tension_val(path.knots[gk_next].left_tension);
        let beta_next = 1.0 / lt_next;
        let lt_k = tension_val(path.knots[gk].left_tension);
        let rt_k = tension_val(path.knots[gk].right_tension);

        let aa = if (rt_prev - 1.0).abs() < EPSILON {
            0.5
        } else {
            alpha_prev / (3.0 - alpha_prev)
        };
        let dd = (3.0 - alpha_prev) * dist[gk];

        let bb = if (lt_next - 1.0).abs() < EPSILON {
            0.5
        } else {
            beta_next / (3.0 - beta_next)
        };
        let ee = (3.0 - beta_next) * dist[gk_prev];

        let cc = uu[li - 1].mul_add(-aa, 1.0);

        let (dd_adj, ee_adj) = if (lt_k - rt_k).abs() < EPSILON {
            (cc * dd, ee)
        } else if lt_k < rt_k {
            let ratio = lt_k / rt_k;
            (cc * dd * ratio * ratio, ee)
        } else {
            let ratio = rt_k / lt_k;
            (cc * dd, ee * ratio * ratio)
        };

        let denom_ff = ee_adj + dd_adj;
        if denom_ff.abs() < NEAR_ZERO {
            uu[li] = 0.0;
            vv[li] = 0.0;
        } else {
            let ff = ee_adj / denom_ff;
            uu[li] = ff * bb;
            let acc = if li + 1 < seg_len - 1 {
                -psi[li + 1] * uu[li]
            } else {
                0.0
            };
            let bk_frac = if cc.abs() < NEAR_ZERO {
                0.0
            } else {
                (1.0 - ff) / cc
            };
            vv[li] = (vv[li - 1] * bk_frac).mul_add(-aa, psi[li].mul_add(-bk_frac, acc));
        }
    }

    // Right boundary (knot at `end`)
    let last = seg_len - 1;
    let ge = indices[last];
    let ge_prev = indices[last - 1];
    let lt_end = path.knots[ge].left_tension;
    let rt_prev_end = path.knots[ge_prev].right_tension;

    match path.knots[ge].left {
        KnotDirection::Given(angle) => {
            theta[last] = math::normalize_angle(
                angle - delta[ge_prev].direction() - psi.get(last).copied().unwrap_or(0.0),
            );
        }
        KnotDirection::Curl(gamma) => {
            let ff = curl_ratio(gamma, lt_end, rt_prev_end);
            // Curl right boundary: theta[n] = -(ff * vv[n-1]) / (1 - ff * uu[n-1])
            let denom = ff.mul_add(-uu[last - 1], 1.0);
            if denom.abs() < NEAR_ZERO {
                theta[last] = 0.0;
            } else {
                theta[last] = -(ff * vv[last - 1]) / denom;
            }
        }
        _ => {
            theta[last] = vv[last - 1];
        }
    }

    // Back-substitution
    for li in (0..last).rev() {
        theta[li] = uu[li].mul_add(-theta[li + 1], vv[li]);
    }

    // Compute phi values and set control points
    let mut phi = vec![0.0; seg_len];
    for li in 1..(seg_len - 1) {
        phi[li] = -(psi[li] + theta[li]);
    }
    phi[last] = -theta[last];

    for li in 0..(seg_len - 1) {
        let ki = indices[li];
        let kj = indices[li + 1];
        set_controls_for_segment(path, ki, kj, delta, dist, theta[li], phi[li + 1]);
    }
}

// ---------------------------------------------------------------------------
// Open path solver
// ---------------------------------------------------------------------------

fn solve_choices_open(path: &mut Path) {
    let n = path.knots.len();
    if n < 2 {
        return;
    }

    // Mirror one-sided interior direction constraints at breakpoints so
    // segment decomposition can use consistent endpoint boundary conditions.
    mirror_one_sided_direction_constraints(path);

    // Find breakpoint indices: interior knots where left OR right is constrained.
    // A breakpoint splits the path into independent sub-segments.
    // The first and last knots are always segment boundaries.
    let mut breaks = vec![0usize];
    for k in 1..(n - 1) {
        if is_breakpoint_dir(&path.knots[k].left) || is_breakpoint_dir(&path.knots[k].right) {
            breaks.push(k);
        }
    }
    breaks.push(n - 1);
    breaks.dedup();

    // Precompute delta and dist for all segments
    let (delta, dist): (Vec<Vec2>, Vec<Scalar>) = (0..(n - 1))
        .map(|i| {
            let d = path.knots[i + 1].point - path.knots[i].point;
            (d, d.length())
        })
        .unzip();

    // Solve each sub-segment independently
    for w in breaks.windows(2) {
        let indices: Vec<usize> = (w[0]..=w[1]).collect();
        solve_segment(path, &indices, &delta, &dist);
    }
}

fn mirror_one_sided_direction_constraints(path: &mut Path) {
    for knot in &mut path.knots {
        if matches!(knot.left, KnotDirection::Open) {
            match knot.right {
                KnotDirection::Given(angle) => knot.left = KnotDirection::Given(angle),
                KnotDirection::Curl(curl) => knot.left = KnotDirection::Curl(curl),
                _ => {}
            }
        }

        if matches!(knot.right, KnotDirection::Open) {
            match knot.left {
                KnotDirection::Given(angle) => knot.right = KnotDirection::Given(angle),
                KnotDirection::Curl(curl) => knot.right = KnotDirection::Curl(curl),
                _ => {}
            }
        }
    }
}

fn infer_right_from_left(path: &mut Path, idx: usize) {
    if !matches!(path.knots[idx].right, KnotDirection::Open) {
        return;
    }

    if let KnotDirection::Explicit(point) = path.knots[idx].left {
        let d = path.knots[idx].point - point;
        if d.length() < EPSILON {
            path.knots[idx].right = KnotDirection::Curl(1.0);
        } else {
            path.knots[idx].right = KnotDirection::Given(d.direction());
        }
    }
}

fn infer_left_from_right(path: &mut Path, idx: usize) {
    if !matches!(path.knots[idx].left, KnotDirection::Open) {
        return;
    }

    if let KnotDirection::Explicit(point) = path.knots[idx].right {
        let d = point - path.knots[idx].point;
        if d.length() < EPSILON {
            path.knots[idx].left = KnotDirection::Curl(1.0);
        } else {
            path.knots[idx].left = KnotDirection::Given(d.direction());
        }
    }
}

/// Two-knot special case for a sub-segment range.
///
/// Handles the four combinations of boundary conditions at a two-knot segment.
/// Follows mp.web's "Reduce to simple case" sections.
fn solve_two_knots_range(
    path: &mut Path,
    i: usize,
    j: usize,
    full_delta: &[Vec2],
    full_dist: &[Scalar],
) {
    if matches!(path.knots[i].right, KnotDirection::Explicit(_))
        && matches!(path.knots[j].left, KnotDirection::Explicit(_))
    {
        return;
    }

    let seg = i.min(full_delta.len() - 1);
    let d = full_delta[seg];
    let chord_angle = d.direction();

    match (&path.knots[i].right, &path.knots[j].left) {
        (KnotDirection::Given(a1), KnotDirection::Given(a2)) => {
            let theta = math::normalize_angle(*a1 - chord_angle);
            let phi = math::normalize_angle(-(*a2 - chord_angle));
            set_controls_for_segment(path, i, j, full_delta, full_dist, theta, phi);
            return;
        }
        (KnotDirection::Given(a1), KnotDirection::Curl(gamma)) => {
            // Given start, curl end: theta from direction, phi via curl ratio.
            let theta = math::normalize_angle(*a1 - chord_angle);
            let lt_j = path.knots[j].left_tension.abs();
            let rt_i = path.knots[i].right_tension.abs();
            let ff = curl_ratio(*gamma, lt_j, rt_i);
            let phi = ff * theta;
            set_controls_for_segment(path, i, j, full_delta, full_dist, theta, phi);
            return;
        }
        (KnotDirection::Curl(gamma), KnotDirection::Given(a2)) => {
            // Curl start, given end: phi from direction, theta via curl ratio.
            let phi = math::normalize_angle(-(*a2 - chord_angle));
            let rt_i = path.knots[i].right_tension.abs();
            let lt_j = path.knots[j].left_tension.abs();
            let ff = curl_ratio(*gamma, rt_i, lt_j);
            let theta = ff * phi;
            set_controls_for_segment(path, i, j, full_delta, full_dist, theta, phi);
            return;
        }
        (KnotDirection::Curl(_), KnotDirection::Curl(_)) => {
            // Both curls: straight line (theta=phi=0).
            set_controls_for_segment(path, i, j, full_delta, full_dist, 0.0, 0.0);
            return;
        }
        _ => {}
    }

    set_controls_for_segment(path, i, j, full_delta, full_dist, 0.0, 0.0);
}

// ---------------------------------------------------------------------------
// Cyclic path solver
// ---------------------------------------------------------------------------

/// Solve a purely cyclic path (all Open directions, no breakpoints).
///
/// Uses the cyclic tridiagonal solver from mp.web:
/// - Forward sweep with uu[k], vv[k], ww[k] (ww tracks theta[0] coefficient)
/// - Backward iteration closure to solve for theta[0] = theta[n]
/// - Standard back-substitution
///
/// The coefficient computation uses the same ratio-based approach as the
/// open solver (aa=A/B, bb=D/C, etc.), since the cyclic and open cases
/// share the same mock-curvature equation structure.
#[expect(
    clippy::too_many_lines,
    reason = "cyclic tridiagonal solver mirrors mp.web structure"
)]
fn solve_choices_cyclic(path: &mut Path) {
    let n = path.knots.len();
    if n < 2 {
        return;
    }

    // Compute delta vectors and distances for all n cyclic segments
    // Chord vectors and distances for all n cyclic segments.
    let (delta, dist): (Vec<Vec2>, Vec<Scalar>) = (0..n)
        .map(|i| {
            let d = path.knots[(i + 1) % n].point - path.knots[i].point;
            (d, d.length())
        })
        .unzip();

    // Turning angles: psi[k] = angle between chord k-1 and chord k.
    // For cyclic paths, psi[0] uses delta[n-1] and delta[0].
    let psi: Vec<Scalar> = (0..n)
        .map(|k| delta[(k + n - 1) % n].angle_to(delta[k]))
        .collect();

    // Forward sweep: compute uu[k], vv[k], ww[k] for k=1..n.
    // Recurrence: theta[k-1] + uu[k-1]*theta[k] = vv[k-1] + ww[k-1]*theta[0]
    // Arrays have size n+1 (indices 0..n), where index n corresponds to knot 0.
    let mut uu = vec![0.0_f64; n + 1];
    let mut vv = vec![0.0_f64; n + 1];
    let mut ww = vec![0.0_f64; n + 1];

    uu[0] = 0.0;
    vv[0] = 0.0;
    ww[0] = 1.0;

    for k in 1..=n {
        let prev = k - 1;
        // Map array indices to knot indices (cyclic)
        let knot_k = k % n;
        let knot_prev = prev % n;
        let knot_next = (k + 1) % n;

        // aa = A_k/B_k = alpha_{k-1} / (3 - alpha_{k-1})
        //   where alpha_{k-1} = 1/|right_tension(prev knot)|
        let rt_prev = tension_val(path.knots[knot_prev].right_tension);
        let (aa, dd) = if (rt_prev - 1.0).abs() < EPSILON {
            (0.5, 2.0 * dist[knot_k])
        } else {
            let alpha_prev = 1.0 / rt_prev;
            (
                alpha_prev / (3.0 - alpha_prev),
                (3.0 - alpha_prev) * dist[knot_k],
            )
        };

        // bb = D_k/C_k = beta_{k+1} / (3 - beta_{k+1})
        //   where beta_{k+1} = 1/|left_tension(next knot)|
        let lt_next = tension_val(path.knots[knot_next].left_tension);
        let (bb, ee) = if (lt_next - 1.0).abs() < EPSILON {
            (0.5, 2.0 * dist[knot_prev])
        } else {
            let beta_next = 1.0 / lt_next;
            (
                beta_next / (3.0 - beta_next),
                (3.0 - beta_next) * dist[knot_prev],
            )
        };

        // cc = 1 - uu[k-1]*aa
        let cc = uu[prev].mul_add(-aa, 1.0);

        // ff = C_k / (C_k + B_k - u_{k-1}*A_k)
        let dd = dd * cc;
        let lt_k = tension_val(path.knots[knot_k].left_tension);
        let rt_k = tension_val(path.knots[knot_k].right_tension);

        let (dd, ee) = if (lt_k - rt_k).abs() < EPSILON {
            (dd, ee)
        } else if lt_k < rt_k {
            let ratio = lt_k / rt_k;
            (dd * ratio * ratio, ee)
        } else {
            let ratio = rt_k / lt_k;
            (dd, ee * ratio * ratio)
        };

        let denom = ee + dd;
        if denom.abs() < NEAR_ZERO {
            uu[k] = 0.0;
            vv[k] = 0.0;
            ww[k] = 0.0;
            continue;
        }

        let ff = ee / denom;
        uu[k] = ff * bb;

        // Compute vv[k] and ww[k]
        let psi_next = psi[knot_next];
        let acc = -psi_next * uu[k];

        let bk_ratio = if cc.abs() < NEAR_ZERO {
            0.0
        } else {
            (1.0 - ff) / cc
        };
        let acc = psi[knot_k].mul_add(-bk_ratio, acc);
        let ak_ratio = bk_ratio * aa;
        vv[k] = vv[prev].mul_add(-ak_ratio, acc);
        if ww[prev] == 0.0 {
            ww[k] = 0.0;
        } else {
            ww[k] = -ww[prev] * ak_ratio;
        }
    }

    // Cyclic closure: solve for theta[0] = theta[n].
    // Backward iteration processes indices {n-1, n-2, ..., 1, n} in that order.
    let mut aa_val = 0.0_f64;
    let mut bb_val = 1.0_f64;
    // Process k = n-1, n-2, ..., 1
    for k in (1..n).rev() {
        aa_val = aa_val.mul_add(-uu[k], vv[k]);
        bb_val = bb_val.mul_add(-uu[k], ww[k]);
    }
    // Final step: process k = n (wraps to knot 0)
    aa_val = aa_val.mul_add(-uu[n], vv[n]);
    bb_val = bb_val.mul_add(-uu[n], ww[n]);

    // theta[0] = aa / (1 - bb)
    let theta0 = if (1.0 - bb_val).abs() < NEAR_ZERO {
        0.0
    } else {
        aa_val / (1.0 - bb_val)
    };

    // Adjust vv to eliminate ww dependency: vv[k] += theta0 * ww[k]
    vv[0] = theta0;
    for k in 1..n {
        vv[k] += theta0 * ww[k];
    }

    // Back-substitution
    let mut theta = vec![0.0_f64; n + 1];
    theta[n] = theta0;
    for k in (0..n).rev() {
        theta[k] = uu[k].mul_add(-theta[k + 1], vv[k]);
    }

    // Set control points for all segments
    for k in 0..n {
        let next = (k + 1) % n;
        let phi_next = -(psi[next] + theta[next]);
        set_controls_for_segment(path, k, next, &delta, &dist, theta[k], phi_next);
    }
}

// ---------------------------------------------------------------------------
// Control point computation
// ---------------------------------------------------------------------------

/// Set cubic Bezier control points for the segment from knot `i` to knot `j`,
/// given the solved angles theta/phi in radians
/// (theta outgoing at i, phi incoming at j).
fn set_controls_for_segment(
    path: &mut Path,
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

/// Clamp velocities for "at least" tension (bounding triangle constraint).
///
/// When `sin(theta)` and `sin(phi)` have the same sign, the bounding
/// triangle condition limits velocities so that the curve stays inside the
/// triangle formed by the tangent lines.
///
/// Arguments:
/// - `rr`, `ss`: computed velocities
/// - `st`, `ct`, `sf`, `cf`: sin/cos of theta and phi
/// - `right_t`: raw right tension (negative means "at least")
/// - `left_t`: raw left tension (negative means "at least")
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

    // Safety factor: multiply by (1 + 1/65536) to avoid boundary case.
    let sine = sine * (1.0 + 1.0 / 65536.0);

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

    if denom.abs() < NEAR_ZERO {
        return 0.0;
    }

    // Divide by tension first, then cap at 4.
    let result = num / (denom * tension);
    result.min(4.0)
}

/// Compute the curl ratio for endpoint curl handling.
///
/// From mp.web's `curl_ratio(gamma, a_tension, b_tension)`.
/// Arguments are the raw tension values (not reciprocals).
///
/// With `alpha = 1/a_tension` and `beta = 1/b_tension`, the formula is:
///   ((3 - alpha) * alpha^2 * gamma + beta^3) / (alpha^3 * gamma + (3 - beta) * beta^2)
///
/// Result is capped at 4.0.
fn curl_ratio(gamma: Scalar, a_tension: Scalar, b_tension: Scalar) -> Scalar {
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

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Get the effective tension value, clamping at minimum and handling
/// "at least" (negative values).
const fn tension_val(t: Scalar) -> Scalar {
    // Negative means "at least" — take absolute value, clamp to minimum.
    t.abs().max(MIN_TENSION)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{EPSILON, Knot};

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
    fn test_two_knot_explicit_controls_are_preserved() {
        let mut k0 = Knot::new(Point::new(0.0, 0.0));
        let mut k1 = Knot::new(Point::new(2.0, 0.0));

        let cp1 = Point::new(-1.0, 2.0);
        let cp2 = Point::new(3.0, 3.0);
        k0.right = KnotDirection::Explicit(cp1);
        k1.left = KnotDirection::Explicit(cp2);

        let mut path = Path::from_knots(vec![k0, k1], false);
        make_choices(&mut path);

        match path.knots[0].right {
            KnotDirection::Explicit(p) => {
                assert!((p.x - cp1.x).abs() < EPSILON && (p.y - cp1.y).abs() < EPSILON);
            }
            _ => panic!("expected explicit right control on first knot"),
        }

        match path.knots[1].left {
            KnotDirection::Explicit(p) => {
                assert!((p.x - cp2.x).abs() < EPSILON && (p.y - cp2.y).abs() < EPSILON);
            }
            _ => panic!("expected explicit left control on second knot"),
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
        let mid = path.point_at(1.0);
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
            #[expect(clippy::cast_precision_loss, reason = "test index fits in f64")]
            let p = path.point_at(i as Scalar);
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
        let k0 = Knot {
            point: Point::new(0.0, 0.0),
            left: KnotDirection::Open,
            right: KnotDirection::Given(90.0_f64.to_radians()),
            left_tension: 0.0,
            right_tension: 0.0,
        };
        let k1 = Knot {
            point: Point::new(10.0, 5.0),
            left: KnotDirection::Given(0.0),
            right: KnotDirection::Open,
            left_tension: 0.0,
            right_tension: 0.0,
        };
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

        let k0 = Knot {
            point: Point::new(0.0, 0.0),
            left: KnotDirection::Open,
            right: KnotDirection::Open,
            left_tension: 0.0,
            right_tension: 4.0,
        };
        let k1 = Knot {
            point: Point::new(10.0, 10.0),
            left: KnotDirection::Open,
            right: KnotDirection::Open,
            left_tension: 4.0,
            right_tension: 0.0,
        };
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
    fn test_curl_breakpoints_produce_straight_lines() {
        // A--B--C in MetaPost expands to A{curl 1}..{curl 1}B{curl 1}..{curl 1}C
        // This should produce straight line segments.
        let a = Point::new(0.0, 0.0);
        let b = Point::new(28.34645, 0.0); // 1cm
        let c = Point::new(0.0, 28.34645);

        let mut k0 = Knot::new(a);
        k0.right = KnotDirection::Curl(1.0);

        let mut k1 = Knot::new(b);
        k1.left = KnotDirection::Curl(1.0);
        k1.right = KnotDirection::Curl(1.0);

        let mut k2 = Knot::new(c);
        k2.left = KnotDirection::Curl(1.0);

        let mut path = Path::from_knots(vec![k0, k1, k2], false);
        make_choices(&mut path);
        assert_all_explicit(&path);

        // Segment A--B: control points should lie on the line from A to B (y=0)
        if let KnotDirection::Explicit(cp) = path.knots[0].right {
            assert!(cp.y.abs() < 0.01, "A--B right cp should be on y=0: {cp:?}");
            assert!(cp.x > 0.0 && cp.x < 28.35, "A--B right cp.x: {cp:?}");
        }
        if let KnotDirection::Explicit(cp) = path.knots[1].left {
            assert!(cp.y.abs() < 0.01, "A--B left cp should be on y=0: {cp:?}");
        }

        // Segment B--C: control points should lie on the line from B to C
        if let KnotDirection::Explicit(cp) = path.knots[1].right {
            // Line from B(28.35, 0) to C(0, 28.35)
            // On this line, x + y = 28.35 (approximately)
            let sum = cp.x + cp.y;
            assert!(
                (sum - 28.34645).abs() < 0.5,
                "B--C right cp not on line: {cp:?}"
            );
        }
    }

    #[test]
    fn test_cyclic_curl_breakpoints_produce_straight_lines() {
        // A--B--C--cycle in MetaPost: every knot has curl(1) on both sides.
        // The cyclic solver should decompose into straight-line segments.
        let a = Point::new(0.0, 0.0);
        let b = Point::new(28.34645, 0.0); // 1cm
        let c = Point::new(0.0, 28.34645);

        let mut k0 = Knot::new(a);
        k0.left = KnotDirection::Curl(1.0);
        k0.right = KnotDirection::Curl(1.0);

        let mut k1 = Knot::new(b);
        k1.left = KnotDirection::Curl(1.0);
        k1.right = KnotDirection::Curl(1.0);

        let mut k2 = Knot::new(c);
        k2.left = KnotDirection::Curl(1.0);
        k2.right = KnotDirection::Curl(1.0);

        let mut path = Path::from_knots(vec![k0, k1, k2], true);
        make_choices(&mut path);
        assert_all_explicit(&path);

        // Segment A→B: control points should lie on y=0
        if let KnotDirection::Explicit(cp) = path.knots[0].right {
            assert!(cp.y.abs() < 0.01, "A→B right cp should be on y=0: {cp:?}");
        }
        if let KnotDirection::Explicit(cp) = path.knots[1].left {
            assert!(cp.y.abs() < 0.01, "A→B left cp should be on y=0: {cp:?}");
        }

        // Segment B→C: control points on line x+y=28.35
        if let KnotDirection::Explicit(cp) = path.knots[1].right {
            let sum = cp.x + cp.y;
            assert!(
                (sum - 28.34645).abs() < 0.5,
                "B→C right cp not on line: {cp:?}"
            );
        }
        if let KnotDirection::Explicit(cp) = path.knots[2].left {
            let sum = cp.x + cp.y;
            assert!(
                (sum - 28.34645).abs() < 0.5,
                "B→C left cp not on line: {cp:?}"
            );
        }

        // Segment C→A: control points on x=0
        if let KnotDirection::Explicit(cp) = path.knots[2].right {
            assert!(cp.x.abs() < 0.01, "C→A right cp should be on x=0: {cp:?}");
        }
        if let KnotDirection::Explicit(cp) = path.knots[0].left {
            assert!(cp.x.abs() < 0.01, "C→A left cp should be on x=0: {cp:?}");
        }
    }

    // -----------------------------------------------------------------------
    // Non-unit tension tests
    // -----------------------------------------------------------------------

    /// Helper: extract explicit control point.
    fn right_cp(path: &Path, k: usize) -> Point {
        match path.knots[k].right {
            KnotDirection::Explicit(p) => p,
            ref other => panic!("knot {k} right is not Explicit: {other:?}"),
        }
    }

    fn left_cp(path: &Path, k: usize) -> Point {
        match path.knots[k].left {
            KnotDirection::Explicit(p) => p,
            ref other => panic!("knot {k} left is not Explicit: {other:?}"),
        }
    }

    #[test]
    fn test_tension_2_shortens_handles() {
        // Straight line with tension 2 vs tension 1.
        // Higher tension → control points closer to knots.
        let mut k0 = Knot::new(Point::new(0.0, 0.0));
        k0.right_tension = 2.0;
        let mut k1 = Knot::new(Point::new(10.0, 0.0));
        k1.left_tension = 2.0;
        let mut t2 = Path::from_knots(vec![k0, k1], false);
        make_choices(&mut t2);

        let mut t1 = make_open_path(&[Point::new(0.0, 0.0), Point::new(10.0, 0.0)]);
        make_choices(&mut t1);

        let d1 = (right_cp(&t1, 0) - t1.knots[0].point).length();
        let d2 = (right_cp(&t2, 0) - t2.knots[0].point).length();
        assert!(
            d2 < d1 * 0.6,
            "tension 2 handles ({d2:.4}) should be much shorter than tension 1 ({d1:.4})"
        );
    }

    #[test]
    fn test_tension_075_lengthens_handles() {
        // Minimum tension (0.75) should produce longer handles than default (1.0).
        let mut k0 = Knot::new(Point::new(0.0, 0.0));
        k0.right_tension = 0.75;
        let mut k1 = Knot::new(Point::new(10.0, 0.0));
        k1.left_tension = 0.75;
        let mut t075 = Path::from_knots(vec![k0, k1], false);
        make_choices(&mut t075);

        let mut t1 = make_open_path(&[Point::new(0.0, 0.0), Point::new(10.0, 0.0)]);
        make_choices(&mut t1);

        let d1 = (right_cp(&t1, 0) - t1.knots[0].point).length();
        let d075 = (right_cp(&t075, 0) - t075.knots[0].point).length();
        assert!(
            d075 > d1 * 1.2,
            "tension 0.75 handles ({d075:.4}) should be longer than tension 1 ({d1:.4})"
        );
    }

    #[test]
    fn test_asymmetric_tension() {
        // tension 1 and 3: right handle normal length, left handle short.
        let mut k0 = Knot::new(Point::new(0.0, 0.0));
        k0.right_tension = 1.0;
        let mut k1 = Knot::new(Point::new(10.0, 0.0));
        k1.left_tension = 3.0;
        let mut path = Path::from_knots(vec![k0, k1], false);
        make_choices(&mut path);
        assert_all_explicit(&path);

        let d_right = (right_cp(&path, 0) - path.knots[0].point).length();
        let d_left = (left_cp(&path, 1) - path.knots[1].point).length();
        assert!(
            d_left < d_right * 0.5,
            "left tension 3 handle ({d_left:.4}) should be much shorter \
             than right tension 1 handle ({d_right:.4})"
        );
    }

    #[test]
    fn test_three_knots_with_tension_2() {
        // Three-knot open path with all tensions = 2.
        let mut k0 = Knot::new(Point::new(0.0, 0.0));
        k0.right_tension = 2.0;
        let mut k1 = Knot::new(Point::new(5.0, 5.0));
        k1.left_tension = 2.0;
        k1.right_tension = 2.0;
        let mut k2 = Knot::new(Point::new(10.0, 0.0));
        k2.left_tension = 2.0;
        let mut path = Path::from_knots(vec![k0, k1, k2], false);
        make_choices(&mut path);
        assert_all_explicit(&path);

        // The curve should still pass through the middle knot exactly.
        let mid = path.point_at(1.0);
        assert!(
            (mid.x - 5.0).abs() < EPSILON && (mid.y - 5.0).abs() < EPSILON,
            "middle knot not hit: {mid:?}"
        );

        // With higher tension, the curve should be tighter (closer to straight lines
        // between knots). Check that the midpoint of segment 0 is closer to the
        // chord midpoint than with default tension.
        let seg0_mid = path.point_at(0.5);
        let chord_mid = Point::new(2.5, 2.5);
        let dev = (seg0_mid - chord_mid).length();
        assert!(
            dev < 1.0,
            "tension 2 should keep curve close to chord, deviation = {dev:.4}"
        );
    }

    #[test]
    fn test_cyclic_with_tension_2() {
        // Cyclic triangle with all tensions = 2.
        let mut k0 = Knot::new(Point::new(0.0, 0.0));
        k0.left_tension = 2.0;
        k0.right_tension = 2.0;
        let mut k1 = Knot::new(Point::new(10.0, 0.0));
        k1.left_tension = 2.0;
        k1.right_tension = 2.0;
        let mut k2 = Knot::new(Point::new(5.0, 8.66));
        k2.left_tension = 2.0;
        k2.right_tension = 2.0;
        let mut path = Path::from_knots(vec![k0, k1, k2], true);
        make_choices(&mut path);
        assert_all_explicit(&path);

        // All handles should be shorter than with default tension.
        let mut default = make_cyclic_path(&[
            Point::new(0.0, 0.0),
            Point::new(10.0, 0.0),
            Point::new(5.0, 8.66),
        ]);
        make_choices(&mut default);

        for k in 0..3 {
            let d_tight = (right_cp(&path, k) - path.knots[k].point).length();
            let d_normal = (right_cp(&default, k) - default.knots[k].point).length();
            assert!(
                d_tight < d_normal,
                "knot {k}: tension 2 handle ({d_tight:.4}) should be shorter than default ({d_normal:.4})"
            );
        }
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
    fn test_curl_2_at_endpoints() {
        // curl 2 should produce a more "curled" start than curl 1.
        // With curl > 1, theta[0] increases, so the first control point
        // deviates more from the chord direction.
        let mut k0_c2 = Knot::new(Point::new(0.0, 0.0));
        k0_c2.right = KnotDirection::Curl(2.0);
        let mut k1_c2 = Knot::new(Point::new(5.0, 5.0));
        k1_c2.left = KnotDirection::Curl(1.0);
        k1_c2.right = KnotDirection::Curl(1.0);
        let mut k2_c2 = Knot::new(Point::new(10.0, 0.0));
        k2_c2.left = KnotDirection::Curl(1.0);
        let mut path_c2 = Path::from_knots(vec![k0_c2, k1_c2, k2_c2], false);
        make_choices(&mut path_c2);
        assert_all_explicit(&path_c2);

        let mut path_c1 = make_open_path(&[
            Point::new(0.0, 0.0),
            Point::new(5.0, 5.0),
            Point::new(10.0, 0.0),
        ]);
        make_choices(&mut path_c1);

        // The first segment's right control point should differ between curl 2 and curl 1.
        let cp_c2 = right_cp(&path_c2, 0);
        let cp_c1 = right_cp(&path_c1, 0);
        let diff = (cp_c2 - cp_c1).length();
        assert!(
            diff > 0.01,
            "curl 2 should produce different control point than curl 1, diff = {diff:.6}"
        );
    }

    #[test]
    fn test_at_least_tension_stores_negative() {
        // "tension atleast 1" is stored as negative tension.
        // With a straight line (theta=phi=0), at_least should have no effect
        // because the bounding triangle condition is trivially satisfied.
        let mut k0 = Knot::new(Point::new(0.0, 0.0));
        k0.right_tension = -1.0; // atleast 1
        let mut k1 = Knot::new(Point::new(10.0, 0.0));
        k1.left_tension = -1.0; // atleast 1
        let mut path_al = Path::from_knots(vec![k0, k1], false);
        make_choices(&mut path_al);
        assert_all_explicit(&path_al);

        // Should be identical to normal tension 1 for a straight line.
        let mut path_n = make_open_path(&[Point::new(0.0, 0.0), Point::new(10.0, 0.0)]);
        make_choices(&mut path_n);

        let cp_al = right_cp(&path_al, 0);
        let cp_n = right_cp(&path_n, 0);
        assert!(
            (cp_al.x - cp_n.x).abs() < 0.01 && (cp_al.y - cp_n.y).abs() < 0.01,
            "atleast on straight line should match normal: al={cp_al:?} n={cp_n:?}"
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

    #[test]
    fn test_three_knot_asymmetric_tension_open() {
        // Three-knot path with different tensions on each side of the middle knot.
        // This exercises the asymmetric scaling code in the forward sweep.
        let mut k0 = Knot::new(Point::new(0.0, 0.0));
        k0.right_tension = 1.0;
        let mut k1 = Knot::new(Point::new(5.0, 5.0));
        k1.left_tension = 1.0;
        k1.right_tension = 3.0;
        let mut k2 = Knot::new(Point::new(10.0, 0.0));
        k2.left_tension = 3.0;
        let mut path = Path::from_knots(vec![k0, k1, k2], false);
        make_choices(&mut path);
        assert_all_explicit(&path);

        // The second segment's handles should be shorter due to high tension.
        let d_seg1 = (right_cp(&path, 1) - path.knots[1].point).length();
        let d_seg0 = (right_cp(&path, 0) - path.knots[0].point).length();
        assert!(
            d_seg1 < d_seg0,
            "segment 1 (tension 3) handle ({d_seg1:.4}) should be shorter \
             than segment 0 (tension 1) handle ({d_seg0:.4})"
        );
    }

    #[test]
    fn test_cyclic_symmetry_preserved() {
        // A regular polygon path should produce symmetric control points.
        // Regular triangle: the handle lengths at all three knots should be equal.
        let r = 10.0;
        let points: Vec<Point> = (0..3)
            .map(|i| {
                let angle = 2.0 * std::f64::consts::PI * f64::from(i) / 3.0;
                Point::new(r * angle.cos(), r * angle.sin())
            })
            .collect();
        let mut path = make_cyclic_path(&points);
        make_choices(&mut path);
        assert_all_explicit(&path);

        let lengths: Vec<f64> = (0..3)
            .map(|k| (right_cp(&path, k) - path.knots[k].point).length())
            .collect();

        // All three handle lengths should be approximately equal.
        for i in 1..3 {
            assert!(
                (lengths[i] - lengths[0]).abs() < 0.01,
                "cyclic symmetry broken: lengths = {lengths:?}"
            );
        }
    }

    /// Regression: curl boundary denominator must use `(1 - ff*uu)`, not
    /// `(1 + ff*uu)`. The sign error produced asymmetric curves when both
    /// endpoints had curl boundaries.
    ///
    /// `MetaPost` reference output verified with `mpost` version 2.11:
    ///   (0,0)..controls (-19.4835,-0.59496) and (-19.4835,28.9414)
    ///    ..(0,28.34645)..controls (15.4556,27.87448) and (12.89085,0.47195)
    ///    ..(28.34645,0)..controls (47.82996,-0.59496) and (47.82996,28.9414)
    ///    ..(28.34645,28.34645)
    #[test]
    fn test_curl_boundary_sign_regression() {
        let cm = 28.34645;
        let mut k0 = Knot::new(Point::new(0.0, 0.0));
        k0.right = KnotDirection::Curl(1.0);
        let k1 = Knot::new(Point::new(0.0, cm));
        let k2 = Knot::new(Point::new(cm, 0.0));
        let k3 = Knot::new(Point::new(cm, cm));

        let mut path = Path::from_knots(vec![k0, k1, k2, k3], false);
        make_choices(&mut path);
        assert_all_explicit(&path);

        // Verify control points match MetaPost's output (tolerance ~0.01)
        let tol = 0.01;

        let rcp0 = right_cp(&path, 0);
        assert!((rcp0.x - (-19.4835)).abs() < tol, "seg0 rcp.x: {}", rcp0.x);
        assert!((rcp0.y - (-0.59496)).abs() < tol, "seg0 rcp.y: {}", rcp0.y);

        let lcp1 = left_cp(&path, 1);
        assert!((lcp1.x - (-19.4835)).abs() < tol, "seg0 lcp.x: {}", lcp1.x);
        assert!((lcp1.y - 28.9414).abs() < tol, "seg0 lcp.y: {}", lcp1.y);

        let rcp2 = right_cp(&path, 2);
        assert!((rcp2.x - 47.82996).abs() < tol, "seg2 rcp.x: {}", rcp2.x);
        assert!((rcp2.y - (-0.59496)).abs() < tol, "seg2 rcp.y: {}", rcp2.y);

        let lcp3 = left_cp(&path, 3);
        assert!((lcp3.x - 47.82996).abs() < tol, "seg2 lcp.x: {}", lcp3.x);
        assert!((lcp3.y - 28.9414).abs() < tol, "seg2 lcp.y: {}", lcp3.y);

        // Segments 0 and 2 should be symmetric: equal handle lengths
        let d0 = (rcp0 - path.knots[0].point).length();
        let d2 = (rcp2 - path.knots[2].point).length();
        assert!(
            (d0 - d2).abs() < 0.01,
            "symmetric curl path should have equal handle lengths: d0={d0:.4}, d2={d2:.4}"
        );
    }

    /// Helper to assert a control point matches `MetaPost` reference (tolerance 0.01).
    fn assert_cp(label: &str, actual: Point, ex: f64, ey: f64) {
        let tol = 0.01;
        assert!(
            (actual.x - ex).abs() < tol && (actual.y - ey).abs() < tol,
            "{label}: expected ({ex}, {ey}), got ({:.5}, {:.5})",
            actual.x,
            actual.y,
        );
    }

    // -------------------------------------------------------------------
    // MetaPost-validated regression tests (mpost 2.11)
    // -------------------------------------------------------------------

    /// Test 1: Symmetric 4-knot cyclic path (square).
    /// Verified against: (0,0)..(100,0)..(100,100)..(0,100)..cycle
    #[test]
    fn test_mpost_cyclic_square() {
        let mut path = Path::from_knots(
            vec![
                Knot::new(Point::new(0.0, 0.0)),
                Knot::new(Point::new(100.0, 0.0)),
                Knot::new(Point::new(100.0, 100.0)),
                Knot::new(Point::new(0.0, 100.0)),
            ],
            true,
        );
        make_choices(&mut path);
        assert_all_explicit(&path);

        // Segment 0→1: (0,0)..controls (27.61424,-27.61424) and (72.38576,-27.61424)..(100,0)
        assert_cp("s0 rcp", right_cp(&path, 0), 27.61424, -27.61424);
        assert_cp("s0 lcp", left_cp(&path, 1), 72.38576, -27.61424);
        // Segment 1→2: (100,0)..controls (127.61424,27.61424) and (127.61424,72.38576)..(100,100)
        assert_cp("s1 rcp", right_cp(&path, 1), 127.61424, 27.61424);
        assert_cp("s1 lcp", left_cp(&path, 2), 127.61424, 72.38576);
        // Segment 2→3: (100,100)..controls (72.38576,127.61424) and (27.61424,127.61424)..(0,100)
        assert_cp("s2 rcp", right_cp(&path, 2), 72.38576, 127.61424);
        assert_cp("s2 lcp", left_cp(&path, 3), 27.61424, 127.61424);
        // Segment 3→0: (0,100)..controls (-27.61424,72.38576) and (-27.61424,27.61424)..cycle
        assert_cp("s3 rcp", right_cp(&path, 3), -27.61424, 72.38576);
        assert_cp("s3 lcp", left_cp(&path, 0), -27.61424, 27.61424);
    }

    /// Test 2: Asymmetric 5-knot cyclic path (tests cyclic closure order).
    /// Verified against: (0,0)..(50,30)..(100,0)..(80,70)..(20,80)..cycle
    #[test]
    fn test_mpost_cyclic_asymmetric() {
        let mut path = Path::from_knots(
            vec![
                Knot::new(Point::new(0.0, 0.0)),
                Knot::new(Point::new(50.0, 30.0)),
                Knot::new(Point::new(100.0, 0.0)),
                Knot::new(Point::new(80.0, 70.0)),
                Knot::new(Point::new(20.0, 80.0)),
            ],
            true,
        );
        make_choices(&mut path);
        assert_all_explicit(&path);

        // Segment 0→1
        assert_cp("s0 rcp", right_cp(&path, 0), 21.04861, -0.46582);
        assert_cp("s0 lcp", left_cp(&path, 1), 28.84277, 30.84305);
        // Segment 1→2
        assert_cp("s1 rcp", right_cp(&path, 1), 70.55287, 29.18105);
        assert_cp("s1 lcp", left_cp(&path, 2), 78.0607, -4.02469);
        // Segment 2→3
        assert_cp("s2 rcp", right_cp(&path, 2), 126.56914, 4.87402);
        assert_cp("s2 lcp", left_cp(&path, 3), 125.06877, 51.75462);
        // Segment 3→4
        assert_cp("s3 rcp", right_cp(&path, 3), 60.86385, 77.74696);
        assert_cp("s3 lcp", left_cp(&path, 4), 40.43141, 83.09282);
        // Segment 4→0
        assert_cp("s4 rcp", right_cp(&path, 4), -43.09167, 70.44946);
        assert_cp("s4 lcp", left_cp(&path, 0), -35.95712, 0.79576);
    }

    /// Test 3: Two-knot Given+Curl path.
    /// Verified against: (0,0){dir 45}..(100,0)
    #[test]
    fn test_mpost_given_curl() {
        let mut k0 = Knot::new(Point::new(0.0, 0.0));
        k0.right = KnotDirection::Given(45.0_f64.to_radians());
        let mut k1 = Knot::new(Point::new(100.0, 0.0));
        k1.left = KnotDirection::Curl(1.0);

        let mut path = Path::from_knots(vec![k0, k1], false);
        make_choices(&mut path);
        assert_all_explicit(&path);

        // (0,0)..controls (27.61424,27.61424) and (72.38576,27.61424)..(100,0)
        assert_cp("rcp", right_cp(&path, 0), 27.61424, 27.61424);
        assert_cp("lcp", left_cp(&path, 1), 72.38576, 27.61424);
    }

    /// Test 4: Two-knot Curl+Given path.
    /// Verified against: (0,0)..{dir 135}(100,0)
    #[test]
    fn test_mpost_curl_given() {
        let mut k0 = Knot::new(Point::new(0.0, 0.0));
        k0.right = KnotDirection::Curl(1.0);
        let mut k1 = Knot::new(Point::new(100.0, 0.0));
        k1.left = KnotDirection::Given(135.0_f64.to_radians());

        let mut path = Path::from_knots(vec![k0, k1], false);
        make_choices(&mut path);
        assert_all_explicit(&path);

        // (0,0)..controls (-160.94757,-160.94757) and (260.94757,-160.94757)..(100,0)
        assert_cp("rcp", right_cp(&path, 0), -160.94757, -160.94757);
        assert_cp("lcp", left_cp(&path, 1), 260.94757, -160.94757);
    }

    /// Test 5: Two-knot Given+Curl with non-default curl value.
    /// Verified against: (0,0){dir 60}..{curl 2}(100,50)
    #[test]
    fn test_mpost_given_curl2() {
        let mut k0 = Knot::new(Point::new(0.0, 0.0));
        k0.right = KnotDirection::Given(60.0_f64.to_radians());
        let mut k1 = Knot::new(Point::new(100.0, 50.0));
        k1.left = KnotDirection::Curl(2.0);

        let mut path = Path::from_knots(vec![k0, k1], false);
        make_choices(&mut path);
        assert_all_explicit(&path);

        // (0,0)..controls (21.11732,36.57639) and (60.40417,60.77927)..(100,50)
        assert_cp("rcp", right_cp(&path, 0), 21.11732, 36.57639);
        assert_cp("lcp", left_cp(&path, 1), 60.40417, 60.77927);
    }

    /// Test 6: Two-knot Given+Given path.
    /// Verified against: (0,0){dir 30}..{dir 150}(100,0)
    #[test]
    fn test_mpost_given_given() {
        let mut k0 = Knot::new(Point::new(0.0, 0.0));
        k0.right = KnotDirection::Given(30.0_f64.to_radians());
        let mut k1 = Knot::new(Point::new(100.0, 0.0));
        k1.left = KnotDirection::Given(150.0_f64.to_radians());

        let mut path = Path::from_knots(vec![k0, k1], false);
        make_choices(&mut path);
        assert_all_explicit(&path);

        // (0,0)..controls (31.36617,18.1092) and (197.65642,-56.3818)..(100,0)
        assert_cp("rcp", right_cp(&path, 0), 31.36617, 18.1092);
        assert_cp("lcp", left_cp(&path, 1), 197.65642, -56.3818);
    }

    /// Test 7: Two-knot path with tension 0.75.
    /// Verified against: (0,0) .. tension 0.75 .. (100,0)
    #[test]
    fn test_mpost_tension_075() {
        let mut k0 = Knot::new(Point::new(0.0, 0.0));
        k0.right_tension = 0.75;
        let mut k1 = Knot::new(Point::new(100.0, 0.0));
        k1.left_tension = 0.75;

        let mut path = Path::from_knots(vec![k0, k1], false);
        make_choices(&mut path);
        assert_all_explicit(&path);

        // (0,0)..controls (44.44444,0) and (55.55556,0)..(100,0)
        assert_cp("rcp", right_cp(&path, 0), 44.44444, 0.0);
        assert_cp("lcp", left_cp(&path, 1), 55.55556, 0.0);
    }

    /// Test 8: 3-knot path with direction constraints.
    /// Verified against: (0,0){dir 45}..(100,50)..{dir -30}(200,0)
    #[test]
    fn test_mpost_3knot_directions() {
        let mut k0 = Knot::new(Point::new(0.0, 0.0));
        k0.right = KnotDirection::Given(45.0_f64.to_radians());
        let k1 = Knot::new(Point::new(100.0, 50.0));
        let mut k2 = Knot::new(Point::new(200.0, 0.0));
        k2.left = KnotDirection::Given((-30.0_f64).to_radians());

        let mut path = Path::from_knots(vec![k0, k1, k2], false);
        make_choices(&mut path);
        assert_all_explicit(&path);

        // Segment 0→1: controls (27.73624,27.73622) and (61.09705,52.54985)
        assert_cp("s0 rcp", right_cp(&path, 0), 27.73624, 27.73622);
        assert_cp("s0 lcp", left_cp(&path, 1), 61.09705, 52.54985);
        // Segment 1→2: controls (138.09456,47.50314) and (167.19278,18.9412)
        assert_cp("s1 rcp", right_cp(&path, 1), 138.09456, 47.50314);
        assert_cp("s1 lcp", left_cp(&path, 2), 167.19278, 18.9412);
    }

    /// Regression: tlhiv example 38 (`--` then `..`) must match `MetaPost`.
    ///
    /// `MetaPost` reference:
    /// (0,0)..controls (0,9.44882) and (0,18.89763)..(0,28.34645)
    ///      ..controls (-12.591,9.73645) and (9.73645,-12.591)..(28.34645,0)
    ///      ..controls (38.37733,6.78662) and (38.37733,21.55983)..(28.34645,28.34645)
    #[test]
    fn test_mpost_example_38_breakpoint_curl() {
        let cm = 28.34645;

        let mut k0 = Knot::new(Point::new(0.0, 0.0));
        k0.right = KnotDirection::Curl(1.0);

        let mut k1 = Knot::new(Point::new(0.0, cm));
        k1.left = KnotDirection::Curl(1.0);

        let k2 = Knot::new(Point::new(cm, 0.0));
        let k3 = Knot::new(Point::new(cm, cm));

        let mut path = Path::from_knots(vec![k0, k1, k2, k3], false);
        make_choices(&mut path);
        assert_all_explicit(&path);

        assert_cp("s0 rcp", right_cp(&path, 0), 0.0, 9.44882);
        assert_cp("s0 lcp", left_cp(&path, 1), 0.0, 18.89763);
        assert_cp("s1 rcp", right_cp(&path, 1), -12.591, 9.73645);
        assert_cp("s1 lcp", left_cp(&path, 2), 9.73645, -12.591);
        assert_cp("s2 rcp", right_cp(&path, 2), 38.37733, 6.78662);
        assert_cp("s2 lcp", left_cp(&path, 3), 38.37733, 21.55983);
    }

    /// Regression: two-knot open cycle must use consistent 180-degree turn sign.
    ///
    /// `MetaPost` reference for `(0,0)..(1cm,1cm)..cycle`:
    /// (0,0)..controls (18.89763,-18.89763) and (47.24408,9.44882)
    ///  ..(28.34645,28.34645)..controls (9.44882,47.24408) and (-18.89763,18.89763)
    ///  ..cycle
    #[test]
    fn test_mpost_example_42_two_knot_cycle() {
        let cm = 28.34645;
        let mut path = Path::from_knots(
            vec![
                Knot::new(Point::new(0.0, 0.0)),
                Knot::new(Point::new(cm, cm)),
            ],
            true,
        );
        make_choices(&mut path);
        assert_all_explicit(&path);

        assert_cp("s0 rcp", right_cp(&path, 0), 18.89763, -18.89763);
        assert_cp("s0 lcp", left_cp(&path, 1), 47.24408, 9.44882);
        assert_cp("s1 rcp", right_cp(&path, 1), 9.44882, 47.24408);
        assert_cp("s1 lcp", left_cp(&path, 0), -18.89763, 18.89763);
    }

    /// Regression: cyclic two-knot path with right-side directions on both knots.
    ///
    /// `MetaPost` reference for `(0,0){up}..(2cm,0){up}..cycle`:
    /// (0,0)..controls (0,37.79527) and (56.6929,-37.79527)
    ///  ..(56.6929,0)..controls (56.6929,37.79527) and (0,-37.79527)..cycle
    #[test]
    fn test_mpost_example_47_two_knot_cyclic_right_directions() {
        let cm = 28.34645;

        let mut k0 = Knot::new(Point::new(0.0, 0.0));
        k0.right = KnotDirection::Given(90.0_f64.to_radians());

        let mut k1 = Knot::new(Point::new(2.0 * cm, 0.0));
        k1.right = KnotDirection::Given(90.0_f64.to_radians());

        let mut path = Path::from_knots(vec![k0, k1], true);
        make_choices(&mut path);
        assert_all_explicit(&path);

        assert_cp("s0 rcp", right_cp(&path, 0), 0.0, 37.79527);
        assert_cp("s0 lcp", left_cp(&path, 1), 56.6929, -37.79527);
        assert_cp("s1 rcp", right_cp(&path, 1), 56.6929, 37.79527);
        assert_cp("s1 lcp", left_cp(&path, 0), 0.0, -37.79527);
    }

    /// Regression: explicit controls must act as cyclic breakpoints.
    ///
    /// This matches the arrowhead path from plain.mp example 17:
    /// (3.69557,1.53079)..controls (2.46371,1.02052) and (1.23186,0.51027)
    ///  ..(0,0)..controls (1.23186,-0.51027) and (2.46371,-1.02052)
    ///  ..(3.69557,-1.53079)..controls (3.69557,-0.51027) and (3.69557,0.51027)
    ///  ..cycle
    #[test]
    fn test_mpost_example_17_arrowhead_breakpoints() {
        let mut k0 = Knot::new(Point::new(3.69557, 1.53079));
        k0.right = KnotDirection::Explicit(Point::new(2.46371, 1.02052));
        k0.left = KnotDirection::Curl(1.0);

        let mut k1 = Knot::new(Point::new(0.0, 0.0));
        k1.left = KnotDirection::Explicit(Point::new(1.23186, 0.51027));
        k1.right = KnotDirection::Explicit(Point::new(1.23186, -0.51027));

        let mut k2 = Knot::new(Point::new(3.69557, -1.53079));
        k2.left = KnotDirection::Explicit(Point::new(2.46371, -1.02052));
        k2.right = KnotDirection::Curl(1.0);

        let mut path = Path::from_knots(vec![k0, k1, k2], true);
        make_choices(&mut path);
        assert_all_explicit(&path);

        assert_cp("s0 rcp", right_cp(&path, 0), 2.46371, 1.02052);
        assert_cp("s0 lcp", left_cp(&path, 1), 1.23186, 0.51027);
        assert_cp("s1 rcp", right_cp(&path, 1), 1.23186, -0.51027);
        assert_cp("s1 lcp", left_cp(&path, 2), 2.46371, -1.02052);
        assert_cp("s2 rcp", right_cp(&path, 2), 3.69557, -0.51027);
        assert_cp("s2 lcp", left_cp(&path, 0), 3.69557, 0.51027);
    }
}
