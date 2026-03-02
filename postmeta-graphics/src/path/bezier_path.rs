//! Resolved cubic Bezier path representation.
//!
//! A [`BezierPath`] stores on-curve knot points and per-segment control point
//! pairs ([`SegmentControls`]).  It is produced by resolving a [`KnotPath`]
//! (running Hobby's algorithm) and provides efficient segment-level access
//! without the direction/tension metadata carried by knots.
//!
//! [`KnotPath`]: super::KnotPath

use crate::bezier::CubicSegment;
use crate::types::{
    EPSILON, Knot, KnotDirection, Point, Scalar, Vec2, index_to_scalar, scalar_to_index,
};

// ---------------------------------------------------------------------------
// SegmentControls
// ---------------------------------------------------------------------------

/// A pair of Bezier control handles for one cubic segment.
///
/// `post` is the handle leaving the start knot (postcontrol), and `pre` is
/// the handle arriving at the end knot (precontrol).
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct SegmentControls {
    /// Handle leaving the start knot (postcontrol).
    pub post: Point,
    /// Handle arriving at the end knot (precontrol).
    pub pre: Point,
}

// ---------------------------------------------------------------------------
// BezierPath
// ---------------------------------------------------------------------------

/// A resolved cubic Bezier path.
///
/// Stores the on-curve knot points and per-segment control point pairs.
/// Created by calling [`KnotPath::resolve()`](super::KnotPath::resolve).
#[derive(Debug, Clone, PartialEq)]
pub struct BezierPath {
    /// On-curve points at each knot.
    points: Vec<Point>,
    /// Per-segment control point pairs.
    controls: Vec<SegmentControls>,
    /// Whether the path is closed.
    is_cyclic: bool,
}

impl BezierPath {
    /// Create an empty open path.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            points: Vec::new(),
            controls: Vec::new(),
            is_cyclic: false,
        }
    }

    /// Construct a `BezierPath` from raw parts.
    ///
    /// # Panics
    ///
    /// Panics (in debug builds) if the number of controls does not match
    /// the expected segment count for the given points and cyclicity.
    #[must_use]
    pub fn from_parts(points: Vec<Point>, controls: Vec<SegmentControls>, is_cyclic: bool) -> Self {
        debug_assert_eq!(
            controls.len(),
            if points.is_empty() {
                0
            } else if is_cyclic {
                points.len()
            } else {
                points.len().saturating_sub(1)
            },
            "controls.len() does not match expected segment count for {} points (cyclic={})",
            points.len(),
            is_cyclic,
        );
        Self {
            points,
            controls,
            is_cyclic,
        }
    }

    /// Number of cubic segments in the path.
    #[must_use]
    pub fn num_segments(&self) -> usize {
        self.controls.len()
    }

    /// Number of on-curve knot points.
    #[must_use]
    pub fn num_knots(&self) -> usize {
        self.points.len()
    }

    /// Whether the path is cyclic (closed).
    #[must_use]
    pub const fn is_cyclic(&self) -> bool {
        self.is_cyclic
    }

    /// Get the on-curve point at knot index `i`.
    ///
    /// # Panics
    ///
    /// Panics if `i >= self.num_knots()`.
    #[must_use]
    pub fn knot_point(&self, i: usize) -> Point {
        self.points[i]
    }

    /// Get all on-curve knot points as a slice.
    #[must_use]
    pub fn knot_points(&self) -> &[Point] {
        &self.points
    }

    /// Get segment `i` as a [`CubicSegment`] (an owned 64-byte copy).
    ///
    /// # Panics
    ///
    /// Panics if `i >= self.num_segments()`.
    #[must_use]
    pub fn segment(&self, i: usize) -> CubicSegment {
        let ctrl = &self.controls[i];
        let j = (i + 1) % self.points.len();
        CubicSegment::new(self.points[i], ctrl.post, ctrl.pre, self.points[j])
    }

    /// Iterate over all segments as [`CubicSegment`] values.
    pub fn segments(&self) -> impl Iterator<Item = CubicSegment> + '_ {
        (0..self.num_segments()).map(move |i| self.segment(i))
    }

    /// Get the segment controls at index `i`.
    ///
    /// # Panics
    ///
    /// Panics if `i >= self.num_segments()`.
    #[must_use]
    pub fn segment_controls(&self, i: usize) -> &SegmentControls {
        &self.controls[i]
    }

    // -----------------------------------------------------------------------
    // Path time helpers (private)
    // -----------------------------------------------------------------------

    /// Normalize a time parameter for this path.
    ///
    /// Cyclic paths wrap around; open paths clamp to `[0, n]`.
    /// Returns `None` if the path has no segments.
    fn normalize_time(&self, t: Scalar) -> Option<Scalar> {
        let n = self.num_segments();
        if n == 0 {
            return None;
        }
        Some(if self.is_cyclic {
            let n_f = index_to_scalar(n);
            let wrapped = ((t % n_f) + n_f) % n_f;
            // Normalize -0.0 to 0.0
            wrapped + 0.0
        } else {
            t.clamp(0.0, index_to_scalar(n))
        })
    }

    // -----------------------------------------------------------------------
    // Path query operations
    // -----------------------------------------------------------------------

    /// Get the point at time `t` on the path.
    ///
    /// `t` ranges from 0 to `num_segments()`. Integer values correspond
    /// to knot points. Fractional values interpolate along the cubic segment.
    #[must_use]
    pub fn point_at(&self, t: Scalar) -> Point {
        if self.points.is_empty() {
            return Point::ZERO;
        }
        let Some(t) = self.normalize_time(t) else {
            return self.points[0];
        };
        let (seg, frac) = time_to_seg_frac(t, self.num_segments());
        self.segment(seg).point_at(frac)
    }

    /// Get the tangent direction at time `t` on the path.
    #[must_use]
    pub fn direction_at(&self, t: Scalar) -> Vec2 {
        if self.points.is_empty() {
            return Vec2::ZERO;
        }
        let Some(t) = self.normalize_time(t) else {
            return Vec2::ZERO;
        };
        let (seg, frac) = time_to_seg_frac(t, self.num_segments());
        self.segment(seg).direction_at(frac)
    }

    /// Find the first time at which the path travels in the given direction.
    ///
    /// Returns `None` if the direction is never matched. If `dir` is `(0,0)`,
    /// returns `Some(0.0)` (undefined direction matches immediately).
    #[must_use]
    pub fn direction_time(&self, dir: Vec2) -> Option<Scalar> {
        // Zero direction matches immediately.
        if dir.x.abs() < EPSILON && dir.y.abs() < EPSILON {
            return Some(0.0);
        }

        let n = self.num_segments();
        if n == 0 {
            return None;
        }

        // Normalize direction for rotation.
        let len = dir.x.hypot(dir.y);
        let (dx, dy) = (dir.x / len, dir.y / len);

        for i in 0..n {
            let seg = self.segment(i);

            // Derivative control points (B'(t)/3 = B(d1,d2,d3;t))
            let d1 = Vec2::new(seg.p1.x - seg.p0.x, seg.p1.y - seg.p0.y);
            let d2 = Vec2::new(seg.p2.x - seg.p1.x, seg.p2.y - seg.p1.y);
            let d3 = Vec2::new(seg.p3.x - seg.p2.x, seg.p3.y - seg.p2.y);

            // Rotate so that (dx,dy) -> (1,0): multiply by conjugate rotation
            let ry1 = d1.y.mul_add(dx, -d1.x * dy);
            let ry2 = d2.y.mul_add(dx, -d2.x * dy);
            let ry3 = d3.y.mul_add(dx, -d3.x * dy);

            let rx1 = d1.x.mul_add(dx, d1.y * dy);
            let rx2 = d2.x.mul_add(dx, d2.y * dy);
            let rx3 = d3.x.mul_add(dx, d3.y * dy);

            // Check t=0: if tangent is zero or matches direction
            if ry1.abs() < EPSILON && rx1 >= -EPSILON {
                return Some(index_to_scalar(i));
            }

            // Find roots of B(ry1, ry2, ry3; t) = 0 in [0,1].
            for t in find_bernstein_roots(ry1, ry2, ry3) {
                if (0.0..=1.0).contains(&t) {
                    let rx = bernstein_eval(rx1, rx2, rx3, t);
                    if rx >= -EPSILON {
                        return Some(index_to_scalar(i) + t);
                    }
                }
            }
        }

        None
    }

    /// Total arc length of the path.
    #[must_use]
    pub fn arc_length(&self) -> Scalar {
        self.segments().map(|s| s.arc_length()).sum()
    }

    /// Find the time parameter at which the cumulative arc length from the
    /// start of the path equals `target`.
    ///
    /// Returns a MetaPost-style time (integer part = segment index, fractional
    /// part = position within that segment). If `target` exceeds the total arc
    /// length, returns `num_segments()`. If `target <= 0`, returns 0.
    #[must_use]
    pub fn arc_time(&self, target: Scalar) -> Scalar {
        let n = self.num_segments();
        if n == 0 || target <= 0.0 {
            return 0.0;
        }

        let mut remaining = target;

        for i in 0..n {
            let seg = self.segment(i);
            let seg_len = seg.arc_length();

            if remaining <= seg_len {
                let local_t = bisect_arc_length(&seg, remaining);
                return index_to_scalar(i) + local_t;
            }

            remaining -= seg_len;
        }

        // Target exceeds total arc length.
        index_to_scalar(n)
    }

    /// Compute the turning number of a cyclic path.
    ///
    /// Returns +1 for counterclockwise simple closed curves, -1 for clockwise,
    /// and 0 for non-cyclic paths or degenerate cases.
    #[must_use]
    pub fn turning_number(&self) -> Scalar {
        if !self.is_cyclic || self.points.len() < 2 {
            return 0.0;
        }

        let n = self.num_segments();
        if n == 0 {
            return 0.0;
        }

        let mut total_angle: Scalar = 0.0;

        // Get initial direction from the first segment.
        let first_seg = self.segment(0);
        let mut prev_dir = first_seg.direction_at(0.0);

        // If the direction is zero (degenerate), try a small offset.
        if prev_dir.x.abs() < EPSILON && prev_dir.y.abs() < EPSILON {
            prev_dir = first_seg.direction_at(1e-6);
        }

        for i in 0..n {
            let seg = self.segment(i);

            for step in 1..=TURNING_STEPS {
                #[allow(clippy::cast_precision_loss)]
                let t = step as Scalar / TURNING_STEPS_F;
                let cur_dir = seg.direction_at(t);

                if cur_dir.x.abs() < EPSILON && cur_dir.y.abs() < EPSILON {
                    continue;
                }

                let cross = prev_dir.x.mul_add(cur_dir.y, -prev_dir.y * cur_dir.x);
                let dot = prev_dir.x.mul_add(cur_dir.x, prev_dir.y * cur_dir.y);
                total_angle += cross.atan2(dot);

                prev_dir = cur_dir;
            }
        }

        (total_angle / (2.0 * std::f64::consts::PI)).round()
    }

    /// Get the precontrol (incoming control) point at time `t`.
    ///
    /// For integer times, returns the precontrol of that knot.
    /// For fractional times, splits the segment and returns the inserted precontrol.
    #[must_use]
    pub fn precontrol_at(&self, t: Scalar) -> Point {
        if self.points.is_empty() {
            return Point::ZERO;
        }
        let Some(t) = self.normalize_time(t) else {
            return self.points[0];
        };
        let n = self.num_segments();
        let (seg, frac) = time_to_seg_frac(t, n);

        if frac.abs() < EPSILON {
            // At a knot point — return the precontrol of that knot.
            if !self.is_cyclic && seg == 0 {
                return self.points[0];
            }
            // The precontrol of knot `seg` is the `pre` of the preceding segment.
            let prev_seg = if seg == 0 { n - 1 } else { seg - 1 };
            self.controls[prev_seg].pre
        } else {
            let cubic = self.segment(seg % n);
            let (left_part, _) = cubic.split(frac);
            left_part.p2
        }
    }

    /// Get the postcontrol (outgoing control) point at time `t`.
    ///
    /// For integer times, returns the postcontrol of that knot.
    /// For fractional times, splits the segment and returns the inserted postcontrol.
    #[must_use]
    pub fn postcontrol_at(&self, t: Scalar) -> Point {
        if self.points.is_empty() {
            return Point::ZERO;
        }
        let Some(t) = self.normalize_time(t) else {
            return self.points[0];
        };
        let n = self.num_segments();
        let (seg, frac) = time_to_seg_frac(t, n);

        if frac.abs() < EPSILON {
            // At a knot point — return the postcontrol of that knot.
            let knot_idx = seg % self.points.len();
            if !self.is_cyclic && knot_idx == self.points.len() - 1 {
                return self.points[knot_idx];
            }
            self.controls[knot_idx].post
        } else {
            let cubic = self.segment(seg % n);
            let (_, right_part) = cubic.split(frac);
            right_part.p1
        }
    }

    /// Extract a subpath from time `t1` to time `t2`.
    ///
    /// For cyclic paths, the subpath wraps around naturally: `subpath(3.5, 1.5)`
    /// on a 4-segment cycle yields the path going 3.5 -> 0/4 -> 1.5 (the long
    /// way around). This matches `MetaPost`'s `chop_path` semantics.
    ///
    /// Returns a new (always open) `BezierPath`.
    #[must_use]
    pub fn subpath(&self, t1: Scalar, t2: Scalar) -> Self {
        if self.points.is_empty() {
            return Self::new();
        }

        let n = self.num_segments();
        if n == 0 {
            return Self::from_parts(vec![self.points[0]], vec![], false);
        }

        // Handle reversed direction: swap, compute, reverse result.
        let (a, b, reversed) = if t1 <= t2 {
            (t1, t2, false)
        } else {
            (t2, t1, true)
        };

        let n_f = index_to_scalar(n);

        // Normalize following MetaPost's chop_path.
        let (a, b) = if self.is_cyclic {
            let shift = a.div_euclid(n_f) * n_f;
            (a - shift, b - shift)
        } else {
            (a.clamp(0.0, n_f), b.clamp(0.0, n_f))
        };

        let result = self.subpath_normalized(a, b, n);
        if reversed { result.reverse() } else { result }
    }

    /// Core subpath extraction with `0 <= a` and `a <= b`.
    ///
    /// For cyclic paths `b` may exceed `n` (indicating wrap-around).
    fn subpath_normalized(&self, start: Scalar, end: Scalar, num_segs: usize) -> Self {
        let (seg1, frac1) = time_to_seg_frac(start, num_segs);
        // For end we decompose manually since it can exceed num_segs for cyclic paths.
        let seg2_raw = scalar_to_index(end).min(if self.is_cyclic {
            usize::MAX
        } else {
            num_segs - 1
        });
        let frac2 = end - index_to_scalar(seg2_raw);

        if seg1 == seg2_raw && frac2 > frac1 {
            // Both endpoints in the same segment
            return self.subpath_single_segment(seg1, frac1, frac2);
        }

        let mut points = Vec::new();
        let mut controls = Vec::new();

        // Start knot from splitting first segment
        let seg1_wrapped = seg1 % num_segs;
        let cubic_first = self.segment(seg1_wrapped);
        let (_, right_part) = cubic_first.split(frac1);
        let start_pt = cubic_first.point_at(frac1);
        points.push(start_pt);

        // End of first partial segment
        let next_knot_idx = (seg1 + 1) % self.points.len();
        controls.push(SegmentControls {
            post: right_part.p1,
            pre: right_part.p2,
        });
        points.push(self.points[next_knot_idx]);

        // Full intermediate segments (wrapping via modulo for cyclic paths)
        for seg in (seg1 + 1)..seg2_raw {
            let seg_idx = seg % num_segs;
            let next_idx = (seg + 1) % self.points.len();
            controls.push(self.controls[seg_idx]);
            points.push(self.points[next_idx]);
        }

        // Split last segment
        if frac2.abs() > EPSILON {
            let seg2_wrapped = seg2_raw % num_segs;
            let cubic_last = self.segment(seg2_wrapped);
            let (left_part, _) = cubic_last.split(frac2);
            let end_pt = cubic_last.point_at(frac2);

            // Update the last control's `post` for the outgoing handle of the
            // last full knot, and add the final partial segment's controls.
            if let Some(last_ctrl) = controls.last_mut() {
                // The preceding segment's `pre` is already correct — it was
                // either from the first split or copied wholesale. Now set
                // up the new segment from the last full knot to the split point.
                let _ = last_ctrl; // just to silence unused warning if needed
            }

            controls.push(SegmentControls {
                post: left_part.p1,
                pre: left_part.p2,
            });
            points.push(end_pt);
        }

        Self::from_parts(points, controls, false)
    }

    /// Extract a subpath where both endpoints lie in the same segment.
    fn subpath_single_segment(&self, seg: usize, frac1: Scalar, frac2: Scalar) -> Self {
        let cubic = self.segment(seg);
        let (_, right) = cubic.split(frac1);
        let t_inner = if (1.0 - frac1).abs() < EPSILON {
            0.0
        } else {
            (frac2 - frac1) / (1.0 - frac1)
        };
        let (sub, _) = right.split(t_inner);
        let p0 = cubic.point_at(frac1);
        let p1 = cubic.point_at(frac2);
        Self::from_parts(
            vec![p0, p1],
            vec![SegmentControls {
                post: sub.p1,
                pre: sub.p2,
            }],
            false,
        )
    }

    /// Reverse the path.
    ///
    /// For cyclic paths, MetaPost-style reversal keeps the same start knot:
    /// Original order `0,1,2,...,n-1` becomes `0,n-1,n-2,...,1`.
    #[must_use]
    pub fn reverse(&self) -> Self {
        if self.points.is_empty() {
            return Self::new();
        }

        if self.is_cyclic {
            // MetaPost-style reverse for cycles keeps the same start knot.
            // Original: 0 -> 1 -> 2 -> ... -> n-1 -> 0
            // Reversed: 0 -> n-1 -> n-2 -> ... -> 1 -> 0
            let n = self.points.len();
            let mut points = Vec::with_capacity(n);
            let mut controls = Vec::with_capacity(n);

            points.push(self.points[0]);
            for i in (1..n).rev() {
                points.push(self.points[i]);
            }

            // The original segment i connects point[i] -> point[(i+1)%n]
            // with controls[i] = { post, pre }.
            // In the reversed path, the segment from point[0] to point[n-1]
            // (which was the original segment n-1 -> 0) needs its controls
            // swapped.
            //
            // Reversed segment j goes from reversed_points[j] to
            // reversed_points[(j+1)%n].
            // reversed_points[0] = original[0]
            // reversed_points[1] = original[n-1]
            // reversed_points[2] = original[n-2]
            // ...
            // reversed_points[k] = original[(n-k) % n] for k >= 1, and
            //                       original[0] for k == 0.
            //
            // Reversed segment 0: original[0] -> original[n-1]
            //   This is the reverse of original segment (n-1): original[n-1] -> original[0]
            //   Original controls[n-1] = { post, pre }
            //   Reversed: { post: pre, pre: post } (swap)
            //
            // Reversed segment j (1 <= j < n): original[(n-j) % n] -> original[(n-j-1) % n]
            //   This is the reverse of original segment (n-j-1): original[n-j-1] -> original[n-j]
            //   Original controls[n-j-1] = { post, pre }
            //   Reversed: { post: pre, pre: post }

            // Segment 0: reverse of original segment (n-1)
            let orig_seg = n - 1;
            controls.push(SegmentControls {
                post: self.controls[orig_seg].pre,
                pre: self.controls[orig_seg].post,
            });

            // Segments 1..n-1: segment j reverses original segment (n-j-1)
            for j in 1..n {
                let orig_seg = n - j - 1;
                controls.push(SegmentControls {
                    post: self.controls[orig_seg].pre,
                    pre: self.controls[orig_seg].post,
                });
            }

            return Self::from_parts(points, controls, true);
        }

        // Open path: simply reverse everything, swapping post/pre.
        let points: Vec<Point> = self.points.iter().rev().copied().collect();
        let controls: Vec<SegmentControls> = self
            .controls
            .iter()
            .rev()
            .map(|c| SegmentControls {
                post: c.pre,
                pre: c.post,
            })
            .collect();

        Self::from_parts(points, controls, false)
    }

    // -----------------------------------------------------------------------
    // Intersection queries
    // -----------------------------------------------------------------------

    /// Find the first intersection between this path and `other`.
    ///
    /// Returns `None` if the paths don't intersect.
    /// The returned times are in the range [0, `num_segments()`].
    #[must_use]
    pub fn intersection_times(&self, other: &Self) -> Option<crate::intersection::Intersection> {
        crate::intersection::bezier_intersection_times(self, other)
    }

    /// Find all intersections between this path and `other`.
    #[must_use]
    pub fn all_intersection_times(&self, other: &Self) -> Vec<crate::intersection::Intersection> {
        crate::intersection::all_bezier_intersection_times(self, other)
    }

    // -----------------------------------------------------------------------
    // Conversion
    // -----------------------------------------------------------------------

    /// Convert this resolved path back to a [`KnotPath`](super::KnotPath)
    /// with explicit control points.
    ///
    /// This is useful for operations (like path concatenation) that still
    /// operate on `KnotPath`.
    #[must_use]
    pub fn to_knot_path(&self) -> super::KnotPath {
        let n = self.num_segments();
        let mut knots = Vec::with_capacity(self.points.len());

        for (i, &point) in self.points.iter().enumerate() {
            let left = if i > 0 || self.is_cyclic {
                let seg_idx = if i == 0 { n - 1 } else { i - 1 };
                KnotDirection::Explicit(self.controls[seg_idx].pre)
            } else {
                KnotDirection::Open
            };

            let right = if i < n {
                KnotDirection::Explicit(self.controls[i].post)
            } else {
                KnotDirection::Open
            };

            knots.push(Knot {
                point,
                left,
                right,
                left_tension: 1.0,
                right_tension: 1.0,
            });
        }

        super::KnotPath::from_knots(knots, self.is_cyclic)
    }
}

impl Default for BezierPath {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Private helper functions
// ---------------------------------------------------------------------------

/// Number of subdivision steps per cubic segment for turning number.
const TURNING_STEPS: usize = 64;
const TURNING_STEPS_F: Scalar = 64.0;

/// Decompose a normalized time into `(segment_index, fraction)`.
fn time_to_seg_frac(t: Scalar, n: usize) -> (usize, Scalar) {
    let seg = scalar_to_index(t).min(n - 1);
    let frac = t - index_to_scalar(seg);
    (seg, frac)
}

/// Evaluate a degree-2 Bernstein polynomial `B(b0, b1, b2; t)`.
fn bernstein_eval(b0: Scalar, b1: Scalar, b2: Scalar, param: Scalar) -> Scalar {
    let s = 1.0 - param;
    s.mul_add(s * b0, (2.0 * s * param).mul_add(b1, param * param * b2))
}

/// Sentinel for unused root slots in [`find_bernstein_roots`].
const NO_ROOT: Scalar = f64::NAN;

/// Find real roots of the degree-2 Bernstein polynomial `B(b0, b1, b2; t) = 0`.
///
/// Returns up to 2 roots (not necessarily in `[0,1]`).  Unused slots are `NAN`.
fn find_bernstein_roots(b0: Scalar, b1: Scalar, b2: Scalar) -> [Scalar; 2] {
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
fn bisect_arc_length(seg: &CubicSegment, target: Scalar) -> Scalar {
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

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{EPSILON, Knot, KnotDirection, Point};

    /// Helper: build a `BezierPath` for a straight line from (0,0) to (10,0).
    fn make_line_bezier() -> BezierPath {
        let points = vec![Point::new(0.0, 0.0), Point::new(10.0, 0.0)];
        let controls = vec![SegmentControls {
            post: Point::new(10.0 / 3.0, 0.0),
            pre: Point::new(20.0 / 3.0, 0.0),
        }];
        BezierPath::from_parts(points, controls, false)
    }

    /// Helper: build a cyclic triangle `BezierPath` with straight-line controls.
    fn make_triangle_bezier() -> BezierPath {
        let pts = [
            Point::new(0.0, 0.0),
            Point::new(10.0, 0.0),
            Point::new(5.0, 10.0),
        ];
        let controls = (0..3)
            .map(|i| {
                let j = (i + 1) % 3;
                SegmentControls {
                    post: pts[i].lerp(pts[j], 1.0 / 3.0),
                    pre: pts[i].lerp(pts[j], 2.0 / 3.0),
                }
            })
            .collect();
        BezierPath::from_parts(pts.to_vec(), controls, true)
    }

    // -- Test 1: BezierPath::new() is empty ----------------------------------

    #[test]
    fn new_is_empty() {
        let bp = BezierPath::new();
        assert_eq!(bp.num_segments(), 0);
        assert_eq!(bp.num_knots(), 0);
        assert!(!bp.is_cyclic());
        assert!(bp.knot_points().is_empty());
    }

    // -- Test 2: BezierPath::from_parts() with a simple line segment ----------

    #[test]
    fn from_parts_line_segment() {
        let bp = make_line_bezier();
        assert_eq!(bp.num_knots(), 2);
        assert_eq!(bp.num_segments(), 1);
        assert!(!bp.is_cyclic());
        assert!((bp.knot_point(0).x - 0.0).abs() < EPSILON);
        assert!((bp.knot_point(1).x - 10.0).abs() < EPSILON);
    }

    // -- Test 3: segment() returns correct CubicSegment ----------------------

    #[test]
    fn segment_returns_correct_cubic() {
        let bp = make_line_bezier();
        let seg = bp.segment(0);
        assert!((seg.p0.x - 0.0).abs() < EPSILON);
        assert!((seg.p1.x - 10.0 / 3.0).abs() < EPSILON);
        assert!((seg.p2.x - 20.0 / 3.0).abs() < EPSILON);
        assert!((seg.p3.x - 10.0).abs() < EPSILON);

        // Midpoint of a straight-line cubic should be at x=5
        let mid = seg.point_at(0.5);
        assert!((mid.x - 5.0).abs() < EPSILON);
        assert!((mid.y - 0.0).abs() < EPSILON);
    }

    // -- Test 4: segments() iterator -----------------------------------------

    #[test]
    fn segments_iterator() {
        let bp = make_triangle_bezier();
        let segs: Vec<_> = bp.segments().collect();
        assert_eq!(segs.len(), 3);

        // Each segment's p0 should match the corresponding knot point
        for (i, seg) in segs.iter().enumerate() {
            assert!(
                (seg.p0.x - bp.knot_point(i).x).abs() < EPSILON
                    && (seg.p0.y - bp.knot_point(i).y).abs() < EPSILON,
                "segment {i} p0 mismatch"
            );
        }
    }

    // -- Test 5: KnotPath::resolve() — 2-knot line, 1 segment ---------------

    #[test]
    fn resolve_two_knot_line() {
        let kp = super::super::KnotPath::from_knots(
            vec![
                Knot::new(Point::new(0.0, 0.0)),
                Knot::new(Point::new(10.0, 0.0)),
            ],
            false,
        );
        let bp = kp.resolve();
        assert_eq!(bp.num_segments(), 1);
        assert_eq!(bp.num_knots(), 2);
        assert!(!bp.is_cyclic());

        // Endpoints should match
        assert!((bp.knot_point(0).x - 0.0).abs() < EPSILON);
        assert!((bp.knot_point(1).x - 10.0).abs() < EPSILON);

        // Midpoint should be near (5, 0)
        let seg = bp.segment(0);
        let mid = seg.point_at(0.5);
        assert!((mid.x - 5.0).abs() < 0.5);
        assert!(mid.y.abs() < 0.5);
    }

    // -- Test 6: KnotPath::resolve() — cyclic triangle, 3 segments -----------

    #[test]
    fn resolve_cyclic_triangle() {
        let kp = super::super::KnotPath::from_knots(
            vec![
                Knot::new(Point::new(0.0, 0.0)),
                Knot::new(Point::new(10.0, 0.0)),
                Knot::new(Point::new(5.0, 10.0)),
            ],
            true,
        );
        let bp = kp.resolve();
        assert_eq!(bp.num_segments(), 3);
        assert_eq!(bp.num_knots(), 3);
        assert!(bp.is_cyclic());

        // Verify knot points match
        assert!((bp.knot_point(0).x - 0.0).abs() < EPSILON);
        assert!((bp.knot_point(0).y - 0.0).abs() < EPSILON);
        assert!((bp.knot_point(1).x - 10.0).abs() < EPSILON);
        assert!((bp.knot_point(2).x - 5.0).abs() < EPSILON);
        assert!((bp.knot_point(2).y - 10.0).abs() < EPSILON);
    }

    // -- Test 7: Roundtrip KnotPath → resolve → BezierPath → to_knot_path ---

    #[test]
    fn roundtrip_knot_bezier_knot() {
        // Open path
        let kp = super::super::KnotPath::from_knots(
            vec![
                Knot::new(Point::new(0.0, 0.0)),
                Knot::new(Point::new(5.0, 5.0)),
                Knot::new(Point::new(10.0, 0.0)),
            ],
            false,
        );
        let bp = kp.resolve();
        let kp2 = bp.to_knot_path();

        assert_eq!(kp2.knots.len(), 3);
        assert!(!kp2.is_cyclic);

        // Knot points should be preserved exactly
        assert!((kp2.knots[0].point.x - 0.0).abs() < EPSILON);
        assert!((kp2.knots[1].point.x - 5.0).abs() < EPSILON);
        assert!((kp2.knots[2].point.x - 10.0).abs() < EPSILON);

        // First knot left should be Open (open path endpoint)
        assert_eq!(kp2.knots[0].left, KnotDirection::Open);
        // Last knot right should be Open (open path endpoint)
        assert_eq!(kp2.knots[2].right, KnotDirection::Open);

        // Middle knot should have Explicit controls on both sides
        assert!(matches!(kp2.knots[1].left, KnotDirection::Explicit(_)));
        assert!(matches!(kp2.knots[1].right, KnotDirection::Explicit(_)));
    }

    #[test]
    fn roundtrip_cyclic() {
        let kp = super::super::KnotPath::from_knots(
            vec![
                Knot::new(Point::new(0.0, 0.0)),
                Knot::new(Point::new(10.0, 0.0)),
                Knot::new(Point::new(5.0, 10.0)),
            ],
            true,
        );
        let bp = kp.resolve();
        let kp2 = bp.to_knot_path();

        assert_eq!(kp2.knots.len(), 3);
        assert!(kp2.is_cyclic);

        // All knots should have Explicit controls on both sides (cyclic)
        for (i, knot) in kp2.knots.iter().enumerate() {
            assert!(
                matches!(knot.left, KnotDirection::Explicit(_)),
                "knot {i} left should be Explicit"
            );
            assert!(
                matches!(knot.right, KnotDirection::Explicit(_)),
                "knot {i} right should be Explicit"
            );
        }
    }

    // -- Default trait -------------------------------------------------------

    #[test]
    fn default_is_empty() {
        let bp = BezierPath::default();
        assert_eq!(bp.num_segments(), 0);
        assert_eq!(bp.num_knots(), 0);
    }

    // -- Cyclic segment wrapping ---------------------------------------------

    #[test]
    fn cyclic_last_segment_wraps() {
        let bp = make_triangle_bezier();
        // Segment 2 should connect knot 2 back to knot 0
        let seg = bp.segment(2);
        assert!((seg.p0.x - 5.0).abs() < EPSILON);
        assert!((seg.p0.y - 10.0).abs() < EPSILON);
        assert!((seg.p3.x - 0.0).abs() < EPSILON);
        assert!((seg.p3.y - 0.0).abs() < EPSILON);
    }

    // =======================================================================
    // Path operation tests
    // =======================================================================

    /// Helper: build a cyclic square `BezierPath` with straight-line controls.
    fn make_square_bezier() -> BezierPath {
        let pts = [
            Point::new(0.0, 0.0),
            Point::new(1.0, 0.0),
            Point::new(1.0, 1.0),
            Point::new(0.0, 1.0),
        ];
        let controls = (0..4)
            .map(|i| {
                let j = (i + 1) % 4;
                SegmentControls {
                    post: pts[i].lerp(pts[j], 1.0 / 3.0),
                    pre: pts[i].lerp(pts[j], 2.0 / 3.0),
                }
            })
            .collect();
        BezierPath::from_parts(pts.to_vec(), controls, true)
    }

    // -- point_at -----------------------------------------------------------

    #[test]
    fn point_at_line_endpoints() {
        let bp = make_line_bezier();
        let p0 = bp.point_at(0.0);
        assert!(p0.x.abs() < EPSILON);
        assert!(p0.y.abs() < EPSILON);

        let p1 = bp.point_at(1.0);
        assert!((p1.x - 10.0).abs() < EPSILON);
    }

    #[test]
    fn point_at_line_midpoint() {
        let bp = make_line_bezier();
        let pmid = bp.point_at(0.5);
        assert!((pmid.x - 5.0).abs() < EPSILON);
    }

    #[test]
    fn point_at_clamps_open() {
        let bp = make_line_bezier();
        let p_neg = bp.point_at(-1.0);
        assert!(p_neg.x.abs() < EPSILON);

        let p_over = bp.point_at(5.0);
        assert!((p_over.x - 10.0).abs() < EPSILON);
    }

    #[test]
    fn point_at_empty() {
        let bp = BezierPath::new();
        assert_eq!(bp.point_at(0.0), Point::ZERO);
    }

    #[test]
    fn point_at_matches_knot_path() {
        // Verify BezierPath.point_at matches the KnotPath free function
        let bp = make_line_bezier();
        let kp = bp.to_knot_path();
        for &t in &[0.0, 0.25, 0.5, 0.75, 1.0] {
            let bp_pt = bp.point_at(t);
            let kp_pt = kp.point_at(t);
            assert!(
                (bp_pt.x - kp_pt.x).abs() < EPSILON && (bp_pt.y - kp_pt.y).abs() < EPSILON,
                "t={t}: bezier={bp_pt:?}, knot={kp_pt:?}"
            );
        }
    }

    // -- direction_at -------------------------------------------------------

    #[test]
    fn direction_at_line() {
        let bp = make_line_bezier();
        let d = bp.direction_at(0.5);
        assert!(d.x > 0.0);
        assert!(d.y.abs() < EPSILON);
    }

    #[test]
    fn direction_at_empty() {
        let bp = BezierPath::new();
        assert_eq!(bp.direction_at(0.0), Vec2::ZERO);
    }

    // -- direction_time -----------------------------------------------------

    #[test]
    fn direction_time_east_on_line() {
        let bp = make_line_bezier();
        let t = bp.direction_time(Vec2::new(1.0, 0.0));
        let t = t.expect("east direction should be found");
        assert!((t - 0.0).abs() < 0.01, "expected ~0, got {t}");
    }

    #[test]
    fn direction_time_west_not_found() {
        let bp = make_line_bezier();
        assert!(
            bp.direction_time(Vec2::new(-1.0, 0.0)).is_none(),
            "west should not be found on an eastward line"
        );
    }

    #[test]
    fn direction_time_zero_dir() {
        let bp = make_line_bezier();
        let t = bp
            .direction_time(Vec2::new(0.0, 0.0))
            .expect("zero direction always matches");
        assert!((t - 0.0).abs() < EPSILON);
    }

    #[test]
    fn direction_time_on_triangle() {
        let bp = make_triangle_bezier();
        let t = bp
            .direction_time(Vec2::new(1.0, 0.0))
            .expect("east direction should be found");
        assert!(t >= 0.0 && t < 0.5, "expected near 0, got {t}");
    }

    // -- arc_length ---------------------------------------------------------

    #[test]
    fn arc_length_line() {
        let bp = make_line_bezier();
        let len = bp.arc_length();
        assert!((len - 10.0).abs() < 0.01, "expected ~10, got {len}");
    }

    #[test]
    fn arc_length_empty() {
        let bp = BezierPath::new();
        assert_eq!(bp.arc_length(), 0.0);
    }

    #[test]
    fn arc_length_matches_knot_path() {
        let bp = make_triangle_bezier();
        let kp = bp.to_knot_path();
        let bp_len = bp.arc_length();
        let kp_len = super::super::arc_length(&kp);
        assert!(
            (bp_len - kp_len).abs() < 0.01,
            "bezier={bp_len}, knot={kp_len}"
        );
    }

    // -- arc_time -----------------------------------------------------------

    #[test]
    fn arc_time_zero() {
        let bp = make_line_bezier();
        assert!((bp.arc_time(0.0)).abs() < EPSILON);
    }

    #[test]
    fn arc_time_full() {
        let bp = make_line_bezier();
        let total = bp.arc_length();
        let t = bp.arc_time(total + 1.0);
        assert!(
            (t - 1.0).abs() < EPSILON,
            "expected num_segments=1, got {t}"
        );
    }

    #[test]
    fn arc_time_half_line() {
        let bp = make_line_bezier();
        let t = bp.arc_time(5.0);
        // For a straight line of length 10, arc_time(5) should be ~0.5
        assert!((t - 0.5).abs() < 0.01, "expected ~0.5, got {t}");
    }

    #[test]
    fn arc_time_matches_knot_path() {
        let bp = make_triangle_bezier();
        let kp = bp.to_knot_path();
        let half_len = bp.arc_length() / 2.0;
        let bp_t = bp.arc_time(half_len);
        let kp_t = super::super::arc_time(&kp, half_len);
        assert!((bp_t - kp_t).abs() < 0.01, "bezier={bp_t}, knot={kp_t}");
    }

    // -- turning_number -----------------------------------------------------

    #[test]
    fn turning_number_ccw_triangle() {
        let bp = make_triangle_bezier();
        assert_eq!(bp.turning_number(), 1.0);
    }

    #[test]
    fn turning_number_cw_triangle() {
        let bp = make_triangle_bezier();
        let rev = bp.reverse();
        assert_eq!(rev.turning_number(), -1.0);
    }

    #[test]
    fn turning_number_open_path() {
        let bp = make_line_bezier();
        assert_eq!(bp.turning_number(), 0.0);
    }

    #[test]
    fn turning_number_ccw_square() {
        let bp = make_square_bezier();
        assert_eq!(bp.turning_number(), 1.0);
    }

    #[test]
    fn turning_number_single_point() {
        let bp = BezierPath::from_parts(vec![Point::new(5.0, 5.0)], vec![], false);
        assert_eq!(bp.turning_number(), 0.0);
    }

    // -- precontrol_at / postcontrol_at -------------------------------------

    #[test]
    fn precontrol_at_open_endpoints() {
        let bp = make_line_bezier();

        // Precontrol at t=0 on open path should be the point itself
        let pre0 = bp.precontrol_at(0.0);
        assert!((pre0.x - 0.0).abs() < EPSILON, "expected 0, got {}", pre0.x);

        // Precontrol at t=1 should be the pre control of segment 0
        let pre1 = bp.precontrol_at(1.0);
        assert!(
            (pre1.x - 20.0 / 3.0).abs() < EPSILON,
            "expected 20/3, got {}",
            pre1.x
        );
    }

    #[test]
    fn postcontrol_at_open_endpoints() {
        let bp = make_line_bezier();

        // Postcontrol at t=0 should be the post control of segment 0
        let post0 = bp.postcontrol_at(0.0);
        assert!(
            (post0.x - 10.0 / 3.0).abs() < EPSILON,
            "expected 10/3, got {}",
            post0.x
        );

        // Postcontrol at t=1 (last knot, open path) should be the point itself
        let post1 = bp.postcontrol_at(1.0);
        assert!(
            (post1.x - 10.0).abs() < EPSILON,
            "expected 10, got {}",
            post1.x
        );
    }

    #[test]
    fn precontrol_at_fractional_time() {
        let bp = make_line_bezier();
        // At fractional time, precontrol is from splitting the segment
        let pre_half = bp.precontrol_at(0.5);
        // For a straight line, the split at 0.5 should give a precontrol
        // near the midpoint on the left side
        assert!(pre_half.x > 0.0 && pre_half.x < 10.0);
    }

    #[test]
    fn postcontrol_at_fractional_time() {
        let bp = make_line_bezier();
        let post_half = bp.postcontrol_at(0.5);
        assert!(post_half.x > 0.0 && post_half.x < 10.0);
    }

    #[test]
    fn precontrol_at_cyclic_knot() {
        let bp = make_triangle_bezier();
        // Precontrol at t=0 on cyclic path uses the pre of segment n-1
        let pre0 = bp.precontrol_at(0.0);
        let expected = bp.segment_controls(2).pre;
        assert!(
            (pre0.x - expected.x).abs() < EPSILON && (pre0.y - expected.y).abs() < EPSILON,
            "pre0={pre0:?}, expected={expected:?}"
        );
    }

    #[test]
    fn precontrol_at_empty() {
        let bp = BezierPath::new();
        assert_eq!(bp.precontrol_at(0.0), Point::ZERO);
    }

    #[test]
    fn postcontrol_at_empty() {
        let bp = BezierPath::new();
        assert_eq!(bp.postcontrol_at(0.0), Point::ZERO);
    }

    // -- subpath ------------------------------------------------------------

    #[test]
    fn subpath_full_line() {
        let bp = make_line_bezier();
        let sub = bp.subpath(0.0, 1.0);
        assert_eq!(sub.num_knots(), 2);
        assert_eq!(sub.num_segments(), 1);
        let p0 = sub.point_at(0.0);
        let p1 = sub.point_at(1.0);
        assert!(p0.x.abs() < EPSILON);
        assert!((p1.x - 10.0).abs() < EPSILON);
    }

    #[test]
    fn subpath_half_line() {
        let bp = make_line_bezier();
        let sub = bp.subpath(0.0, 0.5);
        let end = sub.point_at(index_to_scalar(sub.num_segments()));
        assert!((end.x - 5.0).abs() < 0.1);
    }

    #[test]
    fn subpath_empty() {
        let bp = BezierPath::new();
        let sub = bp.subpath(0.0, 1.0);
        assert_eq!(sub.num_segments(), 0);
    }

    #[test]
    fn subpath_cyclic_wrap() {
        let tri = make_triangle_bezier();
        let sub = tri.subpath(2.5, 0.5);
        assert!(!sub.knot_points().is_empty());

        let p_start = sub.point_at(0.0);
        let p_end = sub.point_at(index_to_scalar(sub.num_segments()));

        let expected_start = tri.point_at(2.5);
        assert!(
            (p_start.x - expected_start.x).abs() < 0.1
                && (p_start.y - expected_start.y).abs() < 0.1,
            "start: {p_start:?}, expected: {expected_start:?}"
        );

        let expected_end = tri.point_at(0.5);
        assert!(
            (p_end.x - expected_end.x).abs() < 0.1 && (p_end.y - expected_end.y).abs() < 0.1,
            "end: {p_end:?}, expected: {expected_end:?}"
        );
    }

    #[test]
    fn subpath_cyclic_forward_wrap() {
        let tri = make_triangle_bezier();
        let sub = tri.subpath(2.5, 4.5);
        assert!(sub.num_knots() >= 3, "should span multiple segments");

        let p_start = sub.point_at(0.0);
        let p_end = sub.point_at(index_to_scalar(sub.num_segments()));

        let expected_start = tri.point_at(2.5);
        assert!(
            (p_start.x - expected_start.x).abs() < 0.1
                && (p_start.y - expected_start.y).abs() < 0.1,
            "start: {p_start:?}, expected: {expected_start:?}"
        );

        let expected_end = tri.point_at(1.5);
        assert!(
            (p_end.x - expected_end.x).abs() < 0.1 && (p_end.y - expected_end.y).abs() < 0.1,
            "end: {p_end:?}, expected: {expected_end:?}"
        );
    }

    // -- reverse ------------------------------------------------------------

    #[test]
    fn reverse_open_preserves_points() {
        let bp = make_line_bezier();
        let rev = bp.reverse();
        assert_eq!(rev.num_knots(), 2);
        assert!((rev.knot_point(0).x - 10.0).abs() < EPSILON);
        assert!(rev.knot_point(1).x.abs() < EPSILON);
    }

    #[test]
    fn reverse_open_swaps_controls() {
        let bp = make_line_bezier();
        let rev = bp.reverse();
        // The original controls were post=10/3, pre=20/3
        // After reverse, the single segment goes 10 -> 0
        // with post=20/3 (was pre), pre=10/3 (was post)
        let ctrl = rev.segment_controls(0);
        assert!((ctrl.post.x - 20.0 / 3.0).abs() < EPSILON);
        assert!((ctrl.pre.x - 10.0 / 3.0).abs() < EPSILON);
    }

    #[test]
    fn reverse_cyclic_keeps_start() {
        let bp = make_triangle_bezier();
        let rev = bp.reverse();
        assert!(rev.is_cyclic());
        assert_eq!(rev.num_knots(), 3);
        assert_eq!(rev.knot_point(0), bp.knot_point(0));
    }

    #[test]
    fn reverse_cyclic_time_mapping() {
        let bp = make_triangle_bezier();
        let rev = bp.reverse();
        let n = index_to_scalar(bp.num_segments());

        for &t in &[0.0, 0.25, 0.9, 1.5, 2.2] {
            let p_rev = rev.point_at(t);
            let mapped = ((n - t) % n + n) % n;
            let p_orig = bp.point_at(mapped);
            assert!(
                (p_rev.x - p_orig.x).abs() < 1e-6 && (p_rev.y - p_orig.y).abs() < 1e-6,
                "t={t}: rev={p_rev:?}, orig={p_orig:?}, mapped={mapped}"
            );
        }
    }

    #[test]
    fn reverse_empty() {
        let bp = BezierPath::new();
        let rev = bp.reverse();
        assert_eq!(rev.num_segments(), 0);
        assert_eq!(rev.num_knots(), 0);
    }

    #[test]
    fn reverse_involution() {
        // Reversing twice should give back the original
        let bp = make_line_bezier();
        let rev2 = bp.reverse().reverse();
        assert_eq!(rev2.num_knots(), bp.num_knots());
        for i in 0..bp.num_knots() {
            assert!(
                (rev2.knot_point(i).x - bp.knot_point(i).x).abs() < EPSILON
                    && (rev2.knot_point(i).y - bp.knot_point(i).y).abs() < EPSILON,
                "knot {i}: rev2={:?}, orig={:?}",
                rev2.knot_point(i),
                bp.knot_point(i)
            );
        }
    }

    #[test]
    fn reverse_cyclic_involution() {
        let bp = make_triangle_bezier();
        let rev2 = bp.reverse().reverse();
        for i in 0..bp.num_knots() {
            assert!(
                (rev2.knot_point(i).x - bp.knot_point(i).x).abs() < EPSILON
                    && (rev2.knot_point(i).y - bp.knot_point(i).y).abs() < EPSILON,
                "knot {i}: rev2={:?}, orig={:?}",
                rev2.knot_point(i),
                bp.knot_point(i)
            );
        }
        // Also check controls
        for i in 0..bp.num_segments() {
            let orig = bp.segment_controls(i);
            let rev2c = rev2.segment_controls(i);
            assert!(
                (rev2c.post.x - orig.post.x).abs() < EPSILON
                    && (rev2c.post.y - orig.post.y).abs() < EPSILON
                    && (rev2c.pre.x - orig.pre.x).abs() < EPSILON
                    && (rev2c.pre.y - orig.pre.y).abs() < EPSILON,
                "segment {i}: rev2={rev2c:?}, orig={orig:?}"
            );
        }
    }

    // -- Cross-validation with KnotPath -------------------------------------

    #[test]
    fn direction_time_matches_knot_path() {
        let bp = make_triangle_bezier();
        let kp = bp.to_knot_path();

        let dir = Vec2::new(1.0, 0.0);
        let bp_t = bp.direction_time(dir);
        let kp_t = kp.direction_time(dir);
        assert_eq!(bp_t.is_some(), kp_t.is_some());
        if let (Some(bt), Some(kt)) = (bp_t, kp_t) {
            assert!((bt - kt).abs() < 0.01, "bezier={bt}, knot={kt}");
        }
    }

    #[test]
    fn turning_number_matches_knot_path() {
        let bp = make_triangle_bezier();
        let kp = bp.to_knot_path();
        let bp_tn = bp.turning_number();
        let kp_tn = super::super::turning_number(&kp);
        assert!(
            (bp_tn - kp_tn).abs() < EPSILON,
            "bezier={bp_tn}, knot={kp_tn}"
        );
    }
}
