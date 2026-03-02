//! Path operations and Hobby's spline algorithm.
//!
//! This module provides:
//! - Hobby's algorithm for computing smooth cubic Bezier control points
//!   through a sequence of knots with direction/tension/curl constraints.
//! - [`BezierPath`] — a resolved cubic Bezier path with per-segment controls.

pub mod bezier_path;
pub mod hobby;

pub use bezier_path::{BezierPath, SegmentControls};

use crate::types::{Knot, KnotDirection};

// ---------------------------------------------------------------------------
// KnotPath
// ---------------------------------------------------------------------------

/// A knot-based path: a sequence of knots with direction/tension constraints,
/// optionally cyclic.
///
/// After Hobby's algorithm runs (via [`resolve()`](Self::resolve)), all
/// `KnotDirection` values will be `Explicit` (computed Bezier control points)
/// and the result is returned as a [`BezierPath`].
#[derive(Debug, Clone, PartialEq)]
pub struct KnotPath {
    pub knots: Vec<Knot>,
    pub is_cyclic: bool,
}

impl KnotPath {
    /// Create an empty open path.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            knots: Vec::new(),
            is_cyclic: false,
        }
    }

    /// Create a path from knots.
    #[must_use]
    pub const fn from_knots(knots: Vec<Knot>, is_cyclic: bool) -> Self {
        Self { knots, is_cyclic }
    }

    /// Number of segments in the path.
    /// For a cyclic path with N knots, there are N segments.
    /// For an open path with N knots, there are N-1 segments.
    #[must_use]
    pub fn num_segments(&self) -> usize {
        if self.knots.is_empty() {
            return 0;
        }
        if self.is_cyclic {
            self.knots.len()
        } else {
            self.knots.len() - 1
        }
    }

    /// Resolve direction constraints via Hobby's algorithm and return
    /// a [`BezierPath`] with explicit cubic control points.
    #[must_use]
    pub fn resolve(mut self) -> BezierPath {
        hobby::make_choices(&mut self);
        self.into_bezier_path()
    }

    /// Convert a fully-resolved `KnotPath` (all directions `Explicit`) into
    /// a [`BezierPath`].  Non-explicit directions fall back to the on-curve
    /// point.
    pub(crate) fn into_bezier_path(self) -> BezierPath {
        if self.knots.is_empty() {
            return BezierPath::new();
        }

        let n = self.num_segments();
        let mut points = Vec::with_capacity(self.knots.len());
        let mut controls = Vec::with_capacity(n);

        for (i, knot) in self.knots.iter().enumerate() {
            points.push(knot.point);
            if i < n {
                let j = (i + 1) % self.knots.len();
                let post = match knot.right {
                    KnotDirection::Explicit(p) => p,
                    _ => knot.point,
                };
                let pre = match self.knots[j].left {
                    KnotDirection::Explicit(p) => p,
                    _ => self.knots[j].point,
                };
                controls.push(SegmentControls { post, pre });
            }
        }

        BezierPath::from_parts(points, controls, self.is_cyclic)
    }
}

impl Default for KnotPath {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::Point;

    #[test]
    fn test_num_segments() {
        // Empty path
        let p = KnotPath::new();
        assert_eq!(p.num_segments(), 0);

        // Open path with 2 knots = 1 segment
        let p = KnotPath::from_knots(
            vec![Knot::new(Point::ZERO), Knot::new(Point::new(10.0, 0.0))],
            false,
        );
        assert_eq!(p.num_segments(), 1);

        // Cyclic path with 3 knots = 3 segments
        let p = KnotPath::from_knots(
            vec![
                Knot::new(Point::new(0.0, 0.0)),
                Knot::new(Point::new(10.0, 0.0)),
                Knot::new(Point::new(5.0, 10.0)),
            ],
            true,
        );
        assert_eq!(p.num_segments(), 3);
    }

    #[test]
    fn test_default() {
        let p = KnotPath::default();
        assert!(p.knots.is_empty());
        assert!(!p.is_cyclic);
    }
}
