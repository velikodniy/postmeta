//! Path knot types: direction constraints and knot definitions.

use super::geometry::{Point, Scalar};

// ---------------------------------------------------------------------------
// KnotDirection — direction constraint at a path knot
// ---------------------------------------------------------------------------

/// Direction/control constraint for one side of a path knot.
#[derive(Debug, Clone, Copy, PartialEq, Default)]
pub enum KnotDirection {
    /// Control point has been explicitly computed as a Bezier handle.
    Explicit(Point),
    /// A specific direction angle in **radians**.
    ///
    /// Note: degrees are used externally, but angles are converted to
    /// radians at parse time. All internal computations use radians.
    Given(Scalar),
    /// Curl parameter (default 1.0 at open-path endpoints).
    Curl(Scalar),
    /// Let the algorithm choose the direction.
    #[default]
    Open,
}

// ---------------------------------------------------------------------------
// Knot
// ---------------------------------------------------------------------------

/// A single knot in a path.
///
/// Each knot has a point plus left (incoming) and right (outgoing)
/// direction constraints and tension values.
#[derive(Debug, Clone, PartialEq)]
pub struct Knot {
    /// The on-curve point.
    pub point: Point,
    /// Incoming (left) direction constraint.
    pub left: KnotDirection,
    /// Outgoing (right) direction constraint.
    pub right: KnotDirection,
    /// Tension on the incoming side (default 1.0; negative = "at least").
    pub left_tension: Scalar,
    /// Tension on the outgoing side (default 1.0; negative = "at least").
    pub right_tension: Scalar,
}

impl Knot {
    /// Create a new knot at the given point with default (open) constraints.
    #[must_use]
    pub const fn new(point: Point) -> Self {
        Self {
            point,
            left: KnotDirection::Open,
            right: KnotDirection::Open,
            left_tension: 1.0,
            right_tension: 1.0,
        }
    }

    /// Create a knot with explicit Bezier control points already computed.
    #[must_use]
    pub const fn with_controls(point: Point, left_cp: Point, right_cp: Point) -> Self {
        Self {
            point,
            left: KnotDirection::Explicit(left_cp),
            right: KnotDirection::Explicit(right_cp),
            left_tension: 1.0,
            right_tension: 1.0,
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
#[expect(
    clippy::float_cmp,
    reason = "exact float comparisons are intentional in tests"
)]
mod tests {
    use super::*;

    #[test]
    fn knot_defaults() {
        let k = Knot::new(Point::new(1.0, 2.0));
        assert_eq!(k.point, Point::new(1.0, 2.0));
        assert_eq!(k.left, KnotDirection::Open);
        assert_eq!(k.right, KnotDirection::Open);
        assert_eq!(k.left_tension, 1.0);
        assert_eq!(k.right_tension, 1.0);
    }
}
