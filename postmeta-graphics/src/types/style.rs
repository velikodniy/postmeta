//! Styling types: colors, line caps, line joins, and dash patterns.

use super::geometry::Scalar;

// ---------------------------------------------------------------------------
// Color
// ---------------------------------------------------------------------------

/// RGB color with components in [0, 1].
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Color {
    pub r: Scalar,
    pub g: Scalar,
    pub b: Scalar,
}

impl Color {
    pub const BLACK: Self = Self {
        r: 0.0,
        g: 0.0,
        b: 0.0,
    };
    pub const WHITE: Self = Self {
        r: 1.0,
        g: 1.0,
        b: 1.0,
    };

    #[must_use]
    pub const fn new(r: Scalar, g: Scalar, b: Scalar) -> Self {
        Self { r, g, b }
    }
}

// ---------------------------------------------------------------------------
// LineCap / LineJoin
// ---------------------------------------------------------------------------

/// Stroke line-cap styles.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum LineCap {
    Butt = 0,
    #[default]
    Round = 1,
    Square = 2,
}

/// Convert a `Scalar` to a `LineCap` by interpreting it as an integer code.
#[expect(
    clippy::cast_possible_truncation,
    reason = "linecap/linejoin values are small integers (0, 1, 2)"
)]
impl From<Scalar> for LineCap {
    fn from(v: Scalar) -> Self {
        match v as i32 {
            0 => Self::Butt,
            2 => Self::Square,
            _ => Self::Round,
        }
    }
}

/// Stroke line-join styles.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum LineJoin {
    Miter = 0,
    #[default]
    Round = 1,
    Bevel = 2,
}

impl From<Scalar> for LineJoin {
    #[expect(
        clippy::cast_possible_truncation,
        reason = "linecap/linejoin values are small integers (0, 1, 2)"
    )]
    fn from(v: Scalar) -> Self {
        match v as i32 {
            0 => Self::Miter,
            2 => Self::Bevel,
            _ => Self::Round,
        }
    }
}

// ---------------------------------------------------------------------------
// DashPattern
// ---------------------------------------------------------------------------

/// A dash pattern: alternating on/off lengths with an offset.
#[derive(Debug, Clone, PartialEq)]
pub struct DashPattern {
    /// Alternating on, off, on, off, ... lengths.
    pub dashes: Vec<Scalar>,
    /// Starting offset into the pattern.
    pub offset: Scalar,
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
    fn linecap_from_scalar() {
        assert_eq!(LineCap::from(0.0), LineCap::Butt);
        assert_eq!(LineCap::from(1.0), LineCap::Round);
        assert_eq!(LineCap::from(2.0), LineCap::Square);
        assert_eq!(LineCap::from(99.0), LineCap::Round);
    }

    #[test]
    fn linejoin_from_scalar() {
        assert_eq!(LineJoin::from(0.0), LineJoin::Miter);
        assert_eq!(LineJoin::from(1.0), LineJoin::Round);
        assert_eq!(LineJoin::from(2.0), LineJoin::Bevel);
        assert_eq!(LineJoin::from(99.0), LineJoin::Round);
    }
}
