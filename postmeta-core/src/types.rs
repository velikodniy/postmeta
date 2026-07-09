//! Runtime value types for the `MetaPost` interpreter
//!
//! Every expression evaluates to a [`Value`]. The type system mirrors the original WEB source (§12): numeric values progress through states from `unknown` → `independent` → `dependent` → `known`.
//! Non-numeric types (boolean, string, pen, path, picture) are either known or unknown, forming rings of equivalent unknowns.

use std::sync::Arc;

use postmeta_graphics::path::BezierPath;
use postmeta_graphics::types::{
    Color, DashPattern, LineCap, LineJoin, Pen, Picture, Scalar, Transform,
};

/// Tolerance for numeric equality in `MetaPost` language semantics
///
/// Values differing by less than this are equal under `=`/`<>` and `Value::PartialEq`, matching `MetaPost`'s limited numeric precision.
pub const NUMERIC_TOLERANCE: Scalar = 1e-4;

// ---------------------------------------------------------------------------
// MetaPost type codes
// ---------------------------------------------------------------------------

/// The type of a `MetaPost` value or variable
///
/// The ordering matters: types >= `Numeric` are numeric; types with `Unknown*` variants can participate in nonlinear equations.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u8)]
pub enum Type {
    #[default]
    Undefined = 0,
    /// No value (e.g. result of a procedure call)
    Vacuous = 1,
    Boolean = 2,
    /// An unknown boolean (in an equivalence ring)
    UnknownBoolean = 3,
    String = 4,
    UnknownString = 5,
    Pen = 6,
    UnknownPen = 7,
    Path = 8,
    UnknownPath = 9,
    Picture = 10,
    UnknownPicture = 11,
    /// A transform (6 numeric parts)
    TransformType = 12,
    /// A color (3 numeric parts: red, green, blue)
    ColorType = 13,
    /// A pair (2 numeric parts: x, y)
    PairType = 14,
    /// Declared numeric but not yet used in equations
    Numeric = 15,
    Known = 16,
    /// Linear combination with fraction coefficients
    Dependent = 17,
    /// A free variable with serial number
    Independent = 18,
}

impl Type {
    #[must_use]
    pub const fn is_numeric(self) -> bool {
        (self as u8) >= (Self::Numeric as u8)
    }

    #[must_use]
    pub const fn is_compound(self) -> bool {
        matches!(self, Self::PairType | Self::ColorType | Self::TransformType)
    }

    /// Number of numeric components of a compound type
    ///
    /// Pairs have 2, colors 3, transforms 6; other types are atomic and return `None`.
    /// Compound allocation, equation splitting, and assignment are all driven by this count, so a future compound type (e.g. `cmykcolor`) only needs an entry here and in [`Self::component_suffixes`].
    #[must_use]
    pub const fn components(self) -> Option<usize> {
        match self {
            Self::PairType => Some(2),
            Self::ColorType => Some(3),
            Self::TransformType => Some(6),
            _ => None,
        }
    }

    /// Variable-name suffixes of the components, in storage order
    ///
    /// These are the `.x`/`.y`-style suffixes used to register component variables (e.g. `p.x`, `c.r`, `T.txx`).
    /// Empty for atomic types.
    #[must_use]
    pub const fn component_suffixes(self) -> &'static [&'static str] {
        match self {
            Self::PairType => &["x", "y"],
            Self::ColorType => &["r", "g", "b"],
            Self::TransformType => &["tx", "ty", "txx", "txy", "tyx", "tyy"],
            _ => &[],
        }
    }

    /// Whether this is an unknown (ring) type
    #[must_use]
    pub const fn is_unknown(self) -> bool {
        matches!(
            self,
            Self::UnknownBoolean
                | Self::UnknownString
                | Self::UnknownPen
                | Self::UnknownPath
                | Self::UnknownPicture
        )
    }

    #[must_use]
    pub const fn known_variant(self) -> Self {
        match self {
            Self::UnknownBoolean => Self::Boolean,
            Self::UnknownString => Self::String,
            Self::UnknownPen => Self::Pen,
            Self::UnknownPath => Self::Path,
            Self::UnknownPicture => Self::Picture,
            other => other,
        }
    }

    #[must_use]
    pub const fn unknown_variant(self) -> Self {
        match self {
            Self::Boolean => Self::UnknownBoolean,
            Self::String => Self::UnknownString,
            Self::Pen => Self::UnknownPen,
            Self::Path => Self::UnknownPath,
            Self::Picture => Self::UnknownPicture,
            other => other,
        }
    }
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Undefined => write!(f, "undefined"),
            Self::Vacuous => write!(f, "vacuous"),
            Self::Boolean | Self::UnknownBoolean => write!(f, "boolean"),
            Self::String | Self::UnknownString => write!(f, "string"),
            Self::Pen | Self::UnknownPen => write!(f, "pen"),
            Self::Path | Self::UnknownPath => write!(f, "path"),
            Self::Picture | Self::UnknownPicture => write!(f, "picture"),
            Self::TransformType => write!(f, "transform"),
            Self::ColorType => write!(f, "color"),
            Self::PairType => write!(f, "pair"),
            Self::Numeric => write!(f, "numeric"),
            Self::Known => write!(f, "known numeric"),
            Self::Dependent => write!(f, "dependent"),
            Self::Independent => write!(f, "independent"),
        }
    }
}

#[inline]
fn scalar_approx_eq(a: Scalar, b: Scalar) -> bool {
    (a - b).abs() < NUMERIC_TOLERANCE
}

// ---------------------------------------------------------------------------
// Known values
// ---------------------------------------------------------------------------

/// A fully-resolved `MetaPost` value
#[derive(Debug, Clone)]
pub enum Value {
    Vacuous,
    Boolean(bool),
    Numeric(Scalar),
    /// Known x, y
    Pair(Scalar, Scalar),
    Color(Color),
    Transform(Transform),
    String(Arc<str>),
    Path(Arc<BezierPath>),
    Pen(Pen),
    Picture(Picture),
}

impl Value {
    #[must_use]
    pub const fn ty(&self) -> Type {
        match self {
            Self::Vacuous => Type::Vacuous,
            Self::Boolean(_) => Type::Boolean,
            Self::Numeric(_) => Type::Known,
            Self::Pair(_, _) => Type::PairType,
            Self::Color(_) => Type::ColorType,
            Self::Transform(_) => Type::TransformType,
            Self::String(_) => Type::String,
            Self::Path(_) => Type::Path,
            Self::Pen(_) => Type::Pen,
            Self::Picture(_) => Type::Picture,
        }
    }

    #[must_use]
    pub const fn as_numeric(&self) -> Option<Scalar> {
        if let Self::Numeric(v) = self {
            Some(*v)
        } else {
            None
        }
    }

    #[must_use]
    pub const fn as_boolean(&self) -> Option<bool> {
        if let Self::Boolean(v) = self {
            Some(*v)
        } else {
            None
        }
    }

    #[must_use]
    pub const fn as_pair(&self) -> Option<(Scalar, Scalar)> {
        if let Self::Pair(x, y) = self {
            Some((*x, *y))
        } else {
            None
        }
    }

    #[must_use]
    pub const fn as_string(&self) -> Option<&Arc<str>> {
        if let Self::String(s) = self {
            Some(s)
        } else {
            None
        }
    }

    #[must_use]
    pub const fn as_path(&self) -> Option<&Arc<BezierPath>> {
        if let Self::Path(p) = self {
            Some(p)
        } else {
            None
        }
    }

    #[must_use]
    pub const fn as_picture(&self) -> Option<&Picture> {
        if let Self::Picture(p) = self {
            Some(p)
        } else {
            None
        }
    }

    #[must_use]
    pub const fn as_pen(&self) -> Option<&Pen> {
        if let Self::Pen(p) = self {
            Some(p)
        } else {
            None
        }
    }

    #[must_use]
    pub const fn as_color(&self) -> Option<&Color> {
        if let Self::Color(c) = self {
            Some(c)
        } else {
            None
        }
    }

    #[must_use]
    pub const fn as_transform(&self) -> Option<Transform> {
        if let Self::Transform(t) = self {
            Some(*t)
        } else {
            None
        }
    }
}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Vacuous, Self::Vacuous) => true,
            (Self::Boolean(a), Self::Boolean(b)) => a == b,
            (Self::Numeric(a), Self::Numeric(b)) => scalar_approx_eq(*a, *b),
            (Self::Pair(ax, ay), Self::Pair(bx, by)) => {
                scalar_approx_eq(*ax, *bx) && scalar_approx_eq(*ay, *by)
            }
            (Self::Color(a), Self::Color(b)) => {
                scalar_approx_eq(a.r, b.r)
                    && scalar_approx_eq(a.g, b.g)
                    && scalar_approx_eq(a.b, b.b)
            }
            (Self::Transform(a), Self::Transform(b)) => {
                scalar_approx_eq(a.tx, b.tx)
                    && scalar_approx_eq(a.ty, b.ty)
                    && scalar_approx_eq(a.txx, b.txx)
                    && scalar_approx_eq(a.txy, b.txy)
                    && scalar_approx_eq(a.tyx, b.tyx)
                    && scalar_approx_eq(a.tyy, b.tyy)
            }
            (Self::String(a), Self::String(b)) => a == b,
            (Self::Path(a), Self::Path(b)) => a == b,
            _ => false,
        }
    }
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Vacuous => write!(f, "vacuous"),
            Self::Boolean(b) => write!(f, "{}", if *b { "true" } else { "false" }),
            Self::Numeric(v) => write!(f, "{v}"),
            Self::Pair(x, y) => write!(f, "({x},{y})"),
            Self::Color(c) => write!(f, "({},{},{})", c.r, c.g, c.b),
            Self::Transform(t) => write!(
                f,
                "({},{},{},{},{},{})",
                t.tx, t.ty, t.txx, t.txy, t.tyx, t.tyy
            ),
            Self::String(s) => write!(f, "\"{s}\""),
            Self::Path(_) => write!(f, "(path)"),
            Self::Pen(_) => write!(f, "(pen)"),
            Self::Picture(_) => write!(f, "(picture)"),
        }
    }
}

// ---------------------------------------------------------------------------
// Pen stroke parameters (for drawing state)
// ---------------------------------------------------------------------------

/// Current drawing parameters, accumulated by `withpen`, `withcolor`, `dashed`
#[derive(Debug, Clone)]
pub struct DrawingState {
    pub pen: Pen,
    pub color: Color,
    pub dash: Option<DashPattern>,
    pub line_cap: LineCap,
    pub line_join: LineJoin,
    pub miter_limit: Scalar,
}

impl Default for DrawingState {
    fn default() -> Self {
        Self {
            pen: Pen::default(),
            color: Color::BLACK,
            dash: None,
            line_cap: LineCap::Round,
            line_join: LineJoin::Round,
            miter_limit: 10.0,
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn type_numeric_classification() {
        assert!(!Type::Boolean.is_numeric());
        assert!(!Type::String.is_numeric());
        assert!(Type::Numeric.is_numeric());
        assert!(Type::Known.is_numeric());
        assert!(Type::Dependent.is_numeric());
        assert!(Type::Independent.is_numeric());
    }

    #[test]
    fn component_counts_match_suffix_lists() {
        for ty in [
            Type::Undefined,
            Type::Boolean,
            Type::String,
            Type::Path,
            Type::Picture,
            Type::PairType,
            Type::ColorType,
            Type::TransformType,
            Type::Numeric,
            Type::Known,
        ] {
            let n = ty.components();
            assert_eq!(
                n.unwrap_or(0),
                ty.component_suffixes().len(),
                "count/suffixes mismatch for {ty:?}"
            );
            assert_eq!(
                n.is_some(),
                ty.is_compound(),
                "compound mismatch for {ty:?}"
            );
        }
    }

    #[test]
    fn type_compound_classification() {
        assert!(Type::PairType.is_compound());
        assert!(Type::ColorType.is_compound());
        assert!(Type::TransformType.is_compound());
        assert!(!Type::Known.is_compound());
        assert!(!Type::Path.is_compound());
    }

    #[test]
    fn type_unknown_known_roundtrip() {
        assert_eq!(Type::Boolean.unknown_variant(), Type::UnknownBoolean);
        assert_eq!(Type::UnknownBoolean.known_variant(), Type::Boolean);
        assert_eq!(Type::String.unknown_variant(), Type::UnknownString);
        assert_eq!(Type::UnknownString.known_variant(), Type::String);
    }

    #[test]
    fn value_type_matches() {
        assert_eq!(Value::Vacuous.ty(), Type::Vacuous);
        assert_eq!(Value::Boolean(true).ty(), Type::Boolean);
        assert_eq!(Value::Numeric(3.14).ty(), Type::Known);
        assert_eq!(Value::Pair(1.0, 2.0).ty(), Type::PairType);
        assert_eq!(Value::String(Arc::from("hi")).ty(), Type::String);
    }

    #[test]
    fn value_extractors() {
        assert_eq!(Value::Numeric(5.0).as_numeric(), Some(5.0));
        assert_eq!(Value::Boolean(true).as_boolean(), Some(true));
        assert_eq!(Value::Pair(1.0, 2.0).as_pair(), Some((1.0, 2.0)));
        assert!(Value::Pen(Pen::null()).as_pen().is_some());
        assert!(Value::Color(Color::new(1.0, 0.0, 0.0)).as_color().is_some());
        assert!(
            Value::Transform(Transform::IDENTITY)
                .as_transform()
                .is_some()
        );
        assert!(Value::Numeric(5.0).as_boolean().is_none());
    }

    #[test]
    fn value_display() {
        assert_eq!(format!("{}", Value::Boolean(true)), "true");
        assert_eq!(format!("{}", Value::Boolean(false)), "false");
        assert_eq!(format!("{}", Value::Numeric(42.0)), "42");
        assert_eq!(format!("{}", Value::Pair(1.0, 2.0)), "(1,2)");
        assert_eq!(format!("{}", Value::String(Arc::from("hi"))), "\"hi\"");
    }

    // Value::PartialEq uses NUMERIC_TOLERANCE (1e-4).

    #[test]
    fn value_eq_numeric_exact() {
        assert_eq!(Value::Numeric(1.0), Value::Numeric(1.0));
    }

    #[test]
    fn value_eq_numeric_within_tolerance() {
        // A diff of 5e-5 is below the 1e-4 tolerance
        let a = Value::Numeric(1.0);
        let b = Value::Numeric(1.00005);
        assert_eq!(a, b, "diff 5e-5 should be equal under NUMERIC_TOLERANCE");
    }

    #[test]
    fn value_eq_numeric_beyond_tolerance() {
        // A diff of 1e-3 exceeds the 1e-4 tolerance
        let a = Value::Numeric(1.0);
        let b = Value::Numeric(1.001);
        assert_ne!(
            a, b,
            "diff 1e-3 should NOT be equal under NUMERIC_TOLERANCE"
        );
    }

    #[test]
    fn value_eq_pair_within_tolerance() {
        let a = Value::Pair(1.0, 2.0);
        let b = Value::Pair(1.00005, 2.0 - 5e-5);
        assert_eq!(
            a, b,
            "pair components within NUMERIC_TOLERANCE should match"
        );
    }

    #[test]
    fn value_eq_pair_beyond_tolerance() {
        let a = Value::Pair(1.0, 2.0);
        let b = Value::Pair(1.001, 2.0);
        assert_ne!(a, b, "pair with 1e-3 x diff should NOT match");
    }

    #[test]
    fn value_eq_color_within_tolerance() {
        let a = Value::Color(Color::new(0.2, 0.4, 0.6));
        let b = Value::Color(Color::new(0.2 + 5e-5, 0.4 - 5e-5, 0.6));
        assert_eq!(
            a, b,
            "color components within NUMERIC_TOLERANCE should match"
        );
    }

    #[test]
    fn value_eq_transform_within_tolerance() {
        let a = Value::Transform(Transform::IDENTITY);
        let b = Value::Transform(Transform {
            tx: 5e-5,
            ty: -5e-5,
            txx: 1.0,
            txy: 0.0,
            tyx: 0.0,
            tyy: 1.0,
        });
        assert_eq!(
            a, b,
            "transform components within NUMERIC_TOLERANCE should match"
        );
    }
}
