//! Core types shared across the `PostMeta` system.

mod geometry;
mod knot;
mod objects;
mod style;

pub use geometry::{EPSILON, NEAR_ZERO, Point, Scalar, Vec2, index_to_scalar, scalar_to_index};
pub use knot::{Knot, KnotDirection};
pub use objects::{FillObject, GraphicsObject, StrokeObject, TextMetrics, TextObject};
pub use style::{Color, DashPattern, LineCap, LineJoin};

// Re-export types whose definitions live in their own top-level modules.
pub use crate::pen::Pen;
pub use crate::picture::Picture;
pub use crate::transform::Transform;
