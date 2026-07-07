//! Applying affine transforms to values.

use std::sync::Arc;

use postmeta_graphics::transform::Transformable;
use postmeta_graphics::types::{Point, Transform};

use crate::error::{ErrorKind, InterpResult, InterpreterError};
use crate::types::{Type, Value};

/// Apply a transform to a value, returning the transformed `(Value, Type)`.
pub(super) fn apply_transform(val: &Value, t: &Transform) -> InterpResult<(Value, Type)> {
    match val {
        Value::Pair(x, y) => {
            let pt = Point::new(*x, *y).transformed(t);
            Ok((Value::Pair(pt.x, pt.y), Type::PairType))
        }
        Value::Path(p) => Ok((Value::Path(Arc::new(p.transformed(t))), Type::Path)),
        Value::Pen(p) => Ok((Value::Pen(p.transformed(t)), Type::Pen)),
        Value::Picture(p) => Ok((Value::Picture(p.transformed(t)), Type::Picture)),
        Value::Transform(existing) => Ok((Value::Transform(existing.then(t)), Type::TransformType)),
        _ => Err(InterpreterError::new(
            ErrorKind::TypeError,
            format!("Cannot transform {}", val.ty()),
        )),
    }
}
