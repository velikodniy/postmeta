//! Path and pen operator evaluation.

use std::sync::Arc;

use postmeta_graphics::path::BezierPath;
use postmeta_graphics::types::{Pen, Point, Vec2};

use crate::error::{ErrorKind, InterpResult, InterpreterError};
use crate::interpreter::helpers::{value_to_pair, value_to_path, value_to_pen, value_to_scalar};
use crate::types::{Type, Value};

pub(super) fn reverse(input: &Value) -> InterpResult<(Value, Type)> {
    if let Value::Path(p) = input {
        Ok((Value::Path(Arc::new(p.reverse())), Type::Path))
    } else {
        Err(InterpreterError::new(
            ErrorKind::TypeError,
            "reverse requires a path",
        ))
    }
}

pub(super) fn make_path(input: &Value) -> InterpResult<(Value, Type)> {
    if let Value::Pen(p) = input {
        Ok((Value::Path(Arc::new(BezierPath::from(p))), Type::Path))
    } else {
        Err(InterpreterError::new(
            ErrorKind::TypeError,
            "makepath requires a pen",
        ))
    }
}

pub(super) fn make_pen(input: &Value) -> InterpResult<(Value, Type)> {
    // mp.web §16987: pair_to_path before makepen
    let owned_path;
    let path_ref: &BezierPath = match input {
        Value::Path(p) => p,
        Value::Pair(x, y) => {
            owned_path = BezierPath::from_parts(vec![Point::new(*x, *y)], vec![], false);
            &owned_path
        }
        _ => {
            return Err(InterpreterError::new(
                ErrorKind::TypeError,
                "makepen requires a path or pair",
            ));
        }
    };
    let result = Pen::try_from(path_ref)
        .map_err(|e| InterpreterError::new(ErrorKind::TypeError, format!("makepen: {e}")))?;
    Ok((Value::Pen(result), Type::Pen))
}

pub(super) fn arc_length(input: &Value) -> InterpResult<(Value, Type)> {
    let p = value_to_path(input)?;
    let len = p.arc_length();
    Ok((Value::Numeric(len), Type::Known))
}

pub(super) fn turning_number(input: &Value) -> InterpResult<(Value, Type)> {
    if let Value::Pair(..) = input {
        Ok((Value::Numeric(0.0), Type::Known))
    } else {
        let p = value_to_path(input)?;
        Ok((Value::Numeric(p.turning_number()), Type::Known))
    }
}

pub(super) fn point_of(first: &Value, second: &Value) -> InterpResult<(Value, Type)> {
    let t = value_to_scalar(first)?;
    let p = value_to_path(second)?;
    let pt = p.point_at(t);
    Ok((Value::Pair(pt.x, pt.y), Type::PairType))
}

pub(super) fn precontrol_of(first: &Value, second: &Value) -> InterpResult<(Value, Type)> {
    let t = value_to_scalar(first)?;
    let p = value_to_path(second)?;
    let pt = p.precontrol_at(t);
    Ok((Value::Pair(pt.x, pt.y), Type::PairType))
}

pub(super) fn postcontrol_of(first: &Value, second: &Value) -> InterpResult<(Value, Type)> {
    let t = value_to_scalar(first)?;
    let p = value_to_path(second)?;
    let pt = p.postcontrol_at(t);
    Ok((Value::Pair(pt.x, pt.y), Type::PairType))
}

pub(super) fn subpath_of(first: &Value, second: &Value) -> InterpResult<(Value, Type)> {
    let (t1, t2) = value_to_pair(first)?;
    let p = value_to_path(second)?;
    Ok((Value::Path(Arc::new(p.subpath(t1, t2))), Type::Path))
}

pub(super) fn pen_offset_of(first: &Value, second: &Value) -> InterpResult<(Value, Type)> {
    let (dx, dy) = value_to_pair(first)?;
    let p = value_to_pen(second)?;
    // Degenerate pens (e.g. nullpen) have no support point;
    // MetaPost treats their offset as the origin.
    let pt = p.offset(Vec2::new(dx, dy)).unwrap_or(Point::ZERO);
    Ok((Value::Pair(pt.x, pt.y), Type::PairType))
}

pub(super) fn arc_time_of(first: &Value, second: &Value) -> InterpResult<(Value, Type)> {
    let target_len = value_to_scalar(first)?;
    let p = value_to_path(second)?;
    let t = p.arc_time(target_len);
    Ok((Value::Numeric(t), Type::Known))
}

pub(super) fn direction_time_of(first: &Value, second: &Value) -> InterpResult<(Value, Type)> {
    let Value::Pair(dx, dy) = first else {
        return Err(InterpreterError::new(
            ErrorKind::TypeError,
            "directiontime requires a pair as first argument",
        ));
    };
    let p = value_to_path(second)?;
    let t = p.direction_time(Vec2::new(*dx, *dy)).unwrap_or(-1.0);
    Ok((Value::Numeric(t), Type::Known))
}

pub(super) fn intersection_times(left: &Value, right: &Value) -> InterpResult<(Value, Type)> {
    let p1 = value_to_path(left)?;
    let p2 = value_to_path(right)?;
    let value = p1.intersection_times(p2).map_or_else(
        || Value::Pair(-1.0, -1.0),
        |isect| Value::Pair(isect.t1, isect.t2),
    );
    Ok((value, Type::PairType))
}
