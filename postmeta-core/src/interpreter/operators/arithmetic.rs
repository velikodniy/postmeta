//! Numeric, boolean, and comparison operator evaluation

use std::cmp::Ordering;

use postmeta_graphics::math;
use postmeta_graphics::types::{Color, Vec2};

use crate::command::{ExpressionBinaryOp, PlusMinusOp, TertiaryBinaryOp};
use crate::error::{ErrorKind, InterpResult, InterpreterError};
use crate::interpreter::Interpreter;
use crate::interpreter::helpers::{value_to_bool, value_to_pair, value_to_scalar};
use crate::types::{Type, Value};

use super::{paths, strings};

pub(super) fn sqrt(input: &Value) -> InterpResult<(Value, Type)> {
    let v = value_to_scalar(input)?;
    Ok((
        Value::Numeric(if v >= 0.0 { v.sqrt() } else { 0.0 }),
        Type::Known,
    ))
}

/// Sine of an angle in degrees
pub(super) fn sind(input: &Value) -> InterpResult<(Value, Type)> {
    let v = value_to_scalar(input)?;
    Ok((Value::Numeric(v.to_radians().sin()), Type::Known))
}

/// Cosine of an angle in degrees
pub(super) fn cosd(input: &Value) -> InterpResult<(Value, Type)> {
    let v = value_to_scalar(input)?;
    Ok((Value::Numeric(v.to_radians().cos()), Type::Known))
}

pub(super) fn floor(input: &Value) -> InterpResult<(Value, Type)> {
    let v = value_to_scalar(input)?;
    Ok((Value::Numeric(v.floor()), Type::Known))
}

pub(super) fn odd(input: &Value) -> InterpResult<(Value, Type)> {
    let v = value_to_scalar(input)?;
    #[expect(
        clippy::cast_possible_truncation,
        reason = "rounding to integer for odd test"
    )]
    let rounded = v.round() as i64;
    Ok((Value::Boolean(rounded % 2 != 0), Type::Boolean))
}

pub(super) fn mexp(input: &Value) -> InterpResult<(Value, Type)> {
    let v = value_to_scalar(input)?;
    Ok((Value::Numeric(math::mexp(v)), Type::Known))
}

pub(super) fn mlog(input: &Value) -> InterpResult<(Value, Type)> {
    let v = value_to_scalar(input)?;
    Ok((Value::Numeric(math::mlog(v)), Type::Known))
}

pub(super) fn angle(input: &Value) -> InterpResult<(Value, Type)> {
    let (px, py) = value_to_pair(input)?;
    let angle = Vec2::new(px, py).direction().to_degrees();
    Ok((Value::Numeric(angle), Type::Known))
}

pub(super) fn uniform_deviate(input: &Value, random_seed: &mut u64) -> InterpResult<(Value, Type)> {
    let v = value_to_scalar(input)?;
    Ok((
        Value::Numeric(math::uniform_deviate(v, random_seed)),
        Type::Known,
    ))
}

pub(super) fn length(input: &Value) -> InterpResult<(Value, Type)> {
    let n = match input {
        Value::Path(p) => {
            #[expect(clippy::cast_precision_loss, reason = "segment count fits in f64")]
            {
                p.num_segments() as f64
            }
        }
        Value::String(s) => {
            #[expect(
                clippy::cast_precision_loss,
                reason = "string length in chars fits in f64 for practical inputs"
            )]
            {
                s.chars().count() as f64
            }
        }
        Value::Pair(x, y) => x.hypot(*y),
        Value::Numeric(v) => v.abs(),
        _ => {
            return Err(InterpreterError::new(
                ErrorKind::TypeError,
                "length requires numeric, path, string, or pair",
            ));
        }
    };
    Ok((Value::Numeric(n), Type::Known))
}

/// Explicit `*` multiplication: scalar with scalar, pair, or color
pub(super) fn times(left: &Value, right: &Value) -> InterpResult<(Value, Type)> {
    match (left, right) {
        (Value::Numeric(a), Value::Numeric(b)) => Ok((Value::Numeric(a * b), Type::Known)),
        (Value::Numeric(a), Value::Pair(bx, by)) => {
            Ok((Value::Pair(a * bx, a * by), Type::PairType))
        }
        (Value::Pair(ax, ay), Value::Numeric(b)) => {
            Ok((Value::Pair(ax * b, ay * b), Type::PairType))
        }
        (Value::Numeric(a), Value::Color(c)) => Ok((
            Value::Color(Color::new(a * c.r, a * c.g, a * c.b)),
            Type::ColorType,
        )),
        (Value::Color(c), Value::Numeric(a)) => Ok((
            Value::Color(Color::new(c.r * a, c.g * a, c.b * a)),
            Type::ColorType,
        )),
        _ => Err(InterpreterError::new(
            ErrorKind::TypeError,
            "Invalid types for *",
        )),
    }
}

/// Implicit multiplication of a numeric `factor` with the right operand
pub(super) fn implicit_mul(factor: &Value, right: &Value) -> InterpResult<(Value, Type)> {
    let a = value_to_scalar(factor)?;
    match right {
        Value::Numeric(b) => Ok((Value::Numeric(a * b), Type::Known)),
        Value::Pair(bx, by) => Ok((Value::Pair(a * bx, a * by), Type::PairType)),
        Value::Color(c) => Ok((
            Value::Color(Color::new(a * c.r, a * c.g, a * c.b)),
            Type::ColorType,
        )),
        _ => Err(InterpreterError::new(
            ErrorKind::TypeError,
            format!("Cannot multiply numeric by {}", right.ty()),
        )),
    }
}

pub(super) fn plus_minus_value(
    op: PlusMinusOp,
    left: &Value,
    right: &Value,
) -> InterpResult<(Value, Type)> {
    let is_plus = op == PlusMinusOp::Plus;

    match (left, right) {
        (Value::Numeric(a), Value::Numeric(b)) => Ok((
            Value::Numeric(if is_plus { a + b } else { a - b }),
            Type::Known,
        )),
        (Value::Pair(ax, ay), Value::Pair(bx, by)) => Ok((
            if is_plus {
                Value::Pair(ax + bx, ay + by)
            } else {
                Value::Pair(ax - bx, ay - by)
            },
            Type::PairType,
        )),
        (Value::Color(a), Value::Color(b)) => Ok((
            Value::Color(if is_plus {
                Color::new(a.r + b.r, a.g + b.g, a.b + b.b)
            } else {
                Color::new(a.r - b.r, a.g - b.g, a.b - b.b)
            }),
            Type::ColorType,
        )),
        (Value::String(a), Value::String(b)) if is_plus => Err(InterpreterError::new(
            ErrorKind::TypeError,
            format!("Cannot add strings (use & for concatenation): \"{a}\" + \"{b}\""),
        )),
        _ => Err(InterpreterError::new(
            ErrorKind::TypeError,
            format!(
                "Incompatible types for {}: {} and {}",
                if is_plus { "+" } else { "-" },
                left.ty(),
                right.ty()
            ),
        )),
    }
}

pub(super) fn tertiary_binary_value(
    op: TertiaryBinaryOp,
    left: &Value,
    right: &Value,
) -> InterpResult<(Value, Type)> {
    match op {
        // Pythagorean addition: `a ++ b = sqrt(a² + b²)`
        TertiaryBinaryOp::PythagAdd => {
            let a = value_to_scalar(left)?;
            let b = value_to_scalar(right)?;
            Ok((Value::Numeric(a.hypot(b)), Type::Known))
        }
        TertiaryBinaryOp::PythagSub => {
            let a = value_to_scalar(left)?;
            let b = value_to_scalar(right)?;
            Ok((Value::Numeric(math::pyth_sub(a, b)), Type::Known))
        }
        TertiaryBinaryOp::Or => {
            let a = value_to_bool(left)?;
            let b = value_to_bool(right)?;
            Ok((Value::Boolean(a || b), Type::Boolean))
        }
        TertiaryBinaryOp::IntersectionTimes => paths::intersection_times(left, right),
    }
}

pub(super) fn expression_binary_value(
    op: ExpressionBinaryOp,
    left: &Value,
    right: &Value,
) -> InterpResult<(Value, Type)> {
    match op {
        ExpressionBinaryOp::LessThan => Ok((
            Value::Boolean(Interpreter::compare_values(left, right, |ord| {
                ord == Ordering::Less
            })?),
            Type::Boolean,
        )),
        ExpressionBinaryOp::LessOrEqual => Ok((
            Value::Boolean(Interpreter::compare_values(left, right, |ord| {
                ord != Ordering::Greater
            })?),
            Type::Boolean,
        )),
        ExpressionBinaryOp::GreaterThan => Ok((
            Value::Boolean(Interpreter::compare_values(left, right, |ord| {
                ord == Ordering::Greater
            })?),
            Type::Boolean,
        )),
        ExpressionBinaryOp::GreaterOrEqual => Ok((
            Value::Boolean(Interpreter::compare_values(left, right, |ord| {
                ord != Ordering::Less
            })?),
            Type::Boolean,
        )),
        ExpressionBinaryOp::EqualTo => Ok((Value::Boolean(left == right), Type::Boolean)),
        ExpressionBinaryOp::UnequalTo => Ok((Value::Boolean(left != right), Type::Boolean)),
        ExpressionBinaryOp::Concatenate => strings::concatenate(left, right),
    }
}
