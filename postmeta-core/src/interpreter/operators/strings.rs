//! String operator evaluation

use std::sync::Arc;

use crate::error::{ErrorKind, InterpResult, InterpreterError};
use crate::interpreter::helpers::{value_to_pair, value_to_scalar, value_to_string};
use crate::types::{Type, Value};

pub(super) fn oct(input: &Value) -> InterpResult<(Value, Type)> {
    let v = value_to_scalar(input)?;
    if !v.is_finite() {
        return Err(InterpreterError::new(
            ErrorKind::TypeError,
            "oct requires a finite numeric value",
        ));
    }
    #[expect(
        clippy::cast_possible_truncation,
        reason = "integer conversion follows MetaPost-style rounding semantics"
    )]
    let n = v.round() as i64;
    Ok((Value::String(Arc::from(format!("{n:o}"))), Type::String))
}

pub(super) fn hex(input: &Value) -> InterpResult<(Value, Type)> {
    let v = value_to_scalar(input)?;
    if !v.is_finite() {
        return Err(InterpreterError::new(
            ErrorKind::TypeError,
            "hex requires a finite numeric value",
        ));
    }
    #[expect(
        clippy::cast_possible_truncation,
        reason = "integer conversion follows MetaPost-style rounding semantics"
    )]
    let n = v.round() as i64;
    Ok((Value::String(Arc::from(format!("{n:X}"))), Type::String))
}

pub(super) fn ascii(input: &Value) -> InterpResult<(Value, Type)> {
    let s = value_to_string(input)?;
    let n = s.chars().next().map_or(0.0, |ch| f64::from(u32::from(ch)));
    Ok((Value::Numeric(n), Type::Known))
}

pub(super) fn char_op(input: &Value) -> InterpResult<(Value, Type)> {
    let v = value_to_scalar(input)?;
    if !v.is_finite() {
        return Err(InterpreterError::new(
            ErrorKind::TypeError,
            "char requires a finite numeric value",
        ));
    }
    #[expect(
        clippy::cast_possible_truncation,
        reason = "character code is computed from rounded numeric"
    )]
    let rounded = v.round() as i64;
    #[expect(
        clippy::cast_possible_truncation,
        reason = "value is constrained to 0..=255 via rem_euclid"
    )]
    let code = rounded.rem_euclid(256) as u32;
    let ch = char::from_u32(code).unwrap_or('\0');
    Ok((Value::String(Arc::from(ch.to_string())), Type::String))
}

pub(super) fn decimal(input: &Value) -> InterpResult<(Value, Type)> {
    let v = value_to_scalar(input)?;
    Ok((
        Value::String(Arc::from(format!("{v}").as_str())),
        Type::String,
    ))
}

pub(super) fn substring_of(first: &Value, second: &Value) -> InterpResult<(Value, Type)> {
    let (start, end) = value_to_pair(first)?;
    let s = value_to_string(second)?;

    let chars: Vec<char> = s.chars().collect();
    #[expect(
        clippy::cast_precision_loss,
        reason = "character count fits in f64 for practical inputs"
    )]
    let char_len_f64 = chars.len() as f64;

    let clamp_idx = |v: f64| -> usize {
        if !v.is_finite() {
            return 0;
        }

        #[expect(
            clippy::cast_possible_truncation,
            reason = "index is clamped to [0, len] before cast"
        )]
        #[expect(
            clippy::cast_sign_loss,
            reason = "index is clamped to non-negative range before cast"
        )]
        {
            v.round().max(0.0).min(char_len_f64) as usize
        }
    };

    let start_idx = clamp_idx(start);
    let end_idx = clamp_idx(end);
    let substr: String = if start_idx < end_idx {
        chars[start_idx..end_idx].iter().collect()
    } else {
        String::new()
    };

    Ok((Value::String(Arc::from(substr)), Type::String))
}

pub(super) fn concatenate(left: &Value, right: &Value) -> InterpResult<(Value, Type)> {
    let a = value_to_string(left)?;
    let b = value_to_string(right)?;
    let result = format!("{a}{b}");
    Ok((Value::String(Arc::from(result)), Type::String))
}
