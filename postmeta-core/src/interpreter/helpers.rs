//! Value extraction and conversion helpers.
//!
//! Free functions used across all interpreter submodules.

use postmeta_graphics::types::{Path, Pen, Scalar, Transform};

use crate::error::{ErrorKind, InterpResult, InterpreterError};
use crate::input::{StoredToken, TokenList};
use crate::symbols::SymbolTable;
use crate::types::Value;

pub(super) fn value_to_scalar(val: &Value) -> InterpResult<Scalar> {
    match val {
        Value::Numeric(v) => Ok(*v),
        _ => Err(InterpreterError::new(
            ErrorKind::TypeError,
            format!("Expected numeric, got {}", val.ty()),
        )),
    }
}

pub(super) fn value_to_pair(val: &Value) -> InterpResult<(Scalar, Scalar)> {
    match val {
        Value::Pair(x, y) => Ok((*x, *y)),
        _ => Err(InterpreterError::new(
            ErrorKind::TypeError,
            format!("Expected pair, got {}", val.ty()),
        )),
    }
}

pub(super) fn value_to_bool(val: &Value) -> InterpResult<bool> {
    match val {
        Value::Boolean(b) => Ok(*b),
        _ => Err(InterpreterError::new(
            ErrorKind::TypeError,
            format!("Expected boolean, got {}", val.ty()),
        )),
    }
}

pub(super) fn value_to_path(val: &Value) -> InterpResult<&Path> {
    match val {
        Value::Path(p) => Ok(p),
        _ => Err(InterpreterError::new(
            ErrorKind::TypeError,
            format!("Expected path, got {}", val.ty()),
        )),
    }
}

pub(super) fn value_to_path_owned(val: Value) -> InterpResult<Path> {
    match val {
        Value::Path(p) => Ok(p),
        _ => Err(InterpreterError::new(
            ErrorKind::TypeError,
            format!("Expected path, got {}", val.ty()),
        )),
    }
}

pub(super) fn value_to_pen(val: &Value) -> InterpResult<&Pen> {
    match val {
        Value::Pen(p) => Ok(p),
        _ => Err(InterpreterError::new(
            ErrorKind::TypeError,
            format!("Expected pen, got {}", val.ty()),
        )),
    }
}

pub(super) fn value_to_string(val: &Value) -> InterpResult<String> {
    match val {
        Value::String(s) => Ok(s.to_string()),
        _ => Err(InterpreterError::new(
            ErrorKind::TypeError,
            format!("Expected string, got {}", val.ty()),
        )),
    }
}

pub(super) fn value_to_transform(val: &Value) -> InterpResult<Transform> {
    match val {
        Value::Transform(t) => Ok(*t),
        _ => Err(InterpreterError::new(
            ErrorKind::TypeError,
            format!("Expected transform, got {}", val.ty()),
        )),
    }
}

/// Convert a runtime `Value` to a `StoredToken` for embedding in token lists.
pub(super) fn value_to_stored_token(val: &Value) -> StoredToken {
    match val {
        Value::Numeric(v) => StoredToken::Numeric(*v),
        Value::String(s) => StoredToken::StringLit(s.to_string()),
        // For non-primitive types, store as numeric 0 (best-effort)
        _ => StoredToken::Numeric(0.0),
    }
}

/// Convert a runtime `Value` to a list of `StoredToken`s that reconstruct it.
///
/// For compound types like pairs and colors, this produces the token sequence
/// `( x , y )` or `( r , g , b )`. For simple types, returns a single token.
pub(super) fn value_to_stored_tokens(val: &Value, symbols: &mut SymbolTable) -> TokenList {
    match val {
        Value::Pair(x, y) => {
            let lparen = symbols.lookup("(");
            let comma = symbols.lookup(",");
            let rparen = symbols.lookup(")");
            vec![
                StoredToken::Symbol(lparen),
                StoredToken::Numeric(*x),
                StoredToken::Symbol(comma),
                StoredToken::Numeric(*y),
                StoredToken::Symbol(rparen),
            ]
        }
        Value::Color(c) => {
            let lparen = symbols.lookup("(");
            let comma = symbols.lookup(",");
            let rparen = symbols.lookup(")");
            vec![
                StoredToken::Symbol(lparen),
                StoredToken::Numeric(c.r),
                StoredToken::Symbol(comma),
                StoredToken::Numeric(c.g),
                StoredToken::Symbol(comma),
                StoredToken::Numeric(c.b),
                StoredToken::Symbol(rparen),
            ]
        }
        _ => vec![value_to_stored_token(val)],
    }
}

pub(super) fn values_equal(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::Numeric(a), Value::Numeric(b)) => (a - b).abs() < 0.0001,
        (Value::Boolean(a), Value::Boolean(b)) => a == b,
        (Value::String(a), Value::String(b)) => a == b,
        (Value::Pair(ax, ay), Value::Pair(bx, by)) => {
            (ax - bx).abs() < 0.0001 && (ay - by).abs() < 0.0001
        }
        _ => false,
    }
}
