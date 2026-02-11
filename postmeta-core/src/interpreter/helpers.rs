//! Value extraction and conversion helpers.
//!
//! Free functions used across all interpreter submodules.

use postmeta_graphics::types::{Path, Pen, Scalar, Transform};

use crate::error::{ErrorKind, InterpResult, InterpreterError};
use crate::input::{StoredToken, TokenList};
use crate::symbols::SymbolTable;
use crate::types::{Type, Value, NUMERIC_TOLERANCE};

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

/// Convert a runtime `Value` to a list of `StoredToken`s that reconstruct it.
///
/// For compound types like pairs and colors, this produces the token sequence
/// `( x , y )` or `( r , g , b )`. For simple types, returns a single capsule
/// or string literal token.
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
        Value::String(s) => vec![StoredToken::StringLit(s.to_string())],
        _ => vec![StoredToken::Capsule(
            val.clone(),
            match val {
                Value::Numeric(_) => Type::Known,
                Value::Boolean(_) => Type::Boolean,
                Value::Transform(..) => Type::TransformType,
                Value::Path(..) => Type::Path,
                Value::Pen(..) => Type::Pen,
                Value::Picture(..) => Type::Picture,
                // Pair and Color are handled above; String has its own arm.
                // Vacuous and any remaining variants fall here.
                _ => Type::Vacuous,
            },
        )],
    }
}

pub(super) fn values_equal(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::Numeric(a), Value::Numeric(b)) => (a - b).abs() < NUMERIC_TOLERANCE,
        (Value::Boolean(a), Value::Boolean(b)) => a == b,
        (Value::String(a), Value::String(b)) => a == b,
        (Value::Pair(ax, ay), Value::Pair(bx, by)) => {
            (ax - bx).abs() < NUMERIC_TOLERANCE && (ay - by).abs() < NUMERIC_TOLERANCE
        }
        _ => false,
    }
}
