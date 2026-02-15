//! Value extraction and conversion helpers.
//!
//! Free functions used across all interpreter submodules.

use postmeta_graphics::path::Path;
use postmeta_graphics::types::{Pen, Scalar, Transform};

use crate::error::{ErrorKind, InterpResult, InterpreterError};
use crate::input::{CapsulePayload, StoredToken, TokenList};
use crate::symbols::SymbolTable;
use crate::types::{Type, Value};

macro_rules! impl_value_extractor {
    ($fn_name:ident, $ret:ty, $expected:literal, $pattern:pat => $result:expr) => {
        pub(super) fn $fn_name(val: &Value) -> InterpResult<$ret> {
            match val {
                $pattern => Ok($result),
                _ => Err(InterpreterError::new(
                    ErrorKind::TypeError,
                    format!("Expected {}, got {}", $expected, val.ty()),
                )),
            }
        }
    };
}

impl_value_extractor!(value_to_scalar, Scalar, "numeric", Value::Numeric(v) => *v);
impl_value_extractor!(
    value_to_pair,
    (Scalar, Scalar),
    "pair",
    Value::Pair(x, y) => (*x, *y)
);
impl_value_extractor!(value_to_bool, bool, "boolean", Value::Boolean(b) => *b);
impl_value_extractor!(value_to_path, &Path, "path", Value::Path(p) => p);

pub(super) fn value_to_path_owned(val: Value) -> InterpResult<Path> {
    match val {
        Value::Path(p) => Ok(p),
        _ => Err(InterpreterError::new(
            ErrorKind::TypeError,
            format!("Expected path, got {}", val.ty()),
        )),
    }
}

impl_value_extractor!(value_to_pen, &Pen, "pen", Value::Pen(p) => p);
impl_value_extractor!(value_to_string, String, "string", Value::String(s) => s.to_string());
impl_value_extractor!(
    value_to_transform,
    Transform,
    "transform",
    Value::Transform(t) => *t
);

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
        _ => vec![StoredToken::Capsule(CapsulePayload {
            value: val.clone(),
            ty: match val {
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
            dep: None,
            pair_dep: None,
        })],
    }
}
