//! Font loading and parsing errors

use std::fmt;

/// Errors from loading or querying fonts
#[derive(Debug)]
pub enum FontError {
    ParseError(String),
}

impl fmt::Display for FontError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ParseError(msg) => write!(f, "font parse error: {msg}"),
        }
    }
}

impl std::error::Error for FontError {}
