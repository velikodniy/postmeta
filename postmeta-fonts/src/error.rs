//! Font loading and parsing errors.

use std::fmt;

/// Errors that can occur when loading or querying fonts.
#[derive(Debug)]
pub enum FontError {
    /// The font data could not be parsed.
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
