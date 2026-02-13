use std::fmt;

/// Errors returned by graphics operations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GraphicsError {
    /// `makepen` was called with an invalid path.
    InvalidPen(&'static str),
}

impl fmt::Display for GraphicsError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidPen(msg) => write!(f, "invalid pen: {msg}"),
        }
    }
}

impl std::error::Error for GraphicsError {}
