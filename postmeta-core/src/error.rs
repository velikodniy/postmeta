//! Error types for the `MetaPost` parser and interpreter

use std::fmt;

use crate::token::Span;

// ---------------------------------------------------------------------------
// Error severity
// ---------------------------------------------------------------------------

/// Severity level for diagnostics
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Severity {
    /// Informational message (e.g. tracing output)
    Info,
    /// Warning (execution continues)
    Warning,
    /// Error (execution may continue with recovery)
    Error,
    /// Fatal error (execution stops)
    Fatal,
}

// ---------------------------------------------------------------------------
// Error type
// ---------------------------------------------------------------------------

/// An error produced by the `MetaPost` parser or interpreter
#[derive(Debug, Clone)]
pub struct InterpreterError {
    pub kind: ErrorKind,
    pub message: String,
    pub span: Option<Span>,
    pub severity: Severity,
}

impl InterpreterError {
    #[must_use]
    pub fn new(kind: ErrorKind, message: impl Into<String>) -> Self {
        Self {
            kind,
            message: message.into(),
            span: None,
            severity: Severity::Error,
        }
    }

    #[must_use]
    pub const fn with_span(mut self, span: Span) -> Self {
        self.span = Some(span);
        self
    }

    #[must_use]
    pub const fn with_severity(mut self, severity: Severity) -> Self {
        self.severity = severity;
        self
    }
}

impl fmt::Display for InterpreterError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(span) = self.span {
            write!(f, "[{}..{}] ", span.start, span.end)?;
        }
        write!(f, "{}", self.message)
    }
}

impl std::error::Error for InterpreterError {}

// ---------------------------------------------------------------------------
// Error kinds
// ---------------------------------------------------------------------------

/// Categories of errors
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ErrorKind {
    // -- Scan errors --
    InvalidCharacter,
    UnterminatedString,

    // -- Parse errors --
    UnexpectedToken,
    MissingToken,
    UnbalancedDelimiter,
    InvalidPath,
    InvalidExpression,

    // -- Type errors --
    /// Wrong type for an operation
    TypeError,
    /// Incompatible types in an equation
    IncompatibleTypes,

    // -- Equation errors --
    /// Inconsistent equation (e.g. `0 = 1`)
    InconsistentEquation,
    /// Redundant equation (e.g. `x = x`)
    RedundantEquation,

    // -- Runtime errors --
    UndefinedVariable,
    /// Division by zero or similar
    ArithmeticError,
    MacroError,
    /// Overflow (too many equations, recursion depth, etc.)
    Overflow,
    IoError,

    // -- Control flow --
    /// `exitif` outside of a loop
    BadExitIf,

    // -- Internal --
    Internal,
}

impl fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidCharacter => write!(f, "invalid character"),
            Self::UnterminatedString => write!(f, "unterminated string"),
            Self::UnexpectedToken => write!(f, "unexpected token"),
            Self::MissingToken => write!(f, "missing token"),
            Self::UnbalancedDelimiter => write!(f, "unbalanced delimiter"),
            Self::InvalidPath => write!(f, "invalid path"),
            Self::InvalidExpression => write!(f, "invalid expression"),
            Self::TypeError => write!(f, "type error"),
            Self::IncompatibleTypes => write!(f, "incompatible types"),
            Self::InconsistentEquation => write!(f, "inconsistent equation"),
            Self::RedundantEquation => write!(f, "redundant equation"),
            Self::UndefinedVariable => write!(f, "undefined variable"),
            Self::ArithmeticError => write!(f, "arithmetic error"),
            Self::MacroError => write!(f, "macro error"),
            Self::Overflow => write!(f, "overflow"),
            Self::IoError => write!(f, "I/O error"),
            Self::BadExitIf => write!(f, "exitif outside loop"),
            Self::Internal => write!(f, "internal error"),
        }
    }
}

/// Result alias using [`InterpreterError`]
pub type InterpResult<T> = Result<T, InterpreterError>;

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn error_display() {
        let err = InterpreterError::new(ErrorKind::UnexpectedToken, "expected `;`")
            .with_span(Span::new(10, 11));
        let s = format!("{err}");
        assert!(s.contains("[10..11]"), "missing span: {s}");
        assert!(s.contains("expected `;`"), "missing message: {s}");
    }

    #[test]
    fn error_without_span() {
        let err = InterpreterError::new(ErrorKind::ArithmeticError, "division by zero");
        let s = format!("{err}");
        assert!(!s.contains('['), "should not have span: {s}");
        assert!(s.contains("division by zero"), "missing message: {s}");
    }
}
