//! Token types for the `MetaPost` scanner
//!
//! The scanner produces three kinds of tokens:
//! - **Symbolic**: identifiers and multi-character operators, looked up by name
//! - **Numeric**: floating-point constants, always non-negative (`-` is a separate token)
//! - **String**: text delimited by `"..."` (no escape sequences)
//!
//! Meaning (keyword, variable, or operator) is determined later by hash-table lookup, not at the scanner level.

use postmeta_graphics::types::Scalar;

// ---------------------------------------------------------------------------
// Source location
// ---------------------------------------------------------------------------

/// A byte-offset span in the source input
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    /// Start byte offset (inclusive)
    pub start: usize,
    /// End byte offset (exclusive)
    pub end: usize,
}

impl Span {
    #[must_use]
    pub const fn new(start: usize, end: usize) -> Self {
        Self { start, end }
    }

    /// A zero-length span at the given position
    #[must_use]
    pub const fn at(pos: usize) -> Self {
        Self {
            start: pos,
            end: pos,
        }
    }

    #[must_use]
    pub const fn len(&self) -> usize {
        self.end - self.start
    }

    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.start == self.end
    }
}

// ---------------------------------------------------------------------------
// Token
// ---------------------------------------------------------------------------

/// A lexical token produced by the scanner
#[derive(Debug, Clone, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

/// The kind and payload of a token
#[derive(Debug, Clone, PartialEq)]
pub enum TokenKind {
    /// An identifier, operator, or punctuation, looked up by name in the hash table
    ///
    /// Primitives like `begingroup`, operators like `<=`, and user variables like `x` are all symbolic tokens.
    Symbolic(String),

    /// A non-negative numeric constant
    ///
    /// `MetaPost` has no negative numeric literals; `-3` is unary minus applied to `3`.
    Numeric(Scalar),

    /// A string literal delimited by `"..."` (no escape processing)
    StringLit(String),

    /// A capsule token carrying an already-evaluated expression
    ///
    /// Used when the expression parser pushes a value back into the input stream.
    /// Avoids allocating a `String` for the display name.
    Capsule,

    Eof,
}

impl TokenKind {
    #[must_use]
    pub fn is_sym(&self, name: &str) -> bool {
        matches!(self, Self::Symbolic(s) if s == name)
    }

    #[must_use]
    pub const fn is_numeric(&self) -> bool {
        matches!(self, Self::Numeric(_))
    }

    #[must_use]
    pub const fn is_string(&self) -> bool {
        matches!(self, Self::StringLit(_))
    }

    #[must_use]
    pub const fn is_eof(&self) -> bool {
        matches!(self, Self::Eof)
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn span_basics() {
        let s = Span::new(10, 20);
        assert_eq!(s.len(), 10);
        assert!(!s.is_empty());

        let z = Span::at(5);
        assert_eq!(z.len(), 0);
        assert!(z.is_empty());
    }

    #[test]
    fn token_kind_predicates() {
        assert!(TokenKind::Symbolic("if".into()).is_sym("if"));
        assert!(!TokenKind::Symbolic("if".into()).is_sym("fi"));
        assert!(TokenKind::Numeric(3.14).is_numeric());
        assert!(TokenKind::StringLit("hello".into()).is_string());
        assert!(TokenKind::Eof.is_eof());
    }
}
