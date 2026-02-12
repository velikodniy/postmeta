//! Lexical scanner for `MetaPost` source code.
//!
//! Implements the character-class–based tokenizer from the original
//! `MetaPost` WEB source. Characters are grouped into classes; consecutive
//! characters of the same class (with exceptions for "isolated" classes)
//! merge into a single symbolic token.
//!
//! # Token production rules
//!
//! | Input              | Token produced                            |
//! |--------------------|-------------------------------------------|
//! | `123`, `3.14`, `.5`  | `Numeric(value)`                            |
//! | `"hello"`            | `StringLit("hello")`                        |
//! | `abc`, `x_1`         | `Symbolic("abc")`, `Symbolic("x_1")`          |
//! | `<=`, `:=`, `..`     | `Symbolic("<=")`, `Symbolic(":=")`, `Symbolic("..")`  |
//! | `(`, `)`, `,`, `;`   | `Symbolic("(")`, etc. (isolated, never merge) |
//! | `% comment`          | Skipped to end of line                    |
//! | lone `.`             | Silently ignored                          |
//! | end of input       | `Eof`                                       |

use crate::token::{Span, Token, TokenKind};

// ---------------------------------------------------------------------------
// Character classes (mirrors mp.web §64)
// ---------------------------------------------------------------------------

/// Character class assignments. Index by byte value.
const fn char_class(c: u8) -> u8 {
    match c {
        b'0'..=b'9' => DIGIT,
        b'.' => PERIOD,
        b' ' | b'\t' | b'\r' | b'\n' | 0x0C => SPACE,
        b'%' => PERCENT,
        b'"' => STRING_DELIM,
        b',' => COMMA,
        b';' => SEMICOLON,
        b'(' => LEFT_PAREN,
        b')' => RIGHT_PAREN,
        b'A'..=b'Z' | b'a'..=b'z' | b'_' => LETTER,
        b'<' | b'=' | b'>' | b':' | b'|' => COMPARISON,
        b'`' | b'\'' => QUOTE,
        b'+' | b'-' => PLUS_MINUS,
        b'*' | b'/' | b'\\' => MUL_DIV,
        b'!' | b'?' => BANG_QUESTION,
        b'#' | b'&' | b'@' | b'$' => HASH_AMP,
        b'^' | b'~' => CARET_TILDE,
        b'[' => LEFT_BRACKET,
        b']' => RIGHT_BRACKET,
        b'{' | b'}' => BRACE,
        _ => INVALID,
    }
}

const DIGIT: u8 = 0;
const PERIOD: u8 = 1;
const SPACE: u8 = 2;
const PERCENT: u8 = 3;
const STRING_DELIM: u8 = 4;
const COMMA: u8 = 5;
const SEMICOLON: u8 = 6;
const LEFT_PAREN: u8 = 7;
const RIGHT_PAREN: u8 = 8;
const LETTER: u8 = 9;
const COMPARISON: u8 = 10;
const QUOTE: u8 = 11;
const PLUS_MINUS: u8 = 12;
const MUL_DIV: u8 = 13;
const BANG_QUESTION: u8 = 14;
const HASH_AMP: u8 = 15;
const CARET_TILDE: u8 = 16;
const LEFT_BRACKET: u8 = 17;
const RIGHT_BRACKET: u8 = 18;
const BRACE: u8 = 19;
const INVALID: u8 = 20;

/// Classes that always produce a single-character token.
const fn is_isolated(class: u8) -> bool {
    matches!(class, COMMA | SEMICOLON | LEFT_PAREN | RIGHT_PAREN)
}

// ---------------------------------------------------------------------------
// Scanner error
// ---------------------------------------------------------------------------

/// An error encountered during scanning.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScanErrorKind {
    InvalidCharacter,
    UnterminatedString,
}

/// An error encountered during scanning.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScanError {
    /// Machine-readable error kind.
    pub kind: ScanErrorKind,
    /// Human-readable error message.
    pub message: String,
    /// Location of the error.
    pub span: Span,
}

impl std::fmt::Display for ScanError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "scan error at {}-{}: {}",
            self.span.start, self.span.end, self.message
        )
    }
}

impl std::error::Error for ScanError {}

// ---------------------------------------------------------------------------
// Scanner
// ---------------------------------------------------------------------------

/// Lexical scanner for `MetaPost` source.
pub struct Scanner {
    /// Source bytes (owned).
    src: Vec<u8>,
    /// Current byte position.
    pos: usize,
    /// Accumulated errors (non-fatal).
    errors: Vec<ScanError>,
}

impl Scanner {
    /// Create a new scanner over the given source string.
    #[must_use]
    pub fn new(source: &str) -> Self {
        Self {
            src: source.as_bytes().to_vec(),
            pos: 0,
            errors: Vec::new(),
        }
    }

    /// Scan the next token.
    pub fn next_token(&mut self) -> Token {
        loop {
            self.skip_whitespace_and_comments();

            if self.pos >= self.src.len() {
                let pos = u32_pos(self.pos);
                return Token {
                    kind: TokenKind::Eof,
                    span: Span::at(pos),
                };
            }

            let start = self.pos;
            let c = self.src[self.pos];
            let class = char_class(c);

            match class {
                DIGIT => return self.scan_number(start),
                PERIOD => {
                    // Look ahead to decide: number, path join, or ignore
                    if let Some(tok) = self.scan_period(start) {
                        return tok;
                    }
                    // Lone period — silently ignored, loop again
                }
                STRING_DELIM => return self.scan_string(start),
                INVALID => {
                    self.pos += 1;
                    self.errors.push(ScanError {
                        kind: ScanErrorKind::InvalidCharacter,
                        message: format!("invalid character: {c:#04x}"),
                        span: Span::new(u32_pos(start), u32_pos(self.pos)),
                    });
                }
                _ => return self.scan_symbolic(start, class),
            }
        }
    }

    /// Scan all remaining tokens (including `Eof`).
    #[cfg(test)]
    pub fn scan_all(&mut self) -> Vec<Token> {
        let mut tokens = Vec::new();
        loop {
            let tok = self.next_token();
            let is_eof = tok.kind.is_eof();
            tokens.push(tok);
            if is_eof {
                break;
            }
        }
        tokens
    }

    /// Return accumulated scan errors.
    #[cfg(test)]
    #[must_use]
    pub fn errors(&self) -> &[ScanError] {
        &self.errors
    }

    /// Drain accumulated scan errors.
    pub fn take_errors(&mut self) -> Vec<ScanError> {
        std::mem::take(&mut self.errors)
    }

    // -- internal helpers --

    /// Skip whitespace and `%`-comments.
    fn skip_whitespace_and_comments(&mut self) {
        while self.pos < self.src.len() {
            let c = self.src[self.pos];
            let class = char_class(c);

            if class == SPACE {
                self.pos += 1;
            } else if class == PERCENT {
                // Skip to end of line
                while self.pos < self.src.len() && self.src[self.pos] != b'\n' {
                    self.pos += 1;
                }
                // Skip the newline itself
                if self.pos < self.src.len() {
                    self.pos += 1;
                }
            } else {
                break;
            }
        }
    }

    /// Scan a numeric token starting at `start`.
    ///
    /// Called when the character at `start` is a digit.
    fn scan_number(&mut self, start: usize) -> Token {
        // Integer part
        while self.pos < self.src.len() && char_class(self.src[self.pos]) == DIGIT {
            self.pos += 1;
        }

        // Check for fractional part: `.` followed by a digit
        if self.pos < self.src.len()
            && self.src[self.pos] == b'.'
            && self.pos + 1 < self.src.len()
            && char_class(self.src[self.pos + 1]) == DIGIT
        {
            self.pos += 1; // consume '.'
            while self.pos < self.src.len() && char_class(self.src[self.pos]) == DIGIT {
                self.pos += 1;
            }
        }

        let text = &self.src[start..self.pos];
        // SAFETY: text is guaranteed to be ASCII digits and at most one '.'
        let s = std::str::from_utf8(text).unwrap_or("0");
        let value = s.parse::<f64>().unwrap_or(0.0);

        Token {
            kind: TokenKind::Numeric(value),
            span: Span::new(u32_pos(start), u32_pos(self.pos)),
        }
    }

    /// Handle a period character.
    ///
    /// Returns `Some(token)` if the period starts a number (`.5`) or a
    /// multi-period symbolic token (`..`, `...`). Returns `None` if the
    /// period should be silently ignored.
    fn scan_period(&mut self, start: usize) -> Option<Token> {
        self.pos += 1; // consume the first '.'

        if self.pos < self.src.len() {
            let next_class = char_class(self.src[self.pos]);

            if next_class == DIGIT {
                // `.5` → numeric token starting with `0.`
                return Some(self.scan_decimal_after_dot(start));
            }

            if next_class == PERIOD {
                // `..` always forms a token.
                // `...` forms a token only when there isn't a fourth period;
                // for longer runs we split as `..`, `..`, ... to match MetaPost.
                self.pos += 1; // consume the second '.'
                if self.pos < self.src.len()
                    && char_class(self.src[self.pos]) == PERIOD
                    && (self.pos + 1 >= self.src.len()
                        || char_class(self.src[self.pos + 1]) != PERIOD)
                {
                    self.pos += 1; // consume a third '.' only for exact `...`
                }
                let text = std::str::from_utf8(&self.src[start..self.pos]).unwrap_or("..");
                return Some(Token {
                    kind: TokenKind::Symbolic(text.to_owned()),
                    span: Span::new(u32_pos(start), u32_pos(self.pos)),
                });
            }
        }

        // Lone period: silently ignored (MetaPost behavior)
        None
    }

    /// Scan the fractional part of a number after the leading `.` has
    /// been consumed. `start` points to the `.`.
    fn scan_decimal_after_dot(&mut self, start: usize) -> Token {
        // Consume digits after the dot
        while self.pos < self.src.len() && char_class(self.src[self.pos]) == DIGIT {
            self.pos += 1;
        }

        let text = &self.src[start..self.pos];
        let s = std::str::from_utf8(text).unwrap_or("0");
        let value = s.parse::<f64>().unwrap_or(0.0);

        Token {
            kind: TokenKind::Numeric(value),
            span: Span::new(u32_pos(start), u32_pos(self.pos)),
        }
    }

    /// Scan a string literal. The opening `"` is at `self.pos`.
    fn scan_string(&mut self, start: usize) -> Token {
        self.pos += 1; // skip opening '"'

        let content_start = self.pos;
        // Scan until closing `"` or end of line
        while self.pos < self.src.len() && self.src[self.pos] != b'"' && self.src[self.pos] != b'\n'
        {
            self.pos += 1;
        }

        let content = &self.src[content_start..self.pos];

        if self.pos < self.src.len() && self.src[self.pos] == b'"' {
            self.pos += 1; // skip closing '"'
        } else {
            // Unterminated string
            self.errors.push(ScanError {
                kind: ScanErrorKind::UnterminatedString,
                message: "unterminated string literal".into(),
                span: Span::new(u32_pos(start), u32_pos(self.pos)),
            });
        }

        let text = String::from_utf8_lossy(content).into_owned();
        Token {
            kind: TokenKind::StringLit(text),
            span: Span::new(u32_pos(start), u32_pos(self.pos)),
        }
    }

    /// Scan a symbolic token. For isolated classes, produces a
    /// single-character token. For others, merges consecutive
    /// same-class characters.
    fn scan_symbolic(&mut self, start: usize, class: u8) -> Token {
        if is_isolated(class) {
            self.pos += 1;
            let text = std::str::from_utf8(&self.src[start..self.pos]).unwrap_or("?");
            return Token {
                kind: TokenKind::Symbolic(text.to_owned()),
                span: Span::new(u32_pos(start), u32_pos(self.pos)),
            };
        }

        // Merge consecutive characters of the same class
        while self.pos < self.src.len() && char_class(self.src[self.pos]) == class {
            self.pos += 1;
        }

        let text = std::str::from_utf8(&self.src[start..self.pos]).unwrap_or("?");
        Token {
            kind: TokenKind::Symbolic(text.to_owned()),
            span: Span::new(u32_pos(start), u32_pos(self.pos)),
        }
    }
}

/// Convert a `usize` position to `u32` for [`Span`].
///
/// Clamps to `u32::MAX` for sources larger than 4 GiB (unreachable in
/// practice for `MetaPost` programs).
#[expect(
    clippy::cast_possible_truncation,
    reason = "explicitly clamped to u32::MAX before cast"
)]
const fn u32_pos(pos: usize) -> u32 {
    if pos > u32::MAX as usize {
        u32::MAX
    } else {
        pos as u32
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn scan(input: &str) -> Vec<Token> {
        Scanner::new(input).scan_all()
    }

    fn kinds(input: &str) -> Vec<TokenKind> {
        scan(input).into_iter().map(|t| t.kind).collect()
    }

    // -- whitespace and comments --

    #[test]
    fn empty_input() {
        let tokens = kinds("");
        assert_eq!(tokens, vec![TokenKind::Eof]);
    }

    #[test]
    fn whitespace_only() {
        let tokens = kinds("   \t\n  ");
        assert_eq!(tokens, vec![TokenKind::Eof]);
    }

    #[test]
    fn comment_skipped() {
        let tokens = kinds("abc % this is a comment\ndef");
        assert_eq!(
            tokens,
            vec![
                TokenKind::Symbolic("abc".into()),
                TokenKind::Symbolic("def".into()),
                TokenKind::Eof,
            ]
        );
    }

    // -- numeric tokens --

    #[test]
    fn integer() {
        let tokens = kinds("42");
        assert_eq!(tokens, vec![TokenKind::Numeric(42.0), TokenKind::Eof]);
    }

    #[test]
    fn decimal() {
        let tokens = kinds("3.14");
        assert_eq!(tokens, vec![TokenKind::Numeric(3.14), TokenKind::Eof]);
    }

    #[test]
    fn leading_dot_number() {
        let tokens = kinds(".5");
        assert_eq!(tokens, vec![TokenKind::Numeric(0.5), TokenKind::Eof]);
    }

    #[test]
    fn number_dot_number() {
        // "1.2.3" → 1.2 then .3 (the second dot starts a new decimal)
        let tokens = kinds("1.2.3");
        assert_eq!(
            tokens,
            vec![
                TokenKind::Numeric(1.2),
                TokenKind::Numeric(0.3),
                TokenKind::Eof,
            ]
        );
    }

    // -- string tokens --

    #[test]
    fn simple_string() {
        let tokens = kinds("\"hello\"");
        assert_eq!(
            tokens,
            vec![TokenKind::StringLit("hello".into()), TokenKind::Eof]
        );
    }

    #[test]
    fn empty_string() {
        let tokens = kinds("\"\"");
        assert_eq!(
            tokens,
            vec![TokenKind::StringLit(String::new()), TokenKind::Eof]
        );
    }

    #[test]
    fn unterminated_string() {
        let mut scanner = Scanner::new("\"hello\nworld");
        let tokens = scanner.scan_all();
        // String terminates at newline
        assert_eq!(tokens[0].kind, TokenKind::StringLit("hello".into()));
        // "world" is a separate symbolic token
        assert_eq!(tokens[1].kind, TokenKind::Symbolic("world".into()));
        assert_eq!(scanner.errors().len(), 1);
        assert_eq!(scanner.errors()[0].kind, ScanErrorKind::UnterminatedString);
    }

    #[test]
    fn invalid_character_error_kind() {
        let mut scanner = Scanner::new("abc\u{7f}def");
        let _ = scanner.scan_all();
        assert_eq!(scanner.errors().len(), 1);
        assert_eq!(scanner.errors()[0].kind, ScanErrorKind::InvalidCharacter);
    }

    // -- symbolic tokens --

    #[test]
    fn identifier() {
        let tokens = kinds("begingroup");
        assert_eq!(
            tokens,
            vec![TokenKind::Symbolic("begingroup".into()), TokenKind::Eof]
        );
    }

    #[test]
    fn identifier_with_underscore() {
        let tokens = kinds("x_pos");
        assert_eq!(
            tokens,
            vec![TokenKind::Symbolic("x_pos".into()), TokenKind::Eof]
        );
    }

    #[test]
    fn identifier_followed_by_digit() {
        // x2 → two tokens: "x" and 2.0 (digits don't merge with letters)
        let tokens = kinds("x2");
        assert_eq!(
            tokens,
            vec![
                TokenKind::Symbolic("x".into()),
                TokenKind::Numeric(2.0),
                TokenKind::Eof,
            ]
        );
    }

    // -- isolated single-character tokens --

    #[test]
    fn isolated_tokens() {
        let tokens = kinds("(a,b);");
        assert_eq!(
            tokens,
            vec![
                TokenKind::Symbolic("(".into()),
                TokenKind::Symbolic("a".into()),
                TokenKind::Symbolic(",".into()),
                TokenKind::Symbolic("b".into()),
                TokenKind::Symbolic(")".into()),
                TokenKind::Symbolic(";".into()),
                TokenKind::Eof,
            ]
        );
    }

    // -- multi-character operator merging --

    #[test]
    fn comparison_operators() {
        let tokens = kinds("<= >= <> :=");
        assert_eq!(
            tokens,
            vec![
                TokenKind::Symbolic("<=".into()),
                TokenKind::Symbolic(">=".into()),
                TokenKind::Symbolic("<>".into()),
                TokenKind::Symbolic(":=".into()),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn path_join() {
        let tokens = kinds("a..b");
        assert_eq!(
            tokens,
            vec![
                TokenKind::Symbolic("a".into()),
                TokenKind::Symbolic("..".into()),
                TokenKind::Symbolic("b".into()),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn three_dots() {
        let tokens = kinds("a...b");
        assert_eq!(
            tokens,
            vec![
                TokenKind::Symbolic("a".into()),
                TokenKind::Symbolic("...".into()),
                TokenKind::Symbolic("b".into()),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn four_dots_split_into_two_path_joins() {
        let tokens = kinds("a....b");
        assert_eq!(
            tokens,
            vec![
                TokenKind::Symbolic("a".into()),
                TokenKind::Symbolic("..".into()),
                TokenKind::Symbolic("..".into()),
                TokenKind::Symbolic("b".into()),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn plus_minus_operators() {
        let tokens = kinds("++ +-+");
        assert_eq!(
            tokens,
            vec![
                TokenKind::Symbolic("++".into()),
                TokenKind::Symbolic("+-+".into()),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn lone_period_ignored() {
        // A period followed by a space or letter is silently ignored
        let tokens = kinds(". a");
        assert_eq!(
            tokens,
            vec![TokenKind::Symbolic("a".into()), TokenKind::Eof]
        );
    }

    #[test]
    fn brackets_and_braces() {
        let tokens = kinds("[]{} ");
        assert_eq!(
            tokens,
            vec![
                TokenKind::Symbolic("[".into()),
                TokenKind::Symbolic("]".into()),
                TokenKind::Symbolic("{}".into()),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn ampersand() {
        let tokens = kinds("a & b");
        assert_eq!(
            tokens,
            vec![
                TokenKind::Symbolic("a".into()),
                TokenKind::Symbolic("&".into()),
                TokenKind::Symbolic("b".into()),
                TokenKind::Eof,
            ]
        );
    }

    // -- span tracking --

    #[test]
    fn spans_are_correct() {
        let tokens = scan("ab 3.5");
        assert_eq!(tokens[0].span, Span::new(0, 2)); // "ab"
        assert_eq!(tokens[1].span, Span::new(3, 6)); // "3.5"
    }

    // -- combined expression --

    #[test]
    fn realistic_expression() {
        let tokens = kinds("z1..controls z2 and z3..z4");
        assert_eq!(
            tokens,
            vec![
                TokenKind::Symbolic("z".into()),
                TokenKind::Numeric(1.0),
                TokenKind::Symbolic("..".into()),
                TokenKind::Symbolic("controls".into()),
                TokenKind::Symbolic("z".into()),
                TokenKind::Numeric(2.0),
                TokenKind::Symbolic("and".into()),
                TokenKind::Symbolic("z".into()),
                TokenKind::Numeric(3.0),
                TokenKind::Symbolic("..".into()),
                TokenKind::Symbolic("z".into()),
                TokenKind::Numeric(4.0),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn draw_statement() {
        let tokens = kinds("draw (0,0)..(10,0);");
        assert_eq!(
            tokens,
            vec![
                TokenKind::Symbolic("draw".into()),
                TokenKind::Symbolic("(".into()),
                TokenKind::Numeric(0.0),
                TokenKind::Symbolic(",".into()),
                TokenKind::Numeric(0.0),
                TokenKind::Symbolic(")".into()),
                TokenKind::Symbolic("..".into()),
                TokenKind::Symbolic("(".into()),
                TokenKind::Numeric(10.0),
                TokenKind::Symbolic(",".into()),
                TokenKind::Numeric(0.0),
                TokenKind::Symbolic(")".into()),
                TokenKind::Symbolic(";".into()),
                TokenKind::Eof,
            ]
        );
    }

    // -- edge cases --

    #[test]
    fn consecutive_strings() {
        let tokens = kinds("\"a\"\"b\"");
        assert_eq!(
            tokens,
            vec![
                TokenKind::StringLit("a".into()),
                TokenKind::StringLit("b".into()),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn number_after_paren() {
        let tokens = kinds("(3)");
        assert_eq!(
            tokens,
            vec![
                TokenKind::Symbolic("(".into()),
                TokenKind::Numeric(3.0),
                TokenKind::Symbolic(")".into()),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn slash_and_star() {
        // Both are class MUL_DIV, so they merge
        let tokens = kinds("/*");
        assert_eq!(
            tokens,
            vec![TokenKind::Symbolic("/*".into()), TokenKind::Eof]
        );
    }

    #[test]
    fn slash_alone() {
        let tokens = kinds("a/b");
        assert_eq!(
            tokens,
            vec![
                TokenKind::Symbolic("a".into()),
                TokenKind::Symbolic("/".into()),
                TokenKind::Symbolic("b".into()),
                TokenKind::Eof,
            ]
        );
    }
}
