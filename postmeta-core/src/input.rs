//! Token input system for the `MetaPost` interpreter.
//!
//! The input system provides a uniform stream of tokens from multiple
//! sources: source text (via the scanner), macro replacement text, loop
//! bodies, and `scantokens` strings. These are managed as a stack of
//! input levels, matching `mp.web`'s input stack.

use crate::command::Command;
use crate::equation::DepList;
use crate::scanner::ScanError;
use crate::scanner::Scanner;
use crate::symbols::{SymbolId, SymbolTable};
use crate::token::{Token, TokenKind};
use crate::types::{Type, Value};

/// Captured expression state used by capsule tokens.
pub type CapsulePayload = (Value, Type, Option<DepList>, Option<(DepList, DepList)>);

// ---------------------------------------------------------------------------
// Resolved token — what the parser sees after hash lookup
// ---------------------------------------------------------------------------

/// A token after symbol-table lookup, ready for parsing.
#[derive(Debug, Clone)]
pub struct ResolvedToken {
    /// The command code from the symbol table.
    pub command: Command,
    /// The modifier from the symbol table.
    pub modifier: u16,
    /// The symbol id (for variables, macros). `None` for literals.
    pub sym: Option<SymbolId>,
    /// The original token (for span info and literal values).
    pub token: Token,
    /// Capsule payload: an already-evaluated expression state.
    ///
    /// Present only when `command == CapsuleToken` and this token was produced
    /// by `back_expr`. The expression parser picks this up instead of
    /// evaluating the token normally.
    pub capsule: Option<CapsulePayload>,
}

// ---------------------------------------------------------------------------
// Stored token (for macro bodies and loop bodies)
// ---------------------------------------------------------------------------

/// A token stored in a macro body or loop iteration list.
#[derive(Debug, Clone)]
pub enum StoredToken {
    /// A symbolic token (referenced by symbol id).
    Symbol(SymbolId),
    /// A numeric literal.
    Numeric(f64),
    /// A string literal.
    StringLit(String),
    /// A macro parameter reference (index into param stack).
    Param(usize),
    /// A capsule: an already-evaluated expression pushed back for rescanning.
    ///
    /// This corresponds to `mp.web`'s `stash_cur_exp`/`back_expr` mechanism.
    /// When the expression parser needs to push a value back into the input
    /// stream (e.g., after discovering that `[` was not the start of a
    /// mediation), the value is wrapped in a capsule token.
    Capsule(Value, Type, Option<DepList>, Option<(DepList, DepList)>),
}

/// A token list (macro body, loop body, etc.).
pub type TokenList = Vec<StoredToken>;

// ---------------------------------------------------------------------------
// Input level
// ---------------------------------------------------------------------------

/// One level on the input stack.
enum InputLevel {
    /// Reading from source text.
    Source {
        /// The scanner for this source.
        scanner: Scanner,
    },
    /// Reading from a token list (macro body, loop, scantokens).
    TokenList {
        /// The tokens to read.
        tokens: TokenList,
        /// Current position in the list.
        pos: usize,
        /// Parameters for macro expansion.
        params: Vec<TokenList>,
        /// Name of this input level (for error messages).
        #[allow(dead_code)]
        name: String,
    },
}

// ---------------------------------------------------------------------------
// Input system
// ---------------------------------------------------------------------------

/// Internal action returned by `try_next_from_current`.
enum LevelAction {
    /// A token was produced.
    Token(ResolvedToken),
    /// The current level is exhausted; pop it.
    Pop,
    /// Skip current stored token and continue reading same level.
    Continue,
    /// A parameter expansion needs to be pushed.
    PushParam(TokenList, usize),
}

/// The token input system, managing a stack of input sources.
pub struct InputSystem {
    /// Stack of input levels (top = currently reading).
    levels: Vec<InputLevel>,
    /// A single token pushed back by `back_input`.
    ///
    /// When set, `next_raw_token` returns this token before reading from the
    /// input stack. Corresponds to `mp.web`'s `back_list(cur_tok)` mechanism,
    /// but simplified to a single slot since `MetaPost` never backs up more
    /// than one token at a time (multiple push-backs use token lists).
    backed_up: Option<ResolvedToken>,
    /// Scanner diagnostics collected while producing tokens.
    pending_scan_errors: Vec<ScanError>,
}

impl InputSystem {
    /// Create a new input system.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            levels: Vec::new(),
            backed_up: None,
            pending_scan_errors: Vec::new(),
        }
    }

    /// Drain scanner diagnostics gathered since the last call.
    pub fn take_scan_errors(&mut self) -> Vec<ScanError> {
        std::mem::take(&mut self.pending_scan_errors)
    }

    /// Push a source text as a new input level.
    pub fn push_source(&mut self, source: &str) {
        let scanner = Scanner::new(source);
        self.levels.push(InputLevel::Source { scanner });
    }

    /// Push a token list as a new input level (for macro expansion).
    pub fn push_token_list(&mut self, tokens: TokenList, params: Vec<TokenList>, name: String) {
        self.levels.push(InputLevel::TokenList {
            tokens,
            pos: 0,
            params,
            name,
        });
    }

    /// Push a token back into the input stream.
    ///
    /// The next call to `next_raw_token` will return this token instead of
    /// reading from the input stack. This is `mp.web`'s `back_input` — used
    /// when the parser has read one token too far and needs to "unscan" it.
    ///
    /// # Panics
    ///
    /// Debug-asserts that no token is already backed up. In `MetaPost`,
    /// `back_input` is always preceded by consuming the previously backed-up
    /// token, so double push-back indicates a logic error.
    pub fn back_input(&mut self, token: ResolvedToken) {
        debug_assert!(
            self.backed_up.is_none(),
            "back_input called while a token is already backed up"
        );
        self.backed_up = Some(token);
    }

    /// Push an already-evaluated expression back into the input stream.
    ///
    /// The value is wrapped in a `StoredToken::Capsule` and placed as a
    /// single-token input level so that the next `next_raw_token` returns a
    /// `CapsuleToken` carrying the value. This is `mp.web`'s `back_expr` —
    /// used when the expression parser needs to re-inject a computed value
    /// (e.g., after discovering that `[` was not a mediation bracket).
    pub fn back_expr(
        &mut self,
        value: Value,
        ty: Type,
        dep: Option<DepList>,
        pair_dep: Option<(DepList, DepList)>,
    ) {
        self.push_token_list(
            vec![StoredToken::Capsule(value, ty, dep, pair_dep)],
            Vec::new(),
            "backed-up expr".into(),
        );
    }

    /// Get the next raw token from the input.
    ///
    /// This handles the input stack: when one level is exhausted,
    /// it pops back to the previous level. If a token was pushed back
    /// via `back_input`, it is returned first.
    pub fn next_raw_token(&mut self, symbols: &mut SymbolTable) -> ResolvedToken {
        // Return any token that was pushed back.
        if let Some(tok) = self.backed_up.take() {
            return tok;
        }

        loop {
            if self.levels.is_empty() {
                return ResolvedToken {
                    command: Command::Stop,
                    modifier: 0,
                    sym: None,
                    token: Token {
                        kind: TokenKind::Eof,
                        span: crate::token::Span::at(0),
                    },
                    capsule: None,
                };
            }

            // Try to get a token from the current level.
            // Returns Some(result) or None (level exhausted or needs expansion).
            let action = self.try_next_from_current(symbols);

            match action {
                LevelAction::Token(tok) => return tok,
                LevelAction::Pop => {
                    self.levels.pop();
                }
                LevelAction::Continue => {}
                LevelAction::PushParam(param_tokens, idx) => {
                    self.levels.push(InputLevel::TokenList {
                        tokens: param_tokens,
                        pos: 0,
                        params: Vec::new(),
                        name: format!("param {idx}"),
                    });
                }
            }
        }
    }

    /// Try to get the next token from the current top level.
    fn try_next_from_current(&mut self, symbols: &mut SymbolTable) -> LevelAction {
        let Some(level) = self.levels.last_mut() else {
            return LevelAction::Pop;
        };

        match level {
            InputLevel::Source { scanner } => {
                let token = scanner.next_token();
                self.pending_scan_errors.extend(scanner.take_errors());
                if token.kind.is_eof() {
                    LevelAction::Pop
                } else {
                    LevelAction::Token(resolve_token(&token, symbols))
                }
            }
            InputLevel::TokenList {
                tokens,
                pos,
                params,
                ..
            } => {
                if *pos >= tokens.len() {
                    return LevelAction::Pop;
                }
                let stored = &tokens[*pos];
                *pos += 1;

                match stored {
                    StoredToken::Symbol(id) => {
                        let id = *id;
                        let entry = symbols.get(id);
                        LevelAction::Token(ResolvedToken {
                            command: entry.command,
                            modifier: entry.modifier,
                            sym: Some(id),
                            token: Token {
                                kind: TokenKind::Symbolic(symbols.name(id).to_owned()),
                                span: crate::token::Span::at(0),
                            },
                            capsule: None,
                        })
                    }
                    StoredToken::Numeric(v) => {
                        let v = *v;
                        LevelAction::Token(ResolvedToken {
                            command: Command::NumericToken,
                            modifier: 0,
                            sym: None,
                            token: Token {
                                kind: TokenKind::Numeric(v),
                                span: crate::token::Span::at(0),
                            },
                            capsule: None,
                        })
                    }
                    StoredToken::StringLit(s) => {
                        let s = s.clone();
                        LevelAction::Token(ResolvedToken {
                            command: Command::StringToken,
                            modifier: 0,
                            sym: None,
                            token: Token {
                                kind: TokenKind::StringLit(s),
                                span: crate::token::Span::at(0),
                            },
                            capsule: None,
                        })
                    }
                    StoredToken::Capsule(val, ty, dep, pair_dep) => {
                        let val = val.clone();
                        let ty = *ty;
                        let dep = dep.clone();
                        let pair_dep = pair_dep.clone();
                        LevelAction::Token(ResolvedToken {
                            command: Command::CapsuleToken,
                            modifier: 0,
                            sym: None,
                            token: Token {
                                kind: TokenKind::Symbolic("<capsule>".to_owned()),
                                span: crate::token::Span::at(0),
                            },
                            capsule: Some((val, ty, dep, pair_dep)),
                        })
                    }
                    StoredToken::Param(idx) => {
                        let idx = *idx;
                        if idx < params.len() {
                            let param_tokens = params[idx].clone();
                            LevelAction::PushParam(param_tokens, idx)
                        } else {
                            // Bad param ref — skip it and continue this level.
                            LevelAction::Continue
                        }
                    }
                }
            }
        }
    }

    /// Check if the input stack is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.levels.is_empty()
    }

    /// Current input depth (for debugging).
    #[must_use]
    pub fn depth(&self) -> usize {
        self.levels.len()
    }
}

impl Default for InputSystem {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Token resolution
// ---------------------------------------------------------------------------

/// Resolve a scanned token by looking up symbolic tokens in the symbol table.
fn resolve_token(token: &Token, symbols: &mut SymbolTable) -> ResolvedToken {
    match &token.kind {
        TokenKind::Symbolic(name) => {
            let id = symbols.lookup(name);
            let entry = symbols.get(id);
            ResolvedToken {
                command: entry.command,
                modifier: entry.modifier,
                sym: Some(id),
                token: token.clone(),
                capsule: None,
            }
        }
        TokenKind::Numeric(_) => ResolvedToken {
            command: Command::NumericToken,
            modifier: 0,
            sym: None,
            token: token.clone(),
            capsule: None,
        },
        TokenKind::StringLit(_) => ResolvedToken {
            command: Command::StringToken,
            modifier: 0,
            sym: None,
            token: token.clone(),
            capsule: None,
        },
        TokenKind::Eof => ResolvedToken {
            command: Command::Stop,
            modifier: 0,
            sym: None,
            token: token.clone(),
            capsule: None,
        },
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn source_input_basic() {
        let mut input = InputSystem::new();
        let mut symbols = SymbolTable::new();
        input.push_source("x + 3;");

        let t1 = input.next_raw_token(&mut symbols);
        assert_eq!(t1.command, Command::TagToken); // x is unknown

        let t2 = input.next_raw_token(&mut symbols);
        assert_eq!(t2.command, Command::PlusOrMinus); // +

        let t3 = input.next_raw_token(&mut symbols);
        assert_eq!(t3.command, Command::NumericToken); // 3

        let t4 = input.next_raw_token(&mut symbols);
        assert_eq!(t4.command, Command::Semicolon); // ;
    }

    #[test]
    fn token_list_input() {
        let mut input = InputSystem::new();
        let mut symbols = SymbolTable::new();

        let x_id = symbols.lookup("x");
        let tokens = vec![StoredToken::Symbol(x_id), StoredToken::Numeric(42.0)];
        input.push_token_list(tokens, Vec::new(), "test".into());

        let t1 = input.next_raw_token(&mut symbols);
        assert_eq!(t1.command, Command::TagToken);

        let t2 = input.next_raw_token(&mut symbols);
        assert_eq!(t2.command, Command::NumericToken);

        // Should get EOF-like after list exhausted
        let t3 = input.next_raw_token(&mut symbols);
        assert_eq!(t3.command, Command::Stop);
    }

    #[test]
    fn nested_input() {
        let mut input = InputSystem::new();
        let mut symbols = SymbolTable::new();

        // Base level
        input.push_source("begingroup");

        let t1 = input.next_raw_token(&mut symbols);
        assert_eq!(t1.command, Command::BeginGroup);

        // Should fall through to EOF
        let t2 = input.next_raw_token(&mut symbols);
        assert_eq!(t2.command, Command::Stop);
    }

    #[test]
    fn back_input_returns_token() {
        let mut input = InputSystem::new();
        let mut symbols = SymbolTable::new();
        input.push_source("x + y");

        // Read "x"
        let t1 = input.next_raw_token(&mut symbols);
        assert_eq!(t1.command, Command::TagToken);

        // Read "+"
        let t2 = input.next_raw_token(&mut symbols);
        assert_eq!(t2.command, Command::PlusOrMinus);

        // Push "+" back
        input.back_input(t2);

        // Next read should return "+" again
        let t2b = input.next_raw_token(&mut symbols);
        assert_eq!(t2b.command, Command::PlusOrMinus);

        // Then "y"
        let t3 = input.next_raw_token(&mut symbols);
        assert_eq!(t3.command, Command::TagToken);
    }

    #[test]
    fn back_input_with_empty_source() {
        let mut input = InputSystem::new();
        let mut symbols = SymbolTable::new();

        // Push a token back with no source
        let token = ResolvedToken {
            command: Command::NumericToken,
            modifier: 0,
            sym: None,
            token: Token {
                kind: TokenKind::Numeric(42.0),
                span: crate::token::Span::at(0),
            },
            capsule: None,
        };
        input.back_input(token);

        // Should get the backed-up token
        let t = input.next_raw_token(&mut symbols);
        assert_eq!(t.command, Command::NumericToken);
        if let TokenKind::Numeric(v) = t.token.kind {
            assert!((v - 42.0).abs() < f64::EPSILON);
        } else {
            panic!("expected numeric token");
        }

        // Then Stop (empty stack)
        let t2 = input.next_raw_token(&mut symbols);
        assert_eq!(t2.command, Command::Stop);
    }

    #[test]
    fn back_expr_produces_capsule_token() {
        use crate::types::{Type, Value};

        let mut input = InputSystem::new();
        let mut symbols = SymbolTable::new();

        // Push an expression capsule
        input.back_expr(Value::Numeric(99.0), Type::Known, None, None);

        let t = input.next_raw_token(&mut symbols);
        assert_eq!(t.command, Command::CapsuleToken);
        assert!(t.capsule.is_some());
        let (val, ty, dep, pair_dep) = t.capsule.unwrap();
        assert_eq!(ty, Type::Known);
        assert_eq!(val.as_numeric(), Some(99.0));
        assert!(dep.is_none());
        assert!(pair_dep.is_none());
    }

    #[test]
    fn back_expr_pair_roundtrip() {
        use crate::types::{Type, Value};

        let mut input = InputSystem::new();
        let mut symbols = SymbolTable::new();
        input.push_source(";");

        // Push a pair capsule
        input.back_expr(Value::Pair(3.0, 7.0), Type::PairType, None, None);

        // Should get capsule first
        let t = input.next_raw_token(&mut symbols);
        assert_eq!(t.command, Command::CapsuleToken);
        let (val, ty, dep, pair_dep) = t.capsule.unwrap();
        assert_eq!(ty, Type::PairType);
        assert_eq!(val.as_pair(), Some((3.0, 7.0)));
        assert!(dep.is_none());
        assert!(pair_dep.is_none());

        // Then ";"
        let t2 = input.next_raw_token(&mut symbols);
        assert_eq!(t2.command, Command::Semicolon);
    }

    #[test]
    fn back_input_then_back_expr() {
        use crate::types::{Type, Value};

        let mut input = InputSystem::new();
        let mut symbols = SymbolTable::new();

        // Push back an expression first (goes on token list stack)
        input.back_expr(Value::Numeric(10.0), Type::Known, None, None);

        // Then push back a token (goes in backed_up slot)
        let semicolon = ResolvedToken {
            command: Command::Semicolon,
            modifier: 0,
            sym: None,
            token: Token {
                kind: TokenKind::Symbolic(";".to_owned()),
                span: crate::token::Span::at(0),
            },
            capsule: None,
        };
        input.back_input(semicolon);

        // backed_up is returned first
        let t1 = input.next_raw_token(&mut symbols);
        assert_eq!(t1.command, Command::Semicolon);

        // Then the capsule from the token list
        let t2 = input.next_raw_token(&mut symbols);
        assert_eq!(t2.command, Command::CapsuleToken);
        assert!(t2.capsule.is_some());
    }

    #[test]
    fn primitives_resolve() {
        let mut input = InputSystem::new();
        let mut symbols = SymbolTable::new();
        input.push_source("if true fi");

        let t1 = input.next_raw_token(&mut symbols);
        assert_eq!(t1.command, Command::IfTest);

        let t2 = input.next_raw_token(&mut symbols);
        assert_eq!(t2.command, Command::Nullary);

        let t3 = input.next_raw_token(&mut symbols);
        assert_eq!(t3.command, Command::FiOrElse);
    }

    #[test]
    fn bad_param_ref_does_not_drop_token_list_level() {
        let mut input = InputSystem::new();
        let mut symbols = SymbolTable::new();

        let x = symbols.lookup("x");
        let y = symbols.lookup("y");

        input.push_token_list(
            vec![
                StoredToken::Param(1),
                StoredToken::Symbol(x),
                StoredToken::Symbol(y),
            ],
            vec![vec![StoredToken::Numeric(7.0)]],
            "bad param ref".into(),
        );

        // Invalid Param(1) should be skipped, not pop the whole level.
        let t1 = input.next_raw_token(&mut symbols);
        assert_eq!(t1.command, Command::TagToken);
        assert_eq!(symbols.name(t1.sym.expect("symbol id")), "x");

        let t2 = input.next_raw_token(&mut symbols);
        assert_eq!(t2.command, Command::TagToken);
        assert_eq!(symbols.name(t2.sym.expect("symbol id")), "y");

        let t3 = input.next_raw_token(&mut symbols);
        assert_eq!(t3.command, Command::Stop);
    }
}
