//! Token input system for the `MetaPost` interpreter.
//!
//! The input system provides a uniform stream of tokens from multiple
//! sources: source text (via the scanner), macro replacement text, loop
//! bodies, and `scantokens` strings. These are managed as a stack of
//! input levels, matching `mp.web`'s input stack.

use std::sync::Arc;

use crate::command::Command;
use crate::equation::DepList;
use crate::expr_value::ExprValue;
use crate::scanner::ScanError;
use crate::scanner::Scanner;
use crate::symbols::{SymbolId, SymbolTable};
use crate::token::{Token, TokenKind};
use crate::types::{Type, Value};

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
    pub capsule: Option<Arc<ExprValue>>,
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
    ///
    /// Wrapped in `Arc` for O(1) cloning — capsules are frequently cloned
    /// when parameter token lists are expanded.
    Capsule(Arc<ExprValue>),
}

/// A mutable token list used while building macro/loop bodies.
pub type TokenList = Vec<StoredToken>;

/// A shared, immutable token list for efficient cloning.
///
/// Macro bodies, loop bodies, and parameter token lists are cloned on
/// every invocation. Using `Arc` makes those clones O(1) reference-count
/// increments instead of O(n) deep copies.
pub type SharedTokenList = Arc<[StoredToken]>;

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
        /// The tokens to read (shared via `Arc` for cheap cloning).
        tokens: SharedTokenList,
        /// Current position in the list.
        pos: usize,
        /// Parameters for macro expansion (shared via `Arc`).
        params: Vec<SharedTokenList>,
        /// Whether this is a loop body iteration (forever/for/forsuffixes).
        /// Used by `exitif` to find and pop the current loop's input level.
        is_loop_body: bool,
    },
    /// A single token pushed back by `back_input`.
    ///
    /// Kept as its own level (as in `mp.web`, where `back_input` pushes a
    /// one-token list) so repeated push-backs stack LIFO and no token can
    /// be silently dropped.
    BackedUp(Box<ResolvedToken>),
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
    PushParam(SharedTokenList, usize),
}

/// The token input system, managing a stack of input sources.
pub struct InputSystem {
    /// Stack of input levels (top = currently reading).
    levels: Vec<InputLevel>,
    /// Scanner diagnostics collected while producing tokens.
    pending_scan_errors: Vec<ScanError>,
}

impl InputSystem {
    /// Create a new input system.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            levels: Vec::new(),
            pending_scan_errors: Vec::new(),
        }
    }

    /// Drain scanner diagnostics gathered since the last call.
    pub fn take_scan_errors(&mut self) -> Vec<ScanError> {
        std::mem::take(&mut self.pending_scan_errors)
    }

    /// Push a source text as a new input level.
    /// Number of source (scanner) levels currently on the input stack.
    ///
    /// Used to bound `input`/`scantokens` nesting so that recursive file
    /// inclusion terminates with an error instead of unbounded growth.
    #[must_use]
    pub fn source_depth(&self) -> usize {
        self.levels
            .iter()
            .filter(|l| matches!(l, InputLevel::Source { .. }))
            .count()
    }

    pub fn push_source(&mut self, source: &str) {
        let scanner = Scanner::new(source);
        self.levels.push(InputLevel::Source { scanner });
    }

    /// Push a token list as a new input level (for macro expansion).
    pub fn push_token_list(
        &mut self,
        tokens: impl Into<SharedTokenList>,
        params: Vec<SharedTokenList>,
        _name: &'static str,
    ) {
        self.levels.push(InputLevel::TokenList {
            tokens: tokens.into(),
            pos: 0,
            params,
            is_loop_body: false,
        });
    }

    /// Push a token list that is a loop body iteration.
    ///
    /// Marked so that `exitif` can find and pop it during premature exit.
    pub fn push_loop_body(&mut self, tokens: SharedTokenList, params: Vec<SharedTokenList>) {
        self.levels.push(InputLevel::TokenList {
            tokens,
            pos: 0,
            params,
            is_loop_body: true,
        });
    }

    /// Pop input levels until a loop body level is found and removed.
    ///
    /// This implements `MetaPost`'s premature loop exit: when `exitif` fires,
    /// all intervening token list levels (macro expansions, backed-up tokens,
    /// etc.) are discarded until the loop body's input level is found and popped.
    /// Source-file levels are never removed.
    ///
    /// Returns `true` if a loop body level was found and removed.
    pub fn pop_to_loop_body(&mut self) -> bool {
        // Also clear any backed-up token
        while let Some(level) = self.levels.last() {
            match level {
                InputLevel::Source { .. } => return false,
                InputLevel::BackedUp(_) => {
                    self.levels.pop();
                }
                InputLevel::TokenList { is_loop_body, .. } => {
                    let is_body = *is_loop_body;
                    self.levels.pop();
                    if is_body {
                        return true;
                    }
                }
            }
        }
        false
    }

    /// Push a token back into the input stream.
    ///
    /// The next call to `next_raw_token` will return this token instead of
    /// reading from the input stack. This is `mp.web`'s `back_input` — used
    /// when the parser has read one token too far and needs to "unscan" it.
    /// Repeated push-backs stack LIFO: the most recently backed-up token is
    /// returned first.
    pub fn back_input(&mut self, token: ResolvedToken) {
        self.levels.push(InputLevel::BackedUp(Box::new(token)));
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
        let tokens: SharedTokenList = vec![StoredToken::Capsule(Arc::new(ExprValue {
            exp: value,
            ty,
            dep,
            pair_dep,
        }))]
        .into();
        self.push_token_list(tokens, Vec::new(), "backed-up expr");
    }

    /// Get the next raw token from the input.
    ///
    /// This handles the input stack: when one level is exhausted,
    /// it pops back to the previous level. If a token was pushed back
    /// via `back_input`, it is returned first.
    pub fn next_raw_token(&mut self, symbols: &mut SymbolTable) -> ResolvedToken {
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
                LevelAction::PushParam(param_tokens, _idx) => {
                    self.levels.push(InputLevel::TokenList {
                        tokens: param_tokens,
                        pos: 0,
                        params: Vec::new(),
                        is_loop_body: false,
                    });
                }
            }
        }
    }

    /// Try to get the next token from the current top level.
    fn try_next_from_current(&mut self, symbols: &mut SymbolTable) -> LevelAction {
        if matches!(self.levels.last(), Some(InputLevel::BackedUp(_)))
            && let Some(InputLevel::BackedUp(token)) = self.levels.pop()
        {
            return LevelAction::Token(*token);
        }

        let Some(level) = self.levels.last_mut() else {
            return LevelAction::Pop;
        };

        match level {
            // Handled (and popped) above.
            InputLevel::BackedUp(_) => LevelAction::Continue,
            InputLevel::Source { scanner } => {
                let token = scanner.next_token();
                self.pending_scan_errors.extend(scanner.take_errors());
                if token.kind.is_eof() {
                    LevelAction::Pop
                } else {
                    LevelAction::Token(resolve_token(token, symbols))
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
                    other => stored_to_resolved(other, symbols)
                        .map_or(LevelAction::Continue, LevelAction::Token),
                }
            }
        }
    }

    /// Check if the input stack is empty.
    #[cfg(test)]
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.levels.is_empty()
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
///
/// Takes the token by value and moves it into the result — no clone — since
/// the caller owns the freshly-scanned token and has no further use for it.
fn resolve_token(token: Token, symbols: &mut SymbolTable) -> ResolvedToken {
    let (command, modifier, sym) = match &token.kind {
        TokenKind::Symbolic(name) => {
            let id = symbols.lookup(name);
            let entry = symbols.get(id);
            (entry.command, entry.modifier, Some(id))
        }
        TokenKind::Numeric(_) => (Command::NumericToken, 0, None),
        TokenKind::StringLit(_) => (Command::StringToken, 0, None),
        TokenKind::Capsule | TokenKind::Eof => (Command::Stop, 0, None),
    };
    ResolvedToken {
        command,
        modifier,
        sym,
        token,
        capsule: None,
    }
}

/// Resolve a stored token (from a macro body, loop, or token list) into a
/// [`ResolvedToken`].
///
/// Returns `None` for [`StoredToken::Param`]: parameter references have no
/// direct resolution — substitution pushes a new input level instead.
/// Symbol names are not materialized on this hot path; consumers that need
/// the name use `symbols.name(sym)`.
fn stored_to_resolved(stored: &StoredToken, symbols: &SymbolTable) -> Option<ResolvedToken> {
    let blank_span = crate::token::Span::at(0);
    match stored {
        StoredToken::Symbol(id) => {
            let entry = symbols.get(*id);
            Some(ResolvedToken {
                command: entry.command,
                modifier: entry.modifier,
                sym: Some(*id),
                token: Token {
                    kind: TokenKind::Symbolic(String::new()),
                    span: blank_span,
                },
                capsule: None,
            })
        }
        StoredToken::Numeric(v) => Some(ResolvedToken {
            command: Command::NumericToken,
            modifier: 0,
            sym: None,
            token: Token {
                kind: TokenKind::Numeric(*v),
                span: blank_span,
            },
            capsule: None,
        }),
        StoredToken::StringLit(s) => Some(ResolvedToken {
            command: Command::StringToken,
            modifier: 0,
            sym: None,
            token: Token {
                kind: TokenKind::StringLit(s.clone()),
                span: blank_span,
            },
            capsule: None,
        }),
        StoredToken::Capsule(payload) => Some(ResolvedToken {
            command: Command::CapsuleToken,
            modifier: 0,
            sym: None,
            token: Token {
                kind: TokenKind::Capsule,
                span: blank_span,
            },
            capsule: Some(payload.clone()),
        }),
        StoredToken::Param(_) => None,
    }
}

/// Convert a resolved token back into its storable form.
///
/// Returns `None` for tokens with no storable representation (EOF, or a
/// capsule token that lost its payload).
pub(crate) fn resolved_to_stored_token(tok: &ResolvedToken) -> Option<StoredToken> {
    if tok.command == Command::CapsuleToken {
        if let Some(payload) = &tok.capsule {
            return Some(StoredToken::Capsule(payload.clone()));
        }
        return None;
    }

    match &tok.token.kind {
        TokenKind::Symbolic(_) => tok.sym.map(StoredToken::Symbol),
        TokenKind::Numeric(v) => Some(StoredToken::Numeric(*v)),
        TokenKind::StringLit(s) => Some(StoredToken::StringLit(s.clone())),
        TokenKind::Capsule | TokenKind::Eof => None,
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
        input.push_token_list(tokens, Vec::new(), "test");

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
        let payload = t.capsule.unwrap();
        assert_eq!(payload.ty, Type::Known);
        assert_eq!(payload.exp.as_numeric(), Some(99.0));
        assert!(payload.dep.is_none());
        assert!(payload.pair_dep.is_none());
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
        let payload = t.capsule.unwrap();
        assert_eq!(payload.ty, Type::PairType);
        assert_eq!(payload.exp.as_pair(), Some((3.0, 7.0)));
        assert!(payload.dep.is_none());
        assert!(payload.pair_dep.is_none());

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

        // Then push back a token (goes on top as a BackedUp level)
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

        // The backed-up token is returned first
        let t1 = input.next_raw_token(&mut symbols);
        assert_eq!(t1.command, Command::Semicolon);

        // Then the capsule from the token list
        let t2 = input.next_raw_token(&mut symbols);
        assert_eq!(t2.command, Command::CapsuleToken);
        assert!(t2.capsule.is_some());
    }

    #[test]
    fn is_empty_accounts_for_backed_token() {
        let mut input = InputSystem::new();
        let token = ResolvedToken {
            command: Command::Semicolon,
            modifier: 0,
            sym: None,
            token: Token {
                kind: TokenKind::Symbolic(";".to_owned()),
                span: crate::token::Span::at(0),
            },
            capsule: None,
        };

        input.back_input(token);
        assert!(!input.is_empty(), "backed token means input is not empty");
    }

    #[test]
    fn back_input_twice_preserves_both_tokens() {
        let mut input = InputSystem::new();
        let mut symbols = SymbolTable::new();

        let first = ResolvedToken {
            command: Command::NumericToken,
            modifier: 0,
            sym: None,
            token: Token {
                kind: TokenKind::Numeric(1.0),
                span: crate::token::Span::at(0),
            },
            capsule: None,
        };
        let second = ResolvedToken {
            command: Command::NumericToken,
            modifier: 0,
            sym: None,
            token: Token {
                kind: TokenKind::Numeric(2.0),
                span: crate::token::Span::at(0),
            },
            capsule: None,
        };

        input.back_input(first);
        input.back_input(second);

        let t1 = input.next_raw_token(&mut symbols);
        let t2 = input.next_raw_token(&mut symbols);
        assert_eq!(t1.token.kind, TokenKind::Numeric(2.0));
        assert_eq!(t2.token.kind, TokenKind::Numeric(1.0));
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
            vec![SharedTokenList::from(vec![StoredToken::Numeric(7.0)])],
            "bad param ref",
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
