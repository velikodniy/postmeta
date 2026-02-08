//! Token input system for the `MetaPost` interpreter.
//!
//! The input system provides a uniform stream of tokens from multiple
//! sources: source text (via the scanner), macro replacement text, loop
//! bodies, and `scantokens` strings. These are managed as a stack of
//! input levels, matching `mp.web`'s input stack.

use crate::command::Command;
use crate::scanner::Scanner;
use crate::symbols::{SymbolId, SymbolTable};
use crate::token::{Token, TokenKind};

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
        scanner: Scanner<'static>,
        /// The source text (owned for lifetime management).
        _source: String,
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
    /// A parameter expansion needs to be pushed.
    PushParam(TokenList, usize),
}

/// The token input system, managing a stack of input sources.
pub struct InputSystem {
    /// Stack of input levels (top = currently reading).
    levels: Vec<InputLevel>,
}

impl InputSystem {
    /// Create a new input system.
    #[must_use]
    pub const fn new() -> Self {
        Self { levels: Vec::new() }
    }

    /// Push a source text as a new input level.
    ///
    /// # Safety
    /// The source string is leaked to create a `'static` reference for
    /// the scanner. This is acceptable because input sources are typically
    /// file contents that live for the duration of the program.
    pub fn push_source(&mut self, source: String) {
        // Leak the string to get a 'static reference for the scanner.
        // This is intentional: source files live for the program's lifetime.
        let leaked: &'static str = Box::leak(source.clone().into_boxed_str());
        let scanner = Scanner::new(leaked);
        self.levels.push(InputLevel::Source {
            scanner,
            _source: source,
        });
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

    /// Get the next raw token from the input.
    ///
    /// This handles the input stack: when one level is exhausted,
    /// it pops back to the previous level.
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
            InputLevel::Source { scanner, .. } => {
                let token = scanner.next_token();
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
                        })
                    }
                    StoredToken::Param(idx) => {
                        let idx = *idx;
                        if idx < params.len() {
                            let param_tokens = params[idx].clone();
                            LevelAction::PushParam(param_tokens, idx)
                        } else {
                            // Bad param ref — try again
                            LevelAction::Pop
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
            }
        }
        TokenKind::Numeric(_) => ResolvedToken {
            command: Command::NumericToken,
            modifier: 0,
            sym: None,
            token: token.clone(),
        },
        TokenKind::StringLit(_) => ResolvedToken {
            command: Command::StringToken,
            modifier: 0,
            sym: None,
            token: token.clone(),
        },
        TokenKind::Eof => ResolvedToken {
            command: Command::Stop,
            modifier: 0,
            sym: None,
            token: token.clone(),
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
        input.push_source("x + 3;".to_owned());

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
        input.push_source("begingroup".to_owned());

        let t1 = input.next_raw_token(&mut symbols);
        assert_eq!(t1.command, Command::BeginGroup);

        // Should fall through to EOF
        let t2 = input.next_raw_token(&mut symbols);
        assert_eq!(t2.command, Command::Stop);
    }

    #[test]
    fn primitives_resolve() {
        let mut input = InputSystem::new();
        let mut symbols = SymbolTable::new();
        input.push_source("if true fi".to_owned());

        let t1 = input.next_raw_token(&mut symbols);
        assert_eq!(t1.command, Command::IfTest);

        let t2 = input.next_raw_token(&mut symbols);
        assert_eq!(t2.command, Command::Nullary);

        let t3 = input.next_raw_token(&mut symbols);
        assert_eq!(t3.command, Command::FiOrElse);
    }
}
