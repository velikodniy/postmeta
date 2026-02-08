//! Symbol table for the `MetaPost` interpreter.
//!
//! The symbol table maps symbolic token names to their meaning:
//! - **Primitives** have a fixed `(Command, u16)` pair
//! - **Variables** (tags) start as `TagToken` and gain structure through
//!   type declarations and equations
//! - **Macros** store a reference to their definition token list
//!
//! This corresponds to `mp.web`'s `hash` and `eqtb` arrays, but uses a
//! `HashMap` for the name→id mapping and a `Vec` for the eqtb entries.

use std::collections::HashMap;

use crate::command::{Command, PRIMITIVES};

// ---------------------------------------------------------------------------
// Symbol identifier
// ---------------------------------------------------------------------------

/// A unique identifier for a symbol in the table.
///
/// The first 256 ids (0–255) are reserved for single-byte characters.
/// Ids 256+ are for multi-character symbolic tokens.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SymbolId(u32);

impl SymbolId {
    /// The null/invalid symbol.
    pub const INVALID: Self = Self(u32::MAX);

    /// Get the raw numeric id.
    #[must_use]
    pub const fn raw(self) -> u32 {
        self.0
    }
}

// ---------------------------------------------------------------------------
// Frozen symbol constants
// ---------------------------------------------------------------------------

/// Reserved symbol ids for tokens that can never be redefined.
/// These correspond to `mp.web`'s `frozen_*` constants.
pub mod frozen {
    use super::SymbolId;

    /// Start of frozen id range. We reserve these at the high end.
    const BASE: u32 = u32::MAX - 100;

    /// Internal inaccessible symbol.
    pub const INACCESSIBLE: SymbolId = SymbolId(BASE);
    /// Internal repeat-loop token.
    pub const REPEAT_LOOP: SymbolId = SymbolId(BASE + 1);
    /// Frozen right delimiter for error recovery.
    pub const RIGHT_DELIMITER: SymbolId = SymbolId(BASE + 2);
    /// Frozen `[` for error recovery.
    pub const LEFT_BRACKET: SymbolId = SymbolId(BASE + 3);
    /// Frozen `/` for fraction handling.
    pub const SLASH: SymbolId = SymbolId(BASE + 4);
    /// Frozen `:` for label handling.
    pub const COLON: SymbolId = SymbolId(BASE + 5);
    /// Frozen `;` for error recovery.
    pub const SEMICOLON: SymbolId = SymbolId(BASE + 6);
    /// Frozen `endfor`.
    pub const END_FOR: SymbolId = SymbolId(BASE + 7);
    /// Frozen `enddef`.
    pub const END_DEF: SymbolId = SymbolId(BASE + 8);
    /// Frozen `fi`.
    pub const FI: SymbolId = SymbolId(BASE + 9);
    /// Frozen `endgroup`.
    pub const END_GROUP: SymbolId = SymbolId(BASE + 10);
    /// Frozen `etex`.
    pub const ETEX: SymbolId = SymbolId(BASE + 11);
    /// Frozen undefined symbol.
    pub const UNDEFINED: SymbolId = SymbolId(BASE + 14);
}

// ---------------------------------------------------------------------------
// Symbol entry (the "eqtb" equivalent)
// ---------------------------------------------------------------------------

/// The meaning of a symbol: its command code and modifier.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SymbolEntry {
    /// The command code — what this symbol does syntactically.
    pub command: Command,
    /// Modifier further identifying the specific operation.
    pub modifier: u16,
}

impl SymbolEntry {
    /// A tag token (unresolved variable name) with no value yet.
    pub const TAG: Self = Self {
        command: Command::TagToken,
        modifier: 0,
    };

    /// An undefined symbol.
    pub const UNDEFINED: Self = Self {
        command: Command::TagToken,
        modifier: 0,
    };
}

// ---------------------------------------------------------------------------
// Symbol table
// ---------------------------------------------------------------------------

/// The symbol table: maps names to ids and ids to meanings.
#[derive(Debug)]
pub struct SymbolTable {
    /// Name → id mapping.
    name_to_id: HashMap<String, SymbolId>,
    /// Id → (name, entry). Index is `id.0` for ids >= 256.
    /// Single-byte chars (0–255) are looked up directly.
    entries: Vec<(String, SymbolEntry)>,
    /// Single-byte character entries (indices 0–255).
    char_entries: [SymbolEntry; 256],
    /// Next available id.
    next_id: u32,
}

impl SymbolTable {
    /// Maximum number of user symbols (not counting single-byte chars).
    const MAX_SYMBOLS: u32 = 100_000;

    /// Create a new symbol table with all primitives pre-registered.
    #[must_use]
    pub fn new() -> Self {
        let mut table = Self {
            name_to_id: HashMap::with_capacity(512),
            entries: Vec::with_capacity(512),
            char_entries: [SymbolEntry::TAG; 256],
            next_id: 256,
        };

        // Register all engine primitives
        for prim in PRIMITIVES {
            table.register_primitive(prim.name, prim.command, prim.modifier);
        }

        // Register single-character punctuation that the scanner produces
        table.register_char_primitive(b'(', Command::LeftDelimiter, 0);
        table.register_char_primitive(b')', Command::RightDelimiter, 0);
        table.register_char_primitive(b'[', Command::LeftBracket, 0);
        table.register_char_primitive(b']', Command::RightBracket, 0);
        table.register_char_primitive(b'{', Command::LeftBrace, 0);
        table.register_char_primitive(b'}', Command::RightBrace, 0);
        table.register_char_primitive(b',', Command::Comma, 0);
        table.register_char_primitive(b';', Command::Semicolon, 0);
        table.register_char_primitive(b':', Command::Colon, 0);

        // Multi-char operators that map to specific commands
        table.register_primitive("..", Command::PathJoin, 0);
        table.register_primitive("...", Command::PathJoin, 1);
        table.register_primitive(":=", Command::Assignment, 0);
        table.register_primitive("::", Command::DoubleColon, 0);
        table.register_primitive("&", Command::Ampersand, 0);

        // Comparison operators — these are expression-level binaries
        table.register_primitive(
            "<",
            Command::ExpressionBinary,
            crate::command::ExpressionBinaryOp::LessThan as u16,
        );
        table.register_primitive(
            "<=",
            Command::ExpressionBinary,
            crate::command::ExpressionBinaryOp::LessOrEqual as u16,
        );
        table.register_primitive(
            ">",
            Command::ExpressionBinary,
            crate::command::ExpressionBinaryOp::GreaterThan as u16,
        );
        table.register_primitive(
            ">=",
            Command::ExpressionBinary,
            crate::command::ExpressionBinaryOp::GreaterOrEqual as u16,
        );
        table.register_primitive(
            "=",
            Command::Equals,
            crate::command::ExpressionBinaryOp::EqualTo as u16,
        );
        table.register_primitive(
            "<>",
            Command::ExpressionBinary,
            crate::command::ExpressionBinaryOp::UnequalTo as u16,
        );

        // Arithmetic operators at various levels
        table.register_primitive(
            "+",
            Command::PlusOrMinus,
            crate::command::PlusMinusOp::Plus as u16,
        );
        table.register_primitive(
            "-",
            Command::PlusOrMinus,
            crate::command::PlusMinusOp::Minus as u16,
        );
        table.register_primitive(
            "*",
            Command::SecondaryBinary,
            crate::command::SecondaryBinaryOp::Times as u16,
        );
        table.register_primitive(
            "/",
            Command::Slash,
            crate::command::SecondaryBinaryOp::Over as u16,
        );
        table.register_primitive(
            "++",
            Command::TertiaryBinary,
            crate::command::TertiaryBinaryOp::PythagAdd as u16,
        );
        table.register_primitive(
            "+-+",
            Command::TertiaryBinary,
            crate::command::TertiaryBinaryOp::PythagSub as u16,
        );

        table
    }

    /// Look up a symbolic token name, returning its id.
    ///
    /// If the name is a single byte, returns the character id directly.
    /// For unknown multi-char names, inserts a new tag token.
    pub fn lookup(&mut self, name: &str) -> SymbolId {
        // Single-byte shortcut
        if name.len() == 1 {
            let b = name.as_bytes()[0];
            return SymbolId(u32::from(b));
        }

        // Check existing
        if let Some(&id) = self.name_to_id.get(name) {
            return id;
        }

        // Insert new tag token
        self.insert_new(name, SymbolEntry::TAG)
    }

    /// Look up without inserting. Returns `None` for unknown symbols.
    #[must_use]
    pub fn lookup_existing(&self, name: &str) -> Option<SymbolId> {
        if name.len() == 1 {
            Some(SymbolId(u32::from(name.as_bytes()[0])))
        } else {
            self.name_to_id.get(name).copied()
        }
    }

    /// Get the entry for a symbol id.
    #[must_use]
    pub fn get(&self, id: SymbolId) -> SymbolEntry {
        if id.0 < 256 {
            self.char_entries[id.0 as usize]
        } else {
            let idx = (id.0 - 256) as usize;
            if idx < self.entries.len() {
                self.entries[idx].1
            } else {
                SymbolEntry::UNDEFINED
            }
        }
    }

    /// Set the entry for a symbol id.
    pub fn set(&mut self, id: SymbolId, entry: SymbolEntry) {
        if id.0 < 256 {
            self.char_entries[id.0 as usize] = entry;
        } else {
            let idx = (id.0 - 256) as usize;
            if idx < self.entries.len() {
                self.entries[idx].1 = entry;
            }
        }
    }

    /// Get the name of a symbol.
    #[must_use]
    pub fn name(&self, id: SymbolId) -> &str {
        if id.0 < 256 {
            // For single-char symbols, return the character as a string.
            // We use a static lookup table for printable ASCII.
            static CHAR_NAMES: std::sync::LazyLock<[String; 256]> =
                std::sync::LazyLock::new(|| {
                    std::array::from_fn(|i| {
                        if (32..127).contains(&i) {
                            // i is always < 256 from array::from_fn, so the cast is safe.
                            #[allow(clippy::cast_possible_truncation)]
                            let ch = i as u8;
                            String::from(char::from(ch))
                        } else {
                            String::new()
                        }
                    })
                });
            &CHAR_NAMES[id.0 as usize]
        } else {
            let idx = (id.0 - 256) as usize;
            if idx < self.entries.len() {
                &self.entries[idx].0
            } else {
                ""
            }
        }
    }

    /// Clear a symbol's meaning (set it back to undefined tag).
    ///
    /// Used by `save` to hide a name in the current scope.
    pub fn clear(&mut self, id: SymbolId) {
        self.set(id, SymbolEntry::TAG);
    }

    /// Register a primitive keyword.
    fn register_primitive(&mut self, name: &str, command: Command, modifier: u16) {
        let entry = SymbolEntry { command, modifier };

        if name.len() == 1 {
            let b = name.as_bytes()[0];
            self.char_entries[b as usize] = entry;
        } else if let Some(&id) = self.name_to_id.get(name) {
            self.set(id, entry);
        } else {
            self.insert_new(name, entry);
        }
    }

    /// Register a single-character primitive.
    const fn register_char_primitive(&mut self, ch: u8, command: Command, modifier: u16) {
        self.char_entries[ch as usize] = SymbolEntry { command, modifier };
    }

    /// Insert a new symbol, returning its id.
    fn insert_new(&mut self, name: &str, entry: SymbolEntry) -> SymbolId {
        let id = SymbolId(self.next_id);
        debug_assert!(self.next_id - 256 < Self::MAX_SYMBOLS);
        self.next_id += 1;
        self.entries.push((name.to_owned(), entry));
        self.name_to_id.insert(name.to_owned(), id);
        id
    }
}

impl Default for SymbolTable {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn primitives_are_registered() {
        let table = SymbolTable::new();

        // Check a few known primitives
        let id = table.lookup_existing("begingroup");
        assert!(id.is_some(), "begingroup not found");
        let entry = table.get(id.unwrap());
        assert_eq!(entry.command, Command::BeginGroup);

        let id = table.lookup_existing("endgroup");
        assert!(id.is_some(), "endgroup not found");
        let entry = table.get(id.unwrap());
        assert_eq!(entry.command, Command::EndGroup);

        let id = table.lookup_existing("if");
        assert!(id.is_some(), "if not found");
        let entry = table.get(id.unwrap());
        assert_eq!(entry.command, Command::IfTest);
    }

    #[test]
    fn single_char_symbols() {
        let table = SymbolTable::new();

        // Parentheses should be delimiters
        let entry = table.get(SymbolId(b'(' as u32));
        assert_eq!(entry.command, Command::LeftDelimiter);

        let entry = table.get(SymbolId(b')' as u32));
        assert_eq!(entry.command, Command::RightDelimiter);

        // Semicolon
        let entry = table.get(SymbolId(b';' as u32));
        assert_eq!(entry.command, Command::Semicolon);
    }

    #[test]
    fn operators_are_registered() {
        let table = SymbolTable::new();

        let id = table.lookup_existing("..").unwrap();
        assert_eq!(table.get(id).command, Command::PathJoin);

        let id = table.lookup_existing(":=").unwrap();
        assert_eq!(table.get(id).command, Command::Assignment);

        let id = table.lookup_existing("+").unwrap();
        assert_eq!(table.get(id).command, Command::PlusOrMinus);

        let id = table.lookup_existing("*").unwrap();
        assert_eq!(table.get(id).command, Command::SecondaryBinary);

        let id = table.lookup_existing("<").unwrap();
        assert_eq!(table.get(id).command, Command::ExpressionBinary);
    }

    #[test]
    fn unknown_symbol_becomes_tag() {
        let mut table = SymbolTable::new();
        let id = table.lookup("myvar");
        let entry = table.get(id);
        assert_eq!(entry.command, Command::TagToken);
    }

    #[test]
    fn lookup_is_idempotent() {
        let mut table = SymbolTable::new();
        let id1 = table.lookup("foo");
        let id2 = table.lookup("foo");
        assert_eq!(id1, id2);
    }

    #[test]
    fn set_and_get() {
        let mut table = SymbolTable::new();
        let id = table.lookup("test_sym");
        let entry = SymbolEntry {
            command: Command::Nullary,
            modifier: 42,
        };
        table.set(id, entry);
        assert_eq!(table.get(id), entry);
    }

    #[test]
    fn clear_resets_to_tag() {
        let mut table = SymbolTable::new();
        let id = table.lookup("x");
        table.set(
            id,
            SymbolEntry {
                command: Command::Nullary,
                modifier: 1,
            },
        );
        table.clear(id);
        assert_eq!(table.get(id).command, Command::TagToken);
    }
}
