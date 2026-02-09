//! The `MetaPost` interpreter.
//!
//! This is the central module that ties together the scanner, symbol table,
//! expression parser, equation solver, and statement executor. It implements
//! `MetaPost`'s direct-interpretation model: expressions are evaluated as
//! they are parsed, with no intermediate AST.
//!
//! # Expression hierarchy
//!
//! The recursive-descent parser follows `MetaPost`'s four precedence levels:
//! - `scan_primary`: atoms, unary operators, grouping
//! - `scan_secondary`: `*`, `/`, `scaled`, `rotated`, etc.
//! - `scan_tertiary`: `+`, `-`, `++`, `+-+`
//! - `scan_expression`: `=`, `<`, `>`, path construction

mod equation;
mod expand;
mod expr;
pub(crate) mod helpers;
mod operators;
mod path_parse;
mod statement;

use postmeta_graphics::types::{Color, Picture, Transform};

use crate::command::Command;
use crate::equation::{const_dep, single_dep, DepList, VarId};
use crate::error::{ErrorKind, InterpResult, InterpreterError};
use crate::filesystem::FileSystem;
use crate::input::{InputSystem, ResolvedToken, TokenList};
use crate::internals::Internals;
use crate::symbols::{SymbolId, SymbolTable};
use crate::types::{DrawingState, Type, Value};
use crate::variables::{NumericState, SaveStack, VarTrie, VarValue, Variables};

use expand::{IfState, MacroInfo};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum LhsBinding {
    Variable { id: VarId, negated: bool },
    Internal { idx: u16 },
}

// ---------------------------------------------------------------------------
// Interpreter state
// ---------------------------------------------------------------------------

/// The `MetaPost` interpreter.
pub struct Interpreter {
    /// Filesystem for `input` commands.
    fs: Box<dyn FileSystem>,
    /// Symbol table (names → command codes).
    pub symbols: SymbolTable,
    /// Variable storage.
    pub variables: Variables,
    /// Variable type trie — tracks declared variable structure.
    pub var_trie: VarTrie,
    /// Internal quantities.
    pub internals: Internals,
    /// Token input system.
    pub input: InputSystem,
    /// Save stack for `begingroup`/`endgroup`.
    pub save_stack: SaveStack,
    /// Current expression value and type.
    cur_exp: Value,
    cur_type: Type,
    /// Linear dependency form for the current numeric expression (if linear).
    cur_dep: Option<DepList>,
    /// Current resolved token (set by `get_next`).
    cur: ResolvedToken,
    /// Last scanned variable id (for assignment LHS tracking).
    last_var_id: Option<VarId>,
    /// Last scanned variable name (for assignment LHS tracking).
    last_var_name: String,
    /// Last scanned internal quantity index (for `interim` assignment).
    last_internal_idx: Option<u16>,
    /// Binding for expression forms that can be equation left-hand sides.
    last_lhs_binding: Option<LhsBinding>,
    /// If-stack depth tracking for nested conditionals.
    if_stack: Vec<IfState>,
    /// Loop nesting depth (for `exitif` to know which loop to break from).
    #[allow(dead_code)]
    loop_depth: u32,
    /// Flag set by `exitif` to signal that the current loop should terminate.
    loop_exit: bool,
    /// Pending loop body for `forever` loops (re-pushed on each `RepeatLoop` sentinel).
    pending_loop_body: Option<TokenList>,
    /// Defined macros: `SymbolId` → macro info.
    macros: std::collections::HashMap<SymbolId, MacroInfo>,
    /// Output pictures (one per `beginfig`/`endfig`).
    pub pictures: Vec<Picture>,
    /// Current picture being built.
    pub current_picture: Picture,
    /// Current figure number (from `beginfig`).
    pub current_fig: Option<i32>,
    /// Drawing state.
    pub drawing_state: DrawingState,
    /// Random seed.
    pub random_seed: u64,
    /// Error list.
    pub errors: Vec<InterpreterError>,
    /// Job name.
    pub job_name: String,
    /// Next delimiter id for `delimiters` command (0 is reserved for `()`).
    next_delimiter_id: u16,
}

impl Interpreter {
    /// Create a new interpreter.
    #[must_use]
    pub fn new() -> Self {
        let mut symbols = SymbolTable::new();
        let internals = Internals::new();

        // Register internal quantities in the symbol table
        for idx in 1..=crate::internals::MAX_GIVEN_INTERNAL {
            let name = internals.name(idx);
            if !name.is_empty() {
                let id = symbols.lookup(name);
                symbols.set(
                    id,
                    crate::symbols::SymbolEntry {
                        command: Command::InternalQuantity,
                        modifier: idx,
                    },
                );
            }
        }

        // Dummy initial token
        let cur = ResolvedToken {
            command: Command::Stop,
            modifier: 0,
            sym: None,
            token: crate::token::Token {
                kind: crate::token::TokenKind::Eof,
                span: crate::token::Span::at(0),
            },
            capsule: None,
        };

        Self {
            fs: Box::new(crate::filesystem::NullFileSystem),
            symbols,
            variables: Variables::new(),
            var_trie: VarTrie::new(),
            internals,
            input: InputSystem::new(),
            save_stack: SaveStack::new(),
            cur_exp: Value::Vacuous,
            cur_type: Type::Vacuous,
            cur_dep: None,
            cur,
            last_var_id: None,
            last_var_name: String::new(),
            last_internal_idx: None,
            last_lhs_binding: None,
            if_stack: Vec::new(),
            loop_depth: 0,
            loop_exit: false,
            pending_loop_body: None,
            macros: std::collections::HashMap::new(),
            pictures: Vec::new(),
            current_picture: Picture::new(),
            current_fig: None,
            drawing_state: DrawingState::default(),
            random_seed: 0,
            errors: Vec::new(),
            job_name: "output".into(),
            next_delimiter_id: 1, // 0 is reserved for built-in ()
        }
    }

    /// Set the filesystem for `input` commands.
    pub fn set_filesystem(&mut self, fs: Box<dyn FileSystem>) {
        self.fs = fs;
    }

    // =======================================================================
    // Token access
    // =======================================================================

    /// Get the next token (raw, no expansion).
    fn get_next(&mut self) {
        self.cur = self.input.next_raw_token(&mut self.symbols);
    }

    /// Get the next token, expanding macros and conditionals.
    ///
    /// This is `get_x_next` from `mp.web`: it calls `get_next` and then
    /// expands any expandable commands until a non-expandable one is found.
    fn get_x_next(&mut self) {
        self.get_next();
        self.expand_current();
    }

    /// Push the current token back into the input stream.
    ///
    /// After calling this, the next `get_next()` or `get_x_next()` will
    /// return the same token again. This is `mp.web`'s `back_input`.
    #[allow(dead_code)] // Used by future steps (variable tree, implicit multiplication)
    pub(super) fn back_input(&mut self) {
        self.input.back_input(self.cur.clone());
    }

    /// Push the current expression back into the input as a capsule token.
    ///
    /// The current `cur_exp`/`cur_type` are stashed into a capsule and
    /// placed on the input stream. The next token read will be a
    /// `CapsuleToken` carrying that value. This is `mp.web`'s `back_expr`.
    #[allow(dead_code)] // Used by future steps (variable tree, mediation disambiguation)
    pub(super) fn back_expr(&mut self) {
        let ty = self.cur_type;
        let val = self.take_cur_exp();
        self.input.back_expr(val, ty);
    }

    /// Store the current token into a token list.
    fn store_current_token(&self, list: &mut TokenList) {
        use crate::input::StoredToken;

        match &self.cur.token.kind {
            crate::token::TokenKind::Symbolic(_) => {
                if let Some(sym) = self.cur.sym {
                    list.push(StoredToken::Symbol(sym));
                }
            }
            crate::token::TokenKind::Numeric(v) => {
                list.push(StoredToken::Numeric(*v));
            }
            crate::token::TokenKind::StringLit(s) => {
                list.push(StoredToken::StringLit(s.clone()));
            }
            crate::token::TokenKind::Eof => {}
        }
    }

    // =======================================================================
    // Value helpers
    // =======================================================================

    /// Take `cur_exp`, replacing it with `Vacuous`.
    fn take_cur_exp(&mut self) -> Value {
        let val = std::mem::replace(&mut self.cur_exp, Value::Vacuous);
        self.cur_type = Type::Vacuous;
        self.cur_dep = None;
        val
    }

    const fn take_cur_dep(&mut self) -> Option<DepList> {
        self.cur_dep.take()
    }

    /// Negate the current expression (unary minus).
    fn negate_cur_exp(&mut self) {
        match &self.cur_exp {
            Value::Numeric(v) => {
                self.cur_exp = Value::Numeric(-v);
                if let Some(mut dep) = self.cur_dep.take() {
                    crate::equation::dep_scale(&mut dep, -1.0);
                    self.cur_dep = Some(dep);
                }
                if let Some(LhsBinding::Variable { id, negated }) = self.last_lhs_binding {
                    self.last_lhs_binding = Some(LhsBinding::Variable {
                        id,
                        negated: !negated,
                    });
                } else {
                    self.last_lhs_binding = None;
                }
            }
            Value::Pair(x, y) => {
                self.cur_exp = Value::Pair(-x, -y);
                self.cur_dep = None;
                if let Some(LhsBinding::Variable { id, negated }) = self.last_lhs_binding {
                    self.last_lhs_binding = Some(LhsBinding::Variable {
                        id,
                        negated: !negated,
                    });
                } else {
                    self.last_lhs_binding = None;
                }
            }
            Value::Color(c) => {
                self.cur_exp = Value::Color(Color::new(-c.r, -c.g, -c.b));
                self.cur_dep = None;
                if let Some(LhsBinding::Variable { id, negated }) = self.last_lhs_binding {
                    self.last_lhs_binding = Some(LhsBinding::Variable {
                        id,
                        negated: !negated,
                    });
                } else {
                    self.last_lhs_binding = None;
                }
            }
            _ => {
                self.last_lhs_binding = None;
                self.report_error(ErrorKind::TypeError, "Cannot negate this type");
            }
        }
    }

    /// Resolve a variable name to its value.
    fn resolve_variable(&mut self, sym: Option<SymbolId>, name: &str) -> InterpResult<()> {
        let var_id = self.variables.lookup(name);
        // Track last scanned variable for assignment LHS
        self.last_var_id = Some(var_id);
        self.last_var_name.clear();
        self.last_var_name.push_str(name);
        self.last_internal_idx = None;
        self.last_lhs_binding = Some(LhsBinding::Variable {
            id: var_id,
            negated: false,
        });

        match self.variables.get(var_id) {
            VarValue::Known(v) => {
                self.cur_exp = v.clone();
                self.cur_type = v.ty();
                self.cur_dep = match v {
                    Value::Numeric(n) => Some(const_dep(*n)),
                    _ => None,
                };
            }
            VarValue::NumericVar(NumericState::Known(v)) => {
                self.cur_exp = Value::Numeric(*v);
                self.cur_type = Type::Known;
                self.cur_dep = Some(const_dep(*v));
            }
            VarValue::NumericVar(NumericState::Independent { .. }) => {
                self.cur_exp = Value::Numeric(0.0);
                self.cur_type = Type::Independent;
                self.cur_dep = Some(single_dep(var_id));
            }
            VarValue::NumericVar(NumericState::Dependent(dep)) => {
                self.cur_exp = Value::Numeric(crate::equation::constant_value(dep).unwrap_or(0.0));
                self.cur_type = Type::Dependent;
                self.cur_dep = Some(dep.clone());
            }
            VarValue::NumericVar(NumericState::Numeric | NumericState::Undefined)
            | VarValue::Undefined => {
                self.variables.make_independent(var_id);
                self.cur_exp = Value::Numeric(0.0);
                self.cur_type = Type::Independent;
                self.cur_dep = Some(single_dep(var_id));
            }
            VarValue::Pair { x, y } => {
                let xv = self.variables.known_value(*x).unwrap_or(0.0);
                let yv = self.variables.known_value(*y).unwrap_or(0.0);
                self.cur_exp = Value::Pair(xv, yv);
                self.cur_type = Type::PairType;
                self.cur_dep = None;
            }
            VarValue::Color { r, g, b } => {
                let rv = self.variables.known_value(*r).unwrap_or(0.0);
                let gv = self.variables.known_value(*g).unwrap_or(0.0);
                let bv = self.variables.known_value(*b).unwrap_or(0.0);
                self.cur_exp = Value::Color(Color::new(rv, gv, bv));
                self.cur_type = Type::ColorType;
                self.cur_dep = None;
            }
            VarValue::Transform {
                tx,
                ty,
                txx,
                txy,
                tyx,
                tyy,
            } => {
                let parts = [*tx, *ty, *txx, *txy, *tyx, *tyy]
                    .map(|id| self.variables.known_value(id).unwrap_or(0.0));
                self.cur_exp = Value::Transform(Transform {
                    tx: parts[0],
                    ty: parts[1],
                    txx: parts[2],
                    txy: parts[3],
                    tyx: parts[4],
                    tyy: parts[5],
                });
                self.cur_type = Type::TransformType;
                self.cur_dep = None;
            }
        }
        let _ = sym; // Used later for equation LHS tracking
        Ok(())
    }

    // =======================================================================
    // Error handling
    // =======================================================================

    /// Record a non-fatal error.
    fn report_error(&mut self, kind: ErrorKind, message: impl Into<String>) {
        self.errors.push(InterpreterError::new(kind, message));
    }

    // =======================================================================
    // Public interface
    // =======================================================================

    /// Run a `MetaPost` program from source text.
    pub fn run(&mut self, source: &str) -> InterpResult<()> {
        self.input.push_source(source.to_owned());
        self.get_x_next();

        while self.cur.command != Command::Stop {
            self.do_statement()?;
        }

        Ok(())
    }

    /// Get the output pictures.
    #[must_use]
    pub fn output(&self) -> &[Picture] {
        &self.pictures
    }
}

impl Default for Interpreter {
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
    fn eval_numeric_literal() {
        let mut interp = Interpreter::new();
        interp.run("show 42;").unwrap();
        // Should have a show message
        assert!(!interp.errors.is_empty());
        let msg = &interp.errors[0].message;
        assert!(msg.contains("42"), "expected 42 in: {msg}");
    }

    #[test]
    fn eval_arithmetic() {
        let mut interp = Interpreter::new();
        interp.run("show 3 + 4;").unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("7"), "expected 7 in: {msg}");
    }

    #[test]
    fn eval_multiplication() {
        let mut interp = Interpreter::new();
        interp.run("show 3 * 5;").unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("15"), "expected 15 in: {msg}");
    }

    #[test]
    fn eval_string() {
        let mut interp = Interpreter::new();
        interp.run("show \"hello\";").unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("hello"), "expected hello in: {msg}");
    }

    #[test]
    fn eval_boolean() {
        let mut interp = Interpreter::new();
        interp.run("show true;").unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("true"), "expected true in: {msg}");
    }

    #[test]
    fn eval_pair() {
        let mut interp = Interpreter::new();
        interp.run("show (3, 4);").unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("(3,4)"), "expected (3,4) in: {msg}");
    }

    #[test]
    fn eval_unary_minus() {
        let mut interp = Interpreter::new();
        interp.run("show -5;").unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("-5"), "expected -5 in: {msg}");
    }

    #[test]
    fn eval_sqrt() {
        let mut interp = Interpreter::new();
        interp.run("show sqrt 9;").unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("3"), "expected 3 in: {msg}");
    }

    #[test]
    fn eval_sind() {
        let mut interp = Interpreter::new();
        interp.run("show sind 90;").unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("1"), "expected 1 in: {msg}");
    }

    #[test]
    fn eval_comparison() {
        let mut interp = Interpreter::new();
        interp.run("show 3 < 5;").unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("true"), "expected true in: {msg}");
    }

    #[test]
    fn eval_string_concat() {
        let mut interp = Interpreter::new();
        interp.run("show \"hello\" & \" world\";").unwrap();
        let msg = &interp.errors[0].message;
        assert!(
            msg.contains("hello world"),
            "expected 'hello world' in: {msg}"
        );
    }

    #[test]
    fn eval_multiple_statements() {
        let mut interp = Interpreter::new();
        interp.run("show 1; show 2; show 3;").unwrap();
        assert_eq!(interp.errors.len(), 3);
    }

    #[test]
    fn eval_internal_quantity() {
        let mut interp = Interpreter::new();
        interp.run("show linecap;").unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("1"), "expected 1 (round) in: {msg}");
    }

    #[test]
    fn eval_pencircle() {
        let mut interp = Interpreter::new();
        interp.run("show pencircle;").unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("pen"), "expected pen in: {msg}");
    }

    #[test]
    fn eval_if_true() {
        let mut interp = Interpreter::new();
        interp.run("show if true: 42 fi;").unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("42"), "expected 42 in: {msg}");
    }

    #[test]
    fn eval_if_false_else() {
        let mut interp = Interpreter::new();
        interp.run("show if false: 1 else: 2 fi;").unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("2"), "expected 2 in: {msg}");
    }

    #[test]
    fn eval_if_false_no_else() {
        let mut interp = Interpreter::new();
        // `if false: show 1; fi; show 2;` — only show 2 should execute
        interp.run("if false: show 1; fi; show 2;").unwrap();
        assert_eq!(
            interp.errors.len(),
            1,
            "expected only 1 show, got {:?}",
            interp.errors
        );
        let msg = &interp.errors[0].message;
        assert!(msg.contains("2"), "expected 2 in: {msg}");
    }

    #[test]
    fn eval_if_elseif() {
        let mut interp = Interpreter::new();
        interp
            .run("if false: show 1; elseif true: show 2; fi;")
            .unwrap();
        assert_eq!(interp.errors.len(), 1);
        let msg = &interp.errors[0].message;
        assert!(msg.contains("2"), "expected 2 in: {msg}");
    }

    #[test]
    fn eval_if_nested() {
        let mut interp = Interpreter::new();
        interp.run("if true: if true: show 42; fi; fi;").unwrap();
        assert_eq!(interp.errors.len(), 1);
        let msg = &interp.errors[0].message;
        assert!(msg.contains("42"), "expected 42 in: {msg}");
    }

    #[test]
    fn eval_for_loop() {
        let mut interp = Interpreter::new();
        interp.run("for i = 1, 2, 3: show i; endfor;").unwrap();
        assert_eq!(
            interp.errors.len(),
            3,
            "expected 3 shows: {:?}",
            interp.errors
        );
        assert!(interp.errors[0].message.contains("1"));
        assert!(interp.errors[1].message.contains("2"));
        assert!(interp.errors[2].message.contains("3"));
    }

    #[test]
    fn eval_for_loop_step() {
        // Accumulate sum inside a for loop
        let mut interp = Interpreter::new();
        interp
            .run("numeric s; s := 0; for i = 1, 2, 3: s := s + i; endfor; show s;")
            .unwrap();
        // s should be 1+2+3 = 6
        let msg = &interp.errors[0].message;
        assert!(msg.contains("6"), "expected 6 in: {msg}");
    }

    #[test]
    fn eval_forever_exitif() {
        let mut interp = Interpreter::new();
        interp
            .run("numeric n; n := 0; forever: n := n + 1; exitif n > 3; endfor; show n;")
            .unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("4"), "expected 4 in: {msg}");
    }

    #[test]
    fn eval_xpart_ypart_pair() {
        let mut interp = Interpreter::new();
        interp.run("show xpart (3, 7);").unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("3"), "expected 3 in: {msg}");

        let mut interp = Interpreter::new();
        interp.run("show ypart (3, 7);").unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("7"), "expected 7 in: {msg}");
    }

    #[test]
    fn eval_assignment_numeric() {
        let mut interp = Interpreter::new();
        interp.run("numeric x; x := 42; show x;").unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("42"), "expected 42 in: {msg}");
    }

    #[test]
    fn eval_assignment_string() {
        let mut interp = Interpreter::new();
        interp.run("string s; s := \"hello\"; show s;").unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("hello"), "expected hello in: {msg}");
    }

    #[test]
    fn eval_assignment_overwrite() {
        let mut interp = Interpreter::new();
        interp.run("numeric x; x := 10; x := 20; show x;").unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("20"), "expected 20 in: {msg}");
    }

    #[test]
    fn eval_assignment_internal() {
        let mut interp = Interpreter::new();
        interp.run("linecap := 0; show linecap;").unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("0"), "expected 0 in: {msg}");
    }

    #[test]
    fn eval_assignment_expr() {
        let mut interp = Interpreter::new();
        interp.run("numeric x; x := 3 + 4; show x;").unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("7"), "expected 7 in: {msg}");
    }

    #[test]
    fn eval_def_simple() {
        let mut interp = Interpreter::new();
        interp
            .run("def double(expr x) = 2 * x enddef; show double(5);")
            .unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("10"), "expected 10 in: {msg}");
    }

    #[test]
    fn eval_def_no_params() {
        let mut interp = Interpreter::new();
        interp.run("def seven = 7 enddef; show seven;").unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("7"), "expected 7 in: {msg}");
    }

    #[test]
    fn eval_def_two_params() {
        let mut interp = Interpreter::new();
        interp
            .run("def add(expr a, expr b) = a + b enddef; show add(3, 4);")
            .unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("7"), "expected 7 in: {msg}");
    }

    #[test]
    fn eval_def_multiple_calls() {
        let mut interp = Interpreter::new();
        interp
            .run("def sq(expr x) = x * x enddef; show sq(3); show sq(5);")
            .unwrap();
        assert_eq!(interp.errors.len(), 2);
        assert!(interp.errors[0].message.contains("9"), "expected 9");
        assert!(interp.errors[1].message.contains("25"), "expected 25");
    }

    #[test]
    fn eval_def_nested_call() {
        let mut interp = Interpreter::new();
        interp
            .run("def double(expr x) = 2 * x enddef; show double(double(3));")
            .unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("12"), "expected 12 in: {msg}");
    }

    #[test]
    fn eval_vardef() {
        let mut interp = Interpreter::new();
        interp
            .run("vardef triple(expr x) = 3 * x enddef; show triple(4);")
            .unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("12"), "expected 12 in: {msg}");
    }

    #[test]
    fn eval_def_with_body_statements() {
        // A macro that assigns to a variable
        let mut interp = Interpreter::new();
        interp
            .run("numeric result; def setresult(expr x) = result := x enddef; setresult(42); show result;")
            .unwrap();
        // Find the show message (skip any info/error messages before it)
        let show_msg = interp
            .errors
            .iter()
            .find(|e| e.message.contains(">>"))
            .map(|e| &e.message);
        assert!(
            show_msg.is_some() && show_msg.unwrap().contains("42"),
            "expected show 42, got errors: {:?}",
            interp.errors.iter().map(|e| &e.message).collect::<Vec<_>>()
        );
    }

    #[test]
    fn eval_def_in_for_loop() {
        let mut interp = Interpreter::new();
        interp
            .run("def inc(expr x) = x + 1 enddef; numeric s; s := 0; for i = 1, 2, 3: s := s + inc(i); endfor; show s;")
            .unwrap();
        // inc(1) + inc(2) + inc(3) = 2 + 3 + 4 = 9
        let show_msg = interp
            .errors
            .iter()
            .find(|e| e.message.contains(">>"))
            .map(|e| &e.message);
        assert!(
            show_msg.is_some() && show_msg.unwrap().contains("9"),
            "expected show 9, got errors: {:?}",
            interp.errors.iter().map(|e| &e.message).collect::<Vec<_>>()
        );
    }

    #[test]
    fn eval_def_with_conditional() {
        let mut interp = Interpreter::new();
        interp
            .run("def myabs(expr x) = if x < 0: -x else: x fi enddef; show myabs(-5); show myabs(3);")
            .unwrap();
        assert_eq!(interp.errors.len(), 2);
        assert!(interp.errors[0].message.contains("5"), "expected 5");
        assert!(interp.errors[1].message.contains("3"), "expected 3");
    }

    #[test]
    fn eval_scantokens_basic() {
        let mut interp = Interpreter::new();
        interp.run("show scantokens \"3 + 4\";").unwrap();
        let show_msg = interp
            .errors
            .iter()
            .find(|e| e.message.contains(">>"))
            .map(|e| &e.message);
        assert!(
            show_msg.is_some() && show_msg.unwrap().contains("7"),
            "expected show 7, got: {:?}",
            interp.errors.iter().map(|e| &e.message).collect::<Vec<_>>()
        );
    }

    #[test]
    fn eval_scantokens_define_and_use() {
        let mut interp = Interpreter::new();
        interp
            .run("scantokens \"def foo = 99 enddef\"; show foo;")
            .unwrap();
        let show_msg = interp
            .errors
            .iter()
            .find(|e| e.message.contains(">>"))
            .map(|e| &e.message);
        assert!(
            show_msg.is_some() && show_msg.unwrap().contains("99"),
            "expected show 99, got: {:?}",
            interp.errors.iter().map(|e| &e.message).collect::<Vec<_>>()
        );
    }

    #[test]
    fn eval_input_file_not_found() {
        let mut interp = Interpreter::new();
        // Should report error but not crash
        interp.run("input nonexistent;").unwrap();
        assert!(
            interp
                .errors
                .iter()
                .any(|e| e.message.contains("not found")),
            "expected file-not-found error: {:?}",
            interp.errors.iter().map(|e| &e.message).collect::<Vec<_>>()
        );
    }

    #[test]
    fn eval_input_with_filesystem() {
        use crate::filesystem::FileSystem;

        struct TestFs;
        impl FileSystem for TestFs {
            fn read_file(&self, name: &str) -> Option<String> {
                if name == "testlib" || name == "testlib.mp" {
                    Some("def tripleplus(expr x) = 3 * x + 1 enddef;".to_owned())
                } else {
                    None
                }
            }
        }

        let mut interp = Interpreter::new();
        interp.set_filesystem(Box::new(TestFs));
        interp.run("input testlib; show tripleplus(10);").unwrap();
        let show_msg = interp
            .errors
            .iter()
            .find(|e| e.message.contains(">>"))
            .map(|e| &e.message);
        assert!(
            show_msg.is_some() && show_msg.unwrap().contains("31"),
            "expected show 31, got: {:?}",
            interp.errors.iter().map(|e| &e.message).collect::<Vec<_>>()
        );
    }

    #[test]
    fn eval_primarydef() {
        let mut interp = Interpreter::new();
        interp
            .run("primarydef a dotprod b = xpart a * xpart b + ypart a * ypart b enddef; show (3,4) dotprod (1,2);")
            .unwrap();
        let msg = &interp.errors[0].message;
        // 3*1 + 4*2 = 11
        assert!(msg.contains("11"), "expected 11 in: {msg}");
    }

    #[test]
    fn eval_xpart_shifted_pair() {
        // (3, 7) shifted (10, 20) = (13, 27)
        let mut interp = Interpreter::new();
        interp.run("show xpart ((3,7) shifted (10,20));").unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("13"), "expected 13 in: {msg}");

        let mut interp = Interpreter::new();
        interp.run("show ypart ((3,7) shifted (10,20));").unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("27"), "expected 27 in: {msg}");
    }

    // -----------------------------------------------------------------------
    // Type declarations
    // -----------------------------------------------------------------------

    #[test]
    fn type_declaration_numeric() {
        let mut interp = Interpreter::new();
        interp.run("numeric x; x := 42; show x;").unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("42"), "expected 42 in: {msg}");
    }

    #[test]
    fn type_declaration_string() {
        let mut interp = Interpreter::new();
        interp.run("string s; s := \"hello\"; show s;").unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("hello"), "expected hello in: {msg}");
    }

    #[test]
    fn type_declaration_boolean() {
        let mut interp = Interpreter::new();
        interp.run("boolean b; b := true; show b;").unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("true"), "expected true in: {msg}");
    }

    #[test]
    fn type_declaration_pair() {
        let mut interp = Interpreter::new();
        interp.run("pair p; p := (3, 7); show p;").unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("(3,7)"), "expected (3,7) in: {msg}");
    }

    #[test]
    fn type_declaration_color() {
        let mut interp = Interpreter::new();
        interp.run("color c; c := (1, 0, 0); show c;").unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("(1,0,0)"), "expected (1,0,0) in: {msg}");
    }

    #[test]
    fn type_declaration_multiple() {
        let mut interp = Interpreter::new();
        interp
            .run("numeric a, b; a := 10; b := 20; show a + b;")
            .unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("30"), "expected 30 in: {msg}");
    }

    // -----------------------------------------------------------------------
    // Delimiters
    // -----------------------------------------------------------------------

    #[test]
    fn delimiters_custom() {
        let mut interp = Interpreter::new();
        interp.run("delimiters {{ }}; show {{ 3 + 4 }};").unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("7"), "expected 7 in: {msg}");
    }

    #[test]
    fn delimiters_pair() {
        let mut interp = Interpreter::new();
        interp.run("delimiters {{ }}; show {{ 2, 5 }};").unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("(2,5)"), "expected (2,5) in: {msg}");
    }

    // -----------------------------------------------------------------------
    // Newinternal
    // -----------------------------------------------------------------------

    #[test]
    fn newinternal_basic() {
        let mut interp = Interpreter::new();
        interp
            .run("newinternal myvar; myvar := 7; show myvar;")
            .unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("7"), "expected 7 in: {msg}");
    }

    #[test]
    fn newinternal_multiple() {
        let mut interp = Interpreter::new();
        interp
            .run("newinternal a, b; a := 3; b := 5; show a + b;")
            .unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("8"), "expected 8 in: {msg}");
    }

    // -----------------------------------------------------------------------
    // Mediation
    // -----------------------------------------------------------------------

    #[test]
    fn mediation_basic() {
        let mut interp = Interpreter::new();
        // 0.5[10,20] = 15
        interp.run("show 0.5[10, 20];").unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("15"), "expected 15 in: {msg}");
    }

    #[test]
    fn mediation_endpoints() {
        let mut interp = Interpreter::new();
        // 0[a,b] = a
        interp.run("show 0[3, 7];").unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("3"), "expected 3 in: {msg}");

        let mut interp = Interpreter::new();
        // 1[a,b] = b
        interp.run("show 1[3, 7];").unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("7"), "expected 7 in: {msg}");
    }

    #[test]
    fn mediation_fraction() {
        let mut interp = Interpreter::new();
        // 1/4[0,100] = 25
        interp.run("show 1/4[0, 100];").unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("25"), "expected 25 in: {msg}");
    }

    // -----------------------------------------------------------------------
    // For step/until
    // -----------------------------------------------------------------------

    #[test]
    fn for_step_until() {
        let mut interp = Interpreter::new();
        // Sum 1 through 5
        interp
            .run("numeric s; s := 0; for k=1 step 1 until 5: s := s + k; endfor; show s;")
            .unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("15"), "expected 15 in: {msg}");
    }

    #[test]
    fn for_step_until_by_two() {
        let mut interp = Interpreter::new();
        // Sum 0, 2, 4, 6, 8, 10 = 30
        interp
            .run("numeric s; s := 0; for k=0 step 2 until 10: s := s + k; endfor; show s;")
            .unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("30"), "expected 30 in: {msg}");
    }

    #[test]
    fn for_step_until_negative() {
        let mut interp = Interpreter::new();
        // Count down: 5, 4, 3, 2, 1 = 15
        interp
            .run("numeric s; s := 0; for k=5 step -1 until 1: s := s + k; endfor; show s;")
            .unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("15"), "expected 15 in: {msg}");
    }

    // -----------------------------------------------------------------------
    // Str operator
    // -----------------------------------------------------------------------

    #[test]
    fn str_operator() {
        let mut interp = Interpreter::new();
        interp.run("show str x;").unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("x"), "expected x in: {msg}");
    }

    #[test]
    fn str_operator_multi_char() {
        let mut interp = Interpreter::new();
        interp.run("show str foo;").unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("foo"), "expected foo in: {msg}");
    }

    // -----------------------------------------------------------------------
    // Undelimited macro parameters
    // -----------------------------------------------------------------------

    #[test]
    fn eval_def_undelimited_primary() {
        let mut interp = Interpreter::new();
        interp
            .run("vardef double primary x = 2*x enddef; show double 5;")
            .unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("10"), "expected 10 in: {msg}");
    }

    #[test]
    fn eval_def_undelimited_secondary() {
        let mut interp = Interpreter::new();
        interp
            .run("vardef neg secondary x = -x enddef; show neg 3;")
            .unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("-3"), "expected -3 in: {msg}");
    }

    #[test]
    fn eval_def_undelimited_expr() {
        let mut interp = Interpreter::new();
        interp
            .run("vardef id expr x = x enddef; show id 5+3;")
            .unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("8"), "expected 8 in: {msg}");
    }

    // -----------------------------------------------------------------------
    // Curl direction in path construction
    // -----------------------------------------------------------------------

    #[test]
    fn curl_direction_in_def() {
        let mut interp = Interpreter::new();
        // This should define -- as a macro without error
        interp
            .run(
                "def -- = {curl 1}..{curl 1} enddef; \
                 path p; p = (0,0)--(1,0); show p;",
            )
            .unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("path"), "expected path in: {msg}");
    }

    // -----------------------------------------------------------------------
    // let: must not expand RHS macro
    // -----------------------------------------------------------------------

    #[test]
    fn let_does_not_expand_rhs() {
        let mut interp = Interpreter::new();
        // Without fix, this crashes with "Expected pair, got known numeric"
        // because the let would try to expand foo's body
        interp
            .run(
                "def foo(expr z, d) = shifted -z rotated d shifted z enddef; \
                 let bar = foo; show 1;",
            )
            .unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("1"), "expected 1 in: {msg}");
    }

    #[test]
    fn let_copies_macro_info() {
        let mut interp = Interpreter::new();
        interp
            .run(
                "tertiarydef p _on_ d = d enddef; \
                 let on = _on_; show 5 on 3;",
            )
            .unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("3"), "expected 3 in: {msg}");
    }

    // -----------------------------------------------------------------------
    // Chained equations
    // -----------------------------------------------------------------------

    #[test]
    fn chained_equation() {
        let mut interp = Interpreter::new();
        // Chained equation with unary-minus LHS: right = -left = (1,0)
        interp
            .run("pair right,left; right=-left=(1,0); show right; show left;")
            .unwrap();
        assert!(
            interp.errors.iter().any(|e| e.message.contains(">> (1,0)")),
            "expected right=(1,0), got: {:?}",
            interp.errors.iter().map(|e| &e.message).collect::<Vec<_>>()
        );
        assert!(
            interp
                .errors
                .iter()
                .any(|e| e.message.contains(">> (-1,0)") || e.message.contains(">> (-1,-0)")),
            "expected left=(-1,0), got: {:?}",
            interp.errors.iter().map(|e| &e.message).collect::<Vec<_>>()
        );
    }

    #[test]
    fn linear_equation_system_solves() {
        let mut interp = Interpreter::new();
        interp
            .run("numeric x,y; x+y=5; x-y=1; show x; show y;")
            .unwrap();

        let messages: Vec<_> = interp.errors.iter().map(|e| e.message.as_str()).collect();
        assert!(
            messages.iter().any(|m| m.contains(">> 3")),
            "expected x=3, got: {:?}",
            messages
        );
        assert!(
            messages.iter().any(|m| m.contains(">> 2")),
            "expected y=2, got: {:?}",
            messages
        );
    }

    #[test]
    fn chained_assignment() {
        let mut interp = Interpreter::new();
        interp
            .run("newinternal a,b,c; a:=b:=c:=0; show a; show b; show c;")
            .unwrap();

        let error_count = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Error)
            .count();
        assert!(error_count == 0, "expected 0 errors, got {error_count}");

        let shows: Vec<_> = interp
            .errors
            .iter()
            .filter(|e| e.message.contains(">>"))
            .map(|e| e.message.as_str())
            .collect();
        assert!(
            shows.iter().filter(|m| m.contains(">> 0")).count() >= 3,
            "expected all values to be 0, got: {:?}",
            shows
        );
    }

    // -----------------------------------------------------------------------
    // Type declaration with subscripts and suffixes
    // -----------------------------------------------------------------------

    #[test]
    fn type_declaration_subscript_array() {
        let mut interp = Interpreter::new();
        // Should not hang
        interp.run("pair z_[];").unwrap();
    }

    #[test]
    fn type_declaration_compound_suffix() {
        let mut interp = Interpreter::new();
        // Should not hang
        interp.run("path path_.l, path_.r;").unwrap();
    }

    // -----------------------------------------------------------------------
    // back_input / back_expr integration
    // -----------------------------------------------------------------------

    #[test]
    fn back_input_rescans_token() {
        let mut interp = Interpreter::new();
        interp.input.push_source("+ 3;".to_owned());
        // Read "+"
        interp.get_next();
        assert_eq!(interp.cur.command, Command::PlusOrMinus);
        // Push it back
        interp.back_input();
        // Read again — should get "+" again
        interp.get_next();
        assert_eq!(interp.cur.command, Command::PlusOrMinus);
    }

    #[test]
    fn back_expr_capsule_roundtrip() {
        let mut interp = Interpreter::new();
        // Push source first (it goes on the bottom of the stack)
        interp.input.push_source(";".to_owned());
        // Set up a capsule with a pair value
        interp.cur_exp = Value::Pair(5.0, 10.0);
        interp.cur_type = Type::PairType;
        // Push it back — this goes on top of the source
        interp.back_expr();
        // Now get_x_next reads from the capsule token list (top of stack)
        interp.get_x_next();
        assert_eq!(interp.cur.command, Command::CapsuleToken);
        interp.scan_primary().unwrap();
        assert_eq!(interp.cur_type, Type::PairType);
        assert_eq!(interp.cur_exp.as_pair(), Some((5.0, 10.0)));
    }

    #[test]
    fn back_expr_numeric_in_expression() {
        // Push a numeric capsule and verify it can participate in arithmetic
        let mut interp = Interpreter::new();
        // Push source first (bottom of stack)
        interp.input.push_source("+ 3;".to_owned());
        // Then push capsule (top of stack)
        interp.cur_exp = Value::Numeric(7.0);
        interp.cur_type = Type::Known;
        interp.back_expr();
        interp.get_x_next();
        interp.scan_expression().unwrap();
        // Should evaluate to 7 + 3 = 10
        assert_eq!(interp.cur_exp, Value::Numeric(10.0));
    }

    // -----------------------------------------------------------------------
    // vardef expansion from scan_primary (TagToken path)
    // -----------------------------------------------------------------------

    #[test]
    fn vardef_suffix_in_equation() {
        // laboff.lft where lft is a vardef — should work as variable, not expand
        let mut interp = Interpreter::new();
        interp
            .run("vardef lft primary x = x enddef; pair laboff.lft; laboff.lft = (1,2); show 1;")
            .unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("1"), "expected 1 in: {msg}");
    }

    #[test]
    fn vardef_suffix_undeclared_equation() {
        // labxf.lft where labxf is undeclared and lft is a vardef
        let mut interp = Interpreter::new();
        interp
            .run("vardef lft primary x = x enddef; labxf.lft = 1; show 1;")
            .unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("1"), "expected 1 in: {msg}");
    }

    #[test]
    fn tertiarydef_with_picture() {
        // Simplified _on_: just shift a picture
        let mut interp = Interpreter::new();
        interp
            .run(
                r#"
            delimiters ();
            tertiarydef p _on_ d =
              begingroup
              p shifted (0,d)
              endgroup
            enddef;
            show nullpicture _on_ 3;
        "#,
            )
            .unwrap();
        let errors: Vec<_> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Error)
            .collect();
        for e in &errors {
            eprintln!("  tertiarydef error: {}", e.message);
        }
        assert!(errors.is_empty(), "had {} errors", errors.len());
    }

    #[test]
    fn error_recovery_skips_to_semicolon() {
        // Statement with unexpected comma should skip to ; and continue
        let mut interp = Interpreter::new();
        interp.run(",,,; show 1;").unwrap();
        // Should have errors for the commas but still process "show 1"
        let show_msgs: Vec<_> = interp
            .errors
            .iter()
            .filter(|e| e.message.contains("1"))
            .collect();
        assert!(!show_msgs.is_empty(), "show 1 should have been processed");
    }

    #[test]
    fn dashpattern_basic() {
        let mut interp = Interpreter::new();
        interp
            .run(
                r#"
            delimiters ();
            tertiarydef p _on_ d =
              begingroup save pic;
              picture pic; pic=p;
              addto pic doublepath (0,0)..(d,0);
              pic shifted (0,d)
              endgroup
            enddef;
            tertiarydef p _off_ d =
              begingroup
              p shifted (0,d)
              endgroup
            enddef;
            vardef dashpattern(text t) =
              save on, off;
              let on=_on_;
              let off=_off_;
              nullpicture t
            enddef;
            show dashpattern(on 3 off 3);
        "#,
            )
            .unwrap();
        // Should produce a picture, not a "Cannot transform" error
        let errors: Vec<_> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Error)
            .collect();
        for e in &errors {
            eprintln!("  dashpattern error: {}", e.message);
        }
        assert!(errors.is_empty(), "dashpattern had {} errors", errors.len());
    }

    #[test]
    fn vardef_stays_tag_token() {
        // After defining a vardef, the symbol should remain TagToken
        let mut interp = Interpreter::new();
        interp.run("vardef foo primary x = x + 1 enddef;").unwrap();
        let sym = interp.symbols.lookup("foo");
        let entry = interp.symbols.get(sym);
        assert_eq!(entry.command, Command::TagToken);
        assert!(interp.macros.contains_key(&sym));
    }

    #[test]
    fn implicit_multiplication() {
        let mut interp = Interpreter::new();
        interp.run("bp := 1; show 3bp;").unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("3"), "expected 3 in: {msg}");
    }

    #[test]
    fn implicit_multiplication_pair() {
        let mut interp = Interpreter::new();
        interp.run("show 2(3,4);").unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("(6,8)"), "expected (6,8) in: {msg}");
    }

    #[test]
    fn vardef_expands_in_expression() {
        // vardef macro should expand when used as standalone primary
        let mut interp = Interpreter::new();
        interp
            .run("vardef foo primary x = x + 1 enddef; show foo 5;")
            .unwrap();
        // show produces an error with the value
        let msg = &interp.errors[0].message;
        assert!(msg.contains("6"), "expected 6 in: {msg}");
    }

    #[test]
    fn vardef_suffix_not_expanded() {
        // A vardef symbol appearing as a suffix should NOT be expanded
        let mut interp = Interpreter::new();
        interp
            .run("pair p.foo; vardef foo primary x = x enddef; p.foo = (1,2);")
            .unwrap();
    }

    // -----------------------------------------------------------------------
    // vardef with @# suffix parameter
    // -----------------------------------------------------------------------

    #[test]
    fn vardef_at_suffix_parses() {
        let mut interp = Interpreter::new();
        interp
            .run("vardef foo@#(expr x) = x enddef; show 1;")
            .unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("1"), "expected 1 in: {msg}");
    }

    // -----------------------------------------------------------------------
    // vardef with expr..of parameter pattern
    // -----------------------------------------------------------------------

    #[test]
    fn vardef_expr_of_pattern() {
        let mut interp = Interpreter::new();
        interp
            .run("vardef direction expr t of p = t enddef; show 1;")
            .unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("1"), "expected 1 in: {msg}");
    }

    // -----------------------------------------------------------------------
    // Multiple delimited parameter groups
    // -----------------------------------------------------------------------

    #[test]
    fn multiple_delimited_param_groups() {
        let mut interp = Interpreter::new();
        interp
            .run("vardef foo(expr u)(text t) = u enddef; show 1;")
            .unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("1"), "expected 1 in: {msg}");
    }

    // -----------------------------------------------------------------------
    // plain.mp loads without hard error
    // -----------------------------------------------------------------------

    #[test]
    fn plain_mp_error_count() {
        use crate::filesystem::FileSystem;
        struct TestFs;
        impl FileSystem for TestFs {
            fn read_file(&self, name: &str) -> Option<String> {
                if name == "plain" || name == "plain.mp" {
                    Some(
                        std::fs::read_to_string(
                            std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                                .parent()
                                .unwrap()
                                .join("lib/plain.mp"),
                        )
                        .ok()?,
                    )
                } else {
                    None
                }
            }
        }
        let mut interp = Interpreter::new();
        interp.set_filesystem(Box::new(TestFs));
        interp.run("input plain;").unwrap();

        let error_count = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Error)
            .count();
        // plain.mp should load without errors.
        assert!(error_count == 0, "expected 0 errors, got {error_count}");
    }

    #[test]
    fn plain_mp_loads() {
        use crate::filesystem::FileSystem;
        struct TestFs;
        impl FileSystem for TestFs {
            fn read_file(&self, name: &str) -> Option<String> {
                if name == "plain" || name == "plain.mp" {
                    Some(
                        std::fs::read_to_string(
                            std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                                .parent()
                                .unwrap()
                                .join("lib/plain.mp"),
                        )
                        .ok()?,
                    )
                } else {
                    None
                }
            }
        }
        let mut interp = Interpreter::new();
        interp.set_filesystem(Box::new(TestFs));
        // Should not return Err (hard error) — warnings are OK
        interp.run("input plain;").unwrap();
    }

    // -----------------------------------------------------------------------
    // Type tests (numeric, pen, etc. as unary operators)
    // -----------------------------------------------------------------------

    #[test]
    fn type_test_numeric() {
        let mut interp = Interpreter::new();
        interp.run("show numeric 5;").unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("true"), "expected true in: {msg}");
    }

    #[test]
    fn type_test_pen() {
        let mut interp = Interpreter::new();
        interp.run("show pen pencircle;").unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("true"), "expected true in: {msg}");
    }

    #[test]
    fn type_test_numeric_on_pen() {
        let mut interp = Interpreter::new();
        interp.run("show numeric pencircle;").unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("false"), "expected false in: {msg}");
    }

    // -----------------------------------------------------------------------
    // Subscript variables
    // -----------------------------------------------------------------------

    #[test]
    fn subscript_bracket() {
        let mut interp = Interpreter::new();
        interp.run("numeric a[]; a[1] := 42; show a[1];").unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("42"), "expected 42 in: {msg}");
    }
}
