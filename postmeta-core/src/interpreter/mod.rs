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

use std::sync::Arc;

use postmeta_graphics::types::{Color, Path, Pen, Picture, Transform};

use crate::command::Command;
use crate::equation::{const_dep, single_dep, DepList, VarId};
use crate::error::{ErrorKind, InterpResult, InterpreterError};
use crate::filesystem::FileSystem;
use crate::input::{InputSystem, ResolvedToken, TokenList};
use crate::internals::Internals;
use crate::symbols::{SymbolId, SymbolTable};
use crate::types::{DrawingState, Type, Value};
use crate::variables::{NumericState, SaveStack, SuffixSegment, VarTrie, VarValue, Variables};

use expand::{ControlFlow, MacroInfo};

// ---------------------------------------------------------------------------
// Current expression state
// ---------------------------------------------------------------------------

/// The interpreter's current expression result.
///
/// Groups the value, type, and linear dependency state that the expression
/// parser writes to and consumers read from. These four fields are always
/// mutated as a unit, so bundling them reduces `Interpreter`'s field count
/// and makes the ownership boundary explicit.
pub(super) struct CurExpr {
    /// The expression value.
    pub exp: Value,
    /// The expression type.
    pub ty: Type,
    /// Scalar linear dependency list (for numeric expressions in the equation system).
    pub dep: Option<DepList>,
    /// Pair (x, y) dependency lists (for pair expressions in the equation system).
    pub pair_dep: Option<(DepList, DepList)>,
}

impl CurExpr {
    const fn new() -> Self {
        Self {
            exp: Value::Vacuous,
            ty: Type::Vacuous,
            dep: None,
            pair_dep: None,
        }
    }

    /// Take the expression value, resetting all fields.
    fn take_exp(&mut self) -> Value {
        let val = std::mem::replace(&mut self.exp, Value::Vacuous);
        self.ty = Type::Vacuous;
        self.dep = None;
        self.pair_dep = None;
        val
    }

    /// Take the scalar dependency list.
    const fn take_dep(&mut self) -> Option<DepList> {
        self.dep.take()
    }

    /// Take the pair dependency lists.
    const fn take_pair_dep(&mut self) -> Option<(DepList, DepList)> {
        self.pair_dep.take()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum LhsBinding {
    Variable { id: VarId, negated: bool },
    Internal { idx: u16 },
    Pair {
        x: Option<Box<Self>>,
        y: Option<Box<Self>>,
    },
    Color {
        r: Option<Box<Self>>,
        g: Option<Box<Self>>,
        b: Option<Box<Self>>,
    },
}

/// Tracks the latest bindable LHS expression context.
///
/// This state is threaded through expression parsing so statements can
/// distinguish equations/assignments to variables, internals, and compound
/// parts.
pub(super) struct LhsTracking {
    /// Binding for expression forms that can be equation left-hand sides.
    pub last_lhs_binding: Option<LhsBinding>,
    /// When true, `=` in `scan_expression` is treated as an equation
    /// delimiter (not consumed). Set before calling `scan_expression` from
    /// statement context; cleared inside `scan_expression` on entry.
    /// Mirrors `mp.web`'s `var_flag = assignment` mechanism.
    pub equals_means_equation: bool,
}

impl LhsTracking {
    const fn new() -> Self {
        Self {
            last_lhs_binding: None,
            equals_means_equation: false,
        }
    }
}

/// Aggregates interpreter picture output/runtime drawing state.
pub(super) struct PictureState {
    /// Output pictures (one per `beginfig`/`endfig`).
    pub pictures: Vec<Picture>,
    /// Current picture being built.
    pub current_picture: Picture,
    /// Temporary buffer for `addto` targeting a named picture variable.
    /// Used to avoid borrow conflicts: the picture is extracted from the
    /// variable, modified here, then flushed back.
    pub named_pic_buf: Option<Picture>,
    /// Current figure number (from `beginfig`).
    pub current_fig: Option<i32>,
    /// Drawing state.
    pub drawing_state: DrawingState,
}

impl PictureState {
    fn new() -> Self {
        Self {
            pictures: Vec::new(),
            current_picture: Picture::new(),
            named_pic_buf: None,
            current_fig: None,
            drawing_state: DrawingState::default(),
        }
    }
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
    /// Current expression result (value, type, and dependency state).
    cur_expr: CurExpr,
    /// Current resolved token (set by `get_next`).
    cur: ResolvedToken,
    /// Latest bindable left-hand-side context.
    lhs_tracking: LhsTracking,
    /// Conditional and loop control state (if-stack, loop exit flag, pending body).
    control_flow: ControlFlow,
    /// Picture output/runtime drawing state.
    picture_state: PictureState,
    /// Defined macros: `SymbolId` → macro info.
    macros: std::collections::HashMap<SymbolId, MacroInfo>,
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
            cur_expr: CurExpr::new(),
            cur,
            lhs_tracking: LhsTracking::new(),
            control_flow: ControlFlow::new(),
            picture_state: PictureState::new(),
            macros: std::collections::HashMap::new(),
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
        for scan_error in self.input.take_scan_errors() {
            let kind = if scan_error.message.contains("unterminated string") {
                ErrorKind::UnterminatedString
            } else {
                ErrorKind::InvalidCharacter
            };
            self.errors
                .push(InterpreterError::new(kind, scan_error.message).with_span(scan_error.span));
        }
    }

    /// Get the next token, expanding macros and conditionals.
    ///
    /// This is `get_x_next` from `mp.web`: it calls `get_next` and then
    /// expands any expandable commands until a non-expandable one is found.
    fn get_x_next(&mut self) {
        // Expansion is token-oriented; it should not overwrite the current
        // expression value that the parser may already have computed.
        let saved_exp = self.cur_expr.exp.clone();
        let saved_type = self.cur_expr.ty;
        let saved_dep = self.cur_expr.dep.clone();
        let saved_pair_dep = self.cur_expr.pair_dep.clone();
        self.get_next();
        self.expand_current();
        self.cur_expr.exp = saved_exp;
        self.cur_expr.ty = saved_type;
        self.cur_expr.dep = saved_dep;
        self.cur_expr.pair_dep = saved_pair_dep;
    }

    /// Push the current token back into the input stream.
    ///
    /// After calling this, the next `get_next()` or `get_x_next()` will
    /// return the same token again. This is `mp.web`'s `back_input`.
    pub(super) fn back_input(&mut self) {
        self.input.back_input(self.cur.clone());
    }

    /// Push the current expression back into the input as a capsule token.
    ///
    /// The current `cur_exp`/`cur_type` are stashed into a capsule and
    /// placed on the input stream. The next token read will be a
    /// `CapsuleToken` carrying that value. This is `mp.web`'s `back_expr`.
    pub(super) fn back_expr(&mut self) {
        let dep = self.take_cur_dep();
        let pair_dep = self.take_cur_pair_dep();
        let ty = self.cur_expr.ty;
        let val = self.take_cur_exp();
        self.input.back_expr(val, ty, dep, pair_dep);
    }

    /// Store the current token into a token list.
    fn store_current_token(&self, list: &mut TokenList) {
        use crate::input::StoredToken;

        if self.cur.command == Command::CapsuleToken {
            if let Some((val, ty, dep, pair_dep)) = &self.cur.capsule {
                list.push(StoredToken::Capsule(
                    val.clone(),
                    *ty,
                    dep.clone(),
                    pair_dep.clone(),
                ));
            }
            return;
        }

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
        self.cur_expr.take_exp()
    }

    const fn take_cur_dep(&mut self) -> Option<DepList> {
        self.cur_expr.take_dep()
    }

    const fn take_cur_pair_dep(&mut self) -> Option<(DepList, DepList)> {
        self.cur_expr.take_pair_dep()
    }

    fn numeric_dep_for_var(&mut self, id: VarId) -> DepList {
        match self.variables.get(id).clone() {
            VarValue::NumericVar(NumericState::Known(v)) => const_dep(v),
            VarValue::NumericVar(NumericState::Independent { .. }) => crate::equation::single_dep(id),
            VarValue::NumericVar(NumericState::Dependent(dep)) => dep,
            VarValue::NumericVar(NumericState::Numeric | NumericState::Undefined)
            | VarValue::Undefined => {
                self.variables.make_independent(id);
                crate::equation::single_dep(id)
            }
            _ => const_dep(self.variables.known_value(id).unwrap_or(0.0)),
        }
    }

    fn cur_symbolic_name(&self) -> Option<&str> {
        if let crate::token::TokenKind::Symbolic(name) = &self.cur.token.kind {
            Some(name)
        } else {
            None
        }
    }

    fn alloc_pair_value(&mut self, name: &str) -> VarValue {
        let x = self.variables.alloc();
        let y = self.variables.alloc();
        self.variables
            .set(x, VarValue::NumericVar(NumericState::Numeric));
        self.variables
            .set(y, VarValue::NumericVar(NumericState::Numeric));
        self.variables.register_name(&format!("{name}.x"), x);
        self.variables.register_name(&format!("{name}.y"), y);
        VarValue::Pair { x, y }
    }

    fn alloc_color_value(&mut self, name: &str) -> VarValue {
        let r = self.variables.alloc();
        let g = self.variables.alloc();
        let b = self.variables.alloc();
        self.variables
            .set(r, VarValue::NumericVar(NumericState::Numeric));
        self.variables
            .set(g, VarValue::NumericVar(NumericState::Numeric));
        self.variables
            .set(b, VarValue::NumericVar(NumericState::Numeric));
        self.variables.register_name(&format!("{name}.r"), r);
        self.variables.register_name(&format!("{name}.g"), g);
        self.variables.register_name(&format!("{name}.b"), b);
        VarValue::Color { r, g, b }
    }

    fn alloc_transform_value(&mut self, name: &str) -> VarValue {
        let tx = self.variables.alloc();
        let ty = self.variables.alloc();
        let txx = self.variables.alloc();
        let txy = self.variables.alloc();
        let tyx = self.variables.alloc();
        let tyy = self.variables.alloc();
        for id in [tx, ty, txx, txy, tyx, tyy] {
            self.variables
                .set(id, VarValue::NumericVar(NumericState::Numeric));
        }
        self.variables.register_name(&format!("{name}.tx"), tx);
        self.variables.register_name(&format!("{name}.ty"), ty);
        self.variables.register_name(&format!("{name}.txx"), txx);
        self.variables.register_name(&format!("{name}.txy"), txy);
        self.variables.register_name(&format!("{name}.tyx"), tyx);
        self.variables.register_name(&format!("{name}.tyy"), tyy);
        VarValue::Transform {
            tx,
            ty,
            txx,
            txy,
            tyx,
            tyy,
        }
    }

    /// Negate the current expression (unary minus).
    fn negate_cur_exp(&mut self) {
        fn negate_binding(binding: &LhsBinding) -> Option<LhsBinding> {
            match binding {
                LhsBinding::Variable { id, negated } => Some(LhsBinding::Variable {
                    id: *id,
                    negated: !negated,
                }),
                LhsBinding::Internal { .. } => None,
                LhsBinding::Pair { x, y } => Some(LhsBinding::Pair {
                    x: x.as_ref().and_then(|b| negate_binding(b).map(Box::new)),
                    y: y.as_ref().and_then(|b| negate_binding(b).map(Box::new)),
                }),
                LhsBinding::Color { r, g, b } => Some(LhsBinding::Color {
                    r: r.as_ref().and_then(|bb| negate_binding(bb).map(Box::new)),
                    g: g.as_ref().and_then(|bb| negate_binding(bb).map(Box::new)),
                    b: b.as_ref().and_then(|bb| negate_binding(bb).map(Box::new)),
                }),
            }
        }

        match &self.cur_expr.exp {
            Value::Numeric(v) => {
                self.cur_expr.exp = Value::Numeric(-v);
                if let Some(mut dep) = self.cur_expr.dep.take() {
                    crate::equation::dep_scale(&mut dep, -1.0);
                    self.cur_expr.dep = Some(dep);
                }
                self.cur_expr.pair_dep = None;
                self.lhs_tracking.last_lhs_binding = self
                    .lhs_tracking
                    .last_lhs_binding
                    .as_ref()
                    .and_then(negate_binding);
            }
            Value::Pair(x, y) => {
                self.cur_expr.exp = Value::Pair(-x, -y);
                self.cur_expr.dep = None;
                if let Some((mut dx, mut dy)) = self.cur_expr.pair_dep.take() {
                    crate::equation::dep_scale(&mut dx, -1.0);
                    crate::equation::dep_scale(&mut dy, -1.0);
                    self.cur_expr.pair_dep = Some((dx, dy));
                }
                self.lhs_tracking.last_lhs_binding = self
                    .lhs_tracking
                    .last_lhs_binding
                    .as_ref()
                    .and_then(negate_binding);
            }
            Value::Color(c) => {
                self.cur_expr.exp = Value::Color(Color::new(-c.r, -c.g, -c.b));
                self.cur_expr.dep = None;
                self.cur_expr.pair_dep = None;
                self.lhs_tracking.last_lhs_binding = self
                    .lhs_tracking
                    .last_lhs_binding
                    .as_ref()
                    .and_then(negate_binding);
            }
            _ => {
                self.lhs_tracking.last_lhs_binding = None;
                self.report_error(ErrorKind::TypeError, "Cannot negate this type");
            }
        }
    }

    fn initialize_declared_variable(
        &mut self,
        var_id: VarId,
        name: &str,
        root_sym: Option<SymbolId>,
        suffixes: &[SuffixSegment],
    ) {
        let needs_init = matches!(
            self.variables.get(var_id),
            VarValue::Undefined | VarValue::NumericVar(NumericState::Numeric | NumericState::Undefined)
        );
        if !needs_init {
            return;
        }

        let Some(root_sym) = root_sym else {
            return;
        };
        let Some(declared_ty) = self.var_trie.declared_type(root_sym, suffixes) else {
            return;
        };

        let val = match declared_ty {
            Type::Numeric => VarValue::NumericVar(NumericState::Numeric),
            Type::Boolean => VarValue::Known(Value::Boolean(false)),
            Type::String => VarValue::Known(Value::String(Arc::from(""))),
            Type::Path => VarValue::Known(Value::Path(Path::default())),
            Type::Pen => VarValue::Known(Value::Pen(Pen::circle(0.0))),
            Type::Picture => VarValue::Known(Value::Picture(Picture::default())),
            Type::PairType => self.alloc_pair_value(name),
            Type::ColorType => self.alloc_color_value(name),
            Type::TransformType => self.alloc_transform_value(name),
            _ => return,
        };
        self.variables.set(var_id, val);
    }

    /// Resolve a variable name to its value.
    fn resolve_variable(
        &mut self,
        sym: Option<SymbolId>,
        name: &str,
        suffixes: &[SuffixSegment],
    ) -> InterpResult<()> {
        let var_id = self.variables.lookup(name);
        self.initialize_declared_variable(var_id, name, sym, suffixes);
        // Track last scanned variable for assignment LHS
        self.lhs_tracking.last_lhs_binding = Some(LhsBinding::Variable {
            id: var_id,
            negated: false,
        });

        match self.variables.get(var_id).clone() {
            VarValue::Known(v) => {
                self.cur_expr.exp = v.clone();
                self.cur_expr.ty = v.ty();
                self.cur_expr.dep = match &v {
                    Value::Numeric(n) => Some(const_dep(*n)),
                    _ => None,
                };
                self.cur_expr.pair_dep = if let Value::Pair(x, y) = &v {
                    Some((const_dep(*x), const_dep(*y)))
                } else {
                    None
                };
            }
            VarValue::NumericVar(NumericState::Known(v)) => {
                self.cur_expr.exp = Value::Numeric(v);
                self.cur_expr.ty = Type::Known;
                self.cur_expr.dep = Some(const_dep(v));
                self.cur_expr.pair_dep = None;
            }
            VarValue::NumericVar(NumericState::Independent { .. }) => {
                self.cur_expr.exp = Value::Numeric(0.0);
                self.cur_expr.ty = Type::Independent;
                self.cur_expr.dep = Some(single_dep(var_id));
                self.cur_expr.pair_dep = None;
            }
            VarValue::NumericVar(NumericState::Dependent(dep)) => {
                self.cur_expr.exp = Value::Numeric(crate::equation::constant_value(&dep).unwrap_or(0.0));
                self.cur_expr.ty = Type::Dependent;
                self.cur_expr.dep = Some(dep);
                self.cur_expr.pair_dep = None;
            }
            VarValue::NumericVar(NumericState::Numeric | NumericState::Undefined)
            | VarValue::Undefined => {
                self.variables.make_independent(var_id);
                self.cur_expr.exp = Value::Numeric(0.0);
                self.cur_expr.ty = Type::Independent;
                self.cur_expr.dep = Some(single_dep(var_id));
                self.cur_expr.pair_dep = None;
            }
            VarValue::Pair { x, y } => {
                let xv = self.variables.known_value(x).unwrap_or(0.0);
                let yv = self.variables.known_value(y).unwrap_or(0.0);
                self.cur_expr.exp = Value::Pair(xv, yv);
                self.cur_expr.ty = Type::PairType;
                self.cur_expr.dep = None;
                self.cur_expr.pair_dep = Some((self.numeric_dep_for_var(x), self.numeric_dep_for_var(y)));
            }
            VarValue::Color { r, g, b } => {
                let rv = self.variables.known_value(r).unwrap_or(0.0);
                let gv = self.variables.known_value(g).unwrap_or(0.0);
                let bv = self.variables.known_value(b).unwrap_or(0.0);
                self.cur_expr.exp = Value::Color(Color::new(rv, gv, bv));
                self.cur_expr.ty = Type::ColorType;
                self.cur_expr.dep = None;
                self.cur_expr.pair_dep = None;
            }
            VarValue::Transform {
                tx,
                ty,
                txx,
                txy,
                tyx,
                tyy,
            } => {
                let parts = [tx, ty, txx, txy, tyx, tyy]
                    .map(|id| self.variables.known_value(id).unwrap_or(0.0));
                self.cur_expr.exp = Value::Transform(Transform {
                    tx: parts[0],
                    ty: parts[1],
                    txx: parts[2],
                    txy: parts[3],
                    tyx: parts[4],
                    tyy: parts[5],
                });
                self.cur_expr.ty = Type::TransformType;
                self.cur_expr.dep = None;
                self.cur_expr.pair_dep = None;
            }
        }
        Ok(())
    }

    // =======================================================================
    // Error handling
    // =======================================================================

    /// Record a non-fatal error.
    fn report_error(&mut self, kind: ErrorKind, message: impl Into<String>) {
        let msg = message.into();
        self.errors.push(InterpreterError::new(kind, msg));
    }

    // =======================================================================
    // Public interface
    // =======================================================================

    /// Run a `MetaPost` program from source text.
    pub fn run(&mut self, source: &str) -> InterpResult<()> {
        self.input.push_source(source);
        self.get_x_next();

        while self.cur.command != Command::Stop {
            self.do_statement()?;
        }

        Ok(())
    }

    /// Get the output pictures.
    #[must_use]
    pub fn output(&self) -> &[Picture] {
        &self.picture_state.pictures
    }

    /// Get the current picture being built.
    #[must_use]
    pub const fn current_picture(&self) -> &Picture {
        &self.picture_state.current_picture
    }

    /// Get the current figure number, if one is active.
    #[must_use]
    pub const fn current_fig(&self) -> Option<i32> {
        self.picture_state.current_fig
    }

    /// Get the current drawing defaults.
    #[must_use]
    pub const fn drawing_state(&self) -> &DrawingState {
        &self.picture_state.drawing_state
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
    fn division_by_variable() {
        // Regression: `360/n` was miscomputed as `360*n` because the
        // fraction check in scan_primary consumed `/` without restoring
        // it when the denominator was a variable (not a numeric literal).
        let mut interp = Interpreter::new();
        interp.run("numeric n; n := 5; show 360/n;").unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("72"), "expected 72 in: {msg}");
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
    fn exitif_outside_loop_reports_error() {
        let mut interp = Interpreter::new();
        interp.run("exitif true;").unwrap();

        let errs: Vec<_> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Error)
            .collect();
        assert!(
            errs.iter().any(|e| e.kind == crate::error::ErrorKind::BadExitIf),
            "expected BadExitIf, got: {errs:?}"
        );
    }

    #[test]
    fn exitif_outside_loop_does_not_leak_into_future_forever() {
        let mut interp = Interpreter::new();
        interp
            .run(concat!(
                "numeric n; n := 0;\n",
                "exitif true;\n",
                "forever: n := n + 1; exitif n = 2; endfor;\n",
                "show n;\n",
            ))
            .unwrap();

        let errs: Vec<_> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Error)
            .collect();
        assert!(
            errs.iter().any(|e| e.kind == crate::error::ErrorKind::BadExitIf),
            "expected BadExitIf from top-level exitif, got: {errs:?}"
        );

        let infos: Vec<_> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Info)
            .map(|e| e.message.clone())
            .collect();
        assert!(
            infos.iter().any(|m| m.contains('2')),
            "expected loop to reach n=2, got infos: {infos:?}"
        );
    }

    #[test]
    fn nested_forever_loops_keep_outer_replay_state() {
        // Regression: nested `forever` loops used a single pending body slot,
        // so an inner loop could clobber outer replay state.
        let mut interp = Interpreter::new();
        interp
            .run(concat!(
                "numeric nouter; nouter := 0;\n",
                "forever:\n",
                "  nouter := nouter + 1;\n",
                "  forever: exitif true; endfor;\n",
                "  exitif nouter > 2;\n",
                "endfor;\n",
                "show nouter;\n",
            ))
            .unwrap();

        let errors: Vec<_> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Error)
            .collect();
        assert!(errors.is_empty(), "unexpected errors: {errors:?}");

        let infos: Vec<_> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Info)
            .map(|e| e.message.clone())
            .collect();
        assert!(
            infos.iter().any(|m| m.contains('3')),
            "expected outer=3 in infos: {infos:?}"
        );
    }

    #[test]
    fn nested_forever_exitif_equals_is_comparison() {
        // Regression: `exitif i = 2` inside expansion context must be parsed
        // as a boolean comparison, not statement equation semantics.
        let mut interp = Interpreter::new();
        interp
            .run(concat!(
                "numeric nouter, i;\n",
                "nouter := 0;\n",
                "forever:\n",
                "  nouter := nouter + 1;\n",
                "  i := 0;\n",
                "  forever: i := i + 1; exitif i = 2; endfor;\n",
                "  exitif nouter = 2;\n",
                "endfor;\n",
                "show nouter; show i;\n",
            ))
            .unwrap();

        let errors: Vec<_> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Error)
            .collect();
        assert!(errors.is_empty(), "unexpected errors: {errors:?}");

        let infos: Vec<_> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Info)
            .map(|e| e.message.clone())
            .collect();
        assert!(
            infos.iter().any(|m| m.contains('2')),
            "expected show outputs containing 2, got infos: {infos:?}"
        );
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
    fn expandafter_text_macro_scantokens() {
        // expandafter mymac scantokens "abc"; should NOT consume the
        // statement after it.  The `;` terminates the text parameter,
        // and `message "B"` must still execute.
        let mut interp = Interpreter::new();
        interp
            .run(concat!(
                "def mymac text t = message \"in mymac\"; enddef;\n",
                "message \"A\";\n",
                "expandafter mymac scantokens \"abc\";\n",
                "message \"B\";\n",
                "message \"C\";\n",
                "end\n",
            ))
            .unwrap();
        let msgs: Vec<&str> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Info)
            .map(|e| e.message.as_str())
            .collect();
        assert_eq!(
            msgs,
            vec!["A", "in mymac", "B", "C"],
            "expandafter consumed a following statement: {msgs:?}"
        );
    }

    #[test]
    fn expandafter_simple_token() {
        // expandafter with a non-expandable B should just reorder.
        let mut interp = Interpreter::new();
        interp
            .run("expandafter message \"hello\"; end")
            .unwrap();
        let msgs: Vec<&str> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Info)
            .map(|e| e.message.as_str())
            .collect();
        assert_eq!(msgs, vec!["hello"]);
    }

    #[test]
    fn expandafter_triple_redefine_macro() {
        // The triple-expandafter pattern from boxes.mp:
        //   expandafter def expandafter clearboxes expandafter =
        //     clearboxes message "hi";
        //   enddef;
        // This should APPEND `message "hi"` to clearboxes' body.
        // Step by step:
        //   1. expandafter reads A=`def`, reads B=`expandafter`, B is expandable
        //   2. Inner expandafter reads A=`clearboxes`, reads B=`expandafter`, B is expandable
        //   3. Innermost expandafter reads A=`=`, reads B=`clearboxes` (a defined macro)
        //   4. One-step expand of clearboxes pushes its body (empty at first)
        //   5. `=` is placed in front → scanner sees `= <old body>`
        //   6. Back in step 2: `clearboxes` is placed in front → `clearboxes = <old body>`
        //   7. Back in step 1: `def` is placed in front → `def clearboxes = <old body> message "hi"; enddef;`
        let mut interp = Interpreter::new();
        interp
            .run(concat!(
                "def clearboxes = enddef;\n",
                "expandafter def expandafter clearboxes expandafter =\n",
                "  clearboxes message \"hi\";\n",
                "enddef;\n",
                "clearboxes;\n",
                "end\n",
            ))
            .unwrap();
        let msgs: Vec<&str> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Info)
            .map(|e| e.message.as_str())
            .collect();
        assert_eq!(
            msgs,
            vec!["hi"],
            "triple expandafter should have appended 'message \"hi\"' to clearboxes: {msgs:?}"
        );
    }

    #[test]
    fn expandafter_triple_accumulate() {
        // Multiple rounds of triple-expandafter accumulation.
        let mut interp = Interpreter::new();
        interp
            .run(concat!(
                "def clearboxes = enddef;\n",
                "expandafter def expandafter clearboxes expandafter =\n",
                "  clearboxes message \"A\";\n",
                "enddef;\n",
                "expandafter def expandafter clearboxes expandafter =\n",
                "  clearboxes message \"B\";\n",
                "enddef;\n",
                "clearboxes;\n",
                "end\n",
            ))
            .unwrap();
        let msgs: Vec<&str> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Info)
            .map(|e| e.message.as_str())
            .collect();
        assert_eq!(
            msgs,
            vec!["A", "B"],
            "triple expandafter should accumulate: {msgs:?}"
        );
    }

    #[test]
    fn known_unknown_operators() {
        let mut interp = Interpreter::new();
        interp
            .run(concat!(
                "numeric x;\n",
                "if unknown x: message \"x unknown\"; fi\n",
                "x := 5;\n",
                "if known x: message \"x known\"; fi\n",
                "pair p;\n",
                "if unknown xpart p: message \"xpart p unknown\"; fi\n",
                "p := (1,2);\n",
                "if known xpart p: message \"xpart p known\"; fi\n",
                "end\n",
            ))
            .unwrap();
        let msgs: Vec<&str> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Info)
            .map(|e| e.message.as_str())
            .collect();
        assert_eq!(
            msgs,
            vec!["x unknown", "x known", "xpart p unknown", "xpart p known"]
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

    #[test]
    fn mediation_preserves_numeric_endpoint_dependencies() {
        let mut interp = Interpreter::new();
        interp
            .run("numeric a,b,c,x; a := 0.25; x = a[b,c]; b = 2; c = 10; show x;")
            .unwrap();

        let infos: Vec<_> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Info)
            .map(|e| e.message.clone())
            .collect();
        assert!(infos.iter().any(|m| m.contains('4')), "expected x=4 in: {infos:?}");
    }

    #[test]
    fn mediation_preserves_pair_endpoint_dependencies() {
        let mut interp = Interpreter::new();
        interp
            .run("numeric a; pair b,c,p; a := 0.5; p = a[b,c]; b = (2,4); c = (6,8); show p;")
            .unwrap();

        let infos: Vec<_> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Info)
            .map(|e| e.message.clone())
            .collect();
        assert!(infos.iter().any(|m| m.contains("(4,6)")), "expected p=(4,6) in: {infos:?}");
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
            interp
                .errors
                .iter()
                .any(|e| e.message.contains(">> (1,0)") || e.message.contains(">> (1,-0)")),
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
        interp.input.push_source("+ 3;");
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
        interp.input.push_source(";");
        // Set up a capsule with a pair value
        interp.cur_expr.exp = Value::Pair(5.0, 10.0);
        interp.cur_expr.ty = Type::PairType;
        // Push it back — this goes on top of the source
        interp.back_expr();
        // Now get_x_next reads from the capsule token list (top of stack)
        interp.get_x_next();
        assert_eq!(interp.cur.command, Command::CapsuleToken);
        interp.scan_primary().unwrap();
        assert_eq!(interp.cur_expr.ty, Type::PairType);
        assert_eq!(interp.cur_expr.exp.as_pair(), Some((5.0, 10.0)));
    }

    #[test]
    fn back_expr_numeric_in_expression() {
        // Push a numeric capsule and verify it can participate in arithmetic
        let mut interp = Interpreter::new();
        // Push source first (bottom of stack)
        interp.input.push_source("+ 3;");
        // Then push capsule (top of stack)
        interp.cur_expr.exp = Value::Numeric(7.0);
        interp.cur_expr.ty = Type::Known;
        interp.back_expr();
        interp.get_x_next();
        interp.scan_expression().unwrap();
        // Should evaluate to 7 + 3 = 10
        assert_eq!(interp.cur_expr.exp, Value::Numeric(10.0));
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
    fn reports_missing_right_paren_in_parenthesized_expression() {
        let mut interp = Interpreter::new();
        interp.run("show (1+2; show 7;").unwrap();

        let errors: Vec<_> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Error)
            .collect();
        assert!(
            errors.iter().any(|e| {
                e.kind == crate::error::ErrorKind::MissingToken && e.message.contains("Expected `)`")
            }),
            "expected missing right paren diagnostic, got: {errors:?}"
        );
    }

    #[test]
    fn reports_missing_right_bracket_in_mediation() {
        let mut interp = Interpreter::new();
        interp.run("show 0.5[(0,0),(2,2); show 9;").unwrap();

        let errors: Vec<_> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Error)
            .collect();
        assert!(
            errors.iter().any(|e| {
                e.kind == crate::error::ErrorKind::MissingToken && e.message.contains("Expected `]`")
            }),
            "expected missing right bracket diagnostic, got: {errors:?}"
        );
    }

    #[test]
    fn reports_missing_right_brace_in_path_direction() {
        let mut interp = Interpreter::new();
        interp
            .run("path p; p := (0,0){curl 1..(1,0); show 1;")
            .unwrap();

        let errors: Vec<_> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Error)
            .collect();
        assert!(
            errors.iter().any(|e| {
                e.kind == crate::error::ErrorKind::MissingToken && e.message.contains("Expected `}`")
            }),
            "expected missing right brace diagnostic, got: {errors:?}"
        );
    }

    #[test]
    fn scanner_unterminated_string_is_reported() {
        let mut interp = Interpreter::new();
        interp.run("show \"unterminated").unwrap();

        let errors: Vec<_> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Error)
            .collect();
        assert!(
            errors
                .iter()
                .any(|e| e.kind == crate::error::ErrorKind::UnterminatedString),
            "expected unterminated-string scanner diagnostic, got: {errors:?}"
        );
    }

    #[test]
    fn scanner_invalid_character_is_reported() {
        let mut interp = Interpreter::new();
        let src = format!("show 1;{}show 2;", '\u{1f}');
        interp.run(&src).unwrap();

        let errors: Vec<_> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Error)
            .collect();
        assert!(
            errors
                .iter()
                .any(|e| e.kind == crate::error::ErrorKind::InvalidCharacter),
            "expected invalid-character scanner diagnostic, got: {errors:?}"
        );
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
              addto pic doublepath (w,w)..(w+d,w);
              w := w+d;
              pic shifted (0,d)
              endgroup
            enddef;
            tertiarydef p _off_ d =
              begingroup w:=w+d;
              p shifted (0,d)
              endgroup
            enddef;
            vardef dashpattern(text t) =
              save on, off, w;
              let on=_on_;
              let off=_off_;
              w = 0;
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
    fn dashed_line_produces_dash_pattern() {
        // Verify that `dashed dashpattern(...)` applies stroke-dasharray to the
        // output picture and doesn't leak intermediate strokes.
        let mut interp = Interpreter::new();
        interp
            .run(
                r#"
            delimiters ();
            tertiarydef p _on_ d =
              begingroup save pic;
              picture pic; pic=p;
              addto pic doublepath (w,w)..(w+d,w);
              w := w+d;
              pic shifted (0,d)
              endgroup
            enddef;
            tertiarydef p _off_ d =
              begingroup w:=w+d;
              p shifted (0,d)
              endgroup
            enddef;
            vardef dashpattern(text t) =
              save on, off, w;
              let on=_on_;
              let off=_off_;
              w = 0;
              nullpicture t
            enddef;
            addto currentpicture doublepath (0,0)..(30,0)
              dashed dashpattern(on 2 off 3);
        "#,
            )
            .unwrap();

        let errors: Vec<_> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Error)
            .collect();
        assert!(errors.is_empty(), "errors: {errors:?}");

        // The picture should have exactly one Stroke object (the dashed line).
        let objects = &interp.current_picture().objects;
        assert_eq!(
            objects.len(),
            1,
            "expected 1 object, got {}: {:?}",
            objects.len(),
            objects
        );

        if let postmeta_graphics::types::GraphicsObject::Stroke(ref stroke) = objects[0] {
            let dash = stroke.dash.as_ref().expect("expected dash pattern");
            // on 2, off 3 → dashes = [2.0, 3.0]
            assert_eq!(dash.dashes.len(), 2, "dashes: {:?}", dash.dashes);
            assert!((dash.dashes[0] - 2.0).abs() < 0.01, "on={}", dash.dashes[0]);
            assert!(
                (dash.dashes[1] - 3.0).abs() < 0.01,
                "off={}",
                dash.dashes[1]
            );
        } else {
            panic!("expected Stroke, got {:?}", objects[0]);
        }
    }

    #[test]
    fn dashed_withdots_uses_leading_offset() {
        // `dashpattern(off 2.5 on 0 off 2.5)` should produce one zero-length
        // dash every 5 units, offset by 2.5 from the path start.
        let mut interp = Interpreter::new();
        interp
            .run(
                r#"
            delimiters ();
            tertiarydef p _on_ d =
              begingroup save pic;
              picture pic; pic=p;
              addto pic doublepath (w,w)..(w+d,w);
              w := w+d;
              pic shifted (0,d)
              endgroup
            enddef;
            tertiarydef p _off_ d =
              begingroup w:=w+d;
              p shifted (0,d)
              endgroup
            enddef;
            vardef dashpattern(text t) =
              save on, off, w;
              let on=_on_;
              let off=_off_;
              w = 0;
              nullpicture t
            enddef;
            addto currentpicture doublepath (0,0)..(30,0)
              dashed dashpattern(off 2.5 on 0 off 2.5);
        "#,
            )
            .unwrap();

        let errors: Vec<_> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Error)
            .collect();
        assert!(errors.is_empty(), "errors: {errors:?}");

        let objects = &interp.current_picture().objects;
        assert_eq!(objects.len(), 1, "expected 1 object, got {}", objects.len());

        if let postmeta_graphics::types::GraphicsObject::Stroke(ref stroke) = objects[0] {
            let dash = stroke.dash.as_ref().expect("expected dash pattern");
            assert_eq!(dash.dashes.len(), 2, "dashes: {:?}", dash.dashes);
            assert!((dash.dashes[0] - 0.0).abs() < 0.01, "on={}", dash.dashes[0]);
            assert!(
                (dash.dashes[1] - 5.0).abs() < 0.01,
                "off={}",
                dash.dashes[1]
            );
            assert!((dash.offset - 2.5).abs() < 0.01, "offset={}", dash.offset);
        } else {
            panic!("expected Stroke, got {:?}", objects[0]);
        }
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
            .run("vardef foo(expr u)(expr v) = show u; show v enddef; foo(1)(2);")
            .unwrap();
        let infos: Vec<_> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Info)
            .map(|e| e.message.clone())
            .collect();
        assert_eq!(infos.len(), 2, "expected 2 show outputs, got: {infos:?}");
        assert!(infos.iter().any(|m| m.contains('1')), "expected u=1 in: {infos:?}");
        assert!(infos.iter().any(|m| m.contains('2')), "expected v=2 in: {infos:?}");
    }

    #[test]
    fn multiple_delimited_groups_allow_boundary_comma() {
        let mut interp = Interpreter::new();
        interp
            .run("vardef foo(expr u)(expr v)=show u; show v enddef; foo(4,5);")
            .unwrap();

        let errors: Vec<_> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Error)
            .collect();
        assert!(errors.is_empty(), "unexpected errors: {errors:?}");

        let infos: Vec<_> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Info)
            .map(|e| e.message.clone())
            .collect();
        assert!(infos.iter().any(|m| m.contains('4')), "expected u=4 in: {infos:?}");
        assert!(infos.iter().any(|m| m.contains('5')), "expected v=5 in: {infos:?}");
    }

    #[test]
    fn pair_equation_assigns_components() {
        let mut interp = Interpreter::new();
        interp
            .run("numeric t, u; (t,u) = (3.5, -2); show t; show u;")
            .unwrap();

        let messages: Vec<_> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Info)
            .map(|e| e.message.clone())
            .collect();
        assert!(
            messages.iter().any(|m| m.contains("3.5")),
            "expected t=3.5 in messages: {messages:?}"
        );
        assert!(
            messages.iter().any(|m| m.contains("-2")),
            "expected u=-2 in messages: {messages:?}"
        );
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

    #[test]
    fn plain_beginfig_draw_endfig() {
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
        interp
            .run("input plain; beginfig(1); draw (0,0)..(10,10); endfig; end;")
            .unwrap();

        let errors = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Error)
            .count();
        assert!(errors == 0, "expected 0 errors, got {errors}");
        assert!(!interp.output().is_empty(), "expected shipped pictures");
    }

    #[test]
    fn plain_path_examples_39_and_56() {
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
        interp
            .run(
                "input plain;
                 beginfig(39);
                   draw (0,0) --- (0,1cm) .. (1cm,0) .. (1cm,1cm);
                 endfig;
                 beginfig(56);
                   draw (0,0) .. tension 2 .. (1cm,1cm) .. (2cm,0);
                 endfig;
                 end;",
            )
            .unwrap();

        let errors = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Error)
            .count();
        assert!(errors == 0, "expected 0 errors, got {errors}");
        assert!(interp.output().len() >= 2, "expected shipped pictures");
    }

    #[test]
    fn plain_fill_has_no_stroke_pen() {
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
        interp
            .run("input plain; beginfig(1); fill fullcircle scaled 10bp; endfig; end;")
            .unwrap();

        let errors = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Error)
            .count();
        assert!(errors == 0, "expected 0 errors, got {errors}");

        let pic = interp.output().last().expect("expected shipped picture");
        let fill = match pic.objects.first().expect("expected one object") {
            postmeta_graphics::types::GraphicsObject::Fill(fill) => fill,
            other => panic!("expected Fill object, got {other:?}"),
        };
        assert!(fill.pen.is_none(), "fill should not carry stroke pen");
    }

    #[test]
    fn plain_filldraw_withpen_sets_stroke_pen() {
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
        interp
            .run(
                "input plain;
                 beginfig(1);
                   filldraw fullcircle scaled 10bp withpen pencircle scaled 2bp;
                 endfig;
                 end;",
            )
            .unwrap();

        let errors = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Error)
            .count();
        assert!(errors == 0, "expected 0 errors, got {errors}");

        let pic = interp.output().last().expect("expected shipped picture");
        let fill = match pic.objects.first().expect("expected one object") {
            postmeta_graphics::types::GraphicsObject::Fill(fill) => fill,
            other => panic!("expected Fill object, got {other:?}"),
        };

        let pen = fill.pen.as_ref().expect("filldraw should keep stroke pen");
        match pen {
            postmeta_graphics::types::Pen::Elliptical(t) => {
                assert!((t.txx - 1.0).abs() < 1e-9, "unexpected txx={}", t.txx);
                assert!((t.tyy - 1.0).abs() < 1e-9, "unexpected tyy={}", t.tyy);
            }
            other => panic!("expected elliptical pen, got {other:?}"),
        }
    }

    #[test]
    fn plain_hide_postfix_preserves_left_expression() {
        use crate::filesystem::FileSystem;
        use crate::variables::VarValue;

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
        interp
            .run(
                "input plain;
                 path p;
                 cuttings := (0,0)--(1cm,0);
                 p := ((0,0)--(1cm,0)) hide(cuttings:=reverse cuttings);
                 end;",
            )
            .unwrap();

        let errors = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Error)
            .count();
        assert!(errors == 0, "expected 0 errors, got {errors}");

        let pid = interp
            .variables
            .lookup_existing("p")
            .expect("path variable p should exist");
        assert!(matches!(
            interp.variables.get(pid),
            VarValue::Known(crate::types::Value::Path(_))
        ));
    }

    #[test]
    fn plain_drawarrow_example_17() {
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
        interp
            .run(
                "input plain;
                 beginfig(17);
                   pair A, B, C;
                   A := (0,0); B := (1cm,0); C := (0,1cm);
                   drawarrow C--B--A;
                   drawarrow A--C withpen pencircle scaled 2bp;
                 endfig;
                 end;",
            )
            .unwrap();

        let errors = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Error)
            .count();
        assert!(errors == 0, "expected 0 errors, got {errors}");
        assert!(!interp.output().is_empty(), "expected shipped pictures");
    }

    #[test]
    fn plain_drawdblarrow_example_18() {
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
        interp
            .run(
                "input plain;
                 beginfig(18);
                   pair A, B, C;
                   A := (0,0); B := (1cm,0); C := (0,1cm);
                   draw C--B--A--cycle;
                   drawdblarrow A--C withpen pencircle scaled 2bp;
                 endfig;
                 end;",
            )
            .unwrap();

        let errors = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Error)
            .count();
        assert!(errors == 0, "expected 0 errors, got {errors}");
        assert!(!interp.output().is_empty(), "expected shipped pictures");
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

    // -----------------------------------------------------------------------
    // Trailing tokens after undelimited macro params
    // -----------------------------------------------------------------------

    #[test]
    fn trailing_tokens_after_undelimited_expr() {
        // A macro with undelimited `primary` param stops scanning after the
        // primary.  The trailing `;` must survive and terminate the statement.
        let mut interp = Interpreter::new();
        interp
            .run("def greet primary x = show x enddef; greet 42;")
            .unwrap();
        let errors: Vec<_> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Error)
            .collect();
        assert!(errors.is_empty(), "unexpected errors: {errors:?}");
        let show_msg = interp
            .errors
            .iter()
            .find(|e| e.severity == crate::error::Severity::Info);
        assert!(
            show_msg.is_some() && show_msg.unwrap().message.contains("42"),
            "expected show 42"
        );
    }

    #[test]
    fn vardef_returns_value() {
        // A vardef should return the value of its last expression.
        let mut interp = Interpreter::new();
        interp
            .run("vardef triple(expr x) = 3 * x enddef; show triple(7);")
            .unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("21"), "expected 21 in: {msg}");
    }

    #[test]
    fn save_restores_variable_binding() {
        let mut interp = Interpreter::new();
        interp
            .run("numeric x; x := 1; begingroup save x; x := 2; endgroup; show x;")
            .unwrap();

        let errors: Vec<_> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Error)
            .collect();
        assert!(errors.is_empty(), "unexpected errors: {errors:?}");

        let msg = interp
            .errors
            .iter()
            .find(|e| e.severity == crate::error::Severity::Info)
            .map(|e| e.message.clone())
            .unwrap_or_default();
        assert!(msg.contains("1"), "expected x to restore to 1, got: {msg}");
    }

    #[test]
    fn whatever_calls_are_independent() {
        let mut interp = Interpreter::new();
        interp
            .run(
                "vardef whatever = save ?; ? enddef; \
                 numeric a,b; \
                 a=whatever; b=whatever; \
                 a=0; b=1; \
                 show a; show b;",
            )
            .unwrap();

        let errors: Vec<_> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Error)
            .collect();
        assert!(errors.is_empty(), "unexpected errors: {errors:?}");

        let infos: Vec<_> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Info)
            .map(|e| e.message.clone())
            .collect();
        assert!(
            infos.iter().any(|m| m.contains(">> 0")),
            "expected show a=0, got: {infos:?}"
        );
        assert!(
            infos.iter().any(|m| m.contains(">> 1")),
            "expected show b=1, got: {infos:?}"
        );
    }

    #[test]
    fn whatever_times_pair_preserves_dependency() {
        let mut interp = Interpreter::new();
        interp
            .run(
                "vardef whatever = save ?; ? enddef; \
                 pair o; \
                 o-(1,2)=whatever*(3,4); \
                 o-(5,6)=whatever*(7,8); \
                 show o;",
            )
            .unwrap();

        let errors: Vec<_> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Error)
            .collect();
        assert!(errors.is_empty(), "unexpected errors: {errors:?}");
    }

    #[test]
    fn whatever_line_intersection_solves_point() {
        let mut interp = Interpreter::new();
        interp
            .run(
                "vardef whatever = save ?; ? enddef; \
                 pair A,B,C,D,M; \
                 A=(0,0); B=(2,3); \
                 C=(1,0); D=(-1,2); \
                 M = whatever [A,B]; \
                 M = whatever [C,D];",
            )
            .unwrap();

        let errors: Vec<_> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Error)
            .collect();
        assert!(errors.is_empty(), "unexpected errors: {errors:?}");

        let mid = interp
            .variables
            .lookup_existing("M")
            .expect("M should exist");
        let (xid, yid) = match interp.variables.get(mid) {
            crate::variables::VarValue::Pair { x, y } => (*x, *y),
            other => panic!("M should be a pair, got {other:?}"),
        };

        let mx = interp.variables.known_value(xid).unwrap_or(0.0);
        let my = interp.variables.known_value(yid).unwrap_or(0.0);

        assert!((mx - 0.4).abs() < 0.01, "mx={mx}");
        assert!((my - 0.6).abs() < 0.01, "my={my}");
    }

    #[test]
    fn whatever_perpendicular_bisectors_solve_circumcenter() {
        let mut interp = Interpreter::new();
        interp
            .run(
                "vardef whatever = save ?; ? enddef; \
                 pair A,B,C,O; \
                 A=(0,0); B=(3,0); C=(1,2); \
                 O - 1/2[B,C] = whatever * (B-C) rotated 90; \
                 O - 1/2[A,B] = whatever * (A-B) rotated 90;",
            )
            .unwrap();

        let errors: Vec<_> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Error)
            .collect();
        assert!(errors.is_empty(), "unexpected errors: {errors:?}");

        let oid = interp
            .variables
            .lookup_existing("O")
            .expect("O should exist");
        let (xid, yid) = match interp.variables.get(oid) {
            crate::variables::VarValue::Pair { x, y } => (*x, *y),
            other => panic!("O should be a pair, got {other:?}"),
        };

        let ox = interp.variables.known_value(xid).unwrap_or(0.0);
        let oy = interp.variables.known_value(yid).unwrap_or(0.0);

        assert!((ox - 1.5).abs() < 0.01, "ox={ox}");
        assert!((oy - 0.5).abs() < 0.01, "oy={oy}");
    }

    #[test]
    fn save_localizes_suffix_bindings_in_recursive_vardef() {
        let mut interp = Interpreter::new();
        interp
            .run(
                "vardef test(expr n) = \
                   save a; numeric a[]; \
                   a[1] := n; \
                   if n>0: \
                     test(n-1); \
                   else: \
                   fi; \
                   show a[1]; \
                 enddef; \
                 test(3);",
            )
            .unwrap();

        let errors: Vec<_> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Error)
            .collect();
        assert!(errors.is_empty(), "unexpected errors: {errors:?}");

        let infos: Vec<_> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Info)
            .map(|e| e.message.clone())
            .collect();

        assert_eq!(infos.len(), 4, "expected 4 recursive samples, got: {infos:?}");
        for i in 0..4 {
            assert!(
                infos.iter().any(|m| m.contains(&format!(">> {i}"))),
                "missing sample {i} in {infos:?}"
            );
        }
    }

    // -----------------------------------------------------------------------
    // btex/etex and infont
    // -----------------------------------------------------------------------

    #[test]
    fn btex_etex_produces_string() {
        // btex Hello World etex should produce a string "Hello World"
        let mut interp = Interpreter::new();
        interp
            .run(r#"string s; s = btex Hello World etex; show s;"#)
            .unwrap();
        let msg = &interp.errors[0].message;
        assert!(
            msg.contains("Hello World"),
            "expected 'Hello World' in: {msg}"
        );
    }

    #[test]
    fn infont_produces_picture() {
        // "abc" infont "cmr10" should produce a picture
        let mut interp = Interpreter::new();
        interp
            .run(r#"picture p; p = "abc" infont "cmr10"; show p;"#)
            .unwrap();
        // The show output should indicate a picture value
        let msg = &interp.errors[0].message;
        // A picture show typically shows the type or contents
        assert!(
            !msg.contains("error"),
            "infont should not produce an error: {msg}"
        );
    }

    #[test]
    fn infont_text_has_bbox() {
        // Corner operators on an infont picture should give non-zero bbox
        let mut interp = Interpreter::new();
        interp
            .run(r#"picture p; p = "Hello" infont "cmr10"; show lrcorner p;"#)
            .unwrap();
        let msg = &interp.errors[0].message;
        // lrcorner should have positive x and negative y (descender)
        assert!(msg.contains(','), "expected a pair in: {msg}");
    }

    #[test]
    fn corner_operators_on_picture() {
        // Test all four corners on a simple filled picture
        let mut interp = Interpreter::new();
        interp
            .run("picture p; p = \"test\" infont \"cmr10\"; show llcorner p; show urcorner p;")
            .unwrap();
        let infos: Vec<_> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Info)
            .map(|e| e.message.clone())
            .collect();
        assert_eq!(infos.len(), 2, "expected 2 corner values, got: {infos:?}");
    }

    #[test]
    fn corner_operators_on_path() {
        // Corner operators should work on paths too
        let mut interp = Interpreter::new();
        interp
            .run("path p; p = (0,0)..(10,20)..(30,5); show llcorner p; show urcorner p;")
            .unwrap();
        let infos: Vec<_> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Info)
            .map(|e| e.message.clone())
            .collect();
        assert_eq!(infos.len(), 2, "expected 2 corner values, got: {infos:?}");
    }

    #[test]
    fn vardef_at_suffix_with_params() {
        // vardef foo@#(expr s) should bind @# to the suffix and s to the arg
        let mut interp = Interpreter::new();
        interp
            .run(r#"vardef foo@#(expr s) = show str @#; show s enddef; foo.bar("hello");"#)
            .unwrap();
        let infos: Vec<_> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Info)
            .map(|e| e.message.clone())
            .collect();
        assert_eq!(infos.len(), 2, "expected 2 show outputs, got: {infos:?}");
        assert!(
            infos[0].contains("bar"),
            "expected @# = bar, got: {}",
            infos[0]
        );
        assert!(
            infos[1].contains("hello"),
            "expected s = hello, got: {}",
            infos[1]
        );
    }

    // -----------------------------------------------------------------------
    // Substring reclassification (primary binary: substring X of Y)
    // -----------------------------------------------------------------------

    #[test]
    fn substring_of_basic() {
        // substring (1,3) of "hello" = "el"
        let mut interp = Interpreter::new();
        interp
            .run(r#"show substring (1,3) of "hello";"#)
            .unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("el"), "expected 'el' in: {msg}");
    }

    #[test]
    fn substring_of_full_range() {
        // substring (0,5) of "hello" = "hello"
        let mut interp = Interpreter::new();
        interp
            .run(r#"show substring (0,5) of "hello";"#)
            .unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("hello"), "expected 'hello' in: {msg}");
    }

    #[test]
    fn substring_of_empty() {
        // substring (2,2) of "hello" = ""
        let mut interp = Interpreter::new();
        interp
            .run(r#"show substring (2,2) of "hello";"#)
            .unwrap();
        let msg = &interp.errors[0].message;
        // Empty string shows as ""
        assert!(
            msg.contains("\"\"") || msg.contains(">>  ") || msg.ends_with(">> "),
            "expected empty string in: {msg}"
        );
    }

    #[test]
    fn substring_of_utf8_is_char_boundary_safe() {
        // Regression: substring used byte slicing and could panic on UTF-8.
        let mut interp = Interpreter::new();
        interp
            .run("show substring (1,2) of \"a😊b\";")
            .unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("😊"), "expected emoji substring in: {msg}");
    }

    #[test]
    fn length_of_utf8_counts_characters() {
        let mut interp = Interpreter::new();
        interp.run("show length \"a😊b\";").unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains('3'), "expected length 3 in: {msg}");
    }

    // -----------------------------------------------------------------------
    // Equals-means-equation flag (= as comparison vs equation)
    // -----------------------------------------------------------------------

    #[test]
    fn equals_as_comparison_in_if() {
        // Inside `if`, `=` should be a comparison, not an equation
        let mut interp = Interpreter::new();
        interp
            .run("if 3 = 3: message \"yes\"; fi")
            .unwrap();
        let msgs: Vec<&str> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Info)
            .map(|e| e.message.as_str())
            .collect();
        assert_eq!(msgs, vec!["yes"]);
    }

    #[test]
    fn equals_as_comparison_in_exitif() {
        // `exitif n = 3` — the `=` must be comparison, not equation.
        // Uses `forever` + `exitif` since `for` pre-pushes all iterations.
        // `exitif` finishes the current iteration body; loop stops at endfor.
        let mut interp = Interpreter::new();
        interp
            .run(concat!(
                "numeric n, s; n := 0; s := 0;\n",
                "forever: s := s + 1; n := n + 1; exitif n = 3; endfor;\n",
                "show n;\n",
            ))
            .unwrap();
        let msg = interp
            .errors
            .iter()
            .find(|e| e.severity == crate::error::Severity::Info)
            .map(|e| e.message.as_str())
            .unwrap_or("");
        // Loop runs 3 times (n=1,2,3), exits when n=3
        assert!(msg.contains("3"), "expected 3 in: {msg}");
    }

    #[test]
    fn equals_as_equation_in_statement() {
        // At statement level, `=` should be an equation
        let mut interp = Interpreter::new();
        interp
            .run("numeric x; x = 42; show x;")
            .unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("42"), "expected 42 in: {msg}");
    }

    // -----------------------------------------------------------------------
    // Binary macro lookahead fix (tertiarydef in text params)
    // -----------------------------------------------------------------------

    #[test]
    fn tertiarydef_or_in_text_param() {
        // `or` is a tertiarydef. Using it inside a text parameter of a macro
        // should not duplicate the closing delimiter.
        let mut interp = Interpreter::new();
        interp
            .run(concat!(
                "tertiarydef a or b = if a: a else: b fi enddef;\n",
                "def test(text t) = t enddef;\n",
                "show test(false or true);\n",
            ))
            .unwrap();
        let errors: Vec<_> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Error)
            .collect();
        assert!(errors.is_empty(), "unexpected errors: {errors:?}");
        let msg = interp
            .errors
            .iter()
            .find(|e| e.severity == crate::error::Severity::Info)
            .map(|e| e.message.as_str())
            .unwrap_or("");
        assert!(msg.contains("true"), "expected true in: {msg}");
    }

    // -----------------------------------------------------------------------
    // String comparison operators
    // -----------------------------------------------------------------------

    #[test]
    fn string_less_than() {
        let mut interp = Interpreter::new();
        interp.run(r#"show "a" < "b";"#).unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("true"), "expected true in: {msg}");
    }

    #[test]
    fn string_greater_than() {
        let mut interp = Interpreter::new();
        interp.run(r#"show "z" > "a";"#).unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("true"), "expected true in: {msg}");
    }

    #[test]
    fn string_less_equal() {
        let mut interp = Interpreter::new();
        interp.run(r#"show "abc" <= "abd";"#).unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("true"), "expected true in: {msg}");
    }

    #[test]
    fn string_greater_equal_same() {
        let mut interp = Interpreter::new();
        interp.run(r#"show "abc" >= "abc";"#).unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("true"), "expected true in: {msg}");
    }

    #[test]
    fn string_comparison_false() {
        let mut interp = Interpreter::new();
        interp.run(r#"show "b" < "a";"#).unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("false"), "expected false in: {msg}");
    }

    // -----------------------------------------------------------------------
    // For-loop token substitution (for-as-expression)
    // -----------------------------------------------------------------------

    #[test]
    fn for_as_expression_sum() {
        // `for i=1,2,3: i + endfor 0` should evaluate to 6
        let mut interp = Interpreter::new();
        interp
            .run("show for i=1,2,3: i + endfor 0;")
            .unwrap();
        let msg = interp
            .errors
            .iter()
            .find(|e| e.severity == crate::error::Severity::Info)
            .map(|e| e.message.as_str())
            .unwrap_or("");
        assert!(msg.contains("6"), "expected 6 in: {msg}");
    }

    #[test]
    fn nested_for_substitutes_outer_loop_variable() {
        // Regression: outer `for` variables must substitute inside nested
        // loop bodies (example 132 relies on this).
        let mut interp = Interpreter::new();
        interp
            .run("for i=1 step 1 until 2: for j=1 step 1 until 2: show i; endfor; endfor;")
            .unwrap();

        let infos: Vec<_> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Info)
            .map(|e| e.message.clone())
            .collect();

        assert_eq!(infos.len(), 4, "expected 4 show outputs, got: {infos:?}");
        assert!(infos[0].contains("1"), "expected 1, got: {}", infos[0]);
        assert!(infos[1].contains("1"), "expected 1, got: {}", infos[1]);
        assert!(infos[2].contains("2"), "expected 2, got: {}", infos[2]);
        assert!(infos[3].contains("2"), "expected 2, got: {}", infos[3]);
    }

    #[test]
    fn nested_for_same_name_shadows_outer_loop_variable() {
        // Guardrail: if an inner loop reuses the same variable name, it
        // should shadow the outer loop variable.
        let mut interp = Interpreter::new();
        interp
            .run("for i=1 step 1 until 2: for i=10 step 1 until 11: show i; endfor; endfor;")
            .unwrap();

        let infos: Vec<_> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Info)
            .map(|e| e.message.clone())
            .collect();

        assert_eq!(infos.len(), 4, "expected 4 show outputs, got: {infos:?}");
        assert!(infos[0].contains("10"), "expected 10, got: {}", infos[0]);
        assert!(infos[1].contains("11"), "expected 11, got: {}", infos[1]);
        assert!(infos[2].contains("10"), "expected 10, got: {}", infos[2]);
        assert!(infos[3].contains("11"), "expected 11, got: {}", infos[3]);
    }

    #[test]
    fn collective_pair_subscript_is_pair_typed() {
        // Regression: `pair A[]` must make `A[1]` a pair, not a numeric.
        let mut interp = Interpreter::new();
        interp
            .run("pair A[]; show pair A[1]; show numeric A[1];")
            .unwrap();

        let infos: Vec<_> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Info)
            .map(|e| e.message.clone())
            .collect();

        assert_eq!(infos.len(), 2, "expected 2 show outputs, got: {infos:?}");
        assert!(infos[0].contains("true"), "expected pair test true, got: {}", infos[0]);
        assert!(infos[1].contains("false"), "expected numeric test false, got: {}", infos[1]);
    }

    #[test]
    fn collective_pair_subscript_works_in_for_sum_expression() {
        // Regression from examples 133/134: summing A[i] must stay pair arithmetic.
        let mut interp = Interpreter::new();
        let result = interp.run(concat!(
            "numeric n; n := 3;\n",
            "pair A[];\n",
            "for i=1 step 1 until n-1: A[i+1] - A[i] = (0,1); endfor;\n",
            "show (0,0) for i=1 step 1 until n: + A[i] endfor;\n",
        ));

        assert!(result.is_ok(), "expected run to succeed, got: {result:?}");
    }

    #[test]
    fn forsuffixes_iterates_suffixes() {
        // forsuffixes should iterate over suffix values
        let mut interp = Interpreter::new();
        interp
            .run(concat!(
                "numeric a.x, a.y, a.z;\n",
                "a.x := 10; a.y := 20; a.z := 30;\n",
                "numeric s; s := 0;\n",
                "forsuffixes $=x,y,z: s := s + a$; endfor;\n",
                "show s;\n",
            ))
            .unwrap();
        let msg = interp
            .errors
            .iter()
            .find(|e| e.severity == crate::error::Severity::Info)
            .map(|e| e.message.as_str())
            .unwrap_or("");
        assert!(msg.contains("60"), "expected 60 in: {msg}");
    }

    // -----------------------------------------------------------------------
    // Implicit multiplication with capsule tokens in for loops
    // -----------------------------------------------------------------------

    #[test]
    fn for_loop_implicit_multiplication() {
        // `for i=0 step 1 until 2: show 72i; endfor`
        // should produce 0, 72, 144 via implicit multiplication 72*i
        let mut interp = Interpreter::new();
        interp
            .run("for i=0 step 1 until 2: show 72i; endfor;")
            .unwrap();
        let infos: Vec<_> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Info)
            .map(|e| e.message.clone())
            .collect();
        assert_eq!(infos.len(), 3, "expected 3 show outputs, got: {infos:?}");
        assert!(infos[0].contains("0"), "expected 0, got: {}", infos[0]);
        assert!(infos[1].contains("72"), "expected 72, got: {}", infos[1]);
        assert!(infos[2].contains("144"), "expected 144, got: {}", infos[2]);
    }

    // ===================================================================
    // Regression tests for equality, step loops, scantokens, equations
    // ===================================================================

    // Lock down the interpreter's comparison tolerance behavior.
    // Value::PartialEq uses NUMERIC_TOLERANCE (1e-4).

    #[test]
    fn equality_comparison_uses_interpreter_tolerance() {
        // 1 = 1.00005 should be true (diff < 1e-4) in MetaPost semantics
        let mut interp = Interpreter::new();
        interp.run("if 1 = 1.00005: show 1; fi;").unwrap();
        let infos: Vec<_> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Info)
            .collect();
        assert!(
            !infos.is_empty(),
            "expected equality to hold for diff 5e-5"
        );
    }

    #[test]
    fn equality_comparison_detects_large_diff() {
        // 1 = 1.001 should be false (diff > 1e-4 threshold for equation consistency)
        let mut interp = Interpreter::new();
        interp.run("if 1 = 1.001: show 1; fi;").unwrap();
        // Should NOT have any info messages if comparison is false
        let infos: Vec<_> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Info)
            .collect();
        assert!(
            infos.is_empty(),
            "1 = 1.001 should be false, but show executed"
        );
    }

    #[test]
    fn undelimited_macro_arg_parse_error_does_not_reuse_stale_cur_expr() {
        let mut interp = Interpreter::new();
        interp
            .run("def f primary p = show p; enddef; show 99; f;")
            .unwrap();

        let infos: Vec<_> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Info)
            .map(|e| e.message.as_str())
            .collect();

        let shows_99 = infos.iter().filter(|msg| msg.contains("99")).count();
        assert_eq!(
            shows_99, 1,
            "missing undelimited arg should not reuse stale expression value"
        );
    }

    // step/until loop edge cases

    #[test]
    fn for_step_until_zero_step_no_hang() {
        // Zero step should produce no iterations (avoids infinite loop)
        let mut interp = Interpreter::new();
        interp
            .run("for i=1 step 0 until 5: show i; endfor;")
            .unwrap();
        let infos: Vec<_> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Info)
            .collect();
        assert!(infos.is_empty(), "zero step should produce no iterations");
    }

    #[test]
    fn for_step_until_inclusive_endpoint() {
        // `for i=0 step 1 until 3` should include i=3
        let mut interp = Interpreter::new();
        interp
            .run("for i=0 step 1 until 3: show i; endfor;")
            .unwrap();
        let infos: Vec<_> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Info)
            .map(|e| e.message.clone())
            .collect();
        assert_eq!(infos.len(), 4, "expected 4 iterations (0,1,2,3), got: {infos:?}");
    }

    #[test]
    fn for_step_until_negative_direction() {
        // `for i=3 step -1 until 1` should produce 3,2,1
        let mut interp = Interpreter::new();
        interp
            .run("for i=3 step -1 until 1: show i; endfor;")
            .unwrap();
        let infos: Vec<_> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Info)
            .map(|e| e.message.clone())
            .collect();
        assert_eq!(infos.len(), 3, "expected 3 iterations (3,2,1), got: {infos:?}");
    }

    #[test]
    fn for_step_until_fractional_inclusive() {
        // `for i=0 step 0.1 until 0.3` should include 0.3 (within tolerance)
        let mut interp = Interpreter::new();
        interp
            .run("for i=0 step 0.1 until 0.3: show i; endfor;")
            .unwrap();
        let infos: Vec<_> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Info)
            .map(|e| e.message.clone())
            .collect();
        assert!(
            infos.len() >= 4,
            "expected at least 4 iterations (0, 0.1, 0.2, 0.3), got {}: {infos:?}",
            infos.len()
        );
    }

    #[test]
    fn for_step_until_wrong_direction_no_iterations() {
        // `for i=1 step -1 until 5` goes the wrong way: should produce no iterations
        let mut interp = Interpreter::new();
        interp
            .run("for i=1 step -1 until 5: show i; endfor;")
            .unwrap();
        let infos: Vec<_> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Info)
            .collect();
        assert!(
            infos.is_empty(),
            "wrong direction should produce no iterations, got: {infos:?}"
        );
    }

    // scantokens normal vs push-only parity

    #[test]
    fn scantokens_preserves_terminator() {
        // scantokens should not eat the `;` after the string expression
        let mut interp = Interpreter::new();
        interp
            .run(r#"scantokens "show 42"; show 99;"#)
            .unwrap();
        let infos: Vec<_> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Info)
            .map(|e| e.message.clone())
            .collect();
        assert!(
            infos.iter().any(|m| m.contains("42")),
            "scantokens should show 42: {infos:?}"
        );
        assert!(
            infos.iter().any(|m| m.contains("99")),
            "statement after scantokens should run: {infos:?}"
        );
    }

    #[test]
    fn expandafter_scantokens_same_as_direct() {
        // expandafter scantokens should produce same result
        let mut interp = Interpreter::new();
        interp
            .run(r#"expandafter show scantokens "42";"#)
            .unwrap();
        let infos: Vec<_> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Info)
            .map(|e| e.message.clone())
            .collect();
        assert!(
            infos.iter().any(|m| m.contains("42")),
            "expandafter scantokens should show 42: {infos:?}"
        );
    }

    // Input source push/pop ordering

    #[test]
    fn nested_source_levels_lifo_order() {
        // Verify that multiple push_source calls work in LIFO order
        let mut interp = Interpreter::new();
        // Push two source levels manually, then run the top-level source
        interp.input.push_source("show 2;");
        interp.input.push_source("show 1;");
        interp.get_x_next();
        while interp.cur.command != Command::Stop {
            interp.do_statement().unwrap();
        }
        let infos: Vec<_> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Info)
            .map(|e| e.message.clone())
            .collect();
        assert_eq!(infos.len(), 2, "expected 2 shows, got: {infos:?}");
        // LIFO: "show 1" runs first (top of stack), then "show 2"
        assert!(infos[0].contains("1"), "first should be 1: {}", infos[0]);
        assert!(infos[1].contains("2"), "second should be 2: {}", infos[1]);
    }

    // Equation solving with transitive dependencies

    #[test]
    fn nonlinear_equation_does_not_assign_bindable_lhs() {
        // Regression: nonlinear equations like `z = x*y` must not silently
        // degrade into assignment (`z := 0`) when dependency tracking is absent.
        let mut interp = Interpreter::new();
        interp.run("numeric x, y, z; z = x*y;").unwrap();

        let errors: Vec<_> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Error)
            .collect();
        assert!(
            errors.iter().any(|e| {
                e.kind == crate::error::ErrorKind::IncompatibleTypes
                    && e.message.contains("Nonlinear equation")
            }),
            "expected nonlinear-equation diagnostic, got: {errors:?}"
        );

        let z_id = interp
            .variables
            .lookup_existing("z")
            .expect("z should exist after declaration");
        assert!(
            !matches!(
                interp.variables.get(z_id),
                crate::variables::VarValue::NumericVar(crate::variables::NumericState::Known(_))
            ),
            "nonlinear equation must not force z to known value"
        );
    }

    #[test]
    fn transitive_equations_solve_correctly() {
        // x + y = 5; y + z = 7; x = 1 => y = 4, z = 3
        let mut interp = Interpreter::new();
        interp
            .run("numeric x, y, z; x + y = 5; y + z = 7; x = 1; show y; show z;")
            .unwrap();
        let infos: Vec<_> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Info)
            .map(|e| e.message.clone())
            .collect();
        assert!(
            infos.iter().any(|m| m.contains("4")),
            "expected y=4: {infos:?}"
        );
        assert!(
            infos.iter().any(|m| m.contains("3")),
            "expected z=3: {infos:?}"
        );
    }

    // save must not affect similar-prefix roots

    #[test]
    fn save_root_does_not_affect_similar_prefix() {
        let mut interp = Interpreter::new();
        interp
            .run(
                "numeric a, ab; a := 1; ab := 2; \
                 begingroup save a; a := 99; endgroup; \
                 show a; show ab;",
            )
            .unwrap();
        let infos: Vec<_> = interp
            .errors
            .iter()
            .filter(|e| e.severity == crate::error::Severity::Info)
            .map(|e| e.message.clone())
            .collect();
        assert!(
            infos.iter().any(|m| m.contains(">> 1")),
            "a should restore to 1: {infos:?}"
        );
        assert!(
            infos.iter().any(|m| m.contains(">> 2")),
            "ab should remain 2: {infos:?}"
        );
    }

    // scan_expression is currently pub; this test works from inside the
    // crate and will survive a visibility narrowing to pub(crate).

    #[test]
    fn scan_expression_internal_usage() {
        let mut interp = Interpreter::new();
        interp.input.push_source("3 + 4;");
        interp.get_x_next();
        interp.scan_expression().unwrap();
        assert_eq!(interp.cur_expr.exp, Value::Numeric(7.0));
    }
}
