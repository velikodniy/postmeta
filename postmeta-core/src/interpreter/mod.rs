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

use postmeta_fonts::FontProvider;
use postmeta_graphics::path::Path;
use postmeta_graphics::types::{Color, Pen, Picture, Transform};

use crate::command::Command;
use crate::equation::{DepList, VarId, const_dep, single_dep};
use crate::error::{ErrorKind, InterpResult, InterpreterError, Severity};
use crate::filesystem::FileSystem;
use crate::input::{InputSystem, ResolvedToken, TokenList};
use crate::internals::Internals;
use crate::scanner::ScanErrorKind;
use crate::symbols::{SymbolId, SymbolTable};
use crate::types::{Type, Value};
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
/// Expression evaluation result.
///
/// Carries a value, its type, and optional dependency information for the
/// equation solver. This is the canonical result type returned by all
/// expression-parsing functions.
#[derive(Clone)]
pub(super) struct ExprResultValue {
    pub exp: Value,
    pub ty: Type,
    pub dep: Option<DepList>,
    pub pair_dep: Option<(DepList, DepList)>,
}

impl ExprResultValue {
    const fn vacuous() -> Self {
        Self {
            exp: Value::Vacuous,
            ty: Type::Vacuous,
            dep: None,
            pair_dep: None,
        }
    }

    const fn typed(exp: Value, ty: Type) -> Self {
        Self {
            ty,
            exp,
            dep: None,
            pair_dep: None,
        }
    }

    const fn plain(exp: Value) -> Self {
        let ty = exp.ty();
        Self::typed(exp, ty)
    }

    fn numeric_known(v: f64) -> Self {
        Self {
            exp: Value::Numeric(v),
            ty: Type::Known,
            dep: Some(const_dep(v)),
            pair_dep: None,
        }
    }

    fn numeric_independent(id: VarId) -> Self {
        Self {
            exp: Value::Numeric(0.0),
            ty: Type::Independent,
            dep: Some(single_dep(id)),
            pair_dep: None,
        }
    }

    fn numeric_dependent(dep: DepList) -> Self {
        Self {
            exp: Value::Numeric(crate::equation::constant_value(&dep).unwrap_or(0.0)),
            ty: Type::Dependent,
            dep: Some(dep),
            pair_dep: None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum LhsBinding {
    Variable {
        id: VarId,
        negated: bool,
    },
    Internal {
        idx: u16,
    },
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
    /// Whether `current_picture` has been modified since the last sync to the
    /// `currentpicture` variable. Enables lazy sync: the variable is only
    /// updated when actually read.
    pub currentpicture_dirty: bool,
}

impl PictureState {
    const fn new() -> Self {
        Self {
            pictures: Vec::new(),
            current_picture: Picture::new(),
            named_pic_buf: None,
            currentpicture_dirty: false,
        }
    }
}

/// Long-lived interpreter machine state.
///
/// This groups the mutable subsystems that represent the `MetaPost` "world":
/// symbol/variable tables, input stack, internals, macro table, and drawing
/// output buffers. The parser/expression front-end state stays on
/// [`Interpreter`] (`cur`, `cur_expr`, `lhs_tracking`).
pub struct MachineState {
    /// Filesystem for `input` commands.
    fs: Box<dyn FileSystem>,
    /// Font provider for text metrics (optional; falls back to heuristics).
    font_provider: Option<Arc<dyn FontProvider>>,
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

// ---------------------------------------------------------------------------
// Interpreter state
// ---------------------------------------------------------------------------

/// The `MetaPost` interpreter.
pub struct Interpreter {
    /// Long-lived machine state.
    state: MachineState,
    /// Stashed expression result for group return values and `get_x_next` protection.
    cur_expr: ExprResultValue,
    /// Current resolved token (set by `get_next`).
    cur: ResolvedToken,
    /// Latest bindable left-hand-side context.
    lhs_tracking: LhsTracking,
    /// Conditional and loop control state (if-stack, loop exit flag, pending body).
    control_flow: ControlFlow,
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
            state: MachineState {
                fs: Box::new(crate::filesystem::NullFileSystem),
                font_provider: None,
                symbols,
                variables: Variables::new(),
                var_trie: VarTrie::new(),
                internals,
                input: InputSystem::new(),
                save_stack: SaveStack::new(),
                picture_state: PictureState::new(),
                macros: std::collections::HashMap::new(),
                random_seed: 0,
                errors: Vec::new(),
                job_name: "output".into(),
                next_delimiter_id: 1, // 0 is reserved for built-in ()
            },
            cur_expr: ExprResultValue::vacuous(),
            cur,
            lhs_tracking: LhsTracking::new(),
            control_flow: ControlFlow::new(),
        }
    }

    /// Set the filesystem for `input` commands.
    pub fn set_filesystem(&mut self, fs: Box<dyn FileSystem>) {
        self.state.fs = fs;
    }

    /// Set the font provider for text metrics and glyph data.
    ///
    /// When set, operators like `infont` and `fontsize` use real OpenType
    /// metrics.  When `None`, the interpreter falls back to heuristics.
    pub fn set_font_provider(&mut self, provider: Arc<dyn FontProvider>) {
        self.state.font_provider = Some(provider);
    }

    // =======================================================================
    // Token access
    // =======================================================================

    /// Get the next token (raw, no expansion).
    fn get_next(&mut self) {
        self.cur = self.state.input.next_raw_token(&mut self.state.symbols);
        for scan_error in self.state.input.take_scan_errors() {
            let kind = match scan_error.kind {
                ScanErrorKind::InvalidCharacter => ErrorKind::InvalidCharacter,
                ScanErrorKind::UnterminatedString => ErrorKind::UnterminatedString,
            };
            self.state
                .errors
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
        // Use take+restore instead of clone to avoid deep-copying expensive
        // values (paths, pictures, dep lists).
        let saved = std::mem::replace(&mut self.cur_expr, ExprResultValue::vacuous());
        self.get_next();
        self.expand_current();
        self.cur_expr = saved;
    }

    /// Push the current token back into the input stream.
    ///
    /// After calling this, the next `get_next()` or `get_x_next()` will
    /// return the same token again. This is `mp.web`'s `back_input`.
    pub(super) fn back_input(&mut self) {
        let cur = self.cur.clone();
        self.state.input.back_input(cur);
    }

    /// Push the current expression back into the input as a capsule token.
    ///
    /// The current `cur_exp`/`cur_type` are stashed into a capsule and
    /// placed on the input stream. The next token read will be a
    /// `CapsuleToken` carrying that value. This is `mp.web`'s `back_expr`.
    /// Push an expression result back into the input as a capsule token.
    ///
    /// The value is stashed into a capsule and placed on the input stream.
    /// The next token read will be a `CapsuleToken` carrying that value.
    /// This is `mp.web`'s `back_expr`.
    pub(super) fn back_expr_value(&mut self, result: ExprResultValue) {
        self.state
            .input
            .back_expr(result.exp, result.ty, result.dep, result.pair_dep);
    }

    /// Store the current token into a token list.
    fn store_current_token(&self, list: &mut TokenList) {
        use crate::input::StoredToken;

        if self.cur.command == Command::CapsuleToken {
            if let Some(payload) = &self.cur.capsule {
                list.push(StoredToken::Capsule(payload.clone()));
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
            crate::token::TokenKind::Capsule | crate::token::TokenKind::Eof => {}
        }
    }

    // =======================================================================
    // Value helpers
    // =======================================================================

    const fn take_cur_result(&mut self) -> ExprResultValue {
        std::mem::replace(&mut self.cur_expr, ExprResultValue::vacuous())
    }

    fn set_cur_result(&mut self, result: ExprResultValue) {
        self.cur_expr = result;
    }

    fn numeric_dep_for_var(&mut self, id: VarId) -> DepList {
        match self.variables.get(id).clone() {
            VarValue::NumericVar(NumericState::Known(v)) => const_dep(v),
            VarValue::NumericVar(NumericState::Independent { .. }) => {
                crate::equation::single_dep(id)
            }
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
        self.cur.sym.map(|id| self.symbols.name(id))
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

    fn default_var_value_for_type(&mut self, ty: Type, name: &str) -> Option<VarValue> {
        match ty {
            Type::Numeric => Some(VarValue::NumericVar(NumericState::Numeric)),
            Type::Boolean => Some(VarValue::Known(Value::Boolean(false))),
            Type::String => Some(VarValue::Known(Value::String(Arc::from("")))),
            Type::Path => Some(VarValue::Known(Value::Path(Path::default()))),
            Type::Pen => Some(VarValue::Known(Value::Pen(Pen::circle(0.0)))),
            Type::Picture => Some(VarValue::Known(Value::Picture(Picture::default()))),
            Type::PairType => Some(self.alloc_pair_value(name)),
            Type::ColorType => Some(self.alloc_color_value(name)),
            Type::TransformType => Some(self.alloc_transform_value(name)),
            _ => None,
        }
    }

    /// Negate the current expression (unary minus).
    fn negate_value(&mut self, mut result: ExprResultValue) -> ExprResultValue {
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

        match &result.exp {
            Value::Numeric(v) => {
                result.exp = Value::Numeric(-v);
                if let Some(mut dep) = result.dep.take() {
                    crate::equation::dep_scale(&mut dep, -1.0);
                    result.dep = Some(dep);
                }
                result.pair_dep = None;
                self.lhs_tracking.last_lhs_binding = self
                    .lhs_tracking
                    .last_lhs_binding
                    .as_ref()
                    .and_then(negate_binding);
            }
            Value::Pair(x, y) => {
                result.exp = Value::Pair(-x, -y);
                result.dep = None;
                if let Some((mut dx, mut dy)) = result.pair_dep.take() {
                    crate::equation::dep_scale(&mut dx, -1.0);
                    crate::equation::dep_scale(&mut dy, -1.0);
                    result.pair_dep = Some((dx, dy));
                }
                self.lhs_tracking.last_lhs_binding = self
                    .lhs_tracking
                    .last_lhs_binding
                    .as_ref()
                    .and_then(negate_binding);
            }
            Value::Color(c) => {
                result.exp = Value::Color(Color::new(-c.r, -c.g, -c.b));
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
        result
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
            VarValue::Undefined
                | VarValue::NumericVar(NumericState::Numeric | NumericState::Undefined)
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

        let Some(val) = self.default_var_value_for_type(declared_ty, name) else {
            return;
        };
        self.variables.set(var_id, val);
    }

    /// Fast path for root-only variable references. Avoids String allocation
    /// entirely when the sym cache hits.
    fn resolve_variable_root(&mut self, sym: Option<SymbolId>) -> InterpResult<ExprResultValue> {
        let var_id = if let Some(s) = sym {
            // Try the sym cache first — no string allocation needed on hit.
            let idx = s.raw() as usize;
            let cached = if idx < self.variables.sym_cache.len() {
                let c = self.variables.sym_cache[idx];
                if c == Variables::SYM_CACHE_EMPTY {
                    None
                } else {
                    Some(c)
                }
            } else {
                None
            };
            if let Some(id) = cached {
                id
            } else {
                // Cache miss — need the name string for HashMap lookup.
                let name = self.symbols.name(s).to_owned();
                self.variables.lookup_by_sym(s, &name)
            }
        } else {
            // No symbol — shouldn't happen for tag tokens, but handle gracefully.
            self.variables.lookup("")
        };
        // For root-only lookups, initialize_declared_variable needs the name
        // only when creating compound sub-parts (pair.x, pair.y, etc.).
        // Check if initialization is needed before allocating the name.
        let needs_init = matches!(
            self.variables.get(var_id),
            VarValue::Undefined
                | VarValue::NumericVar(NumericState::Numeric | NumericState::Undefined)
        );
        if needs_init {
            if let Some(s) = sym {
                let name = self.symbols.name(s).to_owned();
                self.initialize_declared_variable(var_id, &name, sym, &[]);
            }
        }
        self.lhs_tracking.last_lhs_binding = Some(LhsBinding::Variable {
            id: var_id,
            negated: false,
        });
        self.resolve_var_id(var_id)
    }

    /// Resolve a variable name to its value, returning the result.
    fn resolve_variable(
        &mut self,
        sym: Option<SymbolId>,
        name: &str,
        suffixes: &[SuffixSegment],
    ) -> InterpResult<ExprResultValue> {
        let var_id = if suffixes.is_empty() {
            if let Some(s) = sym {
                self.variables.lookup_by_sym(s, name)
            } else {
                self.variables.lookup(name)
            }
        } else {
            self.variables.lookup(name)
        };
        self.initialize_declared_variable(var_id, name, sym, suffixes);
        // Track last scanned variable for assignment LHS
        self.lhs_tracking.last_lhs_binding = Some(LhsBinding::Variable {
            id: var_id,
            negated: false,
        });
        self.resolve_var_id(var_id)
    }

    /// Turn a `VarId` into an `ExprResultValue` by reading the stored value.
    ///
    /// Borrows the variable storage to avoid cloning until actually needed.
    fn resolve_var_id(&mut self, var_id: VarId) -> InterpResult<ExprResultValue> {
        // Match on a borrow first to extract Copy data without cloning.
        // Only clone for variants that need owned data (Known with heap values,
        // Dependent with DepList).
        let result = match self.variables.get(var_id) {
            VarValue::NumericVar(NumericState::Known(v)) => ExprResultValue::numeric_known(*v),
            VarValue::NumericVar(NumericState::Independent { .. }) => {
                ExprResultValue::numeric_independent(var_id)
            }
            VarValue::NumericVar(NumericState::Dependent(dep)) => {
                ExprResultValue::numeric_dependent(dep.clone())
            }
            VarValue::NumericVar(NumericState::Numeric | NumericState::Undefined)
            | VarValue::Undefined => {
                self.variables.make_independent(var_id);
                return Ok(ExprResultValue::numeric_independent(var_id));
            }
            VarValue::Known(Value::Numeric(v)) => ExprResultValue::numeric_known(*v),
            VarValue::Known(Value::Pair(x, y)) => {
                let (x, y) = (*x, *y);
                ExprResultValue {
                    exp: Value::Pair(x, y),
                    ty: Type::PairType,
                    dep: None,
                    pair_dep: Some((const_dep(x), const_dep(y))),
                }
            }
            VarValue::Known(v) => {
                // Path, Pen, Picture, String, etc. — must clone.
                let v = v.clone();
                let ty = v.ty();
                ExprResultValue {
                    exp: v,
                    ty,
                    dep: None,
                    pair_dep: None,
                }
            }
            VarValue::Pair { x, y } => {
                let (x, y) = (*x, *y);
                let xv = self.variables.known_value(x).unwrap_or(0.0);
                let yv = self.variables.known_value(y).unwrap_or(0.0);
                ExprResultValue {
                    exp: Value::Pair(xv, yv),
                    ty: Type::PairType,
                    dep: None,
                    pair_dep: Some((self.numeric_dep_for_var(x), self.numeric_dep_for_var(y))),
                }
            }
            VarValue::Color { r, g, b } => {
                let (r, g, b) = (*r, *g, *b);
                let rv = self.variables.known_value(r).unwrap_or(0.0);
                let gv = self.variables.known_value(g).unwrap_or(0.0);
                let bv = self.variables.known_value(b).unwrap_or(0.0);
                ExprResultValue::plain(Value::Color(Color::new(rv, gv, bv)))
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
                ExprResultValue::plain(Value::Transform(Transform {
                    tx: parts[0],
                    ty: parts[1],
                    txx: parts[2],
                    txy: parts[3],
                    tyx: parts[4],
                    tyy: parts[5],
                }))
            }
        };
        Ok(result)
    }

    // =======================================================================
    // Error handling
    // =======================================================================

    /// Record a non-fatal error.
    fn report_error(&mut self, kind: ErrorKind, message: impl Into<String>) {
        let msg = message.into();
        self.errors.push(InterpreterError::new(kind, msg));
    }

    /// Record an informational diagnostic.
    fn report_info(&mut self, message: impl Into<String>) {
        self.errors.push(
            InterpreterError::new(ErrorKind::Internal, message.into())
                .with_severity(Severity::Info),
        );
    }

    // =======================================================================
    // Public interface
    // =======================================================================

    /// Run a `MetaPost` program from source text.
    pub fn run(&mut self, source: &str) -> InterpResult<()> {
        self.state.input.push_source(source);
        self.get_x_next();

        while self.cur.command != Command::Stop {
            self.do_statement()?;
        }

        Ok(())
    }

    /// Get the output pictures.
    #[must_use]
    pub fn output(&self) -> &[Picture] {
        &self.state.picture_state.pictures
    }

    /// Get the current picture being built.
    #[must_use]
    pub const fn current_picture(&self) -> &Picture {
        &self.state.picture_state.current_picture
    }
}

impl std::ops::Deref for Interpreter {
    type Target = MachineState;

    fn deref(&self) -> &Self::Target {
        &self.state
    }
}

impl std::ops::DerefMut for Interpreter {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.state
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
mod tests;
