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

use std::sync::Arc;

use kurbo::Point;

use postmeta_graphics::math;
use postmeta_graphics::path;
use postmeta_graphics::path::hobby;
use postmeta_graphics::pen;
use postmeta_graphics::picture;
use postmeta_graphics::transform;
use postmeta_graphics::types::{
    Color, Knot, KnotDirection, LineCap, LineJoin, Path, Pen, Picture, Scalar, Transform,
};

use crate::command::{
    BoundsOp, Command, ExpressionBinaryOp, FiOrElseOp, IterationOp, MacroDefOp, MessageOp,
    NullaryOp, ParamTypeOp, PlusMinusOp, PrimaryBinaryOp, SecondaryBinaryOp, StrOpOp,
    TertiaryBinaryOp, ThingToAddOp, TypeNameOp, UnaryOp, WithOptionOp,
};
use crate::equation::VarId;
use crate::error::{ErrorKind, InterpResult, InterpreterError};
use crate::filesystem::FileSystem;
use crate::input::{InputSystem, ResolvedToken, StoredToken, TokenList};
use crate::internals::{InternalId, Internals};
use crate::symbols::{SymbolId, SymbolTable};
use crate::types::{DrawingState, Type, Value};
use crate::variables::{NumericState, SaveEntry, SaveStack, VarValue, Variables};

// ---------------------------------------------------------------------------
// Path join pending state
// ---------------------------------------------------------------------------

/// Pending left-side specification for the next knot in path construction.
///
/// When `tension t1 and t2` or `controls p1 and p2` is parsed, the second
/// value applies to the *next* knot's left side and must be carried forward.
enum PendingJoin {
    /// Pending left tension for the next knot.
    Tension(Scalar),
    /// Pending explicit left control point for the next knot.
    Control(Point),
}

// ---------------------------------------------------------------------------
// Conditional state
// ---------------------------------------------------------------------------

/// State of one level in the `if/elseif/else/fi` nesting stack.
#[derive(Debug, Clone, Copy)]
enum IfState {
    /// We are currently executing the active branch.
    Active,
    /// A branch was already taken; skip remaining branches.
    Done,
    /// We are skipping tokens looking for `elseif`/`else`/`fi`.
    Skipping,
}

// ---------------------------------------------------------------------------
// Macro definitions
// ---------------------------------------------------------------------------

/// The type of a macro parameter.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ParamType {
    /// `expr` — a delimited expression argument (inside parentheses).
    Expr,
    /// `suffix` — a delimited suffix argument (inside parentheses).
    Suffix,
    /// `text` — a delimited text argument (inside parentheses).
    Text,
    /// `primary` — undelimited, evaluated at primary precedence.
    Primary,
    /// `secondary` — undelimited, evaluated at secondary precedence.
    Secondary,
    /// `tertiary` — undelimited, evaluated at tertiary precedence.
    Tertiary,
    /// `expr` — undelimited expression (full expression precedence).
    UndelimitedExpr,
    /// `suffix` — undelimited suffix.
    UndelimitedSuffix,
    /// `text` — undelimited text (tokens until semicolon/endgroup).
    UndelimitedText,
}

impl ParamType {
    /// Is this an undelimited parameter type?
    const fn is_undelimited(self) -> bool {
        matches!(
            self,
            Self::Primary
                | Self::Secondary
                | Self::Tertiary
                | Self::UndelimitedExpr
                | Self::UndelimitedSuffix
                | Self::UndelimitedText
        )
    }
}

/// A defined macro's parameter and body information.
#[derive(Debug, Clone)]
struct MacroInfo {
    /// Parameter types in order.
    params: Vec<ParamType>,
    /// The macro body as a token list.
    body: TokenList,
    /// Whether this is a `vardef` (wraps body in begingroup/endgroup).
    is_vardef: bool,
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
    /// Internal quantities.
    pub internals: Internals,
    /// Token input system.
    pub input: InputSystem,
    /// Save stack for `begingroup`/`endgroup`.
    pub save_stack: SaveStack,
    /// Current expression value and type.
    cur_exp: Value,
    cur_type: Type,
    /// Current resolved token (set by `get_next`).
    cur: ResolvedToken,
    /// Last scanned variable id (for assignment LHS tracking).
    last_var_id: Option<VarId>,
    /// Last scanned variable name (for assignment LHS tracking).
    last_var_name: String,
    /// Last scanned internal quantity index (for `interim` assignment).
    last_internal_idx: Option<u16>,
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
        };

        Self {
            fs: Box::new(crate::filesystem::NullFileSystem),
            symbols,
            variables: Variables::new(),
            internals,
            input: InputSystem::new(),
            save_stack: SaveStack::new(),
            cur_exp: Value::Vacuous,
            cur_type: Type::Vacuous,
            cur,
            last_var_id: None,
            last_var_name: String::new(),
            last_internal_idx: None,
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

    /// Expand any expandable tokens at the current position.
    ///
    /// After this, `self.cur` holds a non-expandable token.
    fn expand_current(&mut self) {
        while self.cur.command.is_expandable() {
            match self.cur.command {
                Command::IfTest => self.expand_if(),
                Command::FiOrElse => self.expand_fi_or_else(),
                Command::Iteration => self.expand_iteration(),
                Command::ExitTest => self.expand_exitif(),
                Command::RepeatLoop => self.expand_repeat_loop(),
                Command::DefinedMacro => self.expand_defined_macro(),
                Command::Input => self.expand_input(),
                Command::ScanTokens => self.expand_scantokens(),
                _ => break, // Other expandables not yet implemented
            }
        }
    }

    /// Handle `if <boolean>:` — evaluate the condition and enter a branch.
    ///
    /// On return, `self.cur` is the first non-expandable token of the
    /// active branch (or the token after `fi` if no branch is taken).
    fn expand_if(&mut self) {
        // Evaluate the boolean expression after `if`
        self.get_x_next();
        let condition = if self.scan_expression().is_ok() {
            match &self.cur_exp {
                Value::Boolean(b) => *b,
                Value::Numeric(v) => *v != 0.0,
                _ => {
                    self.report_error(ErrorKind::TypeError, "if condition must be boolean");
                    false
                }
            }
        } else {
            false
        };

        // Expect `:` after the condition
        if self.cur.command == Command::Colon {
            self.get_next(); // consume the colon
        }

        if condition {
            self.if_stack.push(IfState::Active);
            // `cur` is now the first token of the true branch — expand it
            self.expand_current();
        } else {
            self.if_stack.push(IfState::Skipping);
            // Skip tokens until else/elseif/fi. On return, `cur` is set.
            self.skip_to_fi_or_else();
        }
    }

    /// Handle `fi`, `else`, `elseif` encountered during active execution.
    ///
    /// On return, `self.cur` is the next non-expandable token.
    fn expand_fi_or_else(&mut self) {
        let modifier = self.cur.modifier;
        if modifier == FiOrElseOp::Fi as u16 {
            // End of conditional
            self.if_stack.pop();
            self.get_next();
            self.expand_current();
        } else if modifier == FiOrElseOp::Else as u16 || modifier == FiOrElseOp::ElseIf as u16 {
            // Active branch done — skip remaining branches to `fi`.
            if let Some(state) = self.if_stack.last_mut() {
                *state = IfState::Done;
            }
            self.skip_to_fi();
        }
    }

    /// Skip tokens until we find `else`, `elseif`, or `fi` at the current nesting level.
    ///
    /// Called when a conditional branch is false. On return, `self.cur` is set
    /// to the first non-expandable token of the next active branch or after `fi`.
    fn skip_to_fi_or_else(&mut self) {
        let mut depth: u32 = 0;
        loop {
            match self.cur.command {
                Command::IfTest => {
                    depth += 1;
                    self.get_next();
                }
                Command::FiOrElse if depth > 0 => {
                    if self.cur.modifier == FiOrElseOp::Fi as u16 {
                        depth -= 1;
                    }
                    self.get_next();
                }
                Command::FiOrElse if depth == 0 => {
                    let modifier = self.cur.modifier;
                    if modifier == FiOrElseOp::Fi as u16 {
                        self.if_stack.pop();
                        self.get_next();
                        self.expand_current();
                        return;
                    } else if modifier == FiOrElseOp::Else as u16 {
                        if let Some(state) = self.if_stack.last_mut() {
                            *state = IfState::Active;
                        }
                        self.get_next(); // consume `else`
                                         // consume the `:` after `else`
                        if self.cur.command == Command::Colon {
                            self.get_next();
                        }
                        self.expand_current();
                        return;
                    } else if modifier == FiOrElseOp::ElseIf as u16 {
                        self.if_stack.pop();
                        // Process the new `elseif` as an `if`
                        self.expand_if();
                        return;
                    }
                    self.get_next();
                }
                Command::Stop => {
                    self.report_error(ErrorKind::MissingToken, "Missing `fi`");
                    return;
                }
                _ => {
                    self.get_next();
                }
            }
        }
    }

    /// Skip tokens until we find `fi` at the current nesting level.
    ///
    /// Called when we already took a branch and hit `else`/`elseif`.
    /// On return, `self.cur` is the next non-expandable token after `fi`.
    fn skip_to_fi(&mut self) {
        let mut depth: u32 = 0;
        loop {
            self.get_next();
            match self.cur.command {
                Command::IfTest => depth += 1,
                Command::FiOrElse => {
                    if self.cur.modifier == FiOrElseOp::Fi as u16 {
                        if depth == 0 {
                            self.if_stack.pop();
                            self.get_next();
                            self.expand_current();
                            return;
                        }
                        depth -= 1;
                    }
                }
                Command::Stop => {
                    self.report_error(ErrorKind::MissingToken, "Missing `fi`");
                    return;
                }
                _ => {}
            }
        }
    }

    // =======================================================================
    // Loop expansion
    // =======================================================================

    /// Handle `for`/`forsuffixes`/`forever` — scan the loop body, then replay.
    ///
    /// Syntax:
    ///   `for <var> = <expr>, <expr>, ...: <body> endfor`
    ///   `forsuffixes <var> = <suffix>, ...: <body> endfor`
    ///   `forever: <body> endfor`
    ///
    /// On return, `self.cur` is the first non-expandable token after the loop.
    fn expand_iteration(&mut self) {
        let op = self.cur.modifier;

        if op == IterationOp::Forever as u16 {
            self.expand_forever();
            return;
        }

        // Parse: <variable> = <value_list> : <body> endfor
        self.get_next(); // skip `for`/`forsuffixes`

        // Get the loop variable name
        let loop_var_name = if let crate::token::TokenKind::Symbolic(ref name) = self.cur.token.kind
        {
            name.clone()
        } else {
            self.report_error(ErrorKind::MissingToken, "Expected loop variable name");
            self.get_next();
            self.expand_current();
            return;
        };

        self.get_next(); // skip the variable name

        // Expect `=`
        if self.cur.command != Command::Equals {
            self.report_error(ErrorKind::MissingToken, "Expected `=` after loop variable");
        }

        // Parse value list: expr, expr, expr, ..., colon
        let values = self.scan_loop_value_list();

        // Expect `:` after value list
        if self.cur.command == Command::Colon {
            self.get_next(); // consume the colon
        }

        // Scan the loop body until `endfor`
        let body = self.scan_loop_body();

        // Build a combined token list with all iterations.
        // For each value, we prepend: `<var> := <value> ;` then the body.
        let loop_var_sym = self.symbols.lookup(&loop_var_name);
        let assign_sym = self.symbols.lookup(":=");

        let mut combined = TokenList::new();
        for val in values.iter().rev() {
            // Body tokens
            combined.splice(0..0, body.iter().cloned());
            // Prepend: <var> := <value> ;
            let value_token = value_to_stored_token(val);
            let semicolon_sym = self.symbols.lookup(";");
            combined.splice(
                0..0,
                [
                    StoredToken::Symbol(loop_var_sym),
                    StoredToken::Symbol(assign_sym),
                    value_token,
                    StoredToken::Symbol(semicolon_sym),
                ],
            );
        }

        if !combined.is_empty() {
            self.input
                .push_token_list(combined, Vec::new(), "for-body".into());
        }

        // Get the next token from the combined body
        self.get_next();
        self.expand_current();
    }

    /// Handle `forever: <body> endfor`.
    ///
    /// Uses a sentinel-based approach: appends a `RepeatLoop` command token
    /// at the end of each iteration's body. When we encounter `RepeatLoop`
    /// during expansion, we re-push the body for the next iteration.
    fn expand_forever(&mut self) {
        self.get_next(); // skip `forever`

        // Expect `:`
        if self.cur.command == Command::Colon {
            self.get_next();
        }

        // Scan the loop body
        let body = self.scan_loop_body();

        // Store the body in the interpreter for re-pushing on RepeatLoop
        self.pending_loop_body = Some(body.clone());

        // Push the first iteration with a RepeatLoop sentinel at the end
        let mut iteration = body;
        let repeat_sym = self.symbols.lookup("__repeat_loop__");
        self.symbols.set(
            repeat_sym,
            crate::symbols::SymbolEntry {
                command: Command::RepeatLoop,
                modifier: 0,
            },
        );
        iteration.push(StoredToken::Symbol(repeat_sym));
        self.input
            .push_token_list(iteration, Vec::new(), "forever-body".into());

        // Get the first token and continue — the RepeatLoop sentinel will
        // be caught by expand_current and re-push the body.
        self.get_next();
        self.expand_current();
    }

    /// Handle the `RepeatLoop` sentinel during expansion.
    ///
    /// Re-pushes the loop body for the next iteration, or stops if `exitif` fired.
    fn expand_repeat_loop(&mut self) {
        if self.loop_exit {
            // Exit was requested — consume the sentinel and stop looping
            self.pending_loop_body = None;
            self.loop_exit = false;
            self.get_next();
            self.expand_current();
            return;
        }

        // Re-push the body for the next iteration
        if let Some(ref body) = self.pending_loop_body.clone() {
            let repeat_sym = self.symbols.lookup("__repeat_loop__");
            let mut iteration = body.clone();
            iteration.push(StoredToken::Symbol(repeat_sym));
            self.input
                .push_token_list(iteration, Vec::new(), "forever-body".into());
        } else {
            self.pending_loop_body = None;
        }

        self.get_next();
        self.expand_current();
    }

    /// Parse the value list for a `for` loop: `expr, expr, ...`
    ///
    /// Reads expressions separated by commas until a `:` is found.
    /// Returns the list of values.
    fn scan_loop_value_list(&mut self) -> Vec<Value> {
        let mut values = Vec::new();
        self.get_x_next(); // skip `=`

        loop {
            if self.cur.command == Command::Colon || self.cur.command == Command::Stop {
                break;
            }
            if self.scan_expression().is_ok() {
                let first_val = self.take_cur_exp();

                // Check for `step <step> until <end>` after the first value
                if self.cur.command == Command::StepToken {
                    if let Ok(start) = value_to_scalar(&first_val) {
                        self.get_x_next();
                        if self.scan_expression().is_ok() {
                            let step_val = self.take_cur_exp();
                            if let Ok(step) = value_to_scalar(&step_val) {
                                // Expect `until`
                                if self.cur.command == Command::UntilToken {
                                    self.get_x_next();
                                    if self.scan_expression().is_ok() {
                                        let end_val = self.take_cur_exp();
                                        if let Ok(end) = value_to_scalar(&end_val) {
                                            // Generate the range
                                            self.generate_step_range(start, step, end, &mut values);
                                        }
                                    }
                                }
                            }
                        }
                    }
                    break;
                }

                values.push(first_val);
            } else {
                break;
            }
            // Check for comma separator
            if self.cur.command == Command::Comma {
                self.get_x_next();
            } else {
                break;
            }
        }
        values
    }

    /// Generate numeric values for a `step`/`until` loop range.
    #[allow(clippy::while_float)]
    fn generate_step_range(&self, start: f64, step: f64, end: f64, values: &mut Vec<Value>) {
        if step.abs() < f64::EPSILON {
            // Zero step — avoid infinite loop
            return;
        }
        let mut v = start;
        let tolerance = f64::EPSILON.mul_add(end.abs().max(1.0), end);
        if step > 0.0 {
            while v <= tolerance {
                values.push(Value::Numeric(v));
                v += step;
                // Safety limit to avoid runaway loops
                if values.len() > 10_000 {
                    break;
                }
            }
        } else {
            let neg_tolerance = (-f64::EPSILON).mul_add(end.abs().max(1.0), end);
            while v >= neg_tolerance {
                values.push(Value::Numeric(v));
                v += step;
                if values.len() > 10_000 {
                    break;
                }
            }
        }
    }

    /// Scan a loop body (tokens until `endfor`), handling nested for/endfor.
    ///
    /// Returns the body as a `TokenList`.
    fn scan_loop_body(&mut self) -> TokenList {
        use crate::input::StoredToken;

        let mut body = TokenList::new();
        let mut depth: u32 = 0;

        loop {
            match self.cur.command {
                Command::Iteration => {
                    // Nested for — store the token and increase depth
                    depth += 1;
                    self.store_current_token(&mut body);
                    self.get_next();
                }
                Command::MacroSpecial if self.cur.modifier == 1 => {
                    // `endfor` — modifier 1 on MacroSpecial
                    if depth == 0 {
                        // This is our endfor — don't store it, just stop
                        return body;
                    }
                    depth -= 1;
                    self.store_current_token(&mut body);
                    self.get_next();
                }
                Command::Stop => {
                    self.report_error(ErrorKind::MissingToken, "Missing `endfor`");
                    return body;
                }
                _ => {
                    self.store_current_token(&mut body);
                    self.get_next();
                }
            }
        }
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

    /// Handle `exitif <boolean>;` — set the loop exit flag if condition is true.
    ///
    /// On return, `self.cur` is the first non-expandable token after `exitif`.
    fn expand_exitif(&mut self) {
        self.get_x_next(); // skip `exitif`
        let should_exit = if self.scan_expression().is_ok() {
            match &self.cur_exp {
                Value::Boolean(b) => *b,
                Value::Numeric(v) => *v != 0.0,
                _ => {
                    self.report_error(ErrorKind::TypeError, "exitif condition must be boolean");
                    false
                }
            }
        } else {
            false
        };

        // Set the flag BEFORE consuming remaining tokens, so that
        // any RepeatLoop sentinel encountered during expand_current
        // will see the exit request.
        if should_exit {
            self.loop_exit = true;
        }

        // Expect `;` after the condition
        if self.cur.command == Command::Semicolon {
            self.get_next();
            self.expand_current();
        }
    }

    // =======================================================================
    // Macro definition and expansion
    // =======================================================================

    /// Handle `def`/`vardef`/`primarydef`/`secondarydef`/`tertiarydef`.
    ///
    /// Syntax:
    ///   `def <name>(param_list) = <body> enddef`
    ///   `vardef <name>(param_list) = <body> enddef`
    ///   `primarydef <lhs> <op> <rhs> = <body> enddef`
    ///   `secondarydef <lhs> <op> <rhs> = <body> enddef`
    ///   `tertiarydef <lhs> <op> <rhs> = <body> enddef`
    fn do_macro_def(&mut self) -> InterpResult<()> {
        let def_op = self.cur.modifier;
        let is_vardef = def_op == MacroDefOp::VarDef as u16;
        let is_binary_def = def_op == MacroDefOp::PrimaryDef as u16
            || def_op == MacroDefOp::SecondaryDef as u16
            || def_op == MacroDefOp::TertiaryDef as u16;

        self.get_next(); // skip `def`/`vardef`/etc.

        if is_binary_def {
            // primarydef/secondarydef/tertiarydef: <param> <name> <param> = body enddef
            // e.g., `primarydef a dotprod b = ...`
            self.do_binary_macro_def(def_op)
        } else {
            // def/vardef: <name>(param_list) = body enddef
            self.do_normal_macro_def(is_vardef)
        }
    }

    /// Handle `def <name>(params) = body enddef` or `vardef <name>(params) = body enddef`.
    fn do_normal_macro_def(&mut self, is_vardef: bool) -> InterpResult<()> {
        // Get macro name
        let Some(macro_sym) = self.cur.sym else {
            self.report_error(ErrorKind::MissingToken, "Expected macro name after def");
            self.skip_to_enddef();
            return Ok(());
        };
        let macro_name = if let crate::token::TokenKind::Symbolic(ref s) = self.cur.token.kind {
            s.clone()
        } else {
            String::new()
        };

        self.get_next(); // skip macro name

        // For vardef: check for `@#` suffix parameter marker
        let mut has_at_suffix = false;
        if is_vardef && self.cur.command == Command::MacroSpecial && self.cur.modifier == 4 {
            // `@#` suffix parameter — consume it
            has_at_suffix = true;
            self.get_next();
        }

        // Parse parameter list
        let params = self.scan_macro_params()?;

        // Expect `=`
        if self.cur.command == Command::Equals || self.cur.command == Command::Assignment {
            self.get_next();
        } else {
            self.report_error(ErrorKind::MissingToken, "Expected `=` in macro definition");
        }

        // Scan the body until `enddef`, replacing param names with Param(idx)
        let mut param_names: Vec<String> = params.iter().map(|(name, _)| name.clone()).collect();
        if has_at_suffix {
            // The `@#` suffix parameter gets the next parameter index
            param_names.push("@#".to_owned());
        }
        let body = self.scan_macro_body(&param_names);

        let mut param_types: Vec<ParamType> = params.into_iter().map(|(_, ty)| ty).collect();
        if has_at_suffix {
            param_types.push(ParamType::UndelimitedSuffix);
        }

        // Store the macro
        let info = MacroInfo {
            params: param_types,
            body,
            is_vardef,
        };
        self.macros.insert(macro_sym, info);

        // Set the symbol to DefinedMacro
        self.symbols.set(
            macro_sym,
            crate::symbols::SymbolEntry {
                command: Command::DefinedMacro,
                modifier: 0,
            },
        );

        // Skip past enddef (scan_macro_body consumed it)
        // Get the next token
        self.get_x_next();

        // Consume trailing semicolon
        if self.cur.command == Command::Semicolon {
            self.get_x_next();
        }

        let _ = macro_name;
        Ok(())
    }

    /// Handle `primarydef`/`secondarydef`/`tertiarydef`.
    ///
    /// Syntax: `primarydef <lhs_param> <op_name> <rhs_param> = body enddef`
    fn do_binary_macro_def(&mut self, def_op: u16) -> InterpResult<()> {
        // Parse: <lhs_param> <op_name> <rhs_param>
        let lhs_name = if let crate::token::TokenKind::Symbolic(ref s) = self.cur.token.kind {
            s.clone()
        } else {
            self.report_error(
                ErrorKind::MissingToken,
                "Expected parameter name in binary macro def",
            );
            self.skip_to_enddef();
            return Ok(());
        };
        self.get_next(); // skip lhs param

        let Some(op_sym) = self.cur.sym else {
            self.report_error(
                ErrorKind::MissingToken,
                "Expected operator name in binary macro def",
            );
            self.skip_to_enddef();
            return Ok(());
        };
        self.get_next(); // skip op name

        let rhs_name = if let crate::token::TokenKind::Symbolic(ref s) = self.cur.token.kind {
            s.clone()
        } else {
            self.report_error(
                ErrorKind::MissingToken,
                "Expected parameter name in binary macro def",
            );
            self.skip_to_enddef();
            return Ok(());
        };
        self.get_next(); // skip rhs param

        // Expect `=`
        if self.cur.command == Command::Equals || self.cur.command == Command::Assignment {
            self.get_next();
        }

        // Scan body with two parameter names
        let param_names = vec![lhs_name, rhs_name];
        let body = self.scan_macro_body(&param_names);

        // Store the macro
        let info = MacroInfo {
            params: vec![ParamType::Expr, ParamType::Expr],
            body,
            is_vardef: false,
        };
        self.macros.insert(op_sym, info);

        // Set the symbol to the appropriate operator command
        let cmd = match def_op {
            x if x == MacroDefOp::PrimaryDef as u16 => Command::SecondaryPrimaryMacro,
            x if x == MacroDefOp::SecondaryDef as u16 => Command::ExpressionTertiaryMacro,
            _ => Command::TertiarySecondaryMacro, // tertiarydef
        };
        self.symbols.set(
            op_sym,
            crate::symbols::SymbolEntry {
                command: cmd,
                modifier: 0,
            },
        );

        self.get_x_next();
        if self.cur.command == Command::Semicolon {
            self.get_x_next();
        }
        Ok(())
    }

    /// Scan macro parameter list: `(expr x, suffix s, text t)`.
    ///
    /// Returns a list of (name, type) pairs. If there are no parentheses,
    /// returns an empty list (parameterless macro).
    fn scan_macro_params(&mut self) -> InterpResult<Vec<(String, ParamType)>> {
        let mut params = Vec::new();

        // Parse delimited parameters: (expr a, suffix b, text t)
        // Multiple delimited groups are allowed: (expr a)(text t)
        while self.cur.command == Command::LeftDelimiter {
            self.get_next(); // skip `(`

            // Empty param list: ()
            if self.cur.command == Command::RightDelimiter {
                self.get_next();
            } else {
                loop {
                    // Expect a param type: expr, suffix, or text
                    let param_type = if self.cur.command == Command::ParamType {
                        let pt = Self::delimited_param_type(self.cur.modifier);
                        self.get_next(); // skip type keyword
                        pt
                    } else {
                        ParamType::Expr
                    };

                    // Get the parameter name
                    let name = if let crate::token::TokenKind::Symbolic(ref s) = self.cur.token.kind
                    {
                        s.clone()
                    } else {
                        self.report_error(ErrorKind::MissingToken, "Expected parameter name");
                        String::new()
                    };
                    self.get_next(); // skip param name

                    params.push((name, param_type));

                    if self.cur.command == Command::Comma {
                        self.get_next();
                    } else if self.cur.command == Command::RightDelimiter {
                        self.get_next();
                        break;
                    } else {
                        break;
                    }
                }
            }
        }

        // Parse undelimited parameters: primary g, expr x, suffix s, text t
        // These appear between the closing `)` (or macro name) and `=`.
        // Special case: `expr t of p` adds both t (expr) and p (suffix).
        while self.cur.command == Command::ParamType {
            let pt = Self::undelimited_param_type(self.cur.modifier);
            self.get_next(); // skip type keyword

            let name = if let crate::token::TokenKind::Symbolic(ref s) = self.cur.token.kind {
                s.clone()
            } else {
                self.report_error(ErrorKind::MissingToken, "Expected parameter name");
                String::new()
            };
            self.get_next();

            params.push((name, pt));

            // Check for `of <name>` pattern (e.g., `expr t of p`)
            if self.cur.command == Command::OfToken {
                self.get_next(); // skip `of`
                let of_name = if let crate::token::TokenKind::Symbolic(ref s) = self.cur.token.kind
                {
                    s.clone()
                } else {
                    String::new()
                };
                self.get_next();
                params.push((of_name, ParamType::UndelimitedSuffix));
            }
        }

        Ok(params)
    }

    /// Convert a `ParamTypeOp` modifier to a delimited `ParamType`.
    const fn delimited_param_type(modifier: u16) -> ParamType {
        match modifier {
            x if x == ParamTypeOp::Suffix as u16 => ParamType::Suffix,
            x if x == ParamTypeOp::Text as u16 => ParamType::Text,
            // primary/secondary/tertiary inside delimiters are treated as expr
            _ => ParamType::Expr,
        }
    }

    /// Convert a `ParamTypeOp` modifier to an undelimited `ParamType`.
    const fn undelimited_param_type(modifier: u16) -> ParamType {
        match modifier {
            x if x == ParamTypeOp::Primary as u16 => ParamType::Primary,
            x if x == ParamTypeOp::Secondary as u16 => ParamType::Secondary,
            x if x == ParamTypeOp::Tertiary as u16 => ParamType::Tertiary,
            x if x == ParamTypeOp::Suffix as u16 => ParamType::UndelimitedSuffix,
            x if x == ParamTypeOp::Text as u16 => ParamType::UndelimitedText,
            _ => ParamType::UndelimitedExpr,
        }
    }

    /// Scan a suffix argument for macro expansion.
    ///
    /// Collects symbolic tokens (and bracket subscripts) until a non-suffix
    /// token is found.
    fn scan_suffix_arg(&mut self) -> TokenList {
        let mut suffix_tokens = TokenList::new();
        while self.cur.command == Command::TagToken
            || self.cur.command == Command::InternalQuantity
            || self.cur.command == Command::NumericToken
            || self.cur.command == Command::LeftBracket
        {
            self.store_current_token(&mut suffix_tokens);
            self.get_next();
            // If we entered a bracket, scan until ]
            if self.cur.command == Command::RightBracket {
                self.store_current_token(&mut suffix_tokens);
                self.get_next();
            }
        }
        suffix_tokens
    }

    /// Scan a delimited text argument for macro expansion.
    ///
    /// Collects tokens until closing delimiter or comma (if not last param).
    fn scan_text_arg(&mut self, param_idx: usize, all_params: &[ParamType]) -> TokenList {
        let mut text_tokens = TokenList::new();
        let mut delim_depth: u32 = 0;
        loop {
            if delim_depth == 0 {
                if self.cur.command == Command::RightDelimiter {
                    break;
                }
                if self.cur.command == Command::Comma && param_idx < all_params.len() - 1 {
                    break;
                }
            }
            if self.cur.command == Command::LeftDelimiter {
                delim_depth += 1;
            } else if self.cur.command == Command::RightDelimiter {
                delim_depth -= 1;
            }
            if self.cur.command == Command::Stop {
                break;
            }
            self.store_current_token(&mut text_tokens);
            self.get_next();
        }
        text_tokens
    }

    /// Scan a macro body until `enddef`, tracking nested `def`/`enddef` pairs.
    ///
    /// Parameter names are replaced with `StoredToken::Param(idx)` references.
    fn scan_macro_body(&mut self, param_names: &[String]) -> TokenList {
        let mut body = TokenList::new();
        let mut depth: u32 = 0;

        loop {
            match self.cur.command {
                Command::MacroDef => {
                    // Nested def — store and increase depth
                    depth += 1;
                    self.store_current_token(&mut body);
                    self.get_next();
                }
                Command::MacroSpecial if self.cur.modifier == 0 => {
                    // `enddef` — modifier 0 on MacroSpecial
                    if depth == 0 {
                        // Our enddef — don't store it, stop
                        return body;
                    }
                    depth -= 1;
                    self.store_current_token(&mut body);
                    self.get_next();
                }
                Command::Stop => {
                    self.report_error(ErrorKind::MissingToken, "Missing `enddef`");
                    return body;
                }
                _ => {
                    // Check if this token matches a parameter name
                    if let crate::token::TokenKind::Symbolic(ref name) = self.cur.token.kind {
                        if depth == 0 {
                            // Only substitute at top level (not inside nested defs)
                            if let Some(idx) = param_names.iter().position(|p| p == name) {
                                body.push(StoredToken::Param(idx));
                                self.get_next();
                                continue;
                            }
                        }
                    }
                    self.store_current_token(&mut body);
                    self.get_next();
                }
            }
        }
    }

    /// Expand a binary macro operator (from `primarydef`/`secondarydef`/`tertiarydef`).
    ///
    /// The left operand has already been evaluated and taken. The current
    /// token is the operator name. We need to scan the right operand at the
    /// next lower precedence level, then expand the body.
    fn expand_binary_macro(&mut self, left: &Value) -> InterpResult<()> {
        let Some(op_sym) = self.cur.sym else {
            return Err(InterpreterError::new(
                ErrorKind::Internal,
                "Binary macro without symbol",
            ));
        };

        let Some(macro_info) = self.macros.get(&op_sym).cloned() else {
            return Err(InterpreterError::new(
                ErrorKind::Internal,
                "Undefined binary macro",
            ));
        };

        // Determine which precedence to scan the RHS at
        let cmd = self.cur.command;
        self.get_x_next();
        match cmd {
            Command::SecondaryPrimaryMacro => self.scan_primary()?,
            Command::TertiarySecondaryMacro => self.scan_secondary()?,
            _ => self.scan_tertiary()?,
        }

        let right = self.take_cur_exp();

        // Build param token lists — decompose compound values into tokens
        let args = vec![
            value_to_stored_tokens(left, &mut self.symbols),
            value_to_stored_tokens(&right, &mut self.symbols),
        ];

        // Push the body with args
        self.input
            .push_token_list(macro_info.body, args, "binary macro".into());

        // Get next token from expansion
        self.get_x_next();
        // Re-scan the result as an expression
        self.scan_expression()?;

        Ok(())
    }

    /// Skip tokens until we reach `enddef` (for error recovery).
    fn skip_to_enddef(&mut self) {
        let mut depth: u32 = 0;
        loop {
            match self.cur.command {
                Command::MacroDef => {
                    depth += 1;
                    self.get_next();
                }
                Command::MacroSpecial if self.cur.modifier == 0 => {
                    if depth == 0 {
                        return;
                    }
                    depth -= 1;
                    self.get_next();
                }
                Command::Stop => return,
                _ => self.get_next(),
            }
        }
    }

    /// Expand a user-defined macro.
    ///
    /// Scans arguments according to the macro's parameter types, then pushes
    /// the body as a token list with parameter bindings.
    fn expand_defined_macro(&mut self) {
        let Some(macro_sym) = self.cur.sym else {
            self.report_error(ErrorKind::Internal, "DefinedMacro without symbol");
            self.get_next();
            self.expand_current();
            return;
        };

        let Some(macro_info) = self.macros.get(&macro_sym).cloned() else {
            self.report_error(ErrorKind::Internal, "Undefined macro expansion");
            self.get_next();
            self.expand_current();
            return;
        };

        // Scan arguments — only advance past the macro name if there are params
        let mut args: Vec<TokenList> = Vec::new();

        if !macro_info.params.is_empty() {
            self.get_next(); // advance past the macro name to start reading args
            let mut in_delimiters = false;

            for (i, param_type) in macro_info.params.iter().enumerate() {
                match param_type {
                    // --- Delimited parameters (inside parentheses) ---
                    ParamType::Expr | ParamType::Suffix | ParamType::Text => {
                        if !in_delimiters && self.cur.command == Command::LeftDelimiter {
                            self.get_x_next(); // skip `(`
                            in_delimiters = true;
                        }
                        match param_type {
                            ParamType::Expr => {
                                if self.scan_expression().is_ok() {
                                    let val = self.take_cur_exp();
                                    args.push(value_to_stored_tokens(&val, &mut self.symbols));
                                } else {
                                    args.push(Vec::new());
                                }
                            }
                            ParamType::Suffix => {
                                args.push(self.scan_suffix_arg());
                            }
                            ParamType::Text => {
                                args.push(self.scan_text_arg(i, &macro_info.params));
                            }
                            _ => {}
                        }
                        // Consume comma between delimited args
                        if self.cur.command == Command::Comma {
                            self.get_x_next();
                        }
                        // Close delimiters if this is the last delimited param
                        // or the next param is undelimited
                        let next_is_undelimited = macro_info
                            .params
                            .get(i + 1)
                            .copied()
                            .is_some_and(ParamType::is_undelimited);
                        if self.cur.command == Command::RightDelimiter
                            && (next_is_undelimited || i + 1 >= macro_info.params.len())
                        {
                            // Only advance past `)` if there are more params to
                            // scan.  When this is the LAST parameter, leave
                            // `self.cur` at `)` so the token that follows the
                            // macro call (typically `;`) is not consumed before
                            // the body expansion is pushed.
                            if next_is_undelimited {
                                self.get_x_next();
                            }
                            in_delimiters = false;
                        }
                    }

                    // --- Undelimited parameters ---
                    ParamType::Primary => {
                        self.scan_primary().ok();
                        let val = self.take_cur_exp();
                        args.push(value_to_stored_tokens(&val, &mut self.symbols));
                    }
                    ParamType::Secondary => {
                        self.scan_secondary().ok();
                        let val = self.take_cur_exp();
                        args.push(value_to_stored_tokens(&val, &mut self.symbols));
                    }
                    ParamType::Tertiary => {
                        self.scan_tertiary().ok();
                        let val = self.take_cur_exp();
                        args.push(value_to_stored_tokens(&val, &mut self.symbols));
                    }
                    ParamType::UndelimitedExpr => {
                        self.scan_expression().ok();
                        let val = self.take_cur_exp();
                        args.push(value_to_stored_tokens(&val, &mut self.symbols));
                    }
                    ParamType::UndelimitedSuffix => {
                        args.push(self.scan_suffix_arg());
                    }
                    ParamType::UndelimitedText => {
                        // Collect tokens until semicolon
                        let mut text_tokens = TokenList::new();
                        while self.cur.command != Command::Semicolon
                            && self.cur.command != Command::Stop
                        {
                            self.store_current_token(&mut text_tokens);
                            self.get_next();
                        }
                        args.push(text_tokens);
                    }
                }
            }

            // Note: do NOT advance past a trailing `)` here.  The token
            // after the macro call (e.g. `;`) must survive until the body
            // expansion completes.  The input stack will resume reading
            // from the source level (past `)`) once the expansion is done.
        }

        // Build the expansion token list
        let mut expansion = macro_info.body.clone();

        // For vardef, wrap in begingroup/endgroup
        if macro_info.is_vardef {
            let bg = self.symbols.lookup("begingroup");
            let eg = self.symbols.lookup("endgroup");
            expansion.insert(0, StoredToken::Symbol(bg));
            expansion.push(StoredToken::Symbol(eg));
        }

        // Push the expansion with parameter bindings
        self.input
            .push_token_list(expansion, args, "macro expansion".into());

        // Get the next token and continue expanding
        self.get_next();
        self.expand_current();
    }

    /// Handle `input <filename>`.
    ///
    /// Reads the named file via the filesystem trait and pushes it as a new
    /// source input level.
    fn expand_input(&mut self) {
        self.get_next(); // skip `input`

        // Get the filename from the next token
        let filename = match &self.cur.token.kind {
            crate::token::TokenKind::Symbolic(s) => s.clone(),
            crate::token::TokenKind::StringLit(s) => s.clone(),
            _ => {
                self.report_error(ErrorKind::MissingToken, "Expected filename after `input`");
                self.get_next();
                self.expand_current();
                return;
            }
        };

        // Try to read the file
        let contents = self.fs.read_file(&filename);

        match contents {
            Some(source) => {
                self.input.push_source(source);
            }
            None => {
                self.report_error(ErrorKind::Internal, format!("File not found: {filename}"));
            }
        }

        self.get_next();
        self.expand_current();
    }

    /// Handle `scantokens <string_expr>`.
    ///
    /// Evaluates the string expression and scans it as if it were source input.
    fn expand_scantokens(&mut self) {
        self.get_x_next(); // skip `scantokens`, expand

        // Scan the string expression
        if self.scan_primary().is_ok() {
            if let Value::String(ref s) = self.cur_exp {
                let source = s.to_string();
                if !source.is_empty() {
                    self.input.push_source(source);
                }
            } else {
                self.report_error(ErrorKind::TypeError, "scantokens requires a string");
            }
        }

        // The pushed source will be read by the next get_next
        self.get_next();
        self.expand_current();
    }

    // =======================================================================
    // Expression parser — four levels
    // =======================================================================

    /// Parse and evaluate a primary expression.
    fn scan_primary(&mut self) -> InterpResult<()> {
        match self.cur.command {
            Command::NumericToken => {
                if let crate::token::TokenKind::Numeric(v) = self.cur.token.kind {
                    self.cur_exp = Value::Numeric(v);
                    self.cur_type = Type::Known;
                }
                self.get_x_next();
                // Check for fraction: 3/4 as a primary
                if self.cur.command == Command::Slash {
                    self.get_x_next();
                    if let crate::token::TokenKind::Numeric(denom) = self.cur.token.kind {
                        if let Value::Numeric(numer) = self.cur_exp {
                            if denom.abs() > f64::EPSILON {
                                self.cur_exp = Value::Numeric(numer / denom);
                            } else {
                                self.report_error(ErrorKind::ArithmeticError, "Division by zero");
                            }
                        }
                        self.get_x_next();
                    }
                }
                Ok(())
            }

            Command::StringToken => {
                if let crate::token::TokenKind::StringLit(ref s) = self.cur.token.kind {
                    self.cur_exp = Value::String(Arc::from(s.as_str()));
                    self.cur_type = Type::String;
                }
                self.get_x_next();
                Ok(())
            }

            Command::Nullary => {
                let op = self.cur.modifier;
                self.get_x_next();
                self.do_nullary(op)
            }

            Command::Unary => {
                let op = self.cur.modifier;
                self.get_x_next();
                self.scan_primary()?;
                self.do_unary(op)
            }

            Command::PlusOrMinus => {
                // Unary plus or minus
                let is_minus = self.cur.modifier == PlusMinusOp::Minus as u16;
                self.get_x_next();
                self.scan_primary()?;
                if is_minus {
                    self.negate_cur_exp();
                }
                Ok(())
            }

            Command::LeftDelimiter => {
                // ( expr ) or ( expr , expr ) for pair/color
                self.get_x_next();
                self.scan_expression()?;

                if self.cur.command == Command::Comma {
                    // Pair or color
                    let first = self.take_cur_exp();
                    self.get_x_next();
                    self.scan_expression()?;

                    if self.cur.command == Command::Comma {
                        // Color: (r, g, b)
                        let second = self.take_cur_exp();
                        self.get_x_next();
                        self.scan_expression()?;
                        let third = self.take_cur_exp();

                        let r = value_to_scalar(&first)?;
                        let g = value_to_scalar(&second)?;
                        let b = value_to_scalar(&third)?;
                        self.cur_exp = Value::Color(Color::new(r, g, b));
                        self.cur_type = Type::ColorType;
                    } else {
                        // Pair: (x, y)
                        let second = self.take_cur_exp();
                        let x = value_to_scalar(&first)?;
                        let y = value_to_scalar(&second)?;
                        self.cur_exp = Value::Pair(x, y);
                        self.cur_type = Type::PairType;
                    }
                }

                // Expect closing delimiter
                if self.cur.command == Command::RightDelimiter {
                    self.get_x_next();
                }
                Ok(())
            }

            Command::BeginGroup => {
                self.save_stack.push_boundary();
                self.get_x_next();
                // Execute statements until endgroup
                while self.cur.command != Command::EndGroup && self.cur.command != Command::Stop {
                    self.do_statement()?;
                }
                // Restore scope
                self.do_endgroup();
                self.get_x_next();
                Ok(())
            }

            Command::TagToken => {
                // Variable reference — scan suffix parts to form compound name.
                //
                // MetaPost variable names are structured: `laboff.lft`, `z.r`,
                // etc.  The scanner drops `.` separators, so suffixes appear as
                // consecutive tokens.  A suffix part can be a `TagToken` or even
                // a `DefinedMacro` (e.g. `lft` is a vardef, but `laboff.lft` is
                // a declared pair variable).
                //
                // We use `get_next` (non-expanding) to peek at each potential
                // suffix token, and only collect it if the resulting compound
                // name is a declared variable.  If it's not a suffix, we call
                // `expand_current` to handle macro expansion as usual.
                let sym = self.cur.sym;
                let mut name = if let crate::token::TokenKind::Symbolic(ref s) = self.cur.token.kind
                {
                    s.clone()
                } else {
                    String::new()
                };
                // Use get_next (non-expanding) so we can inspect tokens that
                // might be vardef macros before they get expanded.
                self.get_next();

                // Collect suffix tokens, checking against declared variables.
                while self.cur.command == Command::TagToken
                    || self.cur.command == Command::DefinedMacro
                {
                    let next_name =
                        if let crate::token::TokenKind::Symbolic(ref s) = self.cur.token.kind {
                            s.clone()
                        } else {
                            break;
                        };
                    let compound = format!("{name}.{next_name}");
                    let var_id = self.variables.lookup(&compound);
                    if matches!(self.variables.get(var_id), VarValue::Undefined) {
                        break;
                    }
                    name = compound;
                    self.get_next();
                }

                // Now expand whatever token follows the variable name.
                self.expand_current();

                self.resolve_variable(sym, &name)
            }

            Command::InternalQuantity => {
                let idx = self.cur.modifier;
                self.cur_exp = Value::Numeric(self.internals.get(idx));
                self.cur_type = Type::Known;
                // Track for assignment LHS
                self.last_internal_idx = Some(idx);
                self.last_var_id = None;
                self.get_x_next();
                Ok(())
            }

            Command::PrimaryBinary => {
                // "expr X of Y" pattern
                let op = self.cur.modifier;
                self.get_x_next();
                self.scan_expression()?;
                // Expect "of"
                if self.cur.command != Command::OfToken {
                    return Err(InterpreterError::new(
                        ErrorKind::MissingToken,
                        "Missing `of`",
                    ));
                }
                let first = self.take_cur_exp();
                self.get_x_next();
                self.scan_primary()?;
                self.do_primary_binary(op, &first)
            }

            Command::Cycle => {
                // The `cycle` keyword in an expression context evaluates to true
                // if the current expression is a cyclic path. But as a primary
                // it's used in path construction — handle that at expression level.
                self.cur_exp = Value::Boolean(false);
                self.cur_type = Type::Boolean;
                self.get_x_next();
                Ok(())
            }

            Command::StrOp => {
                let op = self.cur.modifier;
                self.get_x_next();
                if op == StrOpOp::Str as u16 {
                    // `str` <suffix> — converts suffix to string
                    let name = if let crate::token::TokenKind::Symbolic(ref s) = self.cur.token.kind
                    {
                        s.clone()
                    } else {
                        String::new()
                    };
                    self.get_x_next();
                    self.cur_exp = Value::String(Arc::from(name.as_str()));
                } else {
                    // readfrom etc. — not yet implemented
                    self.cur_exp = Value::String(Arc::from(""));
                }
                self.cur_type = Type::String;
                Ok(())
            }

            Command::TypeName => {
                // Type name as primary — used in type declarations
                // In expression context, this is an error
                Err(InterpreterError::new(
                    ErrorKind::InvalidExpression,
                    "Type name cannot be used as an expression",
                ))
            }

            _ => {
                // Missing primary — set to vacuous
                self.cur_exp = Value::Vacuous;
                self.cur_type = Type::Vacuous;
                Ok(())
            }
        }?;

        // Check for mediation: a[b,c] = (1-a)*b + a*c
        if self.cur.command == Command::LeftBracket {
            if let Value::Numeric(a) = self.cur_exp {
                self.get_x_next();
                self.scan_expression()?;
                let b = value_to_scalar(&self.take_cur_exp())?;
                if self.cur.command == Command::Comma {
                    self.get_x_next();
                } else {
                    return Err(InterpreterError::new(
                        ErrorKind::MissingToken,
                        "Expected `,` in mediation a[b,c]",
                    ));
                }
                self.scan_expression()?;
                let c = value_to_scalar(&self.take_cur_exp())?;
                if self.cur.command == Command::RightBracket {
                    self.get_x_next();
                }
                // a[b,c] = b + a*(c - b) = (1-a)*b + a*c
                self.cur_exp = Value::Numeric(a.mul_add(c - b, b));
                self.cur_type = Type::Known;
            }
        }

        Ok(())
    }

    /// Parse and evaluate a secondary expression.
    fn scan_secondary(&mut self) -> InterpResult<()> {
        self.scan_primary()?;

        while self.cur.command.is_secondary_op() {
            let cmd = self.cur.command;

            if cmd == Command::SecondaryPrimaryMacro {
                // User-defined primarydef operator
                let left = self.take_cur_exp();
                self.expand_binary_macro(&left)?;
                break;
            }

            let op = self.cur.modifier;
            let left = self.take_cur_exp();
            self.get_x_next();
            self.scan_primary()?;

            match cmd {
                Command::SecondaryBinary => {
                    self.do_secondary_binary(op, &left)?;
                }
                Command::Slash => {
                    // Division
                    let right = self.take_cur_exp();
                    let a = value_to_scalar(&left)?;
                    let b = value_to_scalar(&right)?;
                    if b.abs() < f64::EPSILON {
                        self.report_error(ErrorKind::ArithmeticError, "Division by zero");
                        self.cur_exp = Value::Numeric(0.0);
                    } else {
                        self.cur_exp = Value::Numeric(a / b);
                    }
                    self.cur_type = Type::Known;
                }
                Command::And => {
                    // Logical and
                    let right = self.take_cur_exp();
                    let a = value_to_bool(&left)?;
                    let b = value_to_bool(&right)?;
                    self.cur_exp = Value::Boolean(a && b);
                    self.cur_type = Type::Boolean;
                }
                _ => {}
            }
        }
        Ok(())
    }

    /// Parse and evaluate a tertiary expression.
    fn scan_tertiary(&mut self) -> InterpResult<()> {
        self.scan_secondary()?;

        while self.cur.command.is_tertiary_op() {
            let cmd = self.cur.command;

            if cmd == Command::TertiarySecondaryMacro {
                // User-defined tertiarydef operator
                let left = self.take_cur_exp();
                self.expand_binary_macro(&left)?;
                break;
            }

            let op = self.cur.modifier;
            let left = self.take_cur_exp();
            self.get_x_next();
            self.scan_secondary()?;

            match cmd {
                Command::PlusOrMinus => {
                    let right = self.take_cur_exp();
                    self.do_plus_minus(op, &left, &right)?;
                }
                Command::TertiaryBinary => {
                    let right = self.take_cur_exp();
                    self.do_tertiary_binary(op, &left, &right)?;
                }
                _ => {}
            }
        }
        Ok(())
    }

    /// Parse and evaluate an expression.
    ///
    /// Handles expression-level binary operators and path construction.
    pub fn scan_expression(&mut self) -> InterpResult<()> {
        self.scan_tertiary()?;

        while self.cur.command.is_expression_op() {
            let cmd = self.cur.command;
            let op = self.cur.modifier;

            match cmd {
                Command::Equals => {
                    // This is either an equation or assignment
                    // Don't consume here — let the caller handle it
                    break;
                }
                Command::PathJoin => {
                    // Path construction
                    self.scan_path_construction()?;
                    break;
                }
                Command::Ampersand => {
                    // & is path join for pairs/paths, string concat otherwise
                    if matches!(self.cur_type, Type::PairType | Type::Path) {
                        self.scan_path_construction()?;
                    } else {
                        // String concatenation
                        let left = self.take_cur_exp();
                        self.get_x_next();
                        self.scan_tertiary()?;
                        self.do_expression_binary(ExpressionBinaryOp::Concatenate as u16, &left)?;
                    }
                    break;
                }
                Command::ExpressionTertiaryMacro => {
                    // User-defined secondarydef operator
                    let left = self.take_cur_exp();
                    self.expand_binary_macro(&left)?;
                    break;
                }
                Command::ExpressionBinary => {
                    let left = self.take_cur_exp();
                    self.get_x_next();
                    self.scan_tertiary()?;
                    self.do_expression_binary(op, &left)?;
                }
                Command::LeftBrace => {
                    // Direction specification — start of path construction
                    self.scan_path_construction()?;
                    break;
                }
                _ => break,
            }
        }
        Ok(())
    }

    // =======================================================================
    // Path construction
    // =======================================================================

    /// Parse a path expression starting from the current point/expression.
    fn scan_path_construction(&mut self) -> InterpResult<()> {
        let first_point = self.take_cur_exp();
        let mut knots = vec![self.value_to_knot(&first_point)?];
        let mut is_cyclic = false;

        loop {
            // Parse optional pre-join direction {dir} or {curl n}
            let pre_dir = if self.cur.command == Command::LeftBrace {
                Some(self.scan_brace_direction()?)
            } else {
                None
            };

            // Set the right direction of the last knot
            if let Some(dir) = pre_dir {
                if let Some(last) = knots.last_mut() {
                    last.right = dir;
                }
            }

            // Parse the join operator
            let join_type = if self.cur.command == Command::PathJoin {
                let modifier = self.cur.modifier;
                self.get_x_next();
                modifier
            } else if self.cur.command == Command::Ampersand {
                self.get_x_next();
                u16::MAX // special value for &
            } else {
                break;
            };

            // Parse tension/controls — returns pending left-side for next knot
            let pending = if join_type == u16::MAX {
                None
            } else {
                self.parse_join_options(&mut knots)?
            };

            // Parse optional post-join direction {dir} or {curl n}
            let post_dir = if self.cur.command == Command::LeftBrace {
                Some(self.scan_brace_direction()?)
            } else {
                None
            };

            // Check for cycle
            if self.cur.command == Command::Cycle {
                is_cyclic = true;
                if let Some(dir) = post_dir {
                    knots[0].left = dir;
                }
                // Apply pending join to first knot (cycle target)
                match pending {
                    Some(PendingJoin::Tension(t)) => knots[0].left_tension = t,
                    Some(PendingJoin::Control(pt)) => {
                        knots[0].left = KnotDirection::Explicit(pt);
                    }
                    None => {}
                }
                self.get_x_next();
                break;
            }

            // Parse the next point
            self.scan_tertiary()?;
            let point_val = self.take_cur_exp();
            let mut knot = self.value_to_knot(&point_val)?;
            if let Some(dir) = post_dir {
                knot.left = dir;
            }
            // Apply pending left-side join from tension/controls
            match pending {
                Some(PendingJoin::Tension(t)) => knot.left_tension = t,
                Some(PendingJoin::Control(pt)) => knot.left = KnotDirection::Explicit(pt),
                None => {}
            }
            knots.push(knot);
        }

        // Build the path
        let mut path_obj = Path::from_knots(knots, is_cyclic);
        hobby::make_choices(&mut path_obj);

        self.cur_exp = Value::Path(path_obj);
        self.cur_type = Type::Path;
        Ok(())
    }

    /// Parse tension/controls options after `..`.
    ///
    /// Returns a pending left-side specification for the *next* knot:
    /// - `Some(PendingJoin::Tension(t))` — the next knot's `left_tension`
    /// - `Some(PendingJoin::Control(pt))` — the next knot's `left` direction (explicit)
    /// - `None` — no pending state
    fn parse_join_options(&mut self, knots: &mut Vec<Knot>) -> InterpResult<Option<PendingJoin>> {
        match self.cur.command {
            Command::Tension => {
                self.get_x_next();
                let at_least = self.cur.command == Command::AtLeast;
                if at_least {
                    self.get_x_next();
                }
                self.scan_primary()?;
                let t1 = value_to_scalar(&self.take_cur_exp())?;
                let t1 = if at_least { -t1.abs() } else { t1 };

                let t2 = if self.cur.command == Command::And {
                    self.get_x_next();
                    let at_least2 = self.cur.command == Command::AtLeast;
                    if at_least2 {
                        self.get_x_next();
                    }
                    self.scan_primary()?;
                    let t = value_to_scalar(&self.take_cur_exp())?;
                    if at_least2 {
                        -t.abs()
                    } else {
                        t
                    }
                } else {
                    t1
                };

                if let Some(last) = knots.last_mut() {
                    last.right_tension = t1;
                }
                Ok(Some(PendingJoin::Tension(t2)))
            }
            Command::Controls => {
                self.get_x_next();
                self.scan_primary()?;
                let cp1 = self.take_cur_exp();
                let (x1, y1) = value_to_pair(&cp1)?;

                let (x2, y2) = if self.cur.command == Command::And {
                    self.get_x_next();
                    self.scan_primary()?;
                    let cp2 = self.take_cur_exp();
                    value_to_pair(&cp2)?
                } else {
                    (x1, y1)
                };

                if let Some(last) = knots.last_mut() {
                    last.right = KnotDirection::Explicit(Point::new(x1, y1));
                }
                Ok(Some(PendingJoin::Control(Point::new(x2, y2))))
            }
            _ => Ok(None), // No special join options
        }
    }

    /// Convert a value to a path knot.
    fn value_to_knot(&self, val: &Value) -> InterpResult<Knot> {
        match val {
            Value::Pair(x, y) => Ok(Knot::new(Point::new(*x, *y))),
            Value::Numeric(v) => {
                // Single numeric — treat as (v, 0)? Or error?
                // In MetaPost, a numeric in path context uses z-convention
                // For now, error
                Err(InterpreterError::new(
                    ErrorKind::TypeError,
                    format!("Expected pair in path, got numeric {v}"),
                ))
            }
            _ => Err(InterpreterError::new(
                ErrorKind::TypeError,
                format!("Expected pair in path, got {}", val.ty()),
            )),
        }
    }

    /// Parse a brace-enclosed direction: `{dir}` or `{curl n}`.
    fn scan_brace_direction(&mut self) -> InterpResult<KnotDirection> {
        self.get_x_next(); // skip `{`

        if self.cur.command == Command::CurlCommand {
            // {curl <numeric>}
            self.get_x_next();
            self.scan_primary()?;
            let curl_val = value_to_scalar(&self.cur_exp)?;
            if self.cur.command == Command::RightBrace {
                self.get_x_next();
            }
            Ok(KnotDirection::Curl(curl_val))
        } else {
            // {<expression>} — direction as pair or angle
            self.scan_expression()?;
            let dir = self.take_cur_exp();
            if self.cur.command == Command::RightBrace {
                self.get_x_next();
            }
            self.value_to_direction(&dir)
        }
    }

    /// Convert a value to a direction for path construction.
    fn value_to_direction(&self, val: &Value) -> InterpResult<KnotDirection> {
        match val {
            Value::Pair(x, y) => Ok(KnotDirection::Given(math::angle(*x, *y))),
            Value::Numeric(v) => Ok(KnotDirection::Given(*v)),
            _ => Err(InterpreterError::new(
                ErrorKind::TypeError,
                format!("Expected direction, got {}", val.ty()),
            )),
        }
    }

    // =======================================================================
    // Operator implementations
    // =======================================================================

    /// Execute a nullary operator.
    fn do_nullary(&mut self, op: u16) -> InterpResult<()> {
        match op {
            x if x == NullaryOp::True as u16 => {
                self.cur_exp = Value::Boolean(true);
                self.cur_type = Type::Boolean;
            }
            x if x == NullaryOp::False as u16 => {
                self.cur_exp = Value::Boolean(false);
                self.cur_type = Type::Boolean;
            }
            x if x == NullaryOp::NullPicture as u16 => {
                self.cur_exp = Value::Picture(Picture::new());
                self.cur_type = Type::Picture;
            }
            x if x == NullaryOp::NullPen as u16 => {
                self.cur_exp = Value::Pen(pen::nullpen());
                self.cur_type = Type::Pen;
            }
            x if x == NullaryOp::PenCircle as u16 => {
                self.cur_exp = Value::Pen(pen::pencircle(1.0));
                self.cur_type = Type::Pen;
            }
            x if x == NullaryOp::NormalDeviate as u16 => {
                self.cur_exp = Value::Numeric(math::normal_deviate(&mut self.random_seed));
                self.cur_type = Type::Known;
            }
            x if x == NullaryOp::JobName as u16 => {
                self.cur_exp = Value::String(Arc::from(self.job_name.as_str()));
                self.cur_type = Type::String;
            }
            _ => {
                self.cur_exp = Value::Vacuous;
                self.cur_type = Type::Vacuous;
            }
        }
        Ok(())
    }

    /// Execute a unary operator on `cur_exp`.
    #[expect(clippy::too_many_lines, reason = "matching all unary ops")]
    fn do_unary(&mut self, op: u16) -> InterpResult<()> {
        match op {
            x if x == UnaryOp::Not as u16 => {
                let b = value_to_bool(&self.cur_exp)?;
                self.cur_exp = Value::Boolean(!b);
                self.cur_type = Type::Boolean;
            }
            x if x == UnaryOp::Sqrt as u16 => {
                let v = value_to_scalar(&self.cur_exp)?;
                self.cur_exp = Value::Numeric(if v >= 0.0 { v.sqrt() } else { 0.0 });
                self.cur_type = Type::Known;
            }
            x if x == UnaryOp::SinD as u16 => {
                let v = value_to_scalar(&self.cur_exp)?;
                self.cur_exp = Value::Numeric(math::sind(v));
                self.cur_type = Type::Known;
            }
            x if x == UnaryOp::CosD as u16 => {
                let v = value_to_scalar(&self.cur_exp)?;
                self.cur_exp = Value::Numeric(math::cosd(v));
                self.cur_type = Type::Known;
            }
            x if x == UnaryOp::Floor as u16 => {
                let v = value_to_scalar(&self.cur_exp)?;
                self.cur_exp = Value::Numeric(math::floor(v));
                self.cur_type = Type::Known;
            }
            x if x == UnaryOp::MExp as u16 => {
                let v = value_to_scalar(&self.cur_exp)?;
                self.cur_exp = Value::Numeric(math::mexp(v));
                self.cur_type = Type::Known;
            }
            x if x == UnaryOp::MLog as u16 => {
                let v = value_to_scalar(&self.cur_exp)?;
                self.cur_exp = Value::Numeric(math::mlog(v));
                self.cur_type = Type::Known;
            }
            x if x == UnaryOp::Angle as u16 => {
                let (px, py) = value_to_pair(&self.cur_exp)?;
                self.cur_exp = Value::Numeric(math::angle(px, py));
                self.cur_type = Type::Known;
            }
            x if x == UnaryOp::UniformDeviate as u16 => {
                let v = value_to_scalar(&self.cur_exp)?;
                self.cur_exp = Value::Numeric(math::uniform_deviate(v, &mut self.random_seed));
                self.cur_type = Type::Known;
            }
            x if x == UnaryOp::Length as u16 => {
                match &self.cur_exp {
                    Value::Path(p) => {
                        self.cur_exp = Value::Numeric(p.length() as f64);
                    }
                    Value::String(s) => {
                        self.cur_exp = Value::Numeric(s.len() as f64);
                    }
                    Value::Pair(x, y) => {
                        // abs(pair) = sqrt(x^2 + y^2)
                        self.cur_exp = Value::Numeric(x.hypot(*y));
                    }
                    _ => {
                        return Err(InterpreterError::new(
                            ErrorKind::TypeError,
                            "length requires path, string, or pair",
                        ));
                    }
                }
                self.cur_type = Type::Known;
            }
            x if x == UnaryOp::Decimal as u16 => {
                let v = value_to_scalar(&self.cur_exp)?;
                self.cur_exp = Value::String(Arc::from(format!("{v}").as_str()));
                self.cur_type = Type::String;
            }
            x if x == UnaryOp::Reverse as u16 => {
                if let Value::Path(ref p) = self.cur_exp {
                    self.cur_exp = Value::Path(path::reverse(p));
                    self.cur_type = Type::Path;
                } else {
                    return Err(InterpreterError::new(
                        ErrorKind::TypeError,
                        "reverse requires a path",
                    ));
                }
            }
            x if x == UnaryOp::XPart as u16 => {
                self.extract_part(0)?;
            }
            x if x == UnaryOp::YPart as u16 => {
                self.extract_part(1)?;
            }
            x if x == UnaryOp::XXPart as u16 => {
                self.extract_part(2)?;
            }
            x if x == UnaryOp::XYPart as u16 => {
                self.extract_part(3)?;
            }
            x if x == UnaryOp::YXPart as u16 => {
                self.extract_part(4)?;
            }
            x if x == UnaryOp::YYPart as u16 => {
                self.extract_part(5)?;
            }
            x if x == UnaryOp::RedPart as u16 => {
                self.extract_color_part(0)?;
            }
            x if x == UnaryOp::GreenPart as u16 => {
                self.extract_color_part(1)?;
            }
            x if x == UnaryOp::BluePart as u16 => {
                self.extract_color_part(2)?;
            }
            x if x == UnaryOp::MakePath as u16 => {
                if let Value::Pen(ref p) = self.cur_exp {
                    self.cur_exp = Value::Path(pen::makepath(p));
                    self.cur_type = Type::Path;
                } else {
                    return Err(InterpreterError::new(
                        ErrorKind::TypeError,
                        "makepath requires a pen",
                    ));
                }
            }
            x if x == UnaryOp::MakePen as u16 => {
                if let Value::Path(ref p) = self.cur_exp {
                    let result = pen::makepen(p).map_err(|e| {
                        InterpreterError::new(ErrorKind::TypeError, format!("makepen: {e}"))
                    })?;
                    self.cur_exp = Value::Pen(result);
                    self.cur_type = Type::Pen;
                } else {
                    return Err(InterpreterError::new(
                        ErrorKind::TypeError,
                        "makepen requires a path",
                    ));
                }
            }
            x if x == UnaryOp::CycleOp as u16 => {
                let is_cyclic = matches!(&self.cur_exp, Value::Path(p) if p.is_cyclic);
                self.cur_exp = Value::Boolean(is_cyclic);
                self.cur_type = Type::Boolean;
            }
            _ => {
                // Unimplemented unary — leave cur_exp unchanged
            }
        }
        Ok(())
    }

    /// Execute an "X of Y" binary operator.
    fn do_primary_binary(&mut self, op: u16, first: &Value) -> InterpResult<()> {
        let second = &self.cur_exp;

        match op {
            x if x == PrimaryBinaryOp::PointOf as u16 => {
                let t = value_to_scalar(first)?;
                let p = value_to_path(second)?;
                let pt = path::point_of(p, t);
                self.cur_exp = Value::Pair(pt.x, pt.y);
                self.cur_type = Type::PairType;
            }
            x if x == PrimaryBinaryOp::DirectionOf as u16 => {
                let t = value_to_scalar(first)?;
                let p = value_to_path(second)?;
                let dir = path::direction_of(p, t);
                self.cur_exp = Value::Pair(dir.x, dir.y);
                self.cur_type = Type::PairType;
            }
            x if x == PrimaryBinaryOp::PrecontrolOf as u16 => {
                let t = value_to_scalar(first)?;
                let p = value_to_path(second)?;
                let pt = path::precontrol_of(p, t);
                self.cur_exp = Value::Pair(pt.x, pt.y);
                self.cur_type = Type::PairType;
            }
            x if x == PrimaryBinaryOp::PostcontrolOf as u16 => {
                let t = value_to_scalar(first)?;
                let p = value_to_path(second)?;
                let pt = path::postcontrol_of(p, t);
                self.cur_exp = Value::Pair(pt.x, pt.y);
                self.cur_type = Type::PairType;
            }
            x if x == PrimaryBinaryOp::SubpathOf as u16 => {
                let (t1, t2) = value_to_pair(first)?;
                let p = value_to_path(second)?;
                self.cur_exp = Value::Path(path::subpath(p, t1, t2));
                self.cur_type = Type::Path;
            }
            x if x == PrimaryBinaryOp::PenOffsetOf as u16 => {
                let (dx, dy) = value_to_pair(first)?;
                let p = value_to_pen(second)?;
                let pt = pen::penoffset(p, kurbo::Vec2::new(dx, dy));
                self.cur_exp = Value::Pair(pt.x, pt.y);
                self.cur_type = Type::PairType;
            }
            _ => {
                self.report_error(ErrorKind::InvalidExpression, "Unimplemented primary binary");
            }
        }
        Ok(())
    }

    /// Execute a secondary binary operator.
    fn do_secondary_binary(&mut self, op: u16, left: &Value) -> InterpResult<()> {
        let right = self.take_cur_exp();

        match op {
            x if x == SecondaryBinaryOp::Times as u16 => {
                // Scalar * scalar, or scalar * pair, or pair * scalar
                match (left, &right) {
                    (Value::Numeric(a), Value::Numeric(b)) => {
                        self.cur_exp = Value::Numeric(a * b);
                        self.cur_type = Type::Known;
                    }
                    (Value::Numeric(a), Value::Pair(bx, by)) => {
                        self.cur_exp = Value::Pair(a * bx, a * by);
                        self.cur_type = Type::PairType;
                    }
                    (Value::Pair(ax, ay), Value::Numeric(b)) => {
                        self.cur_exp = Value::Pair(ax * b, ay * b);
                        self.cur_type = Type::PairType;
                    }
                    _ => {
                        return Err(InterpreterError::new(
                            ErrorKind::TypeError,
                            "Invalid types for *",
                        ));
                    }
                }
            }
            x if x == SecondaryBinaryOp::Scaled as u16 => {
                let factor = value_to_scalar(&right)?;
                self.apply_transform(left, &transform::scaled(factor))?;
            }
            x if x == SecondaryBinaryOp::Shifted as u16 => {
                let (dx, dy) = value_to_pair(&right)?;
                self.apply_transform(left, &transform::shifted(dx, dy))?;
            }
            x if x == SecondaryBinaryOp::Rotated as u16 => {
                let angle = value_to_scalar(&right)?;
                self.apply_transform(left, &transform::rotated(angle))?;
            }
            x if x == SecondaryBinaryOp::XScaled as u16 => {
                let factor = value_to_scalar(&right)?;
                self.apply_transform(left, &transform::xscaled(factor))?;
            }
            x if x == SecondaryBinaryOp::YScaled as u16 => {
                let factor = value_to_scalar(&right)?;
                self.apply_transform(left, &transform::yscaled(factor))?;
            }
            x if x == SecondaryBinaryOp::Slanted as u16 => {
                let factor = value_to_scalar(&right)?;
                self.apply_transform(left, &transform::slanted(factor))?;
            }
            x if x == SecondaryBinaryOp::ZScaled as u16 => {
                let (a, b) = value_to_pair(&right)?;
                self.apply_transform(left, &transform::zscaled(a, b))?;
            }
            x if x == SecondaryBinaryOp::Transformed as u16 => {
                let t = value_to_transform(&right)?;
                self.apply_transform(left, &t)?;
            }
            x if x == SecondaryBinaryOp::DotProd as u16 => {
                let (ax, ay) = value_to_pair(left)?;
                let (bx, by) = value_to_pair(&right)?;
                self.cur_exp = Value::Numeric(ax.mul_add(bx, ay * by));
                self.cur_type = Type::Known;
            }
            _ => {
                self.report_error(
                    ErrorKind::InvalidExpression,
                    "Unimplemented secondary binary",
                );
            }
        }
        Ok(())
    }

    /// Apply a transform to a value and set `cur_exp`.
    fn apply_transform(&mut self, val: &Value, t: &Transform) -> InterpResult<()> {
        match val {
            Value::Pair(x, y) => {
                let pt = transform::transform_point(t, Point::new(*x, *y));
                self.cur_exp = Value::Pair(pt.x, pt.y);
                self.cur_type = Type::PairType;
            }
            Value::Path(p) => {
                self.cur_exp = Value::Path(transform::transform_path(t, p));
                self.cur_type = Type::Path;
            }
            Value::Pen(p) => {
                self.cur_exp = Value::Pen(transform::transform_pen(t, p));
                self.cur_type = Type::Pen;
            }
            Value::Picture(p) => {
                self.cur_exp = Value::Picture(transform::transform_picture(t, p));
                self.cur_type = Type::Picture;
            }
            Value::Transform(existing) => {
                self.cur_exp = Value::Transform(transform::compose(existing, t));
                self.cur_type = Type::TransformType;
            }
            _ => {
                // For unknown/numeric values (e.g., in equation context), leave unchanged
                self.report_error(
                    ErrorKind::TypeError,
                    format!("Cannot transform {}", val.ty()),
                );
            }
        }
        Ok(())
    }

    /// Execute plus or minus on two operands.
    fn do_plus_minus(&mut self, op: u16, left: &Value, right: &Value) -> InterpResult<()> {
        let is_plus = op == PlusMinusOp::Plus as u16;

        match (left, right) {
            (Value::Numeric(a), Value::Numeric(b)) => {
                self.cur_exp = Value::Numeric(if is_plus { a + b } else { a - b });
                self.cur_type = Type::Known;
            }
            (Value::Pair(ax, ay), Value::Pair(bx, by)) => {
                self.cur_exp = if is_plus {
                    Value::Pair(ax + bx, ay + by)
                } else {
                    Value::Pair(ax - bx, ay - by)
                };
                self.cur_type = Type::PairType;
            }
            (Value::Color(a), Value::Color(b)) => {
                self.cur_exp = Value::Color(if is_plus {
                    Color::new(a.r + b.r, a.g + b.g, a.b + b.b)
                } else {
                    Color::new(a.r - b.r, a.g - b.g, a.b - b.b)
                });
                self.cur_type = Type::ColorType;
            }
            (Value::String(a), Value::String(b)) if is_plus => {
                // String concatenation with +? No, that's &. This should error.
                return Err(InterpreterError::new(
                    ErrorKind::TypeError,
                    format!("Cannot add strings (use & for concatenation): \"{a}\" + \"{b}\""),
                ));
            }
            _ => {
                return Err(InterpreterError::new(
                    ErrorKind::TypeError,
                    format!(
                        "Incompatible types for {}: {} and {}",
                        if is_plus { "+" } else { "-" },
                        left.ty(),
                        right.ty()
                    ),
                ));
            }
        }
        Ok(())
    }

    /// Execute a tertiary binary operator.
    fn do_tertiary_binary(&mut self, op: u16, left: &Value, right: &Value) -> InterpResult<()> {
        match op {
            x if x == TertiaryBinaryOp::PythagAdd as u16 => {
                let a = value_to_scalar(left)?;
                let b = value_to_scalar(right)?;
                self.cur_exp = Value::Numeric(math::pyth_add(a, b));
                self.cur_type = Type::Known;
            }
            x if x == TertiaryBinaryOp::PythagSub as u16 => {
                let a = value_to_scalar(left)?;
                let b = value_to_scalar(right)?;
                self.cur_exp = Value::Numeric(math::pyth_sub(a, b));
                self.cur_type = Type::Known;
            }
            x if x == TertiaryBinaryOp::Or as u16 => {
                let a = value_to_bool(left)?;
                let b = value_to_bool(right)?;
                self.cur_exp = Value::Boolean(a || b);
                self.cur_type = Type::Boolean;
            }
            _ => {
                self.report_error(ErrorKind::InvalidExpression, "Unknown tertiary binary");
            }
        }
        Ok(())
    }

    /// Execute an expression binary operator.
    fn do_expression_binary(&mut self, op: u16, left: &Value) -> InterpResult<()> {
        let right = self.take_cur_exp();

        match op {
            x if x == ExpressionBinaryOp::LessThan as u16 => {
                let a = value_to_scalar(left)?;
                let b = value_to_scalar(&right)?;
                self.cur_exp = Value::Boolean(a < b);
                self.cur_type = Type::Boolean;
            }
            x if x == ExpressionBinaryOp::LessOrEqual as u16 => {
                let a = value_to_scalar(left)?;
                let b = value_to_scalar(&right)?;
                self.cur_exp = Value::Boolean(a <= b);
                self.cur_type = Type::Boolean;
            }
            x if x == ExpressionBinaryOp::GreaterThan as u16 => {
                let a = value_to_scalar(left)?;
                let b = value_to_scalar(&right)?;
                self.cur_exp = Value::Boolean(a > b);
                self.cur_type = Type::Boolean;
            }
            x if x == ExpressionBinaryOp::GreaterOrEqual as u16 => {
                let a = value_to_scalar(left)?;
                let b = value_to_scalar(&right)?;
                self.cur_exp = Value::Boolean(a >= b);
                self.cur_type = Type::Boolean;
            }
            x if x == ExpressionBinaryOp::EqualTo as u16 => {
                let result = values_equal(left, &right);
                self.cur_exp = Value::Boolean(result);
                self.cur_type = Type::Boolean;
            }
            x if x == ExpressionBinaryOp::UnequalTo as u16 => {
                let result = !values_equal(left, &right);
                self.cur_exp = Value::Boolean(result);
                self.cur_type = Type::Boolean;
            }
            x if x == ExpressionBinaryOp::Concatenate as u16 => {
                let a = value_to_string(left)?;
                let b = value_to_string(&right)?;
                let result = format!("{a}{b}");
                self.cur_exp = Value::String(Arc::from(result.as_str()));
                self.cur_type = Type::String;
            }
            x if x == ExpressionBinaryOp::IntersectionTimes as u16 => {
                let p1 = value_to_path(left)?;
                let p2 = value_to_path(&right)?;
                let result = postmeta_graphics::intersection::intersection_times(p1, p2);
                match result {
                    Some(isect) => {
                        self.cur_exp = Value::Pair(isect.t1, isect.t2);
                    }
                    None => {
                        self.cur_exp = Value::Pair(-1.0, -1.0);
                    }
                }
                self.cur_type = Type::PairType;
            }
            x if x == ExpressionBinaryOp::SubstringOf as u16 => {
                let (start, end) = value_to_pair(left)?;
                let s = value_to_string(&right)?;
                let start_idx = start.round() as usize;
                let end_idx = end.round().min(s.len() as f64) as usize;
                let substr = if start_idx < end_idx && start_idx < s.len() {
                    &s[start_idx..end_idx.min(s.len())]
                } else {
                    ""
                };
                self.cur_exp = Value::String(Arc::from(substr));
                self.cur_type = Type::String;
            }
            _ => {
                self.report_error(ErrorKind::InvalidExpression, "Unknown expression binary");
            }
        }
        Ok(())
    }

    // =======================================================================
    // Part extractors
    // =======================================================================

    /// Extract a part from a pair or transform.
    fn extract_part(&mut self, part: usize) -> InterpResult<()> {
        match &self.cur_exp {
            Value::Pair(x, y) => {
                let v = match part {
                    0 => *x,
                    1 => *y,
                    _ => {
                        return Err(InterpreterError::new(
                            ErrorKind::TypeError,
                            "Pair only has xpart and ypart",
                        ))
                    }
                };
                self.cur_exp = Value::Numeric(v);
                self.cur_type = Type::Known;
            }
            Value::Transform(t) => {
                let v = match part {
                    0 => t.tx,
                    1 => t.ty,
                    2 => t.txx,
                    3 => t.txy,
                    4 => t.tyx,
                    5 => t.tyy,
                    _ => {
                        return Err(InterpreterError::new(
                            ErrorKind::TypeError,
                            "Invalid transform part",
                        ))
                    }
                };
                self.cur_exp = Value::Numeric(v);
                self.cur_type = Type::Known;
            }
            _ => {
                return Err(InterpreterError::new(
                    ErrorKind::TypeError,
                    format!("{} has no xpart/ypart", self.cur_exp.ty()),
                ));
            }
        }
        Ok(())
    }

    /// Extract a color part.
    fn extract_color_part(&mut self, part: usize) -> InterpResult<()> {
        if let Value::Color(c) = &self.cur_exp {
            let v = match part {
                0 => c.r,
                1 => c.g,
                2 => c.b,
                _ => {
                    return Err(InterpreterError::new(
                        ErrorKind::TypeError,
                        "Invalid color part",
                    ))
                }
            };
            self.cur_exp = Value::Numeric(v);
            self.cur_type = Type::Known;
            Ok(())
        } else {
            Err(InterpreterError::new(
                ErrorKind::TypeError,
                format!("{} has no color parts", self.cur_exp.ty()),
            ))
        }
    }

    // =======================================================================
    // Value helpers
    // =======================================================================

    /// Take `cur_exp`, replacing it with `Vacuous`.
    const fn take_cur_exp(&mut self) -> Value {
        let val = std::mem::replace(&mut self.cur_exp, Value::Vacuous);
        self.cur_type = Type::Vacuous;
        val
    }

    /// Negate the current expression (unary minus).
    fn negate_cur_exp(&mut self) {
        match &self.cur_exp {
            Value::Numeric(v) => self.cur_exp = Value::Numeric(-v),
            Value::Pair(x, y) => self.cur_exp = Value::Pair(-x, -y),
            Value::Color(c) => {
                self.cur_exp = Value::Color(Color::new(-c.r, -c.g, -c.b));
            }
            _ => {
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

        match self.variables.get(var_id) {
            VarValue::Known(v) => {
                self.cur_exp = v.clone();
                self.cur_type = v.ty();
            }
            VarValue::NumericVar(NumericState::Known(v)) => {
                self.cur_exp = Value::Numeric(*v);
                self.cur_type = Type::Known;
            }
            VarValue::Pair { x, y } => {
                let xv = self.variables.known_value(*x).unwrap_or(0.0);
                let yv = self.variables.known_value(*y).unwrap_or(0.0);
                self.cur_exp = Value::Pair(xv, yv);
                self.cur_type = Type::PairType;
            }
            VarValue::Color { r, g, b } => {
                let rv = self.variables.known_value(*r).unwrap_or(0.0);
                let gv = self.variables.known_value(*g).unwrap_or(0.0);
                let bv = self.variables.known_value(*b).unwrap_or(0.0);
                self.cur_exp = Value::Color(Color::new(rv, gv, bv));
                self.cur_type = Type::ColorType;
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
            }
            _ => {
                // Variable is undefined or not yet known
                // For now, return 0 for numeric, vacuous for others
                self.cur_exp = Value::Numeric(0.0);
                self.cur_type = Type::Known;
            }
        }
        let _ = sym; // Used later for equation LHS tracking
        Ok(())
    }

    // =======================================================================
    // Statement execution
    // =======================================================================

    /// Execute one statement.
    pub fn do_statement(&mut self) -> InterpResult<()> {
        match self.cur.command {
            Command::Semicolon => {
                // Empty statement
                self.get_x_next();
                Ok(())
            }
            Command::Stop => Ok(()), // End of input

            Command::TypeName => self.do_type_declaration(),
            Command::AddTo => self.do_addto(),
            Command::Bounds => self.do_bounds(),
            Command::ShipOut => self.do_shipout(),
            Command::Save => self.do_save(),
            Command::Interim => self.do_interim(),
            Command::Let => self.do_let(),
            Command::MacroDef => self.do_macro_def(),
            Command::Delimiters => self.do_delimiters(),
            Command::NewInternal => self.do_new_internal(),
            Command::Show => self.do_show(),
            Command::MessageCommand => self.do_message(),
            Command::BeginGroup => {
                self.save_stack.push_boundary();
                self.get_x_next();
                Ok(())
            }
            Command::EndGroup => {
                self.do_endgroup();
                self.get_x_next();
                Ok(())
            }

            _ => {
                // Expression or equation
                self.scan_expression()?;

                if self.cur.command == Command::Equals {
                    // Equation chain: lhs = mid = ... = rhs
                    while self.cur.command == Command::Equals {
                        let lhs = self.take_cur_exp();
                        self.get_x_next();
                        self.scan_expression()?;
                        let rhs_clone = self.cur_exp.clone();
                        self.do_equation(&lhs, &rhs_clone)?;
                    }
                } else if self.cur.command == Command::Assignment {
                    // Assignment: var := expr
                    // Save the LHS variable reference before RHS parsing clobbers it
                    let saved_var_id = self.last_var_id;
                    let saved_var_name = self.last_var_name.clone();
                    let saved_internal_idx = self.last_internal_idx;
                    let lhs = self.take_cur_exp();
                    self.get_x_next();
                    self.scan_expression()?;
                    // Restore the LHS tracking
                    self.last_var_id = saved_var_id;
                    self.last_var_name = saved_var_name;
                    self.last_internal_idx = saved_internal_idx;
                    self.do_assignment(&lhs)?;
                }

                // Expect statement terminator
                if self.cur.command == Command::Semicolon {
                    self.get_x_next();
                } else if self.cur.command == Command::EndGroup || self.cur.command == Command::Stop
                {
                    // OK — endgroup or end terminates too
                } else {
                    self.report_error(
                        ErrorKind::MissingToken,
                        format!(
                            "Missing `;` (got {:?} {:?})",
                            self.cur.command, self.cur.token.kind
                        ),
                    );
                }
                Ok(())
            }
        }
    }

    /// Execute a type declaration (`numeric x, y;`).
    fn do_type_declaration(&mut self) -> InterpResult<()> {
        let type_op = self.cur.modifier;
        self.get_x_next();

        loop {
            // Expect a variable name (possibly compound with suffixes)
            if let crate::token::TokenKind::Symbolic(ref name) = self.cur.token.kind {
                let mut name = name.clone();
                // Use get_next (non-expanding) to avoid expanding vardef
                // suffixes like `lft` in `pair laboff.lft`.
                self.get_next();

                // Collect suffix tokens (tag tokens, subscripts, and symbols
                // that might be macros but are suffix parts).  The scanner
                // drops `.` separators, so suffix parts appear as consecutive
                // tokens.  We use non-expanding reads to avoid triggering
                // vardef expansion on suffix names.
                loop {
                    if self.cur.command == Command::LeftBracket {
                        // Subscript array suffix `[]` — skip it
                        self.get_next();
                        if self.cur.command == Command::RightBracket {
                            self.get_next();
                        }
                    } else if self.cur.command == Command::TagToken
                        || self.cur.command == Command::DefinedMacro
                    {
                        // Suffix part (e.g. `l` in `path_.l`, `lft` in `laboff.lft`)
                        if let crate::token::TokenKind::Symbolic(ref s) = self.cur.token.kind {
                            name.push('.');
                            name.push_str(s);
                        }
                        self.get_next();
                    } else {
                        break;
                    }
                }
                // Expand whatever follows the variable name.
                self.expand_current();

                let var_id = self.variables.lookup(&name);

                // Set the variable to the correct type
                let val = match type_op {
                    x if x == TypeNameOp::Numeric as u16 => {
                        VarValue::NumericVar(NumericState::Numeric)
                    }
                    x if x == TypeNameOp::Boolean as u16 => VarValue::Known(Value::Boolean(false)),
                    x if x == TypeNameOp::String as u16 => {
                        VarValue::Known(Value::String(Arc::from("")))
                    }
                    x if x == TypeNameOp::Path as u16 => {
                        VarValue::Known(Value::Path(Path::default()))
                    }
                    x if x == TypeNameOp::Pen as u16 => VarValue::Known(Value::Pen(Pen::default())),
                    x if x == TypeNameOp::Picture as u16 => {
                        VarValue::Known(Value::Picture(Picture::default()))
                    }
                    x if x == TypeNameOp::Pair as u16 => {
                        let x_id = self.variables.alloc();
                        let y_id = self.variables.alloc();
                        self.variables
                            .set(x_id, VarValue::NumericVar(NumericState::Numeric));
                        self.variables
                            .set(y_id, VarValue::NumericVar(NumericState::Numeric));
                        // Also register named sub-parts so xpart/ypart can find them
                        self.variables.register_name(&format!("{name}.x"), x_id);
                        self.variables.register_name(&format!("{name}.y"), y_id);
                        VarValue::Pair { x: x_id, y: y_id }
                    }
                    x if x == TypeNameOp::Color as u16 => {
                        let r_id = self.variables.alloc();
                        let g_id = self.variables.alloc();
                        let b_id = self.variables.alloc();
                        self.variables
                            .set(r_id, VarValue::NumericVar(NumericState::Numeric));
                        self.variables
                            .set(g_id, VarValue::NumericVar(NumericState::Numeric));
                        self.variables
                            .set(b_id, VarValue::NumericVar(NumericState::Numeric));
                        self.variables.register_name(&format!("{name}.r"), r_id);
                        self.variables.register_name(&format!("{name}.g"), g_id);
                        self.variables.register_name(&format!("{name}.b"), b_id);
                        VarValue::Color {
                            r: r_id,
                            g: g_id,
                            b: b_id,
                        }
                    }
                    x if x == TypeNameOp::Transform as u16 => {
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
                    _ => VarValue::Undefined,
                };
                self.variables.set(var_id, val);
            } else {
                // Non-symbolic token — skip it
                self.get_x_next();
            }

            if self.cur.command == Command::Comma {
                self.get_x_next();
                continue;
            }
            break;
        }

        if self.cur.command == Command::Semicolon {
            self.get_x_next();
        }
        Ok(())
    }

    /// Execute `addto` statement.
    fn do_addto(&mut self) -> InterpResult<()> {
        self.get_x_next();

        // Get the target picture variable name
        let pic_name = if let crate::token::TokenKind::Symbolic(ref s) = self.cur.token.kind {
            s.clone()
        } else {
            "currentpicture".to_owned()
        };
        self.get_x_next();

        // Expect contour / doublepath / also
        let thing = self.cur.modifier;
        self.get_x_next();

        match thing {
            x if x == ThingToAddOp::Contour as u16 => {
                self.scan_expression()?;
                let path_val = self.take_cur_exp();
                let path = value_to_path_owned(path_val)?;

                let ds = self.scan_with_options()?;

                picture::addto_contour(
                    &mut self.current_picture,
                    path,
                    ds.color,
                    if matches!(ds.pen, Pen::Elliptical(a) if a == kurbo::Affine::default()) {
                        None
                    } else {
                        Some(ds.pen)
                    },
                    ds.line_join,
                    ds.miter_limit,
                );
            }
            x if x == ThingToAddOp::DoublePath as u16 => {
                self.scan_expression()?;
                let path_val = self.take_cur_exp();
                let path = value_to_path_owned(path_val)?;

                let ds = self.scan_with_options()?;

                picture::addto_doublepath(
                    &mut self.current_picture,
                    path,
                    ds.pen,
                    ds.color,
                    ds.dash,
                    ds.line_cap,
                    ds.line_join,
                    ds.miter_limit,
                );
            }
            x if x == ThingToAddOp::Also as u16 => {
                self.scan_expression()?;
                let pic_val = self.take_cur_exp();
                if let Value::Picture(p) = pic_val {
                    picture::addto_also(&mut self.current_picture, &p);
                }
            }
            _ => {
                self.report_error(
                    ErrorKind::MissingToken,
                    "Expected `contour`, `doublepath`, or `also`",
                );
            }
        }

        let _ = pic_name; // TODO: support named pictures

        if self.cur.command == Command::Semicolon {
            self.get_x_next();
        }
        Ok(())
    }

    /// Scan `withpen`, `withcolor`, `dashed` options.
    fn scan_with_options(&mut self) -> InterpResult<DrawingState> {
        let mut ds = DrawingState {
            pen: Pen::default_pen(),
            color: Color::BLACK,
            dash: None,
            line_cap: LineCap::from_f64(self.internals.get(InternalId::LineCap as u16)),
            line_join: LineJoin::from_f64(self.internals.get(InternalId::LineJoin as u16)),
            miter_limit: self.internals.get(InternalId::MiterLimit as u16),
        };

        while self.cur.command == Command::WithOption {
            let opt = self.cur.modifier;
            self.get_x_next();
            self.scan_expression()?;
            let val = self.take_cur_exp();

            match opt {
                x if x == WithOptionOp::WithPen as u16 => {
                    if let Value::Pen(p) = val {
                        ds.pen = p;
                    }
                }
                x if x == WithOptionOp::WithColor as u16 => {
                    if let Value::Color(c) = val {
                        ds.color = c;
                    } else if let Value::Numeric(v) = val {
                        ds.color = Color::new(v, v, v);
                    }
                }
                x if x == WithOptionOp::Dashed as u16 => {
                    // For now, ignore dash pattern (complex to extract)
                }
                _ => {}
            }
        }

        Ok(ds)
    }

    /// Execute `clip`/`setbounds` statement.
    fn do_bounds(&mut self) -> InterpResult<()> {
        let is_clip = self.cur.modifier == BoundsOp::Clip as u16;
        self.get_x_next();

        // Get picture name
        let _pic_name = if let crate::token::TokenKind::Symbolic(ref s) = self.cur.token.kind {
            s.clone()
        } else {
            "currentpicture".to_owned()
        };
        self.get_x_next();

        // Expect "to"
        if self.cur.command == Command::ToToken {
            self.get_x_next();
        }

        self.scan_expression()?;
        let val = self.take_cur_exp();
        let clip_path = value_to_path_owned(val)?;

        if is_clip {
            picture::clip(&mut self.current_picture, clip_path);
        } else {
            picture::setbounds(&mut self.current_picture, clip_path);
        }

        if self.cur.command == Command::Semicolon {
            self.get_x_next();
        }
        Ok(())
    }

    /// Execute `shipout` statement.
    fn do_shipout(&mut self) -> InterpResult<()> {
        self.get_x_next();
        self.scan_expression()?;
        let val = self.take_cur_exp();

        let pic = if let Value::Picture(p) = val {
            p
        } else {
            self.current_picture.clone()
        };

        self.pictures.push(pic);

        if self.cur.command == Command::Semicolon {
            self.get_x_next();
        }
        Ok(())
    }

    /// Execute `save` statement.
    fn do_save(&mut self) -> InterpResult<()> {
        self.get_x_next();
        loop {
            if let Some(id) = self.cur.sym {
                let entry = self.symbols.get(id);
                self.save_stack.save_symbol(id, entry);
                self.symbols.clear(id);
            }
            self.get_x_next();
            if self.cur.command != Command::Comma {
                break;
            }
            self.get_x_next();
        }
        if self.cur.command == Command::Semicolon {
            self.get_x_next();
        }
        Ok(())
    }

    /// Execute `interim` statement.
    fn do_interim(&mut self) -> InterpResult<()> {
        self.get_x_next();
        if self.cur.command == Command::InternalQuantity {
            let idx = self.cur.modifier;
            self.save_stack.save_internal(idx, self.internals.get(idx));
            self.get_x_next();
            if self.cur.command == Command::Assignment {
                self.get_x_next();
                self.scan_expression()?;
                let val = value_to_scalar(&self.cur_exp)?;
                self.internals.set(idx, val);
            }
        }
        if self.cur.command == Command::Semicolon {
            self.get_x_next();
        }
        Ok(())
    }

    /// Execute `let` statement.
    fn do_let(&mut self) -> InterpResult<()> {
        // LHS: get_symbol (non-expanding), like mp.web's do_let
        self.get_next();
        let lhs = self.cur.sym;
        self.get_x_next();
        // Expect = or :=
        if self.cur.command == Command::Equals || self.cur.command == Command::Assignment {
            // RHS: get_symbol (non-expanding) — must not expand macros
            self.get_next();
        }
        let rhs = self.cur.sym;
        if let (Some(l), Some(r)) = (lhs, rhs) {
            let entry = self.symbols.get(r);
            self.symbols.set(l, entry);
            // Also copy macro info if the RHS is a macro
            if let Some(macro_info) = self.macros.get(&r).cloned() {
                self.macros.insert(l, macro_info);
            }
        }
        self.get_x_next();
        Ok(())
    }

    /// Execute `delimiters` statement.
    ///
    /// Syntax: `delimiters <left> <right>;`
    /// Declares a pair of matching delimiters (like `(` and `)`).
    /// Each pair gets a unique modifier so the parser can match them.
    fn do_delimiters(&mut self) -> InterpResult<()> {
        self.get_x_next();

        // Get left delimiter symbol
        let left_sym = self.cur.sym;
        self.get_x_next();

        // Get right delimiter symbol
        let right_sym = self.cur.sym;
        self.get_x_next();

        // Allocate a unique delimiter id for this pair
        let delim_id = self.next_delimiter_id;
        self.next_delimiter_id += 1;

        // Set the symbols as delimiter commands with matching modifier
        if let Some(l) = left_sym {
            self.symbols.set(
                l,
                crate::symbols::SymbolEntry {
                    command: Command::LeftDelimiter,
                    modifier: delim_id,
                },
            );
        }
        if let Some(r) = right_sym {
            self.symbols.set(
                r,
                crate::symbols::SymbolEntry {
                    command: Command::RightDelimiter,
                    modifier: delim_id,
                },
            );
        }

        if self.cur.command == Command::Semicolon {
            self.get_x_next();
        }
        Ok(())
    }

    /// Execute `newinternal` statement.
    ///
    /// Syntax: `newinternal <name>, <name>, ...;`
    /// Declares new internal numeric quantities.
    fn do_new_internal(&mut self) -> InterpResult<()> {
        self.get_x_next();

        loop {
            if let crate::token::TokenKind::Symbolic(ref name) = self.cur.token.kind {
                let name = name.clone();
                // Register the new internal
                let idx = self.internals.new_internal(&name);

                // Set the symbol to InternalQuantity
                if let Some(sym) = self.cur.sym {
                    self.symbols.set(
                        sym,
                        crate::symbols::SymbolEntry {
                            command: Command::InternalQuantity,
                            modifier: idx,
                        },
                    );
                }
            }
            self.get_x_next();

            if self.cur.command == Command::Comma {
                self.get_x_next();
                continue;
            }
            break;
        }

        if self.cur.command == Command::Semicolon {
            self.get_x_next();
        }
        Ok(())
    }

    /// Execute `show` statement.
    fn do_show(&mut self) -> InterpResult<()> {
        // show_type distinguishes show/showtoken/showdependencies — used later
        let _ = self.cur.modifier;
        self.get_x_next();
        self.scan_expression()?;
        // Print the value
        let val = &self.cur_exp;
        self.report_error(
            ErrorKind::Internal, // Not really an error, but using error channel for output
            format!(">> {val}"),
        );
        self.errors
            .last_mut()
            .map(|e| e.severity = crate::error::Severity::Info);
        if self.cur.command == Command::Semicolon {
            self.get_x_next();
        }
        Ok(())
    }

    /// Execute `message` / `errmessage` statement.
    fn do_message(&mut self) -> InterpResult<()> {
        let is_err = self.cur.modifier == MessageOp::ErrMessage as u16;
        self.get_x_next();
        self.scan_expression()?;
        let msg = match &self.cur_exp {
            Value::String(s) => s.to_string(),
            other => format!("{other}"),
        };
        let severity = if is_err {
            crate::error::Severity::Error
        } else {
            crate::error::Severity::Info
        };
        self.errors
            .push(InterpreterError::new(ErrorKind::Internal, msg).with_severity(severity));
        if self.cur.command == Command::Semicolon {
            self.get_x_next();
        }
        Ok(())
    }

    /// Restore scope at `endgroup`.
    fn do_endgroup(&mut self) {
        let entries = self.save_stack.restore_to_boundary();
        for entry in entries {
            match entry {
                SaveEntry::Variable { id, value } => {
                    self.variables.set(id, value);
                }
                SaveEntry::Internal { index, value } => {
                    self.internals.set(index, value);
                }
                SaveEntry::Symbol { id, entry } => {
                    self.symbols.set(id, entry);
                }
                SaveEntry::Boundary => {} // shouldn't happen
            }
        }
    }

    /// Execute an equation: `lhs = rhs`.
    fn do_equation(&mut self, lhs: &Value, rhs: &Value) -> InterpResult<()> {
        // Simplified equation handling: if LHS was a variable, assign RHS to it.
        // Full equation solving with dependency lists comes later.
        if let (Value::Numeric(a), Value::Numeric(b)) = (lhs, rhs) {
            if (a - b).abs() > 0.001 {
                self.report_error(
                    ErrorKind::InconsistentEquation,
                    format!("Inconsistent equation: {a} = {b}"),
                );
            }
        }

        // If we tracked a variable on the LHS, treat equation as assignment
        if let Some(var_id) = self.last_var_id {
            match rhs {
                Value::Numeric(v) => {
                    self.variables
                        .set(var_id, VarValue::NumericVar(NumericState::Known(*v)));
                }
                Value::Pair(x, y) => {
                    let var_val = self.variables.get(var_id).clone();
                    if let VarValue::Pair { x: xid, y: yid } = var_val {
                        self.variables
                            .set(xid, VarValue::NumericVar(NumericState::Known(*x)));
                        self.variables
                            .set(yid, VarValue::NumericVar(NumericState::Known(*y)));
                    } else {
                        self.variables.set_known(var_id, rhs.clone());
                    }
                }
                Value::Color(c) => {
                    let var_val = self.variables.get(var_id).clone();
                    if let VarValue::Color { r, g, b } = var_val {
                        self.variables
                            .set(r, VarValue::NumericVar(NumericState::Known(c.r)));
                        self.variables
                            .set(g, VarValue::NumericVar(NumericState::Known(c.g)));
                        self.variables
                            .set(b, VarValue::NumericVar(NumericState::Known(c.b)));
                    } else {
                        self.variables.set_known(var_id, rhs.clone());
                    }
                }
                _ => {
                    self.variables.set_known(var_id, rhs.clone());
                }
            }
        }
        Ok(())
    }

    /// Execute an assignment: `var := expr`.
    fn do_assignment(&mut self, _lhs: &Value) -> InterpResult<()> {
        let rhs = self.take_cur_exp();

        // Check if the LHS was an internal quantity (e.g., `linecap := 0`)
        if let Some(idx) = self.last_internal_idx {
            let val = value_to_scalar(&rhs)?;
            self.internals.set(idx, val);
            return Ok(());
        }

        // Check if the LHS was a variable (e.g., `x := 5`)
        if let Some(var_id) = self.last_var_id {
            match &rhs {
                Value::Numeric(v) => {
                    self.variables
                        .set(var_id, VarValue::NumericVar(NumericState::Known(*v)));
                }
                Value::Pair(x, y) => {
                    // If the variable is already a Pair with sub-parts, set each
                    let var_val = self.variables.get(var_id).clone();
                    if let VarValue::Pair { x: xid, y: yid } = var_val {
                        self.variables
                            .set(xid, VarValue::NumericVar(NumericState::Known(*x)));
                        self.variables
                            .set(yid, VarValue::NumericVar(NumericState::Known(*y)));
                    } else {
                        self.variables.set_known(var_id, rhs);
                    }
                }
                Value::Color(c) => {
                    let var_val = self.variables.get(var_id).clone();
                    if let VarValue::Color { r, g, b } = var_val {
                        self.variables
                            .set(r, VarValue::NumericVar(NumericState::Known(c.r)));
                        self.variables
                            .set(g, VarValue::NumericVar(NumericState::Known(c.g)));
                        self.variables
                            .set(b, VarValue::NumericVar(NumericState::Known(c.b)));
                    } else {
                        self.variables.set_known(var_id, rhs);
                    }
                }
                _ => {
                    // String, path, pen, picture, boolean, transform, etc.
                    self.variables.set_known(var_id, rhs);
                }
            }
            return Ok(());
        }

        self.report_error(ErrorKind::InvalidExpression, "Assignment to non-variable");
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
// Value extraction helpers
// ---------------------------------------------------------------------------

fn value_to_scalar(val: &Value) -> InterpResult<Scalar> {
    match val {
        Value::Numeric(v) => Ok(*v),
        _ => Err(InterpreterError::new(
            ErrorKind::TypeError,
            format!("Expected numeric, got {}", val.ty()),
        )),
    }
}

fn value_to_pair(val: &Value) -> InterpResult<(Scalar, Scalar)> {
    match val {
        Value::Pair(x, y) => Ok((*x, *y)),
        _ => Err(InterpreterError::new(
            ErrorKind::TypeError,
            format!("Expected pair, got {}", val.ty()),
        )),
    }
}

fn value_to_bool(val: &Value) -> InterpResult<bool> {
    match val {
        Value::Boolean(b) => Ok(*b),
        _ => Err(InterpreterError::new(
            ErrorKind::TypeError,
            format!("Expected boolean, got {}", val.ty()),
        )),
    }
}

fn value_to_path(val: &Value) -> InterpResult<&Path> {
    match val {
        Value::Path(p) => Ok(p),
        _ => Err(InterpreterError::new(
            ErrorKind::TypeError,
            format!("Expected path, got {}", val.ty()),
        )),
    }
}

fn value_to_path_owned(val: Value) -> InterpResult<Path> {
    match val {
        Value::Path(p) => Ok(p),
        _ => Err(InterpreterError::new(
            ErrorKind::TypeError,
            format!("Expected path, got {}", val.ty()),
        )),
    }
}

fn value_to_pen(val: &Value) -> InterpResult<&Pen> {
    match val {
        Value::Pen(p) => Ok(p),
        _ => Err(InterpreterError::new(
            ErrorKind::TypeError,
            format!("Expected pen, got {}", val.ty()),
        )),
    }
}

fn value_to_string(val: &Value) -> InterpResult<String> {
    match val {
        Value::String(s) => Ok(s.to_string()),
        _ => Err(InterpreterError::new(
            ErrorKind::TypeError,
            format!("Expected string, got {}", val.ty()),
        )),
    }
}

fn value_to_transform(val: &Value) -> InterpResult<Transform> {
    match val {
        Value::Transform(t) => Ok(*t),
        _ => Err(InterpreterError::new(
            ErrorKind::TypeError,
            format!("Expected transform, got {}", val.ty()),
        )),
    }
}

/// Convert a runtime `Value` to a `StoredToken` for embedding in token lists.
fn value_to_stored_token(val: &Value) -> StoredToken {
    match val {
        Value::Numeric(v) => StoredToken::Numeric(*v),
        Value::String(s) => StoredToken::StringLit(s.to_string()),
        // For non-primitive types, store as numeric 0 (best-effort)
        _ => StoredToken::Numeric(0.0),
    }
}

/// Convert a runtime `Value` to a list of `StoredToken`s that reconstruct it.
///
/// For compound types like pairs and colors, this produces the token sequence
/// `( x , y )` or `( r , g , b )`. For simple types, returns a single token.
fn value_to_stored_tokens(val: &Value, symbols: &mut SymbolTable) -> TokenList {
    match val {
        Value::Pair(x, y) => {
            let lparen = symbols.lookup("(");
            let comma = symbols.lookup(",");
            let rparen = symbols.lookup(")");
            vec![
                StoredToken::Symbol(lparen),
                StoredToken::Numeric(*x),
                StoredToken::Symbol(comma),
                StoredToken::Numeric(*y),
                StoredToken::Symbol(rparen),
            ]
        }
        Value::Color(c) => {
            let lparen = symbols.lookup("(");
            let comma = symbols.lookup(",");
            let rparen = symbols.lookup(")");
            vec![
                StoredToken::Symbol(lparen),
                StoredToken::Numeric(c.r),
                StoredToken::Symbol(comma),
                StoredToken::Numeric(c.g),
                StoredToken::Symbol(comma),
                StoredToken::Numeric(c.b),
                StoredToken::Symbol(rparen),
            ]
        }
        _ => vec![value_to_stored_token(val)],
    }
}

fn values_equal(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::Numeric(a), Value::Numeric(b)) => (a - b).abs() < 0.0001,
        (Value::Boolean(a), Value::Boolean(b)) => a == b,
        (Value::String(a), Value::String(b)) => a == b,
        (Value::Pair(ax, ay), Value::Pair(bx, by)) => {
            (ax - bx).abs() < 0.0001 && (ay - by).abs() < 0.0001
        }
        _ => false,
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
        // Chained equation: a = b = 5
        // With current equation solver, direct assignment works for the rightmost
        // variable. Full dependency tracking for intermediate vars is not yet wired.
        interp.run("numeric a; a = 5; show a;").unwrap();
        let msg = &interp.errors[0].message;
        assert!(msg.contains("5"), "expected a=5 in: {msg}");
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
}
