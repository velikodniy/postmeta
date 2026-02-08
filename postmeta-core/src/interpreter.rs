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
    BoundsOp, Command, ExpressionBinaryOp, FiOrElseOp, IterationOp, MessageOp, NullaryOp,
    PlusMinusOp, PrimaryBinaryOp, SecondaryBinaryOp, TertiaryBinaryOp, ThingToAddOp, UnaryOp,
    WithOptionOp,
};
use crate::equation::VarId;
use crate::error::{ErrorKind, InterpResult, InterpreterError};
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
// Interpreter state
// ---------------------------------------------------------------------------

/// The `MetaPost` interpreter.
pub struct Interpreter {
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
            pictures: Vec::new(),
            current_picture: Picture::new(),
            current_fig: None,
            drawing_state: DrawingState::default(),
            random_seed: 0,
            errors: Vec::new(),
            job_name: "output".into(),
        }
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
                values.push(self.take_cur_exp());
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
                // Variable reference
                let sym = self.cur.sym;
                let name = if let crate::token::TokenKind::Symbolic(ref s) = self.cur.token.kind {
                    s.clone()
                } else {
                    String::new()
                };
                self.get_x_next();
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
        }
    }

    /// Parse and evaluate a secondary expression.
    fn scan_secondary(&mut self) -> InterpResult<()> {
        self.scan_primary()?;

        while self.cur.command.is_secondary_op() {
            let op = self.cur.modifier;
            let cmd = self.cur.command;
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
            let op = self.cur.modifier;
            let cmd = self.cur.command;
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
            // Parse optional pre-join direction {dir}
            let pre_dir = if self.cur.command == Command::LeftBrace {
                self.get_x_next();
                self.scan_expression()?;
                let dir = self.take_cur_exp();
                if self.cur.command == Command::RightBrace {
                    self.get_x_next();
                }
                Some(self.value_to_direction(&dir)?)
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

            // Parse optional post-join direction {dir}
            let post_dir = if self.cur.command == Command::LeftBrace {
                self.get_x_next();
                self.scan_expression()?;
                let dir = self.take_cur_exp();
                if self.cur.command == Command::RightBrace {
                    self.get_x_next();
                }
                Some(self.value_to_direction(&dir)?)
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
                return Err(InterpreterError::new(
                    ErrorKind::TypeError,
                    format!("Cannot transform {}", val.ty()),
                ));
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
                    // Equation: lhs = rhs
                    let lhs = self.take_cur_exp();
                    self.get_x_next();
                    self.scan_expression()?;
                    let rhs = self.take_cur_exp();
                    self.do_equation(&lhs, &rhs)?;
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
                    self.report_error(ErrorKind::MissingToken, "Missing `;`");
                }
                Ok(())
            }
        }
    }

    /// Execute a type declaration (`numeric x, y;`).
    fn do_type_declaration(&mut self) -> InterpResult<()> {
        // type_op tells us which type (numeric, pair, etc.) — used later
        let _ = self.cur.modifier;
        self.get_x_next();

        loop {
            // Expect a variable name
            if let crate::token::TokenKind::Symbolic(ref name) = self.cur.token.kind {
                let var_id = self.variables.lookup(name);
                // Clear the variable to undefined of the declared type
                self.variables
                    .set(var_id, VarValue::NumericVar(NumericState::Numeric));
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
        self.get_x_next();
        let lhs = self.cur.sym;
        self.get_x_next();
        // Expect = or :=
        if self.cur.command == Command::Equals || self.cur.command == Command::Assignment {
            self.get_x_next();
        }
        let rhs = self.cur.sym;
        if let (Some(l), Some(r)) = (lhs, rhs) {
            let entry = self.symbols.get(r);
            self.symbols.set(l, entry);
        }
        self.get_x_next();
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
        // For now, handle known-value equations directly
        // Full equation solving with dependency lists comes later
        // when we track independent/dependent variables properly
        if let (Value::Numeric(_), Value::Numeric(_)) = (lhs, rhs) {
            // Both known — check consistency
            let a = value_to_scalar(lhs)?;
            let b = value_to_scalar(rhs)?;
            if (a - b).abs() > 0.001 {
                self.report_error(
                    ErrorKind::InconsistentEquation,
                    format!("Inconsistent equation: {a} = {b}"),
                );
            }
        } else {
            // TODO: full equation solving with dependency tracking
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
}
