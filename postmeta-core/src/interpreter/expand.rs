//! Macro expansion, conditionals, and loops.
//!
//! This module handles all expandable commands: `if`/`elseif`/`else`/`fi`,
//! `for`/`forsuffixes`/`forever`/`endfor`/`exitif`, macro definitions
//! (`def`/`vardef`/`primarydef`/`secondarydef`/`tertiarydef`), macro
//! expansion, `input`, and `scantokens`.

use crate::command::{Command, FiOrElseOp, IterationOp, MacroDefOp, MacroSpecialOp, ParamTypeOp};
use crate::error::{ErrorKind, InterpResult, InterpreterError};
use crate::input::{StoredToken, TokenList};
use crate::symbols::SymbolId;
use crate::types::Value;

use super::helpers::value_to_stored_tokens;
use super::{ExprResultValue, Interpreter};

// ---------------------------------------------------------------------------
// Conditional state
// ---------------------------------------------------------------------------

/// State of one level in the `if/elseif/else/fi` nesting stack.
#[derive(Debug, Clone, Copy)]
pub(super) enum IfState {
    /// We are currently executing the active branch.
    Active,
    /// A branch was already taken; skip remaining branches.
    Done,
    /// We are skipping tokens looking for `elseif`/`else`/`fi`.
    Skipping,
}

/// Groups all conditional and loop control state.
///
/// Extracted from `Interpreter` to reduce the top-level field count.
/// Only accessed by the expansion code in this module.
#[derive(Debug, Clone)]
pub(super) struct ForeverLoopFrame {
    /// Loop body tokens replayed by `RepeatLoop`.
    pub body: TokenList,
    /// Set by `exitif` to stop replaying this frame.
    pub exit_requested: bool,
}

#[derive(Debug)]
pub(super) struct ControlFlow {
    /// If-stack depth tracking for nested conditionals.
    pub if_stack: Vec<IfState>,
    /// Active `forever` loop frames (outer -> inner).
    pub forever_stack: Vec<ForeverLoopFrame>,
}

impl ControlFlow {
    pub const fn new() -> Self {
        Self {
            if_stack: Vec::new(),
            forever_stack: Vec::new(),
        }
    }
}

// ---------------------------------------------------------------------------
// Macro definitions
// ---------------------------------------------------------------------------

/// The type of a macro parameter.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum ParamType {
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
    pub(super) const fn is_undelimited(self) -> bool {
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
pub(super) struct MacroInfo {
    /// Parameter types in order.
    pub(super) params: Vec<ParamType>,
    /// Delimited parameter group for each parameter.
    /// `u16::MAX` means the parameter is undelimited.
    pub(super) param_groups: Vec<u16>,
    /// The macro body as a token list.
    pub(super) body: TokenList,
    /// Whether this is a `vardef` (wraps body in begingroup/endgroup).
    pub(super) is_vardef: bool,
    /// Whether this vardef has an `@#` suffix parameter.
    /// When true, the LAST entry in `params` is `UndelimitedSuffix` and
    /// corresponds to the `@#` suffix that appears between the macro name
    /// and the argument list.
    pub(super) has_at_suffix: bool,
}

impl Interpreter {
    /// Expand any expandable tokens at the current position.
    ///
    /// After this, `self.cur` holds a non-expandable token.
    pub(super) fn expand_current(&mut self) {
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
                Command::StartTex => self.expand_start_tex(),
                Command::ExpandAfter => self.expand_expandafter(),
                Command::Relax => {
                    self.get_next();
                    self.expand_current();
                }
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
        self.lhs_tracking.equals_means_equation = false;
        let condition = match self.scan_expression() {
            Ok(result) => match result.exp {
                Value::Boolean(b) => b,
                Value::Numeric(v) => v != 0.0,
                _ => {
                    self.report_error(ErrorKind::TypeError, "if condition must be boolean");
                    false
                }
            },
            Err(err) => {
                self.errors.push(err);
                false
            }
        };

        // Expect `:` after the condition
        if self.cur.command == Command::Colon {
            self.get_next(); // consume the colon
        }

        if condition {
            self.control_flow.if_stack.push(IfState::Active);
            // `cur` is now the first token of the true branch — expand it
            self.expand_current();
        } else {
            self.control_flow.if_stack.push(IfState::Skipping);
            // Skip tokens until else/elseif/fi. On return, `cur` is set.
            self.skip_to_fi_or_else();
        }
    }

    /// Handle `fi`, `else`, `elseif` encountered during active execution.
    ///
    /// On return, `self.cur` is the next non-expandable token.
    fn expand_fi_or_else(&mut self) {
        let Some(modifier) = FiOrElseOp::from_modifier(self.cur.modifier) else {
            self.report_error(ErrorKind::UnexpectedToken, "Invalid fi/else modifier");
            self.get_next();
            self.expand_current();
            return;
        };

        if modifier == FiOrElseOp::Fi {
            // End of conditional
            self.control_flow.if_stack.pop();
            self.get_next();
            self.expand_current();
        } else if modifier == FiOrElseOp::Else || modifier == FiOrElseOp::ElseIf {
            // Active branch done — skip remaining branches to `fi`.
            if let Some(state) = self.control_flow.if_stack.last_mut() {
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
                    if FiOrElseOp::from_modifier(self.cur.modifier) == Some(FiOrElseOp::Fi) {
                        depth -= 1;
                    }
                    self.get_next();
                }
                Command::FiOrElse if depth == 0 => {
                    let Some(modifier) = FiOrElseOp::from_modifier(self.cur.modifier) else {
                        self.report_error(ErrorKind::UnexpectedToken, "Invalid fi/else modifier");
                        self.get_next();
                        continue;
                    };

                    if modifier == FiOrElseOp::Fi {
                        self.control_flow.if_stack.pop();
                        self.get_next();
                        self.expand_current();
                        return;
                    } else if modifier == FiOrElseOp::Else {
                        if let Some(state) = self.control_flow.if_stack.last_mut() {
                            *state = IfState::Active;
                        }
                        self.get_next(); // consume `else`
                                         // consume the `:` after `else`
                        if self.cur.command == Command::Colon {
                            self.get_next();
                        }
                        self.expand_current();
                        return;
                    } else if modifier == FiOrElseOp::ElseIf {
                        self.control_flow.if_stack.pop();
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
                    if FiOrElseOp::from_modifier(self.cur.modifier) == Some(FiOrElseOp::Fi) {
                        if depth == 0 {
                            self.control_flow.if_stack.pop();
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
        let Some(op) = IterationOp::from_modifier(self.cur.modifier) else {
            self.report_error(ErrorKind::UnexpectedToken, "Invalid iteration modifier");
            self.get_next();
            self.expand_current();
            return;
        };

        if op == IterationOp::Forever {
            self.expand_forever();
            return;
        }

        let is_forsuffixes = op == IterationOp::ForSuffixes;

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
        let loop_var_sym = self.symbols.lookup(&loop_var_name);

        self.get_next(); // skip the variable name

        // Expect `=` or `:=` (MetaPost accepts both forms for the loop variable)
        if self.cur.command != Command::Equals && self.cur.command != Command::Assignment {
            self.report_error(ErrorKind::MissingToken, "Expected `=` after loop variable");
        }

        // Parse value list.  For `for` we evaluate expressions.
        // For `forsuffixes` we collect raw suffix tokens.
        let value_token_lists: Vec<TokenList> = if is_forsuffixes {
            self.scan_forsuffixes_value_list()
        } else {
            self.scan_loop_value_list()
                .into_iter()
                .map(|v| value_to_stored_tokens(&v, &mut self.symbols))
                .collect()
        };

        // Expect `:` after value list
        if self.cur.command == Command::Colon {
            self.get_next(); // consume the colon
        }

        // Scan the loop body, replacing occurrences of the loop variable
        // with `Param(0)`.  This mirrors how macro bodies substitute
        // parameter names, and ensures that `for`/`forsuffixes` work as
        // token-level substitution (mp.web §13694).
        let body = self.scan_loop_body_with_param(loop_var_sym);

        // Push iterations in reverse order so the first is on top.
        for val_tokens in value_token_lists.into_iter().rev() {
            let params = vec![val_tokens];
            self.input
                .push_token_list(body.clone(), params, "for-body".into());
        }

        // Get the first token and continue expanding
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

        // Push a new forever-loop frame. Nested forever loops are handled
        // by stack discipline, so each loop replays its own body.
        self.control_flow.forever_stack.push(ForeverLoopFrame {
            body: body.clone(),
            exit_requested: false,
        });

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
        if let Some((exit_requested, body)) = self
            .control_flow
            .forever_stack
            .last()
            .map(|frame| (frame.exit_requested, frame.body.clone()))
        {
            if exit_requested {
                // Exit was requested for this loop.
                self.control_flow.forever_stack.pop();
                self.get_next();
                self.expand_current();
                return;
            }

            // Re-push the body for the next iteration.
            let repeat_sym = self.state.symbols.lookup("__repeat_loop__");
            let mut iteration = body;
            iteration.push(StoredToken::Symbol(repeat_sym));
            self.state
                .input
                .push_token_list(iteration, Vec::new(), "forever-body".into());
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
            if let Ok(first_result) = self.scan_expression() {
                let first_val = first_result.exp;

                // Check for `step <step> until <end>` after the first value
                if self.cur.command == Command::StepToken {
                    if let Ok(start) = super::helpers::value_to_scalar(&first_val) {
                        self.get_x_next();
                        if let Ok(step_result) = self.scan_expression() {
                            let step_val = step_result.exp;
                            if let Ok(step) = super::helpers::value_to_scalar(&step_val) {
                                // Expect `until`
                                if self.cur.command == Command::UntilToken {
                                    self.get_x_next();
                                    if let Ok(end_result) = self.scan_expression() {
                                        let end_val = end_result.exp;
                                        if let Ok(end) = super::helpers::value_to_scalar(&end_val) {
                                            // Generate the range
                                            Self::generate_step_range(
                                                start,
                                                step,
                                                end,
                                                &mut values,
                                            );
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
    ///
    /// Uses index-based computation (`start + i * step`) to avoid accumulating
    /// floating-point drift.  The endpoint is inclusive when the overshoot is
    /// within a small relative/absolute tolerance, matching `MetaPost` semantics.
    fn generate_step_range(start: f64, step: f64, end: f64, values: &mut Vec<Value>) {
        const MAX_ITERATIONS: usize = 10_000;

        if step.abs() < f64::EPSILON {
            return;
        }
        // Wrong direction: positive step with end < start (or vice versa)
        if (step > 0.0 && start > end + f64::EPSILON) || (step < 0.0 && start < end - f64::EPSILON)
        {
            return;
        }
        // Small tolerance so the endpoint is included despite float rounding
        let endpoint_slack = f64::EPSILON * end.abs().max(1.0);
        for i in 0..MAX_ITERATIONS {
            #[allow(clippy::cast_precision_loss)]
            let v = step.mul_add(i as f64, start);
            let past_end = if step > 0.0 {
                v > end + endpoint_slack
            } else {
                v < end - endpoint_slack
            };
            if past_end {
                break;
            }
            values.push(Value::Numeric(v));
        }
    }

    /// Scan a loop body (tokens until `endfor`), handling nested for/endfor.
    ///
    /// Returns the body as a `TokenList`.
    fn scan_loop_body(&mut self) -> TokenList {
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
                Command::MacroSpecial
                    if MacroSpecialOp::from_modifier(self.cur.modifier)
                        == Some(MacroSpecialOp::EndFor) =>
                {
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

    /// Scan a loop body, replacing the loop variable symbol with `Param(0)`.
    ///
    /// This mirrors macro body scanning: every occurrence of the loop
    /// variable is replaced with a `StoredToken::Param(0)` so that the
    /// input system performs token-level substitution at each iteration
    /// (mp.web §13694).  Nested `for`/`endfor` pairs are tracked to find
    /// the matching `endfor`.
    fn scan_loop_body_with_param(&mut self, loop_var: SymbolId) -> TokenList {
        let mut body = TokenList::new();
        // Tracks nested loop scopes. `true` means that nested loop reuses
        // the same loop variable symbol and therefore shadows `loop_var`.
        let mut nested_shadow_stack: Vec<bool> = Vec::new();
        let mut shadow_depth: usize = 0;
        // After seeing `for`/`forsuffixes`, skip substitution for the next
        // token (the nested loop variable declaration token).
        let mut skip_next_substitution = false;

        loop {
            match self.cur.command {
                Command::Iteration => {
                    let op = IterationOp::from_modifier(self.cur.modifier);
                    self.store_current_token(&mut body);
                    self.get_next();

                    if op == Some(IterationOp::Forever) {
                        nested_shadow_stack.push(false);
                        skip_next_substitution = false;
                    } else {
                        let shadows_outer = self.cur.sym == Some(loop_var);
                        nested_shadow_stack.push(shadows_outer);
                        if shadows_outer {
                            shadow_depth += 1;
                        }
                        skip_next_substitution = true;
                    }
                }
                Command::MacroSpecial
                    if MacroSpecialOp::from_modifier(self.cur.modifier)
                        == Some(MacroSpecialOp::EndFor) =>
                {
                    // `endfor`
                    if nested_shadow_stack.is_empty() {
                        return body;
                    }
                    if nested_shadow_stack.pop().is_some_and(|shadowed| shadowed) {
                        shadow_depth = shadow_depth.saturating_sub(1);
                    }
                    self.store_current_token(&mut body);
                    self.get_next();
                }
                Command::Stop => {
                    self.report_error(ErrorKind::MissingToken, "Missing `endfor`");
                    return body;
                }
                _ => {
                    if skip_next_substitution {
                        self.store_current_token(&mut body);
                        skip_next_substitution = false;
                    } else if self.cur.sym == Some(loop_var) && shadow_depth == 0 {
                        // Replace the loop variable with Param(0)
                        body.push(StoredToken::Param(0));
                    } else {
                        self.store_current_token(&mut body);
                    }
                    self.get_next();
                }
            }
        }
    }

    /// Scan the value list for `forsuffixes`.
    ///
    /// Unlike `scan_loop_value_list` (which evaluates expressions),
    /// this collects raw suffix tokens separated by commas until `:`.
    /// Each suffix value is a token list.
    fn scan_forsuffixes_value_list(&mut self) -> Vec<TokenList> {
        let mut values: Vec<TokenList> = Vec::new();
        self.get_x_next(); // skip `=`

        let mut current = TokenList::new();
        loop {
            if self.cur.command == Command::Colon || self.cur.command == Command::Stop {
                if !current.is_empty() {
                    values.push(current);
                }
                break;
            }
            if self.cur.command == Command::Comma {
                values.push(current);
                current = TokenList::new();
                self.get_x_next();
                continue;
            }
            // For `forsuffixes`, the values can be arbitrary tokens
            // including `scantokens` which should be expanded.
            if self.cur.command.is_expandable() {
                self.expand_current();
                continue;
            }
            self.store_current_token(&mut current);
            self.get_next();
        }
        values
    }

    /// Handle `exitif <boolean>;` — set the loop exit flag if condition is true.
    ///
    /// On return, `self.cur` is the first non-expandable token after `exitif`.
    fn expand_exitif(&mut self) {
        self.get_x_next(); // skip `exitif`
        self.lhs_tracking.equals_means_equation = false;
        let should_exit = if let Ok(result) = self.scan_expression() {
            match result.exp {
                Value::Boolean(b) => b,
                Value::Numeric(v) => v != 0.0,
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
            if let Some(frame) = self.control_flow.forever_stack.last_mut() {
                frame.exit_requested = true;
            } else {
                self.report_error(ErrorKind::BadExitIf, "No loop is in progress");
            }
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
    pub(super) fn do_macro_def(&mut self) -> InterpResult<()> {
        let Some(def_op) = MacroDefOp::from_modifier(self.cur.modifier) else {
            self.report_error(ErrorKind::UnexpectedToken, "Invalid macro def modifier");
            return Ok(());
        };
        let is_vardef = def_op == MacroDefOp::VarDef;
        let is_binary_def = matches!(
            def_op,
            MacroDefOp::PrimaryDef | MacroDefOp::SecondaryDef | MacroDefOp::TertiaryDef
        );

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
        if is_vardef
            && self.cur.command == Command::MacroSpecial
            && MacroSpecialOp::from_modifier(self.cur.modifier) == Some(MacroSpecialOp::MacroSuffix)
        {
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
        let mut param_names: Vec<String> = params.iter().map(|(name, _, _)| name.clone()).collect();
        if has_at_suffix {
            // The `@#` suffix parameter gets the next parameter index
            param_names.push("@#".to_owned());
        }
        let body = self.scan_macro_body(&param_names);

        let mut param_types: Vec<ParamType> = params.iter().map(|(_, ty, _)| *ty).collect();
        let mut param_groups: Vec<u16> = params.iter().map(|(_, _, g)| *g).collect();
        if has_at_suffix {
            param_types.push(ParamType::UndelimitedSuffix);
            param_groups.push(u16::MAX);
        }

        // Store the macro
        let info = MacroInfo {
            params: param_types,
            param_groups,
            body,
            is_vardef,
            has_at_suffix,
        };
        self.macros.insert(macro_sym, info);

        // For regular `def`, set the symbol to `DefinedMacro` so that
        // `get_x_next` expands it (expandable = cmd < min_command = 14).
        // For `vardef`, keep the symbol as `TagToken` — the macro nature is
        // detected by `scan_primary` when it checks `self.macros` after
        // suffix collection.  This matches `mp.web`: vardef macros are stored
        // in the variable structure, not in `eq_type`.
        if !is_vardef {
            self.symbols.set(
                macro_sym,
                crate::symbols::SymbolEntry {
                    command: Command::DefinedMacro,
                    modifier: 0,
                },
            );
        }

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
    fn do_binary_macro_def(&mut self, def_op: MacroDefOp) -> InterpResult<()> {
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

        let info = MacroInfo {
            params: vec![ParamType::Expr, ParamType::Expr],
            param_groups: vec![u16::MAX, u16::MAX],
            body,
            is_vardef: false,
            has_at_suffix: false,
        };
        self.macros.insert(op_sym, info);

        // Set the symbol to the appropriate operator command
        let cmd = match def_op {
            MacroDefOp::PrimaryDef => Command::SecondaryPrimaryMacro,
            MacroDefOp::SecondaryDef => Command::ExpressionTertiaryMacro,
            MacroDefOp::TertiaryDef => Command::TertiarySecondaryMacro,
            _ => {
                self.report_error(
                    ErrorKind::UnexpectedToken,
                    "Non-binary macro def used in binary macro handler",
                );
                Command::TertiarySecondaryMacro
            }
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
    /// Returns a list of (name, type, group) tuples. Delimited parameters
    /// within the same `(…)` share a group number. Undelimited parameters
    /// get `u16::MAX`. If there are no parentheses, returns an empty list
    /// (parameterless macro).
    fn scan_macro_params(&mut self) -> InterpResult<Vec<(String, ParamType, u16)>> {
        let mut params: Vec<(String, ParamType, u16)> = Vec::new();
        let mut group_idx: u16 = 0;

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

                    params.push((name, param_type, group_idx));

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
            group_idx += 1;
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

            params.push((name, pt, u16::MAX));

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
                params.push((of_name, ParamType::UndelimitedSuffix, u16::MAX));
            }
        }

        Ok(params)
    }

    /// Convert a `ParamTypeOp` modifier to a delimited `ParamType`.
    const fn delimited_param_type(modifier: u16) -> ParamType {
        match ParamTypeOp::from_modifier(modifier) {
            Some(ParamTypeOp::Suffix) => ParamType::Suffix,
            Some(ParamTypeOp::Text) => ParamType::Text,
            // primary/secondary/tertiary inside delimiters are treated as expr
            _ => ParamType::Expr,
        }
    }

    /// Convert a `ParamTypeOp` modifier to an undelimited `ParamType`.
    const fn undelimited_param_type(modifier: u16) -> ParamType {
        match ParamTypeOp::from_modifier(modifier) {
            Some(ParamTypeOp::Primary) => ParamType::Primary,
            Some(ParamTypeOp::Secondary) => ParamType::Secondary,
            Some(ParamTypeOp::Tertiary) => ParamType::Tertiary,
            Some(ParamTypeOp::Suffix) => ParamType::UndelimitedSuffix,
            Some(ParamTypeOp::Text) => ParamType::UndelimitedText,
            _ => ParamType::UndelimitedExpr,
        }
    }

    /// Scan a suffix argument for macro expansion.
    ///
    /// Collects symbolic tokens (and bracket subscripts) until a non-suffix
    /// token is found.
    fn scan_suffix_arg(&mut self) -> TokenList {
        let mut suffix_tokens = TokenList::new();
        loop {
            if self.cur.command == Command::TagToken
                || self.cur.command == Command::InternalQuantity
                || self.cur.command == Command::NumericToken
            {
                self.store_current_token(&mut suffix_tokens);
                self.get_next();
                continue;
            }

            if self.cur.command == Command::LeftBracket {
                // Capture a full bracketed subscript, including nested brackets.
                let mut depth: u32 = 0;
                loop {
                    if self.cur.command == Command::LeftBracket {
                        depth += 1;
                    } else if self.cur.command == Command::RightBracket {
                        depth -= 1;
                    }

                    self.store_current_token(&mut suffix_tokens);
                    self.get_next();

                    if depth == 0 || self.cur.command == Command::Stop {
                        break;
                    }
                }
                continue;
            }

            break;
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
                Command::MacroSpecial
                    if MacroSpecialOp::from_modifier(self.cur.modifier)
                        == Some(MacroSpecialOp::EndDef) =>
                {
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
                    // Check if this token matches a parameter name.
                    // Parameter substitution applies at ALL nesting depths
                    // (inside nested def..enddef too), matching mp.web behaviour.
                    // The depth counter only tracks def/enddef pairs to find the
                    // outer body boundary.
                    if let crate::token::TokenKind::Symbolic(ref name) = self.cur.token.kind {
                        if let Some(idx) = param_names.iter().position(|p| p == name) {
                            body.push(StoredToken::Param(idx));
                            self.get_next();
                            continue;
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
    pub(super) fn expand_binary_macro(&mut self, left: &Value) -> InterpResult<ExprResultValue> {
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
        let rhs_result = match cmd {
            Command::SecondaryPrimaryMacro => self.scan_primary()?,
            Command::TertiarySecondaryMacro => self.scan_secondary()?,
            _ => self.scan_tertiary()?,
        };

        let right = rhs_result.exp;

        // Build param token lists — decompose compound values into tokens
        let args = vec![
            value_to_stored_tokens(left, &mut self.symbols),
            value_to_stored_tokens(&right, &mut self.symbols),
        ];

        // After scanning the RHS, `self.cur` holds the first token
        // beyond the operand (the look-ahead).  mp.web §15789 uses
        // `back_input` to push this token back BEFORE the body
        // expansion so it is naturally read after the body is consumed.
        //
        // In our architecture, `back_input` uses a single slot with
        // highest priority, so we instead push the look-ahead as a
        // one-token level below the body.
        let mut saved = TokenList::new();
        self.store_current_token(&mut saved);
        if !saved.is_empty() {
            self.input
                .push_token_list(saved, Vec::new(), "binary-mac-saved".into());
        }

        // Push the body on top — it will be read before the saved token.
        self.input
            .push_token_list(macro_info.body, args, "binary macro".into());

        // Get next token from expansion and evaluate the body
        self.get_x_next();
        self.scan_expression()
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
                Command::MacroSpecial
                    if MacroSpecialOp::from_modifier(self.cur.modifier)
                        == Some(MacroSpecialOp::EndDef) =>
                {
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
    pub(super) fn expand_defined_macro(&mut self) {
        if !self.expand_defined_macro_inner() {
            self.get_next();
            self.expand_current();
            return;
        }
        self.get_next();
        self.expand_current();
    }

    /// Core logic for expanding a user-defined macro: scan arguments and push
    /// the body expansion onto the input stack.  Returns `false` on error
    /// (caller decides whether to advance the token stream).
    fn expand_defined_macro_inner(&mut self) -> bool {
        let Some(macro_sym) = self.cur.sym else {
            self.report_error(ErrorKind::Internal, "DefinedMacro without symbol");
            return false;
        };

        let Some(macro_info) = self.macros.get(&macro_sym).cloned() else {
            self.report_error(ErrorKind::Internal, "Undefined macro expansion");
            return false;
        };

        // Scan arguments — only advance past the macro name if there are params
        let mut args: Vec<TokenList> = Vec::new();

        if !macro_info.params.is_empty() {
            self.get_x_next(); // advance past the macro name, expanding conditionals/etc.

            // For vardefs with `@#`, the suffix tokens sit between the macro
            // name and the argument list `(`.  Collect them now, before the
            // regular param loop, and insert the arg at the `@#` position
            // (the last param) afterwards.
            let at_suffix_arg = if macro_info.has_at_suffix {
                Some(self.scan_suffix_arg())
            } else {
                None
            };

            let mut in_delimiters = false;

            // Number of regular params (excluding the trailing @# if present).
            let regular_param_count = if macro_info.has_at_suffix {
                macro_info.params.len() - 1
            } else {
                macro_info.params.len()
            };

            for i in 0..regular_param_count {
                let param_type = &macro_info.params[i];
                let current_group = macro_info.param_groups.get(i).copied().unwrap_or(u16::MAX);
                let next_group = macro_info
                    .param_groups
                    .get(i + 1)
                    .copied()
                    .unwrap_or(u16::MAX);
                match param_type {
                    // --- Delimited parameters (inside parentheses) ---
                    ParamType::Expr | ParamType::Suffix | ParamType::Text => {
                        if !in_delimiters {
                            if self.cur.command == Command::LeftDelimiter {
                                self.get_x_next(); // skip `(`
                                in_delimiters = true;
                            } else {
                                self.report_error(
                                    ErrorKind::MissingToken,
                                    "Expected `(` for delimited macro argument",
                                );
                            }
                        }
                        match param_type {
                            ParamType::Expr => {
                                if let Ok(result) = self.scan_expression() {
                                    args.push(value_to_stored_tokens(
                                        &result.exp,
                                        &mut self.symbols,
                                    ));
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
                        // Determine if the next regular param is undelimited.
                        let next_regular_is_undelimited = if i + 1 < regular_param_count {
                            macro_info.params[i + 1].is_undelimited()
                        } else {
                            false
                        };
                        // After scanning the argument, we see either `,` or `)`.
                        //
                        // mp.web §13242: when we see `,` and the NEXT param is
                        // delimited but in a DIFFERENT group, the comma crosses
                        // the group boundary — no `)(`  pair is required.  We
                        // simply consume the comma and stay in_delimiters.
                        if self.cur.command == Command::Comma {
                            self.get_x_next();
                        }
                        // Close delimiters when we see `)` and either the next
                        // param is undelimited, in a different delimited group,
                        // or this is the last regular parameter.
                        if self.cur.command == Command::RightDelimiter
                            && (next_regular_is_undelimited
                                || i + 1 >= regular_param_count
                                || (next_group != current_group && next_group != u16::MAX))
                        {
                            // Only advance past `)` if there are more params to
                            // scan.  When this is the LAST parameter, leave
                            // `self.cur` at `)` so the token that follows the
                            // macro call (typically `;`) is not consumed before
                            // the body expansion is pushed.
                            if i + 1 < regular_param_count {
                                self.get_x_next();
                            }
                            in_delimiters = false;
                        }
                    }

                    // --- Undelimited parameters ---
                    ParamType::Primary => {
                        args.push(self.scan_undelimited_value_arg(Self::scan_primary));
                    }
                    ParamType::Secondary => {
                        args.push(self.scan_undelimited_value_arg(Self::scan_secondary));
                    }
                    ParamType::Tertiary => {
                        args.push(self.scan_undelimited_value_arg(Self::scan_tertiary));
                    }
                    ParamType::UndelimitedExpr => {
                        args.push(self.scan_undelimited_value_arg(Self::scan_expression));
                    }
                    ParamType::UndelimitedSuffix => {
                        args.push(self.scan_suffix_arg());
                    }
                    ParamType::UndelimitedText => {
                        // Collect tokens until semicolon/endgroup
                        let mut text_tokens = TokenList::new();
                        while self.cur.command != Command::Semicolon
                            && self.cur.command != Command::EndGroup
                            && self.cur.command != Command::Stop
                        {
                            self.store_current_token(&mut text_tokens);
                            self.get_next();
                        }
                        args.push(text_tokens);
                    }
                }
            }

            // Append the pre-collected @# suffix arg at the end (its param
            // index in the body matches the last position).
            if let Some(suffix_arg) = at_suffix_arg {
                args.push(suffix_arg);
            }
        }

        // When the last *regular* parameter is undelimited, `self.cur` holds
        // the first token AFTER the arguments (mp.web §389).  We must
        // preserve it by pushing it as a one-token input level BEFORE the
        // body expansion.  For `@#` vardefs the trailing `UndelimitedSuffix`
        // was already collected before the regular params, so check the last
        // regular param instead.
        let last_regular_param = if macro_info.has_at_suffix {
            let regular_count = macro_info.params.len().saturating_sub(1);
            macro_info
                .params
                .get(regular_count.saturating_sub(1))
                .copied()
        } else {
            macro_info.params.last().copied()
        };
        let last_param = last_regular_param.or_else(|| {
            if macro_info.has_at_suffix {
                macro_info.params.last().copied()
            } else {
                None
            }
        });
        let last_param_undelimited = last_param.is_some_and(ParamType::is_undelimited);
        if last_param_undelimited {
            let mut trailing = TokenList::new();
            self.store_current_token(&mut trailing);
            if !trailing.is_empty() {
                self.input
                    .push_token_list(trailing, Vec::new(), "trailing token".into());
            }
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

        // Push the body expansion on top of the trailing token level
        self.input
            .push_token_list(expansion, args, "macro expansion".into());

        true
    }

    fn scan_undelimited_value_arg(
        &mut self,
        scanner: fn(&mut Self) -> InterpResult<super::ExprResultValue>,
    ) -> TokenList {
        match scanner(self) {
            Ok(result) => value_to_stored_tokens(&result.exp, &mut self.symbols),
            Err(err) => {
                self.errors.push(err);
                Vec::new()
            }
        }
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
                self.input.push_source(&source);
            }
            None => {
                self.report_error(ErrorKind::Internal, format!("File not found: {filename}"));
            }
        }

        self.get_next();
        self.expand_current();
    }

    /// Handle `btex ... etex`.
    ///
    /// Collects the raw text between `btex` and `etex` (without macro
    /// expansion) and produces a string value. In the original `MetaPost` this
    /// would be shipped to TeX for typesetting; `PostMeta` treats it as plain
    /// text. The `thelabel` macro in `plain.mp` will then apply `infont` to
    /// convert it into a picture.
    fn expand_start_tex(&mut self) {
        let mut parts: Vec<String> = Vec::new();

        // Read raw tokens (no expansion) until EtexMarker or end of input.
        loop {
            self.get_next();
            match self.cur.command {
                Command::EtexMarker | Command::Stop => break,
                _ => {
                    // Reconstruct text from token content.
                    match &self.cur.token.kind {
                        crate::token::TokenKind::Symbolic(s) => parts.push(s.clone()),
                        crate::token::TokenKind::Numeric(v) => parts.push(v.to_string()),
                        crate::token::TokenKind::StringLit(s) => {
                            parts.push(format!("\"{s}\""));
                        }
                        crate::token::TokenKind::Eof => break,
                    }
                }
            }
        }

        let text: std::sync::Arc<str> = parts.join(" ").into();

        // Push a string capsule — `thelabel` will call `s infont defaultfont`
        // to convert to a picture.
        self.back_expr_value(super::ExprResultValue::plain(Value::String(text)));

        // Advance past the capsule and continue expansion.
        self.get_next();
        self.expand_current();
    }

    /// Handle `scantokens <string_expr>`.
    ///
    /// Evaluates the string expression and scans it as if it were source input.
    ///
    /// mp.web §13039: after `scan_primary` obtains the string, the token
    /// that terminated the primary (e.g. `;`) is pushed back via
    /// `back_input`, then the source string is pushed on top.  This
    /// ensures the terminator is read after the scantokens source is
    /// exhausted.
    ///
    /// In our architecture `back_input` uses a single slot with highest
    /// priority, so we instead push the saved token as a one-token level
    /// *below* the source (push it first, then push the source on top).
    fn expand_scantokens(&mut self) {
        self.expand_scantokens_inner();
        self.get_next();
        self.expand_current();
    }

    /// Core logic for `scantokens`: scan the string expression and push the
    /// resulting source onto the input stack.
    fn expand_scantokens_inner(&mut self) {
        self.get_x_next(); // skip `scantokens`, expand

        // Scan the string expression
        if let Ok(result) = self.scan_primary() {
            if let Value::String(ref s) = result.exp {
                let source = s.to_string();

                // Save the token that terminated scan_primary (mp.web's
                // back_input).  Push it as a level below the source so it
                // is read after the source is exhausted.
                let mut saved = TokenList::new();
                self.store_current_token(&mut saved);
                if !saved.is_empty() {
                    self.input
                        .push_token_list(saved, Vec::new(), "scantokens-saved".into());
                }

                if !source.is_empty() {
                    self.input.push_source(&source);
                }
            } else {
                self.report_error(ErrorKind::TypeError, "scantokens requires a string");
            }
        }
    }

    /// Handle `expandafter`.
    ///
    /// mp.web §13032: `expandafter A B` performs ONE expansion step on B,
    /// then places A in front of B's expansion result.
    ///
    /// ```text
    /// get_t_next;  p := cur_tok;  {read A}
    /// get_t_next;                 {read B}
    /// if cur_cmd < min_command then expand else back_input;
    /// back_list(p);               {push A in front}
    /// ```
    ///
    /// In our architecture each expand handler ends with
    /// `get_next(); expand_current();`, performing full expansion.
    /// For expandafter we need exactly one step, so we call a
    /// push-only variant of the handler that sets up the input stack
    /// but does **not** read the first result token.  Then we push A
    /// on top and let `get_next(); expand_current();` do the rest.
    fn expand_expandafter(&mut self) {
        self.expand_expandafter_push_only();

        // Read the first result token and continue expanding.
        self.get_next();
        self.expand_current();
    }

    /// Convert `self.cur` to a `StoredToken`, if possible.
    fn resolved_to_stored(&self) -> Option<StoredToken> {
        match &self.cur.token.kind {
            crate::token::TokenKind::Symbolic(_) => self.cur.sym.map(StoredToken::Symbol),
            crate::token::TokenKind::Numeric(v) => Some(StoredToken::Numeric(*v)),
            crate::token::TokenKind::StringLit(s) => Some(StoredToken::StringLit(s.clone())),
            crate::token::TokenKind::Eof => None,
        }
    }

    /// Push-only variant of `expand_scantokens` for use by `expandafter`.
    ///
    /// Same as `expand_scantokens` but does NOT call `get_next();
    /// expand_current();` — the source is left on the input stack.
    fn expand_scantokens_push_only(&mut self) {
        self.expand_scantokens_inner();
    }

    /// Push-only variant of `expand_defined_macro` for use by `expandafter`.
    ///
    /// Same as `expand_defined_macro` but does NOT call `get_next();
    /// expand_current();` — the expansion is left on the input stack.
    fn expand_defined_macro_push_only(&mut self) {
        self.expand_defined_macro_inner();
    }

    /// Push-only variant of `expand_expandafter`.
    ///
    /// Performs the full expandafter logic (read A, read B, one-step expand B,
    /// push A in front) but does NOT call `get_next(); expand_current()` at
    /// the end.  Used by `expand_one_step` for nested expandafter chains.
    fn expand_expandafter_push_only(&mut self) {
        // Read token A without expanding.
        self.get_next();
        let saved_a: TokenList = std::iter::once_with(|| self.resolved_to_stored())
            .flatten()
            .collect();

        // Read token B without expanding.
        self.get_next();

        if self.cur.command.is_expandable() {
            // Perform ONE expansion step for B.
            self.expand_one_step();
        } else {
            // B is not expandable — push it back.
            let mut saved_b = TokenList::new();
            self.store_current_token(&mut saved_b);
            if !saved_b.is_empty() {
                self.input
                    .push_token_list(saved_b, Vec::new(), "expandafter-b".into());
            }
        }

        // Push A in front of whatever B produced.
        if !saved_a.is_empty() {
            self.input
                .push_token_list(saved_a, Vec::new(), "expandafter-a".into());
        }

        // Do NOT call get_next/expand_current — caller handles continuation.
    }

    /// Perform exactly one expansion step for the token in `self.cur`.
    ///
    /// This dispatches to a push-only variant of the appropriate handler.
    /// After this call, the expansion result is on the input stack but
    /// `self.cur` is stale — the caller must call `get_next()` to read
    /// the first result token.
    fn expand_one_step(&mut self) {
        match self.cur.command {
            Command::DefinedMacro => self.expand_defined_macro_push_only(),
            Command::ScanTokens => self.expand_scantokens_push_only(),
            Command::ExpandAfter => self.expand_expandafter_push_only(),
            Command::IfTest => {
                // For conditionals, full expansion is the only sensible
                // one-step behaviour: evaluate the condition and enter
                // the correct branch.
                self.expand_if();
                // expand_if left self.cur at the first token of the
                // branch — push it back so the caller can re-read it.
                let mut saved = TokenList::new();
                self.store_current_token(&mut saved);
                if !saved.is_empty() {
                    self.input
                        .push_token_list(saved, Vec::new(), "expandafter-if".into());
                }
            }
            Command::Input => {
                self.expand_input();
                let mut saved = TokenList::new();
                self.store_current_token(&mut saved);
                if !saved.is_empty() {
                    self.input
                        .push_token_list(saved, Vec::new(), "expandafter-input".into());
                }
            }
            _ => {
                // For other expandable commands (iteration, exitif,
                // repeat_loop, etc.), fall back to full expansion and
                // push the result back.
                self.expand_current();
                let mut saved = TokenList::new();
                self.store_current_token(&mut saved);
                if !saved.is_empty() {
                    self.input
                        .push_token_list(saved, Vec::new(), "expandafter-other".into());
                }
            }
        }
    }
}
