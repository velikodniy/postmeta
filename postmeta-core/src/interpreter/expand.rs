//! Macro expansion, conditionals, and loops.
//!
//! This module handles all expandable commands: `if`/`elseif`/`else`/`fi`,
//! `for`/`forsuffixes`/`forever`/`endfor`/`exitif`, macro definitions
//! (`def`/`vardef`/`primarydef`/`secondarydef`/`tertiarydef`), macro
//! expansion, `input`, and `scantokens`.

use crate::command::{Command, FiOrElseOp, IterationOp, MacroDefOp, ParamTypeOp};
use crate::error::{ErrorKind, InterpResult, InterpreterError};
use crate::input::{StoredToken, TokenList};
use crate::types::Value;

use super::helpers::value_to_stored_tokens;
use super::Interpreter;

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
    /// The macro body as a token list.
    pub(super) body: TokenList,
    /// Whether this is a `vardef` (wraps body in begingroup/endgroup).
    pub(super) is_vardef: bool,
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
            // Use value_to_stored_tokens to correctly handle compound types
            // like pairs `(x,y)` and colors `(r,g,b)`.
            let value_tokens = value_to_stored_tokens(val, &mut self.symbols);
            let semicolon_sym = self.symbols.lookup(";");
            let mut prefix = vec![
                StoredToken::Symbol(loop_var_sym),
                StoredToken::Symbol(assign_sym),
            ];
            prefix.extend(value_tokens);
            prefix.push(StoredToken::Symbol(semicolon_sym));
            combined.splice(0..0, prefix);
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
                    if let Ok(start) = super::helpers::value_to_scalar(&first_val) {
                        self.get_x_next();
                        if self.scan_expression().is_ok() {
                            let step_val = self.take_cur_exp();
                            if let Ok(step) = super::helpers::value_to_scalar(&step_val) {
                                // Expect `until`
                                if self.cur.command == Command::UntilToken {
                                    self.get_x_next();
                                    if self.scan_expression().is_ok() {
                                        let end_val = self.take_cur_exp();
                                        if let Ok(end) = super::helpers::value_to_scalar(&end_val) {
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
    pub(super) fn do_macro_def(&mut self) -> InterpResult<()> {
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
    pub(super) fn expand_binary_macro(&mut self, left: &Value) -> InterpResult<()> {
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

        // After scanning the RHS, `self.cur` holds the first token
        // beyond the operand.  This look-ahead may belong to an outer
        // input level (e.g. remaining text-parameter tokens).  Append
        // it to the body token list so it reappears naturally after
        // the body is consumed, preventing token loss.
        let mut body = macro_info.body;
        self.store_current_token(&mut body);

        // Push the body (with appended look-ahead) and args
        self.input
            .push_token_list(body, args, "binary macro".into());

        // Get next token from expansion and evaluate the body
        self.get_x_next();
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
    pub(super) fn expand_defined_macro(&mut self) {
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
            self.get_x_next(); // advance past the macro name, expanding conditionals/etc.
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
}
