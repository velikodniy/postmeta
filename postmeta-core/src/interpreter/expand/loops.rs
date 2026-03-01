use std::sync::Arc;

use crate::command::{Command, IterationOp, MacroSpecialOp};
use crate::error::ErrorKind;
use crate::input::{SharedTokenList, StoredToken, TokenList};
use crate::interpreter::helpers;
use crate::symbols::SymbolId;
use crate::types::Value;

use postmeta_graphics::types::{GraphicsObject, Picture};

use super::{ForeverLoopFrame, Interpreter};

impl Interpreter {
    /// Handle `for`/`forsuffixes`/`forever` — scan the loop body, then replay.
    ///
    /// Syntax:
    ///   `for <var> = <expr>, <expr>, ...: <body> endfor`
    ///   `forsuffixes <var> = <suffix>, ...: <body> endfor`
    ///   `forever: <body> endfor`
    ///
    /// On return, `self.cur` is the first non-expandable token after the loop.
    pub(in crate::interpreter) fn expand_iteration(&mut self) {
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
        let loop_var_name = if let Some(name) = self.cur_symbolic_name() {
            name.to_owned()
        } else {
            self.report_error(ErrorKind::MissingToken, "Expected loop variable name");
            self.get_next();
            self.expand_current();
            return;
        };
        let loop_var_sym = self.state.symbols.lookup(&loop_var_name);

        self.get_next(); // skip the variable name

        // Check for `within` (picture iteration)
        if self.cur.command == Command::WithinToken {
            self.expand_for_within(loop_var_sym);
            return;
        }

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
                .map(|v| helpers::value_to_stored_tokens(&v, &mut self.state.symbols))
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
        let mut body = self.scan_loop_body_with_param(loop_var_sym);

        if value_token_lists.is_empty() {
            // No iterations — skip the loop entirely.
            self.get_next();
            self.expand_current();
            return;
        }

        // Use sentinel-based replay (like `forever`) so that `exitif`
        // can interrupt iteration.  Push the first iteration's body with
        // a RepeatLoop sentinel at the end; store remaining iterations
        // in the loop frame.
        let mut iter = value_token_lists.into_iter();
        let Some(first_params) = iter.next() else {
            // Unreachable: we checked non-empty above.
            self.get_next();
            self.expand_current();
            return;
        };
        // Store remaining in reverse so Vec::pop() yields the next iteration.
        let remaining: Vec<SharedTokenList> = iter.map(Into::into).rev().collect();

        // Append RepeatLoop sentinel to the body and freeze as Arc.
        let repeat_sym = self.state.symbols.lookup("__repeat_loop__");
        self.state.symbols.set(
            repeat_sym,
            crate::symbols::SymbolEntry {
                command: Command::RepeatLoop,
                modifier: 0,
            },
        );
        body.push(StoredToken::Symbol(repeat_sym));
        let body: SharedTokenList = body.into();

        self.control_flow.forever_stack.push(ForeverLoopFrame {
            body: Arc::clone(&body),
            is_for_loop: true,
            remaining_iterations: remaining,
        });

        self.state
            .input
            .push_loop_body(body, vec![SharedTokenList::from(first_params)]);

        // Get the first token and continue expanding
        self.get_next();
        self.expand_current();
    }

    /// Handle `for <var> within <picture expr>: <body> endfor`.
    ///
    /// Evaluates the picture expression, splits it into individual components
    /// (treating ClipStart..ClipEnd and SetBoundsStart..SetBoundsEnd groups
    /// as single components), and iterates with each component wrapped in
    /// its own picture capsule.
    fn expand_for_within(&mut self, loop_var_sym: SymbolId) {
        // Skip `within` and evaluate the picture expression.
        self.get_next();
        self.expand_current();
        let pic = if let Ok(result) = self.scan_expression() {
            if let Value::Picture(p) = result.exp {
                p
            } else {
                self.report_error(ErrorKind::TypeError, "Expected picture after `within`");
                Picture::new()
            }
        } else {
            self.report_error(
                ErrorKind::InvalidExpression,
                "Missing picture expression after `within`",
            );
            Picture::new()
        };

        // Expect `:` after picture expression.
        if self.cur.command == Command::Colon {
            self.get_next();
        }

        // Scan the loop body with parameter substitution.
        let mut body = self.scan_loop_body_with_param(loop_var_sym);

        // Split the picture into components.  Clip/SetBounds groups
        // count as single components (the group start, all contents,
        // and the group end).
        let components = split_picture_components(&pic);

        if components.is_empty() {
            // No components — skip.
            self.get_next();
            self.expand_current();
            return;
        }

        // Convert each component picture to a token list (capsule).
        let value_token_lists: Vec<TokenList> = components
            .into_iter()
            .map(|comp| {
                helpers::value_to_stored_tokens(&Value::Picture(comp), &mut self.state.symbols)
            })
            .collect();

        let mut iter = value_token_lists.into_iter();
        let Some(first_params) = iter.next() else {
            // Unreachable: we checked non-empty above.
            self.get_next();
            self.expand_current();
            return;
        };
        let remaining: Vec<SharedTokenList> = iter.map(Into::into).rev().collect();

        // Append RepeatLoop sentinel.
        let repeat_sym = self.state.symbols.lookup("__repeat_loop__");
        self.state.symbols.set(
            repeat_sym,
            crate::symbols::SymbolEntry {
                command: Command::RepeatLoop,
                modifier: 0,
            },
        );
        body.push(StoredToken::Symbol(repeat_sym));
        let body: SharedTokenList = body.into();

        self.control_flow.forever_stack.push(ForeverLoopFrame {
            body: Arc::clone(&body),
            is_for_loop: true,
            remaining_iterations: remaining,
        });

        self.state
            .input
            .push_loop_body(body, vec![SharedTokenList::from(first_params)]);

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

        // Scan the loop body, append RepeatLoop sentinel, and freeze.
        let mut body = self.scan_loop_body();
        let repeat_sym = self.state.symbols.lookup("__repeat_loop__");
        self.state.symbols.set(
            repeat_sym,
            crate::symbols::SymbolEntry {
                command: Command::RepeatLoop,
                modifier: 0,
            },
        );
        body.push(StoredToken::Symbol(repeat_sym));
        let body: SharedTokenList = body.into();

        // Push a new forever-loop frame. Nested forever loops are handled
        // by stack discipline, so each loop replays its own body.
        self.control_flow.forever_stack.push(ForeverLoopFrame {
            body: Arc::clone(&body),
            is_for_loop: false,
            remaining_iterations: Vec::new(),
        });

        // Push the first iteration
        self.state.input.push_loop_body(body, Vec::new());

        // Get the first token and continue — the RepeatLoop sentinel will
        // be caught by expand_current and re-push the body.
        self.get_next();
        self.expand_current();
    }

    /// Handle the `RepeatLoop` sentinel during expansion.
    ///
    /// Re-pushes the loop body for the next iteration.
    /// For `forever` loops (no `is_for_loop` flag), unconditionally replays.
    /// For `for`/`forsuffixes` loops, pops the next iteration params from the queue;
    /// when the queue is empty the loop is finished and the frame is popped.
    pub(super) fn expand_repeat_loop(&mut self) {
        if let Some(frame) = self.control_flow.forever_stack.last_mut() {
            if frame.is_for_loop {
                // `for`/`forsuffixes` loop — check for remaining iterations.
                if let Some(params) = frame.remaining_iterations.pop() {
                    // Body already has RepeatLoop sentinel; Arc::clone is O(1).
                    let body = Arc::clone(&frame.body);
                    self.state.input.push_loop_body(body, vec![params]);
                } else {
                    // No more iterations — loop is done.
                    self.control_flow.forever_stack.pop();
                }
            } else {
                // `forever` loop — replay unconditionally.
                let body = Arc::clone(&frame.body);
                self.state.input.push_loop_body(body, Vec::new());
            }
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
                    if let Ok(start) = helpers::value_to_scalar(&first_val) {
                        self.get_x_next();
                        if let Ok(step_result) = self.scan_expression() {
                            let step_val = step_result.exp;
                            if let Ok(step) = helpers::value_to_scalar(&step_val) {
                                // Expect `until`
                                if self.cur.command == Command::UntilToken {
                                    self.get_x_next();
                                    if let Ok(end_result) = self.scan_expression() {
                                        let end_val = end_result.exp;
                                        if let Ok(end) = helpers::value_to_scalar(&end_val) {
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

    /// Handle `exitif <boolean>;`.
    ///
    /// This handler does NOT advance past the final token.
    /// The caller (`expand_current` loop) calls `get_next()` afterwards.
    pub(super) fn expand_exitif(&mut self) {
        self.get_x_next(); // skip `exitif`
        self.lhs_tracking.equals_means_equation = false;
        let should_exit = match self.scan_expression() {
            Ok(result) => match result.exp {
                Value::Boolean(b) => b,
                Value::Numeric(v) => v != 0.0,
                _ => {
                    self.report_error(ErrorKind::TypeError, "exitif condition must be boolean");
                    false
                }
            },
            Err(e) => {
                self.state.errors.push(e);
                false
            }
        };
        if should_exit {
            if self.control_flow.forever_stack.is_empty() {
                self.report_error(ErrorKind::BadExitIf, "No loop is in progress");
            } else {
                // Premature exit: pop input levels until the loop body level
                // is found, then pop the loop frame.
                self.state.input.pop_to_loop_body();
                self.control_flow.forever_stack.pop();
            }
        } else if self.cur.command != Command::Semicolon {
            self.report_error(
                ErrorKind::MissingToken,
                "After `exitif <boolean exp>` I expect to see a semicolon",
            );
        }
        // Do NOT advance — the expand_current loop calls get_next().
    }
}

/// Split a picture into its top-level components.
///
/// Each `Fill`, `Stroke`, or `Text` object becomes a single-element picture.
/// `ClipStart`..`ClipEnd` and `SetBoundsStart`..`SetBoundsEnd` groups
/// (including all nested content) become one picture each.
fn split_picture_components(pic: &Picture) -> Vec<Picture> {
    let mut result = Vec::new();
    let objects = &pic.objects;
    let mut i = 0;

    while i < objects.len() {
        match &objects[i] {
            GraphicsObject::ClipStart(_) | GraphicsObject::SetBoundsStart(_) => {
                // Collect the entire group: start, contents, and matching end.
                let start = i;
                let mut depth = 1u32;
                i += 1;
                while i < objects.len() && depth > 0 {
                    match &objects[i] {
                        GraphicsObject::ClipStart(_) | GraphicsObject::SetBoundsStart(_) => {
                            depth += 1;
                        }
                        GraphicsObject::ClipEnd | GraphicsObject::SetBoundsEnd => {
                            depth -= 1;
                        }
                        _ => {}
                    }
                    i += 1;
                }
                let mut comp = Picture::new();
                comp.objects = objects[start..i].to_vec();
                result.push(comp);
            }
            GraphicsObject::ClipEnd | GraphicsObject::SetBoundsEnd => {
                // Stray end marker — skip it.
                i += 1;
            }
            _ => {
                // Single object: Fill, Stroke, or Text.
                let mut comp = Picture::new();
                comp.objects.push(objects[i].clone());
                result.push(comp);
                i += 1;
            }
        }
    }

    result
}
