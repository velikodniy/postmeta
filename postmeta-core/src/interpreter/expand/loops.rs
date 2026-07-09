use std::sync::Arc;

use crate::command::{Command, IterationOp, MacroSpecialOp};
use crate::error::ErrorKind;
use crate::input::{SharedTokenList, StoredToken, TokenList};
use crate::interpreter::helpers;
use crate::symbols::SymbolId;
use crate::types::Value;

use postmeta_graphics::types::Picture;

use super::{ForeverLoopFrame, Interpreter};
use crate::interpreter::EqualsMode;

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
        self.get_next();

        let loop_var_name = if let Some(name) = self.cur_symbolic_name() {
            name.to_owned()
        } else {
            self.report_error(ErrorKind::MissingToken, "Expected loop variable name");
            self.get_next();
            self.expand_current();
            return;
        };
        let loop_var_sym = self.state.symbols.lookup(&loop_var_name);

        self.get_next();

        if self.cur.command == Command::WithinToken {
            self.expand_for_within(loop_var_sym);
            return;
        }

        // Expect `=` or `:=` (MetaPost accepts both forms for the loop variable)
        if self.cur.command != Command::Equals && self.cur.command != Command::Assignment {
            self.report_error(ErrorKind::MissingToken, "Expected `=` after loop variable");
        }

        // For `for`, evaluate expressions; for `forsuffixes`, collect raw suffix tokens
        let value_token_lists: Vec<TokenList> = if is_forsuffixes {
            self.scan_forsuffixes_value_list()
        } else {
            self.scan_loop_value_list()
                .into_iter()
                .map(|v| helpers::value_to_stored_tokens(&v, &mut self.state.symbols))
                .collect()
        };

        if self.cur.command == Command::Colon {
            self.get_next();
        }

        // Scan the loop body, replacing occurrences of the loop variable with `Param(0)`.
        // This mirrors how macro bodies substitute parameter names, ensuring `for`/`forsuffixes` work as token-level substitution (`mp.web` §13694).
        let mut body = self.scan_loop_body_with_param(loop_var_sym);

        if value_token_lists.is_empty() {
            // No iterations — skip the loop entirely
            self.get_next();
            self.expand_current();
            return;
        }

        // Use sentinel-based replay (like `forever`) so `exitif` can interrupt iteration.
        // Push the first iteration's body with a RepeatLoop sentinel at the end; store remaining iterations in the loop frame.
        let mut iter = value_token_lists.into_iter();
        let Some(first_params) = iter.next() else {
            // Unreachable: checked non-empty above
            self.get_next();
            self.expand_current();
            return;
        };
        // Store remaining in reverse so Vec::pop() yields the next iteration
        let remaining: Vec<SharedTokenList> = iter.map(Into::into).rev().collect();

        // Append RepeatLoop sentinel to the body and freeze as Arc
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

    /// Handle `for <var> within <picture expr>: <body> endfor`.
    ///
    /// Evaluates the picture expression, splits it into individual top-level components, and iterates with each component wrapped in its own picture capsule.
    fn expand_for_within(&mut self, loop_var_sym: SymbolId) {
        // Skip `within` and evaluate the picture expression
        self.get_next();
        self.expand_current();
        let pic = if let Ok(result) = self.scan_expression(EqualsMode::Relation) {
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

        if self.cur.command == Command::Colon {
            self.get_next();
        }

        // Scan the loop body with parameter substitution
        let mut body = self.scan_loop_body_with_param(loop_var_sym);

        let components = split_picture_components(&pic);

        if components.is_empty() {
            // No components — skip
            self.get_next();
            self.expand_current();
            return;
        }

        // Convert each component picture to a token list (capsule)
        let value_token_lists: Vec<TokenList> = components
            .into_iter()
            .map(|comp| {
                helpers::value_to_stored_tokens(&Value::Picture(comp), &mut self.state.symbols)
            })
            .collect();

        let mut iter = value_token_lists.into_iter();
        let Some(first_params) = iter.next() else {
            // Unreachable: checked non-empty above
            self.get_next();
            self.expand_current();
            return;
        };
        let remaining: Vec<SharedTokenList> = iter.map(Into::into).rev().collect();

        // Append RepeatLoop sentinel to the body and freeze as Arc
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
    /// Uses a sentinel-based approach: appends a `RepeatLoop` command token at the end of each iteration's body.
    /// When `RepeatLoop` is encountered during expansion, the body is re-pushed for the next iteration.
    fn expand_forever(&mut self) {
        self.get_next();

        if self.cur.command == Command::Colon {
            self.get_next();
        }

        // Scan the loop body, append RepeatLoop sentinel, and freeze
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

        // Nested forever loops are handled by stack discipline, so each loop replays its own body
        self.control_flow.forever_stack.push(ForeverLoopFrame {
            body: Arc::clone(&body),
            is_for_loop: false,
            remaining_iterations: Vec::new(),
        });

        self.state.input.push_loop_body(body, Vec::new());

        // The RepeatLoop sentinel will be caught by expand_current and re-push the body
        self.get_next();
        self.expand_current();
    }

    /// Handle the `RepeatLoop` sentinel during expansion.
    ///
    /// Re-pushes the loop body for the next iteration.
    /// For `forever` loops (no `is_for_loop` flag), unconditionally replays.
    /// For `for`/`forsuffixes` loops, pops the next iteration params from the queue; when the queue is empty the loop is finished and the frame is popped.
    pub(super) fn expand_repeat_loop(&mut self) {
        if let Some(frame) = self.control_flow.forever_stack.last_mut() {
            if frame.is_for_loop {
                // `for`/`forsuffixes` loop — check for remaining iterations
                if let Some(params) = frame.remaining_iterations.pop() {
                    // Body already has RepeatLoop sentinel; Arc::clone is O(1)
                    let body = Arc::clone(&frame.body);
                    self.state.input.push_loop_body(body, vec![params]);
                } else {
                    // No more iterations — loop is done
                    self.control_flow.forever_stack.pop();
                }
            } else {
                // `forever` loop — replay unconditionally
                let body = Arc::clone(&frame.body);
                self.state.input.push_loop_body(body, Vec::new());
            }
        }

        self.get_next();
        self.expand_current();
    }

    /// Parse the value list for a `for` loop: `expr, expr, ...`.
    ///
    /// Reads expressions separated by commas until a `:` is found; returns the list of values.
    fn scan_loop_value_list(&mut self) -> Vec<Value> {
        let mut values = Vec::new();
        self.get_x_next();

        loop {
            if self.cur.command == Command::Colon || self.cur.command == Command::Stop {
                break;
            }
            if let Ok(first_result) = self.scan_expression(EqualsMode::Relation) {
                let first_val = first_result.exp;

                // Check for `step <step> until <end>` after the first value
                if self.cur.command == Command::StepToken {
                    if let Ok(start) = helpers::value_to_scalar(&first_val) {
                        self.get_x_next();
                        if let Ok(step_result) = self.scan_expression(EqualsMode::Relation) {
                            let step_val = step_result.exp;
                            if let Ok(step) = helpers::value_to_scalar(&step_val) {
                                if self.cur.command == Command::UntilToken {
                                    self.get_x_next();
                                    if let Ok(end_result) =
                                        self.scan_expression(EqualsMode::Relation)
                                    {
                                        let end_val = end_result.exp;
                                        if let Ok(end) = helpers::value_to_scalar(&end_val) {
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
    /// Uses index-based computation (`start + i * step`) to avoid accumulating floating-point drift.
    /// The endpoint is inclusive when the overshoot is within a small relative/absolute tolerance, matching `MetaPost` semantics.
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

    /// Scan a loop body (tokens until `endfor`), handling nested for/endfor; returns the body as a `TokenList`
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
    /// This mirrors macro body scanning: every occurrence of the loop variable is replaced with a `StoredToken::Param(0)` so the input system performs token-level substitution at each iteration (`mp.web` §13694).
    /// Nested `for`/`endfor` pairs are tracked to find the matching `endfor`.
    fn scan_loop_body_with_param(&mut self, loop_var: SymbolId) -> TokenList {
        let mut body = TokenList::new();
        // Tracks nested loop scopes; `true` means the nested loop reuses the same loop variable symbol and therefore shadows `loop_var`
        let mut nested_shadow_stack: Vec<bool> = Vec::new();
        let mut shadow_depth: usize = 0;
        // After seeing `for`/`forsuffixes`, skip substitution for the next token (the nested loop variable declaration token)
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
    /// Unlike `scan_loop_value_list` (which evaluates expressions), this collects raw suffix tokens separated by commas until `:`.
    /// Each suffix value is a token list.
    fn scan_forsuffixes_value_list(&mut self) -> Vec<TokenList> {
        let mut values: Vec<TokenList> = Vec::new();
        self.get_x_next();

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
            // For `forsuffixes`, the values can be arbitrary tokens including `scantokens`, which should be expanded
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
        self.get_x_next();
        let should_exit = match self.scan_expression(EqualsMode::Relation) {
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
                // Premature exit: pop input levels until the loop body level is found, then pop the loop frame
                self.state.input.pop_to_loop_body();
                self.control_flow.forever_stack.pop();
            }
        } else if self.cur.command != Command::Semicolon {
            self.report_error(
                ErrorKind::MissingToken,
                "After `exitif <boolean exp>` I expect to see a semicolon",
            );
        }
        // Do NOT advance — the expand_current loop calls get_next()
    }
}

/// Split a picture into its top-level components: each `GraphicsObject` becomes its own single-element picture.
/// A nested `GraphicsObject::Picture` (used for `clip`/`setbounds` groups) is already a single top-level object, so its whole group carries over intact.
fn split_picture_components(pic: &Picture) -> Vec<Picture> {
    let mut result = Vec::new();
    let objects = pic.objects();

    for obj in objects {
        let mut comp = Picture::new();
        comp.push(obj.clone());
        result.push(comp);
    }

    result
}
