use crate::command::{Command, FiOrElseOp};
use crate::error::ErrorKind;
use crate::types::Value;

use super::{IfState, Interpreter};

impl Interpreter {
    /// Handle `if <boolean>:` — evaluate the condition and enter a branch.
    ///
    /// On return, `self.cur` is the first non-expandable token of the
    /// active branch (or the token after `fi` if no branch is taken).
    pub(in crate::interpreter) fn expand_if(&mut self) {
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
                self.state.errors.push(err);
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
    pub(in crate::interpreter) fn expand_fi_or_else(&mut self) {
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
}
