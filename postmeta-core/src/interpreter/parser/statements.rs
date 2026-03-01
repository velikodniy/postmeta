use crate::command::{Command, MacroSpecialOp};
use crate::error::{ErrorKind, InterpResult};
use crate::interpreter::{Interpreter, LhsBinding};
use crate::types::Value;

impl Interpreter {
    /// Execute one statement.
    ///
    /// # Errors
    ///
    /// Returns an error when expression parsing/evaluation fails inside a statement.
    #[allow(clippy::too_many_lines)]
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
            Command::Outer => self.do_outer(),
            Command::Save => self.do_save(),
            Command::Interim => self.do_interim(),
            Command::Let => self.do_let(),
            Command::MacroDef => self.do_macro_def(),
            Command::Delimiters => self.do_delimiters(),
            Command::NewInternal => self.do_new_internal(),
            Command::IfTest => {
                self.expand_if();
                Ok(())
            }
            Command::FiOrElse => {
                self.expand_fi_or_else();
                Ok(())
            }
            Command::Iteration => {
                self.expand_iteration();
                Ok(())
            }
            Command::Input => {
                self.expand_input();
                Ok(())
            }
            Command::Show => self.do_show(),
            Command::MessageCommand => self.do_message(),
            Command::ModeCommand => self.do_mode_command(),
            Command::RandomSeed => self.do_randomseed(),
            Command::EveryJob => self.do_unimplemented_statement("everyjob"),
            Command::Special => self.do_special(),
            Command::Write => self.do_unimplemented_statement("write"),
            Command::DoubleColon => {
                self.report_error(ErrorKind::UnexpectedToken, "Unexpected `::`");
                self.get_x_next();
                Ok(())
            }
            Command::BeginGroup => {
                self.state.scope_manager.begin_group(&mut self.state.macros);
                self.get_x_next();
                Ok(())
            }
            Command::EndGroup => {
                self.do_endgroup();
                self.get_x_next();
                Ok(())
            }

            _ => {
                // Expression or equation — `=` should be treated as an
                // equation delimiter, not as comparison (mp.web: var_flag = assignment).
                self.lhs_tracking.equals_means_equation = true;
                let mut cur_result = self.scan_expression()?;

                if self.cur.command == Command::Equals {
                    // Equation chain: lhs = mid = ... = rhs.
                    // All left-hand sides are equated to the FINAL rightmost value.
                    type PendingEquationLhs = (
                        Value,
                        Option<LhsBinding>,
                        Option<crate::equation::DepList>,
                        Option<(crate::equation::DepList, crate::equation::DepList)>,
                    );

                    let mut pending_lhs: Vec<PendingEquationLhs> = Vec::new();
                    while self.cur.command == Command::Equals {
                        let lhs_binding = self.lhs_tracking.last_lhs_binding.clone();
                        pending_lhs.push((
                            cur_result.exp,
                            lhs_binding,
                            cur_result.dep,
                            cur_result.pair_dep,
                        ));
                        self.get_x_next();
                        self.lhs_tracking.equals_means_equation = true;
                        cur_result = self.scan_expression()?;
                    }

                    let rhs_clone = cur_result.exp;
                    let rhs_dep = cur_result.dep;
                    let rhs_pair_dep = cur_result.pair_dep;
                    for (lhs, lhs_binding, lhs_dep, lhs_pair_dep) in &pending_lhs {
                        self.do_equation(
                            lhs,
                            &rhs_clone,
                            lhs_binding.clone(),
                            (lhs_dep.clone(), lhs_pair_dep.clone()),
                            (rhs_dep.clone(), rhs_pair_dep.clone()),
                        )?;
                    }
                } else if self.cur.command == Command::Assignment {
                    // Assignment chain: a := b := ... := rhs
                    // All left-hand sides receive the final rhs value.
                    let mut pending_lhs: Vec<Option<LhsBinding>> = Vec::new();
                    while self.cur.command == Command::Assignment {
                        pending_lhs.push(self.lhs_tracking.last_lhs_binding.clone());
                        self.get_x_next();
                        self.lhs_tracking.equals_means_equation = true;
                        cur_result = self.scan_expression()?;
                    }

                    let rhs = cur_result.exp;
                    for lhs_binding in pending_lhs {
                        self.assign_binding(lhs_binding, &rhs)?;
                    }
                } else {
                    // Bare expression-statement (no `=` or `:=`).
                    // Preserve the result in cur_expr so that
                    // begingroup/endgroup can return the last expression
                    // as the group's value (mp.web's "stash_cur_exp").
                    self.set_cur_result(cur_result);
                }

                // Expect statement terminator
                if self.cur.command == Command::Semicolon {
                    self.get_x_next();
                } else if self.cur.command == Command::EndGroup
                    || self.cur.command == Command::Stop
                    || self.cur.command == Command::NewInternal
                {
                    // OK — some commands may begin immediately without an
                    // explicit semicolon between statements.
                } else if self.cur.command == Command::MacroSpecial
                    && MacroSpecialOp::from_modifier(self.cur.modifier)
                        == Some(MacroSpecialOp::EndDef)
                {
                    // Allow an implicit terminator before `enddef` in macro bodies.
                    self.get_x_next();
                } else {
                    self.report_error(
                        ErrorKind::MissingToken,
                        format!(
                            "Missing `;` (got {:?} {:?})",
                            self.cur.command, self.cur.token.kind
                        ),
                    );
                    // Skip to the next semicolon (or end) to recover.
                    while self.cur.command != Command::Semicolon
                        && self.cur.command != Command::Stop
                        && self.cur.command != Command::EndGroup
                    {
                        self.get_x_next();
                    }
                }
                Ok(())
            }
        }
    }
}
