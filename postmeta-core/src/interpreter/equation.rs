//! Equation and assignment logic.
//!
//! Handles `lhs = rhs` equations (including unknown-variable assignment)
//! and `:=` explicit assignments.

use crate::equation::{dep_add_scaled, solve_equation, DepList, SolveResult};
use crate::error::{ErrorKind, InterpResult};
use crate::types::Value;
use crate::variables::{NumericState, VarValue};

use super::helpers::value_to_scalar;
use super::{Interpreter, LhsBinding};

impl Interpreter {
    /// Execute an equation: `lhs = rhs`.
    ///
    /// If the LHS has a bindable form (`x`, `-x`, internal quantity), treat the
    /// equation like assignment to that LHS. Otherwise check numeric consistency.
    /// Full dependency-list equation solving is deferred.
    pub(super) fn do_equation(
        &mut self,
        lhs: &Value,
        rhs: &Value,
        lhs_binding: Option<LhsBinding>,
        lhs_dep: Option<DepList>,
        rhs_dep: Option<DepList>,
    ) -> InterpResult<()> {
        if let (Some(ld), Some(rd)) = (lhs_dep, rhs_dep) {
            if lhs_binding.is_some()
                && crate::equation::is_constant(&ld)
                && crate::equation::is_constant(&rd)
            {
                self.assign_binding(lhs_binding, rhs)?;
                return Ok(());
            }

            let equation_dep = dep_add_scaled(&ld, &rd, -1.0);
            match solve_equation(&equation_dep) {
                SolveResult::Solved { var_id, dep } => {
                    self.variables.apply_linear_solution(var_id, &dep);
                    return Ok(());
                }
                SolveResult::Redundant => return Ok(()),
                SolveResult::Inconsistent(v) => {
                    self.report_error(
                        ErrorKind::InconsistentEquation,
                        format!("Inconsistent equation residual: {v}"),
                    );
                    return Ok(());
                }
            }
        }

        if lhs_binding.is_some() {
            self.assign_binding(lhs_binding, rhs)?;
            return Ok(());
        }

        // Both sides are known — check consistency for numeric equations
        if let (Value::Numeric(a), Value::Numeric(b)) = (lhs, rhs) {
            if (a - b).abs() > 0.001 {
                self.report_error(
                    ErrorKind::InconsistentEquation,
                    format!("Inconsistent equation: {a} = {b}"),
                );
            }
        }
        Ok(())
    }

    pub(super) fn assign_binding(
        &mut self,
        lhs_binding: Option<LhsBinding>,
        rhs: &Value,
    ) -> InterpResult<()> {
        match lhs_binding {
            Some(LhsBinding::Variable { id, negated }) => {
                let assigned = Self::apply_lhs_negation(rhs, negated)?;
                self.assign_to_variable(id, &assigned);
            }
            Some(LhsBinding::Internal { idx }) => match value_to_scalar(rhs) {
                Ok(val) => self.internals.set(idx, val),
                Err(_) => {
                    self.report_error(
                        ErrorKind::TypeError,
                        format!(
                            "Internal quantity `{}` requires numeric, got {}",
                            self.internals.name(idx),
                            rhs.ty()
                        ),
                    );
                }
            },
            None => {
                if !matches!(rhs, Value::Vacuous) {
                    self.report_error(ErrorKind::InvalidExpression, "Assignment to non-variable");
                }
            }
        }
        Ok(())
    }

    fn apply_lhs_negation(rhs: &Value, negated: bool) -> InterpResult<Value> {
        if !negated {
            return Ok(rhs.clone());
        }

        match rhs {
            Value::Numeric(v) => Ok(Value::Numeric(-v)),
            Value::Pair(x, y) => Ok(Value::Pair(-x, -y)),
            Value::Color(c) => Ok(Value::Color(postmeta_graphics::types::Color::new(
                -c.r, -c.g, -c.b,
            ))),
            _ => Err(crate::error::InterpreterError::new(
                ErrorKind::TypeError,
                format!("Cannot assign negated equation to {}", rhs.ty()),
            )),
        }
    }

    /// Assign a value to a variable, handling compound types (Pair, Color).
    pub(super) fn assign_to_variable(&mut self, var_id: crate::equation::VarId, value: &Value) {
        match value {
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
                    self.variables.set_known(var_id, value.clone());
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
                    self.variables.set_known(var_id, value.clone());
                }
            }
            _ => {
                self.variables.set_known(var_id, value.clone());
            }
        }
    }
}
