//! Equation and assignment logic.
//!
//! Handles `lhs = rhs` equations (including unknown-variable assignment)
//! and `:=` explicit assignments.

use crate::error::{ErrorKind, InterpResult};
use crate::types::Value;
use crate::variables::{NumericState, VarValue};

use super::helpers::value_to_scalar;
use super::Interpreter;

impl Interpreter {
    /// Execute an equation: `lhs = rhs`.
    ///
    /// If the LHS is an unknown variable, treat as assignment (`var = val`).
    /// If both sides are known numerics, check consistency.
    /// Full dependency-list equation solving is deferred.
    pub(super) fn do_equation(&mut self, lhs: &Value, rhs: &Value) -> InterpResult<()> {
        // Check if the LHS was an unknown variable — if so, treat equation
        // as assignment.  This covers `mm = 2.83464`, `origin = (0,0)`, etc.
        let lhs_is_unknown = self
            .last_var_id
            .is_some_and(|id| self.variables.is_unknown(id));

        if lhs_is_unknown {
            if let Some(var_id) = self.last_var_id {
                self.assign_to_variable(var_id, rhs);
                return Ok(());
            }
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

        // If we tracked a variable on the LHS, also assign
        if let Some(var_id) = self.last_var_id {
            self.assign_to_variable(var_id, rhs);
        }
        Ok(())
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

    /// Execute an assignment: `var := expr`.
    pub(super) fn do_assignment(&mut self, _lhs: &Value) -> InterpResult<()> {
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
}
