//! Equation and assignment logic.
//!
//! Handles `lhs = rhs` equations (including unknown-variable assignment)
//! and `:=` explicit assignments.

use crate::equation::{
    const_dep, dep_add_scaled, dep_substitute, solve_equation, DepList, SolveResult,
};
use crate::error::{ErrorKind, InterpResult};
use crate::types::Value;
use crate::variables::{NumericState, VarValue};

use super::helpers::value_to_scalar;
use super::{Interpreter, LhsBinding};

impl Interpreter {
    fn reduce_dep_with_knowns(&self, dep: DepList) -> DepList {
        let mut reduced = dep;

        loop {
            let mut changed = false;
            let vars: Vec<_> = reduced.iter().filter_map(|t| t.var_id).collect();

            for id in vars {
                if !reduced.iter().any(|t| t.var_id == Some(id)) {
                    continue;
                }

                match self.variables.get(id) {
                    VarValue::NumericVar(NumericState::Known(v)) => {
                        reduced = dep_substitute(&reduced, id, &const_dep(*v));
                        changed = true;
                    }
                    VarValue::NumericVar(NumericState::Dependent(dep)) => {
                        reduced = dep_substitute(&reduced, id, dep);
                        changed = true;
                    }
                    _ => {}
                }
            }

            if !changed {
                break;
            }
        }

        reduced
    }

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
        lhs_deps: (Option<DepList>, Option<(DepList, DepList)>),
        rhs_deps: (Option<DepList>, Option<(DepList, DepList)>),
    ) -> InterpResult<()> {
        let (lhs_dep, lhs_pair_dep) = lhs_deps;
        let (rhs_dep, rhs_pair_dep) = rhs_deps;

        if let (Some((lx, ly)), Some((rx, ry))) = (lhs_pair_dep, rhs_pair_dep) {
            let eqx = self.reduce_dep_with_knowns(dep_add_scaled(&lx, &rx, -1.0));
            match solve_equation(&eqx) {
                SolveResult::Solved { var_id, dep } => {
                    self.variables.apply_linear_solution(var_id, &dep);
                }
                SolveResult::Redundant => {}
                SolveResult::Inconsistent(v) => {
                    self.report_error(
                        ErrorKind::InconsistentEquation,
                        format!("Inconsistent pair equation residual (x): {v}"),
                    );
                }
            }

            let eqy = self.reduce_dep_with_knowns(dep_add_scaled(&ly, &ry, -1.0));
            match solve_equation(&eqy) {
                SolveResult::Solved { var_id, dep } => {
                    self.variables.apply_linear_solution(var_id, &dep);
                }
                SolveResult::Redundant => {}
                SolveResult::Inconsistent(v) => {
                    self.report_error(
                        ErrorKind::InconsistentEquation,
                        format!("Inconsistent pair equation residual (y): {v}"),
                    );
                }
            }
            return Ok(());
        }

        if let (Some(ld), Some(rd)) = (lhs_dep, rhs_dep) {
            if lhs_binding.is_some()
                && crate::equation::is_constant(&ld)
                && crate::equation::is_constant(&rd)
            {
                self.assign_binding(lhs_binding, rhs)?;
                return Ok(());
            }

            let equation_dep = self.reduce_dep_with_knowns(dep_add_scaled(&ld, &rd, -1.0));
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
            Some(LhsBinding::Pair { x, y }) => {
                if let Value::Pair(rx, ry) = rhs {
                    if let Some(bx) = x {
                        self.assign_binding(Some(*bx), &Value::Numeric(*rx))?;
                    }
                    if let Some(by) = y {
                        self.assign_binding(Some(*by), &Value::Numeric(*ry))?;
                    }
                } else {
                    self.report_error(
                        ErrorKind::TypeError,
                        format!("Pair equation requires pair RHS, got {}", rhs.ty()),
                    );
                }
            }
            Some(LhsBinding::Color { r, g, b }) => {
                if let Value::Color(c) = rhs {
                    if let Some(br) = r {
                        self.assign_binding(Some(*br), &Value::Numeric(c.r))?;
                    }
                    if let Some(bg) = g {
                        self.assign_binding(Some(*bg), &Value::Numeric(c.g))?;
                    }
                    if let Some(bb) = b {
                        self.assign_binding(Some(*bb), &Value::Numeric(c.b))?;
                    }
                } else {
                    self.report_error(
                        ErrorKind::TypeError,
                        format!("Color equation requires color RHS, got {}", rhs.ty()),
                    );
                }
            }
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
        let currentpicture_id = self.variables.lookup_existing("currentpicture");

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

        if Some(var_id) == currentpicture_id {
            if let Value::Picture(p) = value {
                self.current_picture = p.clone();
            }
        }
    }
}
