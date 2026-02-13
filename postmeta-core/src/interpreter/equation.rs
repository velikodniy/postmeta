//! Equation and assignment logic.
//!
//! Handles `lhs = rhs` equations (including unknown-variable assignment)
//! and `:=` explicit assignments.

use crate::equation::{
    DepList, SolveResult, const_dep, dep_add_scaled, dep_substitute, solve_equation,
};
use crate::error::{ErrorKind, InterpResult};
use crate::types::Value;
use crate::variables::{NumericState, VarValue};

use super::helpers::value_to_scalar;
use super::{Interpreter, LhsBinding};

impl Interpreter {
    /// Substitute all known and dependent variables in `dep` until only
    /// independent variables (or a constant) remain.
    fn reduce_dep_with_knowns(&mut self, dep: DepList) -> DepList {
        const MAX_REDUCTION_PASSES: usize = 1024;
        let mut reduced = dep;

        // Repeat because substituting one dependent variable may introduce
        // another known/dependent variable into the dep list.
        for _ in 0..MAX_REDUCTION_PASSES {
            let mut substitutions = Vec::new();
            for term in &reduced {
                let Some(id) = term.var_id else { continue };
                match self.variables.get(id) {
                    VarValue::NumericVar(NumericState::Known(v)) => {
                        substitutions.push((id, const_dep(*v)));
                    }
                    VarValue::NumericVar(NumericState::Dependent(sub)) => {
                        substitutions.push((id, sub.clone()));
                    }
                    _ => {}
                }
            }

            if substitutions.is_empty() {
                return reduced;
            }

            for (id, replacement) in substitutions {
                reduced = dep_substitute(&reduced, id, &replacement);
            }
        }

        self.report_error(
            ErrorKind::Internal,
            "Dependency reduction exceeded iteration limit; possible cycle in equation dependencies",
        );

        reduced
    }

    fn apply_solve_result(&mut self, result: SolveResult, inconsistent_context: &str) {
        match result {
            SolveResult::Solved { var_id, dep } => {
                self.variables.apply_linear_solution(var_id, &dep);
            }
            SolveResult::Redundant => {}
            SolveResult::Inconsistent(v) => {
                self.report_error(
                    ErrorKind::InconsistentEquation,
                    format!("{inconsistent_context}: {v}"),
                );
            }
        }
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
            self.apply_solve_result(
                solve_equation(&eqx),
                "Inconsistent pair equation residual (x)",
            );

            let eqy = self.reduce_dep_with_knowns(dep_add_scaled(&ly, &ry, -1.0));
            self.apply_solve_result(
                solve_equation(&eqy),
                "Inconsistent pair equation residual (y)",
            );
            return Ok(());
        }

        if let (Some(ld), Some(rd)) = (lhs_dep.as_ref(), rhs_dep.as_ref()) {
            let equation_dep = self.reduce_dep_with_knowns(dep_add_scaled(ld, rd, -1.0));
            self.apply_solve_result(
                solve_equation(&equation_dep),
                "Inconsistent equation residual",
            );
            return Ok(());
        }

        // If one side is numeric with missing deps (nonlinear result) and the
        // equation has a bindable LHS, do NOT silently assign — the deps were
        // lost due to nonlinearity.  Nonlinear dependency errors are reported
        // at the operation site (mul_deps); here we just prevent silent
        // assignment of the junk value.
        if matches!((lhs, rhs), (Value::Numeric(_), Value::Numeric(_)))
            && (lhs_dep.is_none() || rhs_dep.is_none())
        {
            return Ok(());
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

        if let Value::Picture(p) = value
            && self
                .variables
                .lookup_existing("currentpicture")
                .is_some_and(|id| id == var_id)
        {
            self.picture_state.current_picture = p.clone();
        }
    }
}
