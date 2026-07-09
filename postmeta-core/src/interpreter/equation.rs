//! Equation and assignment logic — the stateful side of equation solving.
//!
//! Handles `lhs = rhs` equations (including unknown-variable assignment) and `:=` explicit assignments.
//! Compound types (pair, color, transform) split into one equation per component, driven by [`Type::components`](crate::types::Type::components).
//!
//! The pure dependency-list algebra lives in [`crate::equation`]; this module is its interpreter-facing client.
//! `reduce_dep_with_knowns` stays here because substitution reads the variable store to discover which variables became known or dependent.

use crate::equation::{
    DepList, SolveResult, const_dep, dep_add_scaled, dep_scale, dep_substitute, solve_equation,
};
use crate::error::{ErrorKind, InterpResult};
use crate::types::Type;
use crate::types::Value;
use crate::variables::{NumericState, VarValue};

use super::helpers::value_to_scalar;
use super::{Interpreter, LhsBinding};

/// Numeric components of a known compound value, in storage order (matching [`Type::component_suffixes`])
fn value_components(value: &Value) -> Option<Vec<f64>> {
    match value {
        Value::Pair(x, y) => Some(vec![*x, *y]),
        Value::Color(c) => Some(vec![c.r, c.g, c.b]),
        Value::Transform(t) => Some(vec![t.tx, t.ty, t.txx, t.txy, t.tyx, t.tyy]),
        _ => None,
    }
}

/// Human-readable kind for compound-equation error messages
const fn compound_kind(ty: Type) -> &'static str {
    match ty {
        Type::PairType => "pair",
        Type::ColorType => "color",
        Type::TransformType => "transform",
        _ => "compound",
    }
}

impl Interpreter {
    /// Substitute known and dependent variables in `dep` until only independent variables (or a constant) remain
    fn reduce_dep_with_knowns(&mut self, dep: DepList) -> DepList {
        const MAX_REDUCTION_PASSES: usize = 1024;
        let mut reduced = dep;

        // Repeat because one substitution may introduce another known/dependent variable into the dep list
        for _ in 0..MAX_REDUCTION_PASSES {
            let mut substitutions = Vec::new();
            for term in &reduced {
                let Some(id) = term.var_id else { continue };
                match self.state.variables.get(id) {
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
                self.state.variables.apply_linear_solution(var_id, &dep);
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

    /// Dependency lists for each numeric component of one equation side, in storage order.
    ///
    /// Three sources, tried in order:
    /// 1. expression-level pair dependencies (pairs only — the expression pipeline tracks components for pairs);
    /// 2. a bare compound variable reference: each component variable's dependency (negated for `-v` forms);
    /// 3. a known compound value: constant dependencies.
    ///
    /// Returns `None` when the side has no component representation; the caller then falls back to scalar or assignment handling.
    fn side_component_deps(
        &mut self,
        value: &Value,
        binding: Option<&LhsBinding>,
        pair_dep: Option<&(DepList, DepList)>,
    ) -> Option<Vec<DepList>> {
        if let Some((dx, dy)) = pair_dep {
            return Some(vec![dx.clone(), dy.clone()]);
        }

        // The parser clears the binding for anything but a bare (possibly negated) variable reference, so a Variable binding here means the whole side IS that variable
        if let Some(LhsBinding::Variable { id, negated }) = binding {
            let n = value.ty().components()?;
            let ids = self.state.variables.get(*id).component_ids()?;
            if ids.len() == n {
                let mut deps: Vec<DepList> =
                    ids.iter().map(|c| self.numeric_dep_for_var(*c)).collect();
                if *negated {
                    for dep in &mut deps {
                        dep_scale(dep, -1.0);
                    }
                }
                return Some(deps);
            }
        }

        value_components(value).map(|cs| cs.into_iter().map(const_dep).collect())
    }

    /// Execute an equation: `lhs = rhs`.
    ///
    /// Compound types (pair, color, transform) are solved component-wise.
    /// A bindable LHS (`x`, `-x`, internal quantity) is treated as an assignment target.
    /// Otherwise numeric consistency is checked.
    pub(super) fn do_equation(
        &mut self,
        lhs: &Value,
        rhs: &Value,
        lhs_binding: Option<LhsBinding>,
        rhs_binding: Option<&LhsBinding>,
        lhs_deps: (Option<DepList>, Option<(DepList, DepList)>),
        rhs_deps: (Option<DepList>, Option<(DepList, DepList)>),
    ) -> InterpResult<()> {
        let (lhs_dep, lhs_pair_dep) = lhs_deps;
        let (rhs_dep, rhs_pair_dep) = rhs_deps;

        // Component-wise solving for compound types: one equation per component, in storage order (x-then-y for pairs)
        if lhs.ty().is_compound() || rhs.ty().is_compound() {
            let lhs_comps =
                self.side_component_deps(lhs, lhs_binding.as_ref(), lhs_pair_dep.as_ref());
            let rhs_comps = self.side_component_deps(rhs, rhs_binding, rhs_pair_dep.as_ref());
            if let (Some(lhs_comps), Some(rhs_comps)) = (lhs_comps, rhs_comps)
                && lhs_comps.len() == rhs_comps.len()
            {
                let ty = if lhs.ty().is_compound() {
                    lhs.ty()
                } else {
                    rhs.ty()
                };
                let kind = compound_kind(ty);
                let labels = ty.component_suffixes();
                for ((ld, rd), label) in lhs_comps.iter().zip(&rhs_comps).zip(labels) {
                    let eq = self.reduce_dep_with_knowns(dep_add_scaled(ld, rd, -1.0));
                    self.apply_solve_result(
                        solve_equation(&eq),
                        &format!("Inconsistent {kind} equation residual ({label})"),
                    );
                }
                return Ok(());
            }
        }

        if let (Some(ld), Some(rd)) = (lhs_dep.as_ref(), rhs_dep.as_ref()) {
            let equation_dep = self.reduce_dep_with_knowns(dep_add_scaled(ld, rd, -1.0));
            self.apply_solve_result(
                solve_equation(&equation_dep),
                "Inconsistent equation residual",
            );
            return Ok(());
        }

        // A numeric side with missing deps lost them to nonlinearity, so do NOT silently assign the junk value.
        // The nonlinearity error is reported at the operation site (mul_deps).
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
                Ok(val) => self.state.internals.set(idx, val),
                Err(_) => {
                    self.report_error(
                        ErrorKind::TypeError,
                        format!(
                            "Internal quantity `{}` requires numeric, got {}",
                            self.state.internals.name(idx),
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

    /// Assign a value to a variable.
    ///
    /// When variable and value are compound of the same width (pair, color, transform), each component variable is set to its known component value.
    /// Otherwise the value is stored on the variable itself.
    pub(super) fn assign_to_variable(&mut self, var_id: crate::equation::VarId, value: &Value) {
        if let Value::Numeric(v) = value {
            self.state
                .variables
                .set(var_id, VarValue::NumericVar(NumericState::Known(*v)));
        } else if let (Some(ids), Some(vals)) = (
            self.state.variables.get(var_id).component_ids(),
            value_components(value),
        ) && ids.len() == vals.len()
        {
            for (id, v) in ids.into_iter().zip(vals) {
                self.state
                    .variables
                    .set(id, VarValue::NumericVar(NumericState::Known(v)));
            }
        } else {
            self.state.variables.set_known(var_id, value.clone());
        }

        self.state
            .picture_manager
            .sync_runtime_for_picture_assignment(&self.state.variables, var_id, value);
    }
}
