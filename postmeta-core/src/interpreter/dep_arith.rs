//! Dependency-list propagation for arithmetic on unknown quantities.
//!
//! These helpers compute the `DepList` bookkeeping for multiplication,
//! division, addition/subtraction, and affine transforms so that partially
//! known expressions can participate in linear equation solving.

use crate::command::SecondaryBinaryOp;
use crate::equation::{DepList, const_dep, constant_value, dep_add_scaled, dep_scale};
use crate::error::{ErrorKind, InterpResult, InterpreterError};
use crate::types::{Type, Value};
use crate::variables::VarValue;

use super::helpers::{value_to_pair, value_to_scalar, value_to_transform};
use super::{ExprResultValue, Interpreter, LhsBinding};

impl Interpreter {
    /// Compute dependency info for multiplication (`*`).
    #[allow(clippy::too_many_lines)]
    pub(super) fn mul_deps(
        &mut self,
        val: Value,
        ty: Type,
        left_val: &Value,
        left_dep: Option<DepList>,
        left_pair_dep: Option<(DepList, DepList)>,
        right: &ExprResultValue,
    ) -> ExprResultValue {
        let left_const = left_dep.as_ref().and_then(constant_value);
        let right_const = right.dep.as_ref().and_then(constant_value);

        match val {
            Value::Numeric(_) => {
                let dep = left_const.map_or_else(
                    || {
                        let result = right_const.and_then(|factor| {
                            left_dep.as_ref().map(|d| {
                                let mut d = d.clone();
                                dep_scale(&mut d, factor);
                                d
                            })
                        });
                        // Both operands are non-constant dependents: nonlinear
                        if result.is_none()
                            && left_dep
                                .as_ref()
                                .is_some_and(|d| constant_value(d).is_none())
                            && right
                                .dep
                                .as_ref()
                                .is_some_and(|d| constant_value(d).is_none())
                        {
                            self.report_error(
                                ErrorKind::IncompatibleTypes,
                                "Nonlinear dependency in multiplication",
                            );
                        }
                        result
                    },
                    |factor| {
                        right.dep.clone().map(|mut d| {
                            dep_scale(&mut d, factor);
                            d
                        })
                    },
                );
                ExprResultValue {
                    exp: val,
                    ty,
                    dep,
                    pair_dep: None,
                }
            }
            Value::Pair(_, _) => {
                let pair_deps = match (left_val, &right.exp) {
                    (Value::Numeric(_), Value::Pair(rx, ry)) => {
                        let left_linear = left_dep
                            .as_ref()
                            .is_some_and(|d| constant_value(d).is_none());
                        let right_linear = right.pair_dep.as_ref().is_some_and(|(dx, dy)| {
                            constant_value(dx).is_none() || constant_value(dy).is_none()
                        });
                        if left_linear && right_linear {
                            self.report_error(
                                ErrorKind::IncompatibleTypes,
                                "Nonlinear dependency in multiplication",
                            );
                            None
                        } else if left_linear {
                            let dep = left_dep.unwrap_or_else(|| const_dep(0.0));
                            let mut dx = dep.clone();
                            let mut dy = dep;
                            dep_scale(&mut dx, *rx);
                            dep_scale(&mut dy, *ry);
                            Some((dx, dy))
                        } else {
                            let scalar = left_const
                                .unwrap_or_else(|| value_to_scalar(left_val).unwrap_or(0.0));
                            let (mut dx, mut dy) = right
                                .pair_dep
                                .clone()
                                .unwrap_or_else(|| (const_dep(*rx), const_dep(*ry)));
                            dep_scale(&mut dx, scalar);
                            dep_scale(&mut dy, scalar);
                            Some((dx, dy))
                        }
                    }
                    (Value::Pair(lx, ly), Value::Numeric(_)) => {
                        let left_linear = left_pair_dep.as_ref().is_some_and(|(dx, dy)| {
                            constant_value(dx).is_none() || constant_value(dy).is_none()
                        });
                        let right_linear = right
                            .dep
                            .as_ref()
                            .is_some_and(|d| constant_value(d).is_none());
                        if left_linear && right_linear {
                            self.report_error(
                                ErrorKind::IncompatibleTypes,
                                "Nonlinear dependency in multiplication",
                            );
                            None
                        } else if right_linear {
                            let dep = right.dep.clone().unwrap_or_else(|| const_dep(0.0));
                            let mut dx = dep.clone();
                            let mut dy = dep;
                            dep_scale(&mut dx, *lx);
                            dep_scale(&mut dy, *ly);
                            Some((dx, dy))
                        } else {
                            let scalar = right_const
                                .unwrap_or_else(|| value_to_scalar(&right.exp).unwrap_or(0.0));
                            let (mut dx, mut dy) =
                                left_pair_dep.unwrap_or_else(|| (const_dep(*lx), const_dep(*ly)));
                            dep_scale(&mut dx, scalar);
                            dep_scale(&mut dy, scalar);
                            Some((dx, dy))
                        }
                    }
                    _ => None,
                };
                ExprResultValue {
                    exp: val,
                    ty,
                    dep: None,
                    pair_dep: pair_deps,
                }
            }
            _ => ExprResultValue::typed(val, ty),
        }
    }

    /// Compute dependency info for division (`/`).
    pub(super) fn div_deps(
        &mut self,
        left_val: &Value,
        left_dep: Option<DepList>,
        left_pair_dep: Option<(DepList, DepList)>,
        right: &ExprResultValue,
    ) -> InterpResult<ExprResultValue> {
        let b = value_to_scalar(&right.exp)?;
        if b.abs() < f64::EPSILON {
            self.report_error(ErrorKind::ArithmeticError, "Division by zero");
            return Ok(match left_val {
                Value::Pair(_, _) => ExprResultValue {
                    exp: Value::Pair(0.0, 0.0),
                    ty: Type::PairType,
                    dep: None,
                    pair_dep: Some((const_dep(0.0), const_dep(0.0))),
                },
                _ => ExprResultValue::numeric_known(0.0),
            });
        }

        let right_is_linear = right
            .dep
            .as_ref()
            .is_some_and(|d| constant_value(d).is_none());
        if right_is_linear {
            self.report_error(
                ErrorKind::IncompatibleTypes,
                "Nonlinear dependency in division",
            );
        }

        Ok(match left_val {
            Value::Numeric(a) => {
                let divisor = right
                    .dep
                    .as_ref()
                    .and_then(constant_value)
                    .or_else(|| value_to_scalar(&right.exp).ok());
                let dep = if right_is_linear {
                    None
                } else {
                    divisor.and_then(|c| {
                        if c.abs() < f64::EPSILON {
                            None
                        } else {
                            left_dep.map(|mut d| {
                                dep_scale(&mut d, 1.0 / c);
                                d
                            })
                        }
                    })
                };
                ExprResultValue {
                    exp: Value::Numeric(a / b),
                    ty: Type::Known,
                    dep,
                    pair_dep: None,
                }
            }
            Value::Pair(x, y) => {
                let pair_dep = if right_is_linear {
                    None
                } else {
                    let (mut dx, mut dy) =
                        left_pair_dep.unwrap_or_else(|| (const_dep(*x), const_dep(*y)));
                    dep_scale(&mut dx, 1.0 / b);
                    dep_scale(&mut dy, 1.0 / b);
                    Some((dx, dy))
                };
                ExprResultValue {
                    exp: Value::Pair(x / b, y / b),
                    ty: Type::PairType,
                    dep: None,
                    pair_dep,
                }
            }
            _ => {
                return Err(InterpreterError::new(
                    ErrorKind::TypeError,
                    format!(
                        "Invalid types for /: {} and {}",
                        left_val.ty(),
                        right.exp.ty()
                    ),
                ));
            }
        })
    }

    /// Compute dependency info for addition/subtraction (`+`, `-`).
    pub(super) fn add_sub_deps(
        val: Value,
        ty: Type,
        factor: f64,
        left_val: &Value,
        left_dep: Option<DepList>,
        left_pair_dep: Option<(DepList, DepList)>,
        right: &ExprResultValue,
    ) -> ExprResultValue {
        if matches!(val, Value::Pair(_, _)) {
            let (lx, ly) = if let Value::Pair(x, y) = left_val {
                (*x, *y)
            } else {
                (0.0, 0.0)
            };
            let (rx, ry) = if let Value::Pair(x, y) = &right.exp {
                (*x, *y)
            } else {
                (0.0, 0.0)
            };
            let (ldx, ldy) = left_pair_dep.unwrap_or_else(|| (const_dep(lx), const_dep(ly)));
            let (rdx, rdy) = right
                .pair_dep
                .clone()
                .unwrap_or_else(|| (const_dep(rx), const_dep(ry)));
            ExprResultValue {
                exp: val,
                ty,
                dep: None,
                pair_dep: Some((
                    dep_add_scaled(&ldx, &rdx, factor),
                    dep_add_scaled(&ldy, &rdy, factor),
                )),
            }
        } else {
            let dep = if matches!((left_dep.as_ref(), right.dep.as_ref()), (None, None)) {
                None
            } else {
                let left_numeric = if let Value::Numeric(v) = left_val {
                    *v
                } else {
                    0.0
                };
                let right_numeric = if let Value::Numeric(v) = &right.exp {
                    *v
                } else {
                    0.0
                };

                let left_dep = left_dep.unwrap_or_else(|| const_dep(left_numeric));
                let right_dep = right
                    .dep
                    .clone()
                    .unwrap_or_else(|| const_dep(right_numeric));
                Some(dep_add_scaled(&left_dep, &right_dep, factor))
            };
            ExprResultValue {
                exp: val,
                ty,
                dep,
                pair_dep: None,
            }
        }
    }

    /// Compute pair dependency info for non-`*` secondary ops (transforms).
    #[allow(clippy::too_many_arguments)]
    pub(super) fn transform_deps(
        &mut self,
        val: Value,
        ty: Type,
        op: SecondaryBinaryOp,
        left_val: &Value,
        left_pair_dep: Option<(DepList, DepList)>,
        right: &ExprResultValue,
        right_binding: Option<&LhsBinding>,
    ) -> ExprResultValue {
        let pair_dep = if matches!(val, Value::Pair(_, _)) {
            let base_dep = left_pair_dep.or_else(|| {
                if let Value::Pair(lx, ly) = left_val {
                    Some((const_dep(*lx), const_dep(*ly)))
                } else {
                    None
                }
            });

            base_dep.map(|(ldx, ldy)| {
                // Unknown transform: propagate component deps individually
                if op == SecondaryBinaryOp::Transformed
                    && let Some(LhsBinding::Variable { id, .. }) = right_binding
                    && let VarValue::Transform {
                        tx,
                        ty: ty_id,
                        txx,
                        txy,
                        tyx,
                        tyy,
                    } = self.state.variables.get(*id).clone()
                {
                    let (lx, ly) = if let Value::Pair(lx, ly) = left_val {
                        (*lx, *ly)
                    } else {
                        (0.0, 0.0)
                    };

                    let mut dep_x = self.numeric_dep_for_var(tx);
                    dep_x = dep_add_scaled(&dep_x, &self.numeric_dep_for_var(txx), lx);
                    dep_x = dep_add_scaled(&dep_x, &self.numeric_dep_for_var(txy), ly);

                    let mut dep_y = self.numeric_dep_for_var(ty_id);
                    dep_y = dep_add_scaled(&dep_y, &self.numeric_dep_for_var(tyx), lx);
                    dep_y = dep_add_scaled(&dep_y, &self.numeric_dep_for_var(tyy), ly);

                    return (dep_x, dep_y);
                }

                // Known transform: apply affine transform to dep lists
                let t = Self::secondary_op_to_transform(op, &right.exp);

                let mut new_x = ldx.clone();
                dep_scale(&mut new_x, t.txx);
                new_x = dep_add_scaled(&new_x, &ldy, t.txy);
                new_x = dep_add_scaled(&new_x, &const_dep(t.tx), 1.0);

                let mut new_y = ldx;
                dep_scale(&mut new_y, t.tyx);
                new_y = dep_add_scaled(&new_y, &ldy, t.tyy);
                new_y = dep_add_scaled(&new_y, &const_dep(t.ty), 1.0);

                (new_x, new_y)
            })
        } else {
            None
        };
        ExprResultValue {
            exp: val,
            ty,
            dep: None,
            pair_dep,
        }
    }

    /// Convert a secondary binary op + RHS value into a concrete transform.
    fn secondary_op_to_transform(
        op: SecondaryBinaryOp,
        right: &Value,
    ) -> postmeta_graphics::types::Transform {
        use postmeta_graphics::types::Transform;

        match op {
            SecondaryBinaryOp::Scaled => Transform::scaled(value_to_scalar(right).unwrap_or(1.0)),
            SecondaryBinaryOp::Shifted => {
                let (dx, dy) = value_to_pair(right).unwrap_or((0.0, 0.0));
                Transform::shifted(dx, dy)
            }
            SecondaryBinaryOp::Rotated => Transform::rotated(value_to_scalar(right).unwrap_or(0.0)),
            SecondaryBinaryOp::XScaled => Transform::xscaled(value_to_scalar(right).unwrap_or(1.0)),
            SecondaryBinaryOp::YScaled => Transform::yscaled(value_to_scalar(right).unwrap_or(1.0)),
            SecondaryBinaryOp::Slanted => Transform::slanted(value_to_scalar(right).unwrap_or(0.0)),
            SecondaryBinaryOp::ZScaled => {
                let (a, b) = value_to_pair(right).unwrap_or((1.0, 0.0));
                Transform::zscaled(a, b)
            }
            SecondaryBinaryOp::Transformed => {
                value_to_transform(right).unwrap_or(Transform::IDENTITY)
            }
            SecondaryBinaryOp::Times | SecondaryBinaryOp::Over | SecondaryBinaryOp::Infont => {
                Transform::IDENTITY
            }
        }
    }
}
