//! Operator dispatch.
//!
//! Implements all nullary, unary, and binary operators at each precedence level.

use std::sync::Arc;

use kurbo::Point;

use postmeta_graphics::math;
use postmeta_graphics::path;
use postmeta_graphics::pen;
use postmeta_graphics::transform;
use postmeta_graphics::types::{Color, Picture, Transform};

use crate::command::{
    ExpressionBinaryOp, NullaryOp, PlusMinusOp, PrimaryBinaryOp, SecondaryBinaryOp,
    TertiaryBinaryOp, UnaryOp,
};
use crate::error::{ErrorKind, InterpResult, InterpreterError};
use crate::types::{Type, Value};

use super::helpers::{
    value_to_bool, value_to_pair, value_to_path, value_to_pen, value_to_scalar, value_to_string,
    value_to_transform, values_equal,
};
use super::Interpreter;

impl Interpreter {
    /// Execute a nullary operator.
    pub(super) fn do_nullary(&mut self, op: u16) -> InterpResult<()> {
        match op {
            x if x == NullaryOp::True as u16 => {
                self.cur_exp = Value::Boolean(true);
                self.cur_type = Type::Boolean;
            }
            x if x == NullaryOp::False as u16 => {
                self.cur_exp = Value::Boolean(false);
                self.cur_type = Type::Boolean;
            }
            x if x == NullaryOp::NullPicture as u16 => {
                self.cur_exp = Value::Picture(Picture::new());
                self.cur_type = Type::Picture;
            }
            x if x == NullaryOp::NullPen as u16 => {
                self.cur_exp = Value::Pen(pen::nullpen());
                self.cur_type = Type::Pen;
            }
            x if x == NullaryOp::PenCircle as u16 => {
                self.cur_exp = Value::Pen(pen::pencircle(1.0));
                self.cur_type = Type::Pen;
            }
            x if x == NullaryOp::NormalDeviate as u16 => {
                self.cur_exp = Value::Numeric(math::normal_deviate(&mut self.random_seed));
                self.cur_type = Type::Known;
            }
            x if x == NullaryOp::JobName as u16 => {
                self.cur_exp = Value::String(Arc::from(self.job_name.as_str()));
                self.cur_type = Type::String;
            }
            _ => {
                self.cur_exp = Value::Vacuous;
                self.cur_type = Type::Vacuous;
            }
        }
        Ok(())
    }

    /// Execute a unary operator on `cur_exp`.
    #[expect(clippy::too_many_lines, reason = "matching all unary ops")]
    pub(super) fn do_unary(&mut self, op: u16) -> InterpResult<()> {
        match op {
            x if x == UnaryOp::Not as u16 => {
                let b = value_to_bool(&self.cur_exp)?;
                self.cur_exp = Value::Boolean(!b);
                self.cur_type = Type::Boolean;
            }
            x if x == UnaryOp::Sqrt as u16 => {
                let v = value_to_scalar(&self.cur_exp)?;
                self.cur_exp = Value::Numeric(if v >= 0.0 { v.sqrt() } else { 0.0 });
                self.cur_type = Type::Known;
            }
            x if x == UnaryOp::SinD as u16 => {
                let v = value_to_scalar(&self.cur_exp)?;
                self.cur_exp = Value::Numeric(math::sind(v));
                self.cur_type = Type::Known;
            }
            x if x == UnaryOp::CosD as u16 => {
                let v = value_to_scalar(&self.cur_exp)?;
                self.cur_exp = Value::Numeric(math::cosd(v));
                self.cur_type = Type::Known;
            }
            x if x == UnaryOp::Floor as u16 => {
                let v = value_to_scalar(&self.cur_exp)?;
                self.cur_exp = Value::Numeric(math::floor(v));
                self.cur_type = Type::Known;
            }
            x if x == UnaryOp::MExp as u16 => {
                let v = value_to_scalar(&self.cur_exp)?;
                self.cur_exp = Value::Numeric(math::mexp(v));
                self.cur_type = Type::Known;
            }
            x if x == UnaryOp::MLog as u16 => {
                let v = value_to_scalar(&self.cur_exp)?;
                self.cur_exp = Value::Numeric(math::mlog(v));
                self.cur_type = Type::Known;
            }
            x if x == UnaryOp::Angle as u16 => {
                let (px, py) = value_to_pair(&self.cur_exp)?;
                self.cur_exp = Value::Numeric(math::angle(px, py));
                self.cur_type = Type::Known;
            }
            x if x == UnaryOp::UniformDeviate as u16 => {
                let v = value_to_scalar(&self.cur_exp)?;
                self.cur_exp = Value::Numeric(math::uniform_deviate(v, &mut self.random_seed));
                self.cur_type = Type::Known;
            }
            x if x == UnaryOp::Length as u16 => {
                match &self.cur_exp {
                    Value::Path(p) => {
                        self.cur_exp = Value::Numeric(p.length() as f64);
                    }
                    Value::String(s) => {
                        self.cur_exp = Value::Numeric(s.len() as f64);
                    }
                    Value::Pair(x, y) => {
                        // abs(pair) = sqrt(x^2 + y^2)
                        self.cur_exp = Value::Numeric(x.hypot(*y));
                    }
                    _ => {
                        return Err(InterpreterError::new(
                            ErrorKind::TypeError,
                            "length requires path, string, or pair",
                        ));
                    }
                }
                self.cur_type = Type::Known;
            }
            x if x == UnaryOp::Decimal as u16 => {
                let v = value_to_scalar(&self.cur_exp)?;
                self.cur_exp = Value::String(Arc::from(format!("{v}").as_str()));
                self.cur_type = Type::String;
            }
            x if x == UnaryOp::Reverse as u16 => {
                if let Value::Path(ref p) = self.cur_exp {
                    self.cur_exp = Value::Path(path::reverse(p));
                    self.cur_type = Type::Path;
                } else {
                    return Err(InterpreterError::new(
                        ErrorKind::TypeError,
                        "reverse requires a path",
                    ));
                }
            }
            x if x == UnaryOp::XPart as u16 => {
                self.extract_part(0)?;
            }
            x if x == UnaryOp::YPart as u16 => {
                self.extract_part(1)?;
            }
            x if x == UnaryOp::XXPart as u16 => {
                self.extract_part(2)?;
            }
            x if x == UnaryOp::XYPart as u16 => {
                self.extract_part(3)?;
            }
            x if x == UnaryOp::YXPart as u16 => {
                self.extract_part(4)?;
            }
            x if x == UnaryOp::YYPart as u16 => {
                self.extract_part(5)?;
            }
            x if x == UnaryOp::RedPart as u16 => {
                self.extract_color_part(0)?;
            }
            x if x == UnaryOp::GreenPart as u16 => {
                self.extract_color_part(1)?;
            }
            x if x == UnaryOp::BluePart as u16 => {
                self.extract_color_part(2)?;
            }
            x if x == UnaryOp::MakePath as u16 => {
                if let Value::Pen(ref p) = self.cur_exp {
                    self.cur_exp = Value::Path(pen::makepath(p));
                    self.cur_type = Type::Path;
                } else {
                    return Err(InterpreterError::new(
                        ErrorKind::TypeError,
                        "makepath requires a pen",
                    ));
                }
            }
            x if x == UnaryOp::MakePen as u16 => {
                if let Value::Path(ref p) = self.cur_exp {
                    let result = pen::makepen(p).map_err(|e| {
                        InterpreterError::new(ErrorKind::TypeError, format!("makepen: {e}"))
                    })?;
                    self.cur_exp = Value::Pen(result);
                    self.cur_type = Type::Pen;
                } else {
                    return Err(InterpreterError::new(
                        ErrorKind::TypeError,
                        "makepen requires a path",
                    ));
                }
            }
            x if x == UnaryOp::CycleOp as u16 => {
                let is_cyclic = matches!(&self.cur_exp, Value::Path(p) if p.is_cyclic);
                self.cur_exp = Value::Boolean(is_cyclic);
                self.cur_type = Type::Boolean;
            }
            _ => {
                // Unimplemented unary — leave cur_exp unchanged
            }
        }
        Ok(())
    }

    /// Execute an "X of Y" binary operator.
    pub(super) fn do_primary_binary(&mut self, op: u16, first: &Value) -> InterpResult<()> {
        let second = &self.cur_exp;

        match op {
            x if x == PrimaryBinaryOp::PointOf as u16 => {
                let t = value_to_scalar(first)?;
                let p = value_to_path(second)?;
                let pt = path::point_of(p, t);
                self.cur_exp = Value::Pair(pt.x, pt.y);
                self.cur_type = Type::PairType;
            }
            x if x == PrimaryBinaryOp::DirectionOf as u16 => {
                let t = value_to_scalar(first)?;
                let p = value_to_path(second)?;
                let dir = path::direction_of(p, t);
                self.cur_exp = Value::Pair(dir.x, dir.y);
                self.cur_type = Type::PairType;
            }
            x if x == PrimaryBinaryOp::PrecontrolOf as u16 => {
                let t = value_to_scalar(first)?;
                let p = value_to_path(second)?;
                let pt = path::precontrol_of(p, t);
                self.cur_exp = Value::Pair(pt.x, pt.y);
                self.cur_type = Type::PairType;
            }
            x if x == PrimaryBinaryOp::PostcontrolOf as u16 => {
                let t = value_to_scalar(first)?;
                let p = value_to_path(second)?;
                let pt = path::postcontrol_of(p, t);
                self.cur_exp = Value::Pair(pt.x, pt.y);
                self.cur_type = Type::PairType;
            }
            x if x == PrimaryBinaryOp::SubpathOf as u16 => {
                let (t1, t2) = value_to_pair(first)?;
                let p = value_to_path(second)?;
                self.cur_exp = Value::Path(path::subpath(p, t1, t2));
                self.cur_type = Type::Path;
            }
            x if x == PrimaryBinaryOp::PenOffsetOf as u16 => {
                let (dx, dy) = value_to_pair(first)?;
                let p = value_to_pen(second)?;
                let pt = pen::penoffset(p, kurbo::Vec2::new(dx, dy));
                self.cur_exp = Value::Pair(pt.x, pt.y);
                self.cur_type = Type::PairType;
            }
            _ => {
                self.report_error(ErrorKind::InvalidExpression, "Unimplemented primary binary");
            }
        }
        Ok(())
    }

    /// Execute a secondary binary operator.
    pub(super) fn do_secondary_binary(&mut self, op: u16, left: &Value) -> InterpResult<()> {
        let right = self.take_cur_exp();

        match op {
            x if x == SecondaryBinaryOp::Times as u16 => {
                // Scalar * scalar, or scalar * pair, or pair * scalar
                match (left, &right) {
                    (Value::Numeric(a), Value::Numeric(b)) => {
                        self.cur_exp = Value::Numeric(a * b);
                        self.cur_type = Type::Known;
                    }
                    (Value::Numeric(a), Value::Pair(bx, by)) => {
                        self.cur_exp = Value::Pair(a * bx, a * by);
                        self.cur_type = Type::PairType;
                    }
                    (Value::Pair(ax, ay), Value::Numeric(b)) => {
                        self.cur_exp = Value::Pair(ax * b, ay * b);
                        self.cur_type = Type::PairType;
                    }
                    _ => {
                        return Err(InterpreterError::new(
                            ErrorKind::TypeError,
                            "Invalid types for *",
                        ));
                    }
                }
            }
            x if x == SecondaryBinaryOp::Scaled as u16 => {
                let factor = value_to_scalar(&right)?;
                self.apply_transform(left, &transform::scaled(factor))?;
            }
            x if x == SecondaryBinaryOp::Shifted as u16 => {
                let (dx, dy) = value_to_pair(&right)?;
                self.apply_transform(left, &transform::shifted(dx, dy))?;
            }
            x if x == SecondaryBinaryOp::Rotated as u16 => {
                let angle = value_to_scalar(&right)?;
                self.apply_transform(left, &transform::rotated(angle))?;
            }
            x if x == SecondaryBinaryOp::XScaled as u16 => {
                let factor = value_to_scalar(&right)?;
                self.apply_transform(left, &transform::xscaled(factor))?;
            }
            x if x == SecondaryBinaryOp::YScaled as u16 => {
                let factor = value_to_scalar(&right)?;
                self.apply_transform(left, &transform::yscaled(factor))?;
            }
            x if x == SecondaryBinaryOp::Slanted as u16 => {
                let factor = value_to_scalar(&right)?;
                self.apply_transform(left, &transform::slanted(factor))?;
            }
            x if x == SecondaryBinaryOp::ZScaled as u16 => {
                let (a, b) = value_to_pair(&right)?;
                self.apply_transform(left, &transform::zscaled(a, b))?;
            }
            x if x == SecondaryBinaryOp::Transformed as u16 => {
                let t = value_to_transform(&right)?;
                self.apply_transform(left, &t)?;
            }
            x if x == SecondaryBinaryOp::DotProd as u16 => {
                let (ax, ay) = value_to_pair(left)?;
                let (bx, by) = value_to_pair(&right)?;
                self.cur_exp = Value::Numeric(ax.mul_add(bx, ay * by));
                self.cur_type = Type::Known;
            }
            _ => {
                self.report_error(
                    ErrorKind::InvalidExpression,
                    "Unimplemented secondary binary",
                );
            }
        }
        Ok(())
    }

    /// Apply a transform to a value and set `cur_exp`.
    fn apply_transform(&mut self, val: &Value, t: &Transform) -> InterpResult<()> {
        match val {
            Value::Pair(x, y) => {
                let pt = transform::transform_point(t, Point::new(*x, *y));
                self.cur_exp = Value::Pair(pt.x, pt.y);
                self.cur_type = Type::PairType;
            }
            Value::Path(p) => {
                self.cur_exp = Value::Path(transform::transform_path(t, p));
                self.cur_type = Type::Path;
            }
            Value::Pen(p) => {
                self.cur_exp = Value::Pen(transform::transform_pen(t, p));
                self.cur_type = Type::Pen;
            }
            Value::Picture(p) => {
                self.cur_exp = Value::Picture(transform::transform_picture(t, p));
                self.cur_type = Type::Picture;
            }
            Value::Transform(existing) => {
                self.cur_exp = Value::Transform(transform::compose(existing, t));
                self.cur_type = Type::TransformType;
            }
            _ => {
                // For unknown/numeric values (e.g., in equation context), leave unchanged
                self.report_error(
                    ErrorKind::TypeError,
                    format!("Cannot transform {}", val.ty()),
                );
            }
        }
        Ok(())
    }

    /// Execute plus or minus on two operands.
    pub(super) fn do_plus_minus(
        &mut self,
        op: u16,
        left: &Value,
        right: &Value,
    ) -> InterpResult<()> {
        let is_plus = op == PlusMinusOp::Plus as u16;

        match (left, right) {
            (Value::Numeric(a), Value::Numeric(b)) => {
                self.cur_exp = Value::Numeric(if is_plus { a + b } else { a - b });
                self.cur_type = Type::Known;
            }
            (Value::Pair(ax, ay), Value::Pair(bx, by)) => {
                self.cur_exp = if is_plus {
                    Value::Pair(ax + bx, ay + by)
                } else {
                    Value::Pair(ax - bx, ay - by)
                };
                self.cur_type = Type::PairType;
            }
            (Value::Color(a), Value::Color(b)) => {
                self.cur_exp = Value::Color(if is_plus {
                    Color::new(a.r + b.r, a.g + b.g, a.b + b.b)
                } else {
                    Color::new(a.r - b.r, a.g - b.g, a.b - b.b)
                });
                self.cur_type = Type::ColorType;
            }
            (Value::String(a), Value::String(b)) if is_plus => {
                // String concatenation with +? No, that's &. This should error.
                return Err(InterpreterError::new(
                    ErrorKind::TypeError,
                    format!("Cannot add strings (use & for concatenation): \"{a}\" + \"{b}\""),
                ));
            }
            _ => {
                return Err(InterpreterError::new(
                    ErrorKind::TypeError,
                    format!(
                        "Incompatible types for {}: {} and {}",
                        if is_plus { "+" } else { "-" },
                        left.ty(),
                        right.ty()
                    ),
                ));
            }
        }
        Ok(())
    }

    /// Execute a tertiary binary operator.
    pub(super) fn do_tertiary_binary(
        &mut self,
        op: u16,
        left: &Value,
        right: &Value,
    ) -> InterpResult<()> {
        match op {
            x if x == TertiaryBinaryOp::PythagAdd as u16 => {
                let a = value_to_scalar(left)?;
                let b = value_to_scalar(right)?;
                self.cur_exp = Value::Numeric(math::pyth_add(a, b));
                self.cur_type = Type::Known;
            }
            x if x == TertiaryBinaryOp::PythagSub as u16 => {
                let a = value_to_scalar(left)?;
                let b = value_to_scalar(right)?;
                self.cur_exp = Value::Numeric(math::pyth_sub(a, b));
                self.cur_type = Type::Known;
            }
            x if x == TertiaryBinaryOp::Or as u16 => {
                let a = value_to_bool(left)?;
                let b = value_to_bool(right)?;
                self.cur_exp = Value::Boolean(a || b);
                self.cur_type = Type::Boolean;
            }
            _ => {
                self.report_error(ErrorKind::InvalidExpression, "Unknown tertiary binary");
            }
        }
        Ok(())
    }

    /// Execute an expression binary operator.
    pub(super) fn do_expression_binary(&mut self, op: u16, left: &Value) -> InterpResult<()> {
        let right = self.take_cur_exp();

        match op {
            x if x == ExpressionBinaryOp::LessThan as u16 => {
                let a = value_to_scalar(left)?;
                let b = value_to_scalar(&right)?;
                self.cur_exp = Value::Boolean(a < b);
                self.cur_type = Type::Boolean;
            }
            x if x == ExpressionBinaryOp::LessOrEqual as u16 => {
                let a = value_to_scalar(left)?;
                let b = value_to_scalar(&right)?;
                self.cur_exp = Value::Boolean(a <= b);
                self.cur_type = Type::Boolean;
            }
            x if x == ExpressionBinaryOp::GreaterThan as u16 => {
                let a = value_to_scalar(left)?;
                let b = value_to_scalar(&right)?;
                self.cur_exp = Value::Boolean(a > b);
                self.cur_type = Type::Boolean;
            }
            x if x == ExpressionBinaryOp::GreaterOrEqual as u16 => {
                let a = value_to_scalar(left)?;
                let b = value_to_scalar(&right)?;
                self.cur_exp = Value::Boolean(a >= b);
                self.cur_type = Type::Boolean;
            }
            x if x == ExpressionBinaryOp::EqualTo as u16 => {
                let result = values_equal(left, &right);
                self.cur_exp = Value::Boolean(result);
                self.cur_type = Type::Boolean;
            }
            x if x == ExpressionBinaryOp::UnequalTo as u16 => {
                let result = !values_equal(left, &right);
                self.cur_exp = Value::Boolean(result);
                self.cur_type = Type::Boolean;
            }
            x if x == ExpressionBinaryOp::Concatenate as u16 => {
                let a = value_to_string(left)?;
                let b = value_to_string(&right)?;
                let result = format!("{a}{b}");
                self.cur_exp = Value::String(Arc::from(result.as_str()));
                self.cur_type = Type::String;
            }
            x if x == ExpressionBinaryOp::IntersectionTimes as u16 => {
                let p1 = value_to_path(left)?;
                let p2 = value_to_path(&right)?;
                let result = postmeta_graphics::intersection::intersection_times(p1, p2);
                match result {
                    Some(isect) => {
                        self.cur_exp = Value::Pair(isect.t1, isect.t2);
                    }
                    None => {
                        self.cur_exp = Value::Pair(-1.0, -1.0);
                    }
                }
                self.cur_type = Type::PairType;
            }
            x if x == ExpressionBinaryOp::SubstringOf as u16 => {
                let (start, end) = value_to_pair(left)?;
                let s = value_to_string(&right)?;
                let start_idx = start.round() as usize;
                let end_idx = end.round().min(s.len() as f64) as usize;
                let substr = if start_idx < end_idx && start_idx < s.len() {
                    &s[start_idx..end_idx.min(s.len())]
                } else {
                    ""
                };
                self.cur_exp = Value::String(Arc::from(substr));
                self.cur_type = Type::String;
            }
            _ => {
                self.report_error(ErrorKind::InvalidExpression, "Unknown expression binary");
            }
        }
        Ok(())
    }

    // =======================================================================
    // Part extractors
    // =======================================================================

    /// Extract a part from a pair or transform.
    fn extract_part(&mut self, part: usize) -> InterpResult<()> {
        match &self.cur_exp {
            Value::Pair(x, y) => {
                let v = match part {
                    0 => *x,
                    1 => *y,
                    _ => {
                        return Err(InterpreterError::new(
                            ErrorKind::TypeError,
                            "Pair only has xpart and ypart",
                        ))
                    }
                };
                self.cur_exp = Value::Numeric(v);
                self.cur_type = Type::Known;
            }
            Value::Transform(t) => {
                let v = match part {
                    0 => t.tx,
                    1 => t.ty,
                    2 => t.txx,
                    3 => t.txy,
                    4 => t.tyx,
                    5 => t.tyy,
                    _ => {
                        return Err(InterpreterError::new(
                            ErrorKind::TypeError,
                            "Invalid transform part",
                        ))
                    }
                };
                self.cur_exp = Value::Numeric(v);
                self.cur_type = Type::Known;
            }
            _ => {
                return Err(InterpreterError::new(
                    ErrorKind::TypeError,
                    format!("{} has no xpart/ypart", self.cur_exp.ty()),
                ));
            }
        }
        Ok(())
    }

    /// Extract a color part.
    fn extract_color_part(&mut self, part: usize) -> InterpResult<()> {
        if let Value::Color(c) = &self.cur_exp {
            let v = match part {
                0 => c.r,
                1 => c.g,
                2 => c.b,
                _ => {
                    return Err(InterpreterError::new(
                        ErrorKind::TypeError,
                        "Invalid color part",
                    ))
                }
            };
            self.cur_exp = Value::Numeric(v);
            self.cur_type = Type::Known;
            Ok(())
        } else {
            Err(InterpreterError::new(
                ErrorKind::TypeError,
                format!("{} has no color parts", self.cur_exp.ty()),
            ))
        }
    }
}
