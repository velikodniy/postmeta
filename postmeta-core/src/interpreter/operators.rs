//! Operator dispatch.
//!
//! Implements all nullary, unary, and binary operators at each precedence level.

use std::sync::Arc;

use postmeta_graphics::bbox;
use postmeta_graphics::math;
use postmeta_graphics::path;
use postmeta_graphics::pen;
use postmeta_graphics::transform;
use postmeta_graphics::transform::Transformable;
use postmeta_graphics::types::{
    Color, GraphicsObject, Pen, Picture, Point, TextObject, Transform, Vec2,
};

use crate::command::{
    ExpressionBinaryOp, NullaryOp, PlusMinusOp, PrimaryBinaryOp, SecondaryBinaryOp,
    TertiaryBinaryOp, UnaryOp,
};
use crate::error::{ErrorKind, InterpResult, InterpreterError};
use crate::types::{Type, Value};

use super::helpers::{
    value_to_bool, value_to_pair, value_to_path, value_to_pen, value_to_scalar, value_to_string,
    value_to_transform,
};
use super::{Interpreter, LhsBinding};

impl Interpreter {
    /// Execute a nullary operator.
    pub(super) fn do_nullary(&mut self, op: NullaryOp) -> InterpResult<()> {
        match op {
            NullaryOp::True => {
                self.cur_expr.exp = Value::Boolean(true);
                self.cur_expr.ty = Type::Boolean;
            }
            NullaryOp::False => {
                self.cur_expr.exp = Value::Boolean(false);
                self.cur_expr.ty = Type::Boolean;
            }
            NullaryOp::NullPicture => {
                self.cur_expr.exp = Value::Picture(Picture::new());
                self.cur_expr.ty = Type::Picture;
            }
            NullaryOp::NullPen => {
                self.cur_expr.exp = Value::Pen(Pen::null());
                self.cur_expr.ty = Type::Pen;
            }
            NullaryOp::PenCircle => {
                self.cur_expr.exp = Value::Pen(Pen::circle(1.0));
                self.cur_expr.ty = Type::Pen;
            }
            NullaryOp::NormalDeviate => {
                self.cur_expr.exp = Value::Numeric(math::normal_deviate(&mut self.random_seed));
                self.cur_expr.ty = Type::Known;
            }
            NullaryOp::JobName => {
                self.cur_expr.exp = Value::String(Arc::from(self.job_name.as_str()));
                self.cur_expr.ty = Type::String;
            }
            NullaryOp::ReadString => {
                self.cur_expr.exp = Value::Vacuous;
                self.cur_expr.ty = Type::Vacuous;
            }
        }
        Ok(())
    }

    /// Execute a unary operator on `cur_exp`.
    #[expect(clippy::too_many_lines, reason = "matching all unary ops")]
    pub(super) fn do_unary(&mut self, op: UnaryOp) -> InterpResult<()> {
        self.lhs_tracking.last_lhs_binding = None;
        match op {
            UnaryOp::Not => {
                let b = value_to_bool(&self.cur_expr.exp)?;
                self.cur_expr.exp = Value::Boolean(!b);
                self.cur_expr.ty = Type::Boolean;
            }
            UnaryOp::Sqrt => {
                let v = value_to_scalar(&self.cur_expr.exp)?;
                self.cur_expr.exp = Value::Numeric(if v >= 0.0 { v.sqrt() } else { 0.0 });
                self.cur_expr.ty = Type::Known;
            }
            UnaryOp::SinD => {
                let v = value_to_scalar(&self.cur_expr.exp)?;
                self.cur_expr.exp = Value::Numeric(math::sind(v));
                self.cur_expr.ty = Type::Known;
            }
            UnaryOp::CosD => {
                let v = value_to_scalar(&self.cur_expr.exp)?;
                self.cur_expr.exp = Value::Numeric(math::cosd(v));
                self.cur_expr.ty = Type::Known;
            }
            UnaryOp::Floor => {
                let v = value_to_scalar(&self.cur_expr.exp)?;
                self.cur_expr.exp = Value::Numeric(math::floor(v));
                self.cur_expr.ty = Type::Known;
            }
            UnaryOp::MExp => {
                let v = value_to_scalar(&self.cur_expr.exp)?;
                self.cur_expr.exp = Value::Numeric(math::mexp(v));
                self.cur_expr.ty = Type::Known;
            }
            UnaryOp::MLog => {
                let v = value_to_scalar(&self.cur_expr.exp)?;
                self.cur_expr.exp = Value::Numeric(math::mlog(v));
                self.cur_expr.ty = Type::Known;
            }
            UnaryOp::Angle => {
                let (px, py) = value_to_pair(&self.cur_expr.exp)?;
                self.cur_expr.exp = Value::Numeric(math::angle(px, py));
                self.cur_expr.ty = Type::Known;
            }
            UnaryOp::UniformDeviate => {
                let v = value_to_scalar(&self.cur_expr.exp)?;
                self.cur_expr.exp = Value::Numeric(math::uniform_deviate(v, &mut self.random_seed));
                self.cur_expr.ty = Type::Known;
            }
            UnaryOp::Length => {
                match &self.cur_expr.exp {
                    Value::Path(p) => {
                        #[expect(clippy::cast_precision_loss, reason = "segment count fits in f64")]
                        let n = p.num_segments() as f64;
                        self.cur_expr.exp = Value::Numeric(n);
                    }
                    Value::String(s) => {
                        #[expect(
                            clippy::cast_precision_loss,
                            reason = "string length in chars fits in f64 for practical inputs"
                        )]
                        let n = s.chars().count() as f64;
                        self.cur_expr.exp = Value::Numeric(n);
                    }
                    Value::Pair(x, y) => {
                        // abs(pair) = sqrt(x^2 + y^2)
                        self.cur_expr.exp = Value::Numeric(x.hypot(*y));
                    }
                    _ => {
                        return Err(InterpreterError::new(
                            ErrorKind::TypeError,
                            "length requires path, string, or pair",
                        ));
                    }
                }
                self.cur_expr.ty = Type::Known;
            }
            UnaryOp::Decimal => {
                let v = value_to_scalar(&self.cur_expr.exp)?;
                self.cur_expr.exp = Value::String(Arc::from(format!("{v}").as_str()));
                self.cur_expr.ty = Type::String;
            }
            UnaryOp::Reverse => {
                if let Value::Path(ref p) = self.cur_expr.exp {
                    self.cur_expr.exp = Value::Path(path::reverse(p));
                    self.cur_expr.ty = Type::Path;
                } else {
                    return Err(InterpreterError::new(
                        ErrorKind::TypeError,
                        "reverse requires a path",
                    ));
                }
            }
            UnaryOp::XPart => {
                self.extract_part(0)?;
            }
            UnaryOp::YPart => {
                self.extract_part(1)?;
            }
            UnaryOp::XXPart => {
                self.extract_part(2)?;
            }
            UnaryOp::XYPart => {
                self.extract_part(3)?;
            }
            UnaryOp::YXPart => {
                self.extract_part(4)?;
            }
            UnaryOp::YYPart => {
                self.extract_part(5)?;
            }
            UnaryOp::RedPart => {
                self.extract_color_part(0)?;
            }
            UnaryOp::GreenPart => {
                self.extract_color_part(1)?;
            }
            UnaryOp::BluePart => {
                self.extract_color_part(2)?;
            }
            UnaryOp::MakePath => {
                if let Value::Pen(ref p) = self.cur_expr.exp {
                    self.cur_expr.exp = Value::Path(pen::makepath(p));
                    self.cur_expr.ty = Type::Path;
                } else {
                    return Err(InterpreterError::new(
                        ErrorKind::TypeError,
                        "makepath requires a pen",
                    ));
                }
            }
            UnaryOp::MakePen => {
                if let Value::Path(ref p) = self.cur_expr.exp {
                    let result = pen::makepen(p).map_err(|e| {
                        InterpreterError::new(ErrorKind::TypeError, format!("makepen: {e}"))
                    })?;
                    self.cur_expr.exp = Value::Pen(result);
                    self.cur_expr.ty = Type::Pen;
                } else {
                    return Err(InterpreterError::new(
                        ErrorKind::TypeError,
                        "makepen requires a path",
                    ));
                }
            }
            UnaryOp::CycleOp => {
                let is_cyclic = matches!(&self.cur_expr.exp, Value::Path(p) if p.is_cyclic);
                self.cur_expr.exp = Value::Boolean(is_cyclic);
                self.cur_expr.ty = Type::Boolean;
            }
            UnaryOp::LLCorner | UnaryOp::LRCorner | UnaryOp::ULCorner | UnaryOp::URCorner => {
                let bb = match &self.cur_expr.exp {
                    Value::Picture(pic) => bbox::picture_bbox(pic, false),
                    Value::Path(p) => bbox::path_bbox(p),
                    Value::Pen(p) => {
                        let mut bb = bbox::BoundingBox::EMPTY;
                        match p {
                            postmeta_graphics::types::Pen::Elliptical(t) => {
                                // Include the four cardinal pen offsets
                                for pt in [
                                    t.apply_to_point(Point::new(1.0, 0.0)),
                                    t.apply_to_point(Point::new(-1.0, 0.0)),
                                    t.apply_to_point(Point::new(0.0, 1.0)),
                                    t.apply_to_point(Point::new(0.0, -1.0)),
                                ] {
                                    bb.include_point(pt);
                                }
                            }
                            postmeta_graphics::types::Pen::Polygonal(verts) => {
                                for v in verts {
                                    bb.include_point(*v);
                                }
                            }
                        }
                        bb
                    }
                    _ => {
                        return Err(InterpreterError::new(
                            ErrorKind::TypeError,
                            format!(
                                "corner operators require a picture or path, got {}",
                                self.cur_expr.exp.ty()
                            ),
                        ));
                    }
                };
                let (px, py) = match op {
                    UnaryOp::LLCorner => (bb.min_x, bb.min_y),
                    UnaryOp::LRCorner => (bb.max_x, bb.min_y),
                    UnaryOp::ULCorner => (bb.min_x, bb.max_y),
                    UnaryOp::URCorner => (bb.max_x, bb.max_y),
                    _ => (bb.max_x, bb.max_y),
                };
                self.cur_expr.exp = Value::Pair(px, py);
                self.cur_expr.ty = Type::PairType;
            }
            _ => {
                // Unimplemented unary — leave cur_exp unchanged
            }
        }
        Ok(())
    }

    /// Execute an "X of Y" binary operator.
    pub(super) fn do_primary_binary(
        &mut self,
        op: PrimaryBinaryOp,
        first: &Value,
    ) -> InterpResult<()> {
        let second = &self.cur_expr.exp;

        match op {
            PrimaryBinaryOp::PointOf => {
                let t = value_to_scalar(first)?;
                let p = value_to_path(second)?;
                let pt = path::point_of(p, t);
                self.cur_expr.exp = Value::Pair(pt.x, pt.y);
                self.cur_expr.ty = Type::PairType;
            }
            PrimaryBinaryOp::DirectionOf => {
                let t = value_to_scalar(first)?;
                let p = value_to_path(second)?;
                let dir = path::direction_of(p, t);
                self.cur_expr.exp = Value::Pair(dir.x, dir.y);
                self.cur_expr.ty = Type::PairType;
            }
            PrimaryBinaryOp::PrecontrolOf => {
                let t = value_to_scalar(first)?;
                let p = value_to_path(second)?;
                let pt = path::precontrol_of(p, t);
                self.cur_expr.exp = Value::Pair(pt.x, pt.y);
                self.cur_expr.ty = Type::PairType;
            }
            PrimaryBinaryOp::PostcontrolOf => {
                let t = value_to_scalar(first)?;
                let p = value_to_path(second)?;
                let pt = path::postcontrol_of(p, t);
                self.cur_expr.exp = Value::Pair(pt.x, pt.y);
                self.cur_expr.ty = Type::PairType;
            }
            PrimaryBinaryOp::SubpathOf => {
                let (t1, t2) = value_to_pair(first)?;
                let p = value_to_path(second)?;
                self.cur_expr.exp = Value::Path(path::subpath(p, t1, t2));
                self.cur_expr.ty = Type::Path;
            }
            PrimaryBinaryOp::PenOffsetOf => {
                let (dx, dy) = value_to_pair(first)?;
                let p = value_to_pen(second)?;
                let pt = pen::penoffset(p, Vec2::new(dx, dy));
                self.cur_expr.exp = Value::Pair(pt.x, pt.y);
                self.cur_expr.ty = Type::PairType;
            }
            PrimaryBinaryOp::SubstringOf => {
                let (start, end) = value_to_pair(first)?;
                let s = value_to_string(second)?;

                let chars: Vec<char> = s.chars().collect();
                #[expect(
                    clippy::cast_precision_loss,
                    reason = "character count fits in f64 for practical inputs"
                )]
                let char_len_f64 = chars.len() as f64;

                let clamp_idx = |v: f64| -> usize {
                    if !v.is_finite() {
                        return 0;
                    }

                    #[expect(
                        clippy::cast_possible_truncation,
                        reason = "index is clamped to [0, len] before cast"
                    )]
                    {
                        v.round().max(0.0).min(char_len_f64) as usize
                    }
                };

                let start_idx = clamp_idx(start);
                let end_idx = clamp_idx(end);
                let substr: String = if start_idx < end_idx {
                    chars[start_idx..end_idx].iter().collect()
                } else {
                    String::new()
                };

                self.cur_expr.exp = Value::String(Arc::from(substr));
                self.cur_expr.ty = Type::String;
            }
            PrimaryBinaryOp::DirectionTimeOf | PrimaryBinaryOp::ArcTimeOf => {
                self.report_error(ErrorKind::InvalidExpression, "Unimplemented primary binary");
            }
        }
        Ok(())
    }

    /// Execute a secondary binary operator.
    pub(super) fn do_secondary_binary(
        &mut self,
        op: SecondaryBinaryOp,
        left: &Value,
    ) -> InterpResult<()> {
        let right = self.take_cur_exp();

        match op {
            SecondaryBinaryOp::Times => {
                // Scalar * scalar, or scalar * pair, or pair * scalar
                match (left, &right) {
                    (Value::Numeric(a), Value::Numeric(b)) => {
                        self.cur_expr.exp = Value::Numeric(a * b);
                        self.cur_expr.ty = Type::Known;
                    }
                    (Value::Numeric(a), Value::Pair(bx, by)) => {
                        self.cur_expr.exp = Value::Pair(a * bx, a * by);
                        self.cur_expr.ty = Type::PairType;
                    }
                    (Value::Pair(ax, ay), Value::Numeric(b)) => {
                        self.cur_expr.exp = Value::Pair(ax * b, ay * b);
                        self.cur_expr.ty = Type::PairType;
                    }
                    _ => {
                        return Err(InterpreterError::new(
                            ErrorKind::TypeError,
                            "Invalid types for *",
                        ));
                    }
                }
            }
            SecondaryBinaryOp::Scaled => {
                let factor = value_to_scalar(&right)?;
                self.apply_transform(left, &transform::scaled(factor))?;
            }
            SecondaryBinaryOp::Shifted => {
                let (dx, dy) = value_to_pair(&right)?;
                self.apply_transform(left, &transform::shifted(dx, dy))?;
            }
            SecondaryBinaryOp::Rotated => {
                let angle = value_to_scalar(&right)?;
                self.apply_transform(left, &transform::rotated(angle))?;
            }
            SecondaryBinaryOp::XScaled => {
                let factor = value_to_scalar(&right)?;
                self.apply_transform(left, &transform::xscaled(factor))?;
            }
            SecondaryBinaryOp::YScaled => {
                let factor = value_to_scalar(&right)?;
                self.apply_transform(left, &transform::yscaled(factor))?;
            }
            SecondaryBinaryOp::Slanted => {
                let factor = value_to_scalar(&right)?;
                self.apply_transform(left, &transform::slanted(factor))?;
            }
            SecondaryBinaryOp::ZScaled => {
                let (a, b) = value_to_pair(&right)?;
                self.apply_transform(left, &transform::zscaled(a, b))?;
            }
            SecondaryBinaryOp::Transformed => {
                let t = value_to_transform(&right)?;
                self.apply_transform(left, &t)?;
            }
            SecondaryBinaryOp::DotProd => {
                let (ax, ay) = value_to_pair(left)?;
                let (bx, by) = value_to_pair(&right)?;
                self.cur_expr.exp = Value::Numeric(ax.mul_add(bx, ay * by));
                self.cur_expr.ty = Type::Known;
            }
            SecondaryBinaryOp::Infont => {
                let text = value_to_string(left)?;
                let font_name = value_to_string(&right)?;
                // Default font size — MetaPost uses 10pt for design size.
                // `plain.mp` applies `scaled defaultscale` after infont.
                let font_size = 10.0;
                let text_obj = TextObject {
                    text: Arc::from(text.as_ref()),
                    font_name: Arc::from(font_name.as_ref()),
                    font_size,
                    color: Color::BLACK,
                    transform: Transform::IDENTITY,
                };
                let mut pic = Picture::new();
                pic.objects.push(GraphicsObject::Text(text_obj));
                self.cur_expr.exp = Value::Picture(pic);
                self.cur_expr.ty = Type::Picture;
            }
            SecondaryBinaryOp::Over => {
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
                let pt = Point::new(*x, *y).transformed(t);
                self.cur_expr.exp = Value::Pair(pt.x, pt.y);
                self.cur_expr.ty = Type::PairType;
            }
            Value::Path(p) => {
                self.cur_expr.exp = Value::Path(p.transformed(t));
                self.cur_expr.ty = Type::Path;
            }
            Value::Pen(p) => {
                self.cur_expr.exp = Value::Pen(p.transformed(t));
                self.cur_expr.ty = Type::Pen;
            }
            Value::Picture(p) => {
                self.cur_expr.exp = Value::Picture(p.transformed(t));
                self.cur_expr.ty = Type::Picture;
            }
            Value::Transform(existing) => {
                self.cur_expr.exp = Value::Transform(existing.transformed(t));
                self.cur_expr.ty = Type::TransformType;
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
        op: PlusMinusOp,
        left: &Value,
        right: &Value,
    ) -> InterpResult<()> {
        let is_plus = op == PlusMinusOp::Plus;

        match (left, right) {
            (Value::Numeric(a), Value::Numeric(b)) => {
                self.cur_expr.exp = Value::Numeric(if is_plus { a + b } else { a - b });
                self.cur_expr.ty = Type::Known;
            }
            (Value::Pair(ax, ay), Value::Pair(bx, by)) => {
                self.cur_expr.exp = if is_plus {
                    Value::Pair(ax + bx, ay + by)
                } else {
                    Value::Pair(ax - bx, ay - by)
                };
                self.cur_expr.ty = Type::PairType;
            }
            (Value::Color(a), Value::Color(b)) => {
                self.cur_expr.exp = Value::Color(if is_plus {
                    Color::new(a.r + b.r, a.g + b.g, a.b + b.b)
                } else {
                    Color::new(a.r - b.r, a.g - b.g, a.b - b.b)
                });
                self.cur_expr.ty = Type::ColorType;
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

    /// Perform implicit multiplication (e.g., `3x`, `2bp`, `.5(1,2)`).
    ///
    /// The `factor` is the numeric value on the left; `cur_exp`/`cur_type`
    /// hold the right operand (the result of the recursive `scan_primary`).
    pub(super) fn do_implicit_mul(&mut self, factor: &Value) -> InterpResult<()> {
        let a = value_to_scalar(factor)?;
        match &self.cur_expr.exp {
            Value::Numeric(b) => {
                self.cur_expr.exp = Value::Numeric(a * b);
                self.cur_expr.ty = Type::Known;
            }
            Value::Pair(bx, by) => {
                self.cur_expr.exp = Value::Pair(a * bx, a * by);
                self.cur_expr.ty = Type::PairType;
            }
            Value::Color(c) => {
                self.cur_expr.exp = Value::Color(Color::new(a * c.r, a * c.g, a * c.b));
                self.cur_expr.ty = Type::ColorType;
            }
            _ => {
                return Err(InterpreterError::new(
                    ErrorKind::TypeError,
                    format!("Cannot multiply numeric by {}", self.cur_expr.ty),
                ));
            }
        }
        Ok(())
    }

    /// Execute a tertiary binary operator.
    pub(super) fn do_tertiary_binary(
        &mut self,
        op: TertiaryBinaryOp,
        left: &Value,
        right: &Value,
    ) -> InterpResult<()> {
        match op {
            TertiaryBinaryOp::PythagAdd => {
                let a = value_to_scalar(left)?;
                let b = value_to_scalar(right)?;
                self.cur_expr.exp = Value::Numeric(math::pyth_add(a, b));
                self.cur_expr.ty = Type::Known;
            }
            TertiaryBinaryOp::PythagSub => {
                let a = value_to_scalar(left)?;
                let b = value_to_scalar(right)?;
                self.cur_expr.exp = Value::Numeric(math::pyth_sub(a, b));
                self.cur_expr.ty = Type::Known;
            }
            TertiaryBinaryOp::Or => {
                let a = value_to_bool(left)?;
                let b = value_to_bool(right)?;
                self.cur_expr.exp = Value::Boolean(a || b);
                self.cur_expr.ty = Type::Boolean;
            }
        }
        Ok(())
    }

    /// Execute an expression binary operator.
    pub(super) fn do_expression_binary(
        &mut self,
        op: ExpressionBinaryOp,
        left: &Value,
    ) -> InterpResult<()> {
        let right = self.take_cur_exp();

        match op {
            ExpressionBinaryOp::LessThan => {
                let result = match (left, &right) {
                    (Value::String(a), Value::String(b)) => a < b,
                    _ => value_to_scalar(left)? < value_to_scalar(&right)?,
                };
                self.cur_expr.exp = Value::Boolean(result);
                self.cur_expr.ty = Type::Boolean;
            }
            ExpressionBinaryOp::LessOrEqual => {
                let result = match (left, &right) {
                    (Value::String(a), Value::String(b)) => a <= b,
                    _ => value_to_scalar(left)? <= value_to_scalar(&right)?,
                };
                self.cur_expr.exp = Value::Boolean(result);
                self.cur_expr.ty = Type::Boolean;
            }
            ExpressionBinaryOp::GreaterThan => {
                let result = match (left, &right) {
                    (Value::String(a), Value::String(b)) => a > b,
                    _ => value_to_scalar(left)? > value_to_scalar(&right)?,
                };
                self.cur_expr.exp = Value::Boolean(result);
                self.cur_expr.ty = Type::Boolean;
            }
            ExpressionBinaryOp::GreaterOrEqual => {
                let result = match (left, &right) {
                    (Value::String(a), Value::String(b)) => a >= b,
                    _ => value_to_scalar(left)? >= value_to_scalar(&right)?,
                };
                self.cur_expr.exp = Value::Boolean(result);
                self.cur_expr.ty = Type::Boolean;
            }
            ExpressionBinaryOp::EqualTo => {
                let result = left == &right;
                self.cur_expr.exp = Value::Boolean(result);
                self.cur_expr.ty = Type::Boolean;
            }
            ExpressionBinaryOp::UnequalTo => {
                let result = left != &right;
                self.cur_expr.exp = Value::Boolean(result);
                self.cur_expr.ty = Type::Boolean;
            }
            ExpressionBinaryOp::Concatenate => {
                let a = value_to_string(left)?;
                let b = value_to_string(&right)?;
                let result = format!("{a}{b}");
                self.cur_expr.exp = Value::String(Arc::from(result.as_str()));
                self.cur_expr.ty = Type::String;
            }
            ExpressionBinaryOp::IntersectionTimes => {
                let p1 = value_to_path(left)?;
                let p2 = value_to_path(&right)?;
                let result = postmeta_graphics::intersection::intersection_times(p1, p2);
                match result {
                    Some(isect) => {
                        self.cur_expr.exp = Value::Pair(isect.t1, isect.t2);
                    }
                    None => {
                        self.cur_expr.exp = Value::Pair(-1.0, -1.0);
                    }
                }
                self.cur_expr.ty = Type::PairType;
            }
        }
        Ok(())
    }

    // =======================================================================
    // Part extractors
    // =======================================================================

    /// Extract a part from a pair or transform.
    ///
    /// When the operand has a pair dependency list (i.e. the pair variable
    /// is not fully known), the extracted component's dependency is
    /// propagated to `cur_dep` / `last_lhs_binding` so that it can
    /// participate in linear equation solving (e.g. `xpart A = 0`).
    fn extract_part(&mut self, part: usize) -> InterpResult<()> {
        match &self.cur_expr.exp {
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
                self.cur_expr.exp = Value::Numeric(v);
                // Propagate the component's dependency so equations work.
                if let Some((dx, dy)) = self.cur_expr.pair_dep.take() {
                    let dep = if part == 0 { dx } else { dy };
                    if crate::equation::is_constant(&dep) {
                        // Fully known component — no dependency to track.
                        self.cur_expr.dep = Some(dep);
                        self.cur_expr.ty = Type::Known;
                    } else {
                        // Extract the primary VarId from the dep for LHS binding.
                        let primary_var = dep.iter().find_map(|t| t.var_id);
                        if let Some(vid) = primary_var {
                            self.lhs_tracking.last_lhs_binding = Some(LhsBinding::Variable {
                                id: vid,
                                negated: false,
                            });
                        }
                        self.cur_expr.dep = Some(dep);
                        self.cur_expr.ty = Type::Dependent;
                    }
                } else {
                    self.cur_expr.ty = Type::Known;
                }
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
                self.cur_expr.exp = Value::Numeric(v);
                self.cur_expr.ty = Type::Known;
            }
            _ => {
                return Err(InterpreterError::new(
                    ErrorKind::TypeError,
                    format!("{} has no xpart/ypart", self.cur_expr.exp.ty()),
                ));
            }
        }
        Ok(())
    }

    /// Extract a color part.
    fn extract_color_part(&mut self, part: usize) -> InterpResult<()> {
        if let Value::Color(c) = &self.cur_expr.exp {
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
            self.cur_expr.exp = Value::Numeric(v);
            self.cur_expr.ty = Type::Known;
            Ok(())
        } else {
            Err(InterpreterError::new(
                ErrorKind::TypeError,
                format!("{} has no color parts", self.cur_expr.exp.ty()),
            ))
        }
    }
}
