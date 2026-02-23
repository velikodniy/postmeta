//! Operator dispatch.
//!
//! Implements all nullary, unary, and binary operators at each precedence level.

use std::cmp::Ordering;
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
use crate::variables::VarValue;

impl Interpreter {
    fn compare_values(
        left: &Value,
        right: &Value,
        predicate: fn(Ordering) -> bool,
    ) -> InterpResult<bool> {
        if let (Value::String(a), Value::String(b)) = (left, right) {
            Ok(predicate(a.cmp(b)))
        } else {
            let l = value_to_scalar(left)?;
            let r = value_to_scalar(right)?;
            Ok(l.partial_cmp(&r).is_some_and(predicate))
        }
    }

    /// Evaluate a nullary operator, returning `(value, type)`.
    pub(super) fn eval_nullary(&mut self, op: NullaryOp) -> (Value, Type) {
        match op {
            NullaryOp::True => (Value::Boolean(true), Type::Boolean),
            NullaryOp::False => (Value::Boolean(false), Type::Boolean),
            NullaryOp::NullPicture => (Value::Picture(Picture::new()), Type::Picture),
            NullaryOp::NullPen => (Value::Pen(Pen::null()), Type::Pen),
            NullaryOp::PenCircle => (Value::Pen(Pen::circle(1.0)), Type::Pen),
            NullaryOp::NormalDeviate => (
                Value::Numeric(math::normal_deviate(&mut self.random_seed)),
                Type::Known,
            ),
            NullaryOp::JobName => (
                Value::String(Arc::from(self.job_name.as_str())),
                Type::String,
            ),
            NullaryOp::ReadString => (Value::Vacuous, Type::Vacuous),
        }
    }

    /// Execute a unary operator, returning the result.
    ///
    /// Most operators are pure: they transform an input value into an output
    /// `(Value, Type)` via [`Self::eval_unary`].  The part-extraction operators
    /// (`xpart`, `ypart`, etc.) additionally propagate pair dependency info for
    /// the equation solver.
    pub(super) fn do_unary(
        &mut self,
        op: UnaryOp,
        input: Value,
        pair_dep: Option<(crate::equation::DepList, crate::equation::DepList)>,
    ) -> InterpResult<super::ExprResultValue> {
        // Save the operand binding before clearing — part-extraction operators
        // need it to find transform sub-part VarIds for equation solving.
        let operand_binding = self.lhs_tracking.last_lhs_binding.take();

        // Part-extraction operators need pair_dep access — handle them here.
        match op {
            UnaryOp::XPart => return self.extract_part(&input, 0, pair_dep, operand_binding),
            UnaryOp::YPart => return self.extract_part(&input, 1, pair_dep, operand_binding),
            UnaryOp::XXPart => return self.extract_part(&input, 2, pair_dep, operand_binding),
            UnaryOp::XYPart => return self.extract_part(&input, 3, pair_dep, operand_binding),
            UnaryOp::YXPart => return self.extract_part(&input, 4, pair_dep, operand_binding),
            UnaryOp::YYPart => return self.extract_part(&input, 5, pair_dep, operand_binding),
            _ => {}
        }

        // All remaining unary operators are pure value transformations.
        let (val, ty) = Self::eval_unary(op, &input, &mut self.random_seed)?;
        // Synthesize const_dep for known numeric results so that dependency
        // tracking is preserved through subsequent arithmetic (e.g.,
        // `alpha = angle(A) - angle(B)` where both angle calls return known
        // values that need to flow through subtraction into the equation solver).
        let dep = if let Value::Numeric(v) = &val {
            Some(crate::equation::const_dep(*v))
        } else {
            None
        };
        Ok(super::ExprResultValue {
            exp: val,
            ty,
            dep,
            pair_dep: None,
        })
    }

    /// Pure evaluation of a unary operator.
    ///
    /// Returns the result `(Value, Type)`.  Does NOT handle part-extraction
    /// operators (xpart, ypart, etc.) — those need pair dependency propagation
    /// and are handled by [`Self::do_unary`] directly.
    fn eval_unary(
        op: UnaryOp,
        input: &Value,
        random_seed: &mut u64,
    ) -> InterpResult<(Value, Type)> {
        match op {
            UnaryOp::Not => {
                let b = value_to_bool(input)?;
                Ok((Value::Boolean(!b), Type::Boolean))
            }
            UnaryOp::Sqrt => {
                let v = value_to_scalar(input)?;
                Ok((
                    Value::Numeric(if v >= 0.0 { v.sqrt() } else { 0.0 }),
                    Type::Known,
                ))
            }
            // Sine of an angle in degrees
            UnaryOp::SinD => {
                let v = value_to_scalar(input)?;
                Ok((Value::Numeric(v.to_radians().sin()), Type::Known))
            }
            // Cosine of an angle in degrees
            UnaryOp::CosD => {
                let v = value_to_scalar(input)?;
                Ok((Value::Numeric(v.to_radians().cos()), Type::Known))
            }
            UnaryOp::Floor => {
                let v = value_to_scalar(input)?;
                Ok((Value::Numeric(v.floor()), Type::Known))
            }
            UnaryOp::Odd => {
                let v = value_to_scalar(input)?;
                #[expect(
                    clippy::cast_possible_truncation,
                    reason = "rounding to integer for odd test"
                )]
                let rounded = v.round() as i64;
                Ok((Value::Boolean(rounded % 2 != 0), Type::Boolean))
            }
            UnaryOp::MExp => {
                let v = value_to_scalar(input)?;
                Ok((Value::Numeric(math::mexp(v)), Type::Known))
            }
            UnaryOp::MLog => {
                let v = value_to_scalar(input)?;
                Ok((Value::Numeric(math::mlog(v)), Type::Known))
            }
            UnaryOp::Oct => {
                let v = value_to_scalar(input)?;
                if !v.is_finite() {
                    return Err(InterpreterError::new(
                        ErrorKind::TypeError,
                        "oct requires a finite numeric value",
                    ));
                }
                #[expect(
                    clippy::cast_possible_truncation,
                    reason = "integer conversion follows MetaPost-style rounding semantics"
                )]
                let n = v.round() as i64;
                Ok((Value::String(Arc::from(format!("{n:o}"))), Type::String))
            }
            UnaryOp::Hex => {
                let v = value_to_scalar(input)?;
                if !v.is_finite() {
                    return Err(InterpreterError::new(
                        ErrorKind::TypeError,
                        "hex requires a finite numeric value",
                    ));
                }
                #[expect(
                    clippy::cast_possible_truncation,
                    reason = "integer conversion follows MetaPost-style rounding semantics"
                )]
                let n = v.round() as i64;
                Ok((Value::String(Arc::from(format!("{n:X}"))), Type::String))
            }
            UnaryOp::ASCII => {
                let s = value_to_string(input)?;
                let n = s.chars().next().map_or(0.0, |ch| f64::from(u32::from(ch)));
                Ok((Value::Numeric(n), Type::Known))
            }
            UnaryOp::Char => {
                let v = value_to_scalar(input)?;
                if !v.is_finite() {
                    return Err(InterpreterError::new(
                        ErrorKind::TypeError,
                        "char requires a finite numeric value",
                    ));
                }
                #[expect(
                    clippy::cast_possible_truncation,
                    reason = "character code is computed from rounded numeric"
                )]
                let rounded = v.round() as i64;
                let code = rounded.rem_euclid(256) as u32;
                let ch = char::from_u32(code).unwrap_or('\0');
                Ok((Value::String(Arc::from(ch.to_string())), Type::String))
            }
            UnaryOp::Angle => {
                let (px, py) = value_to_pair(input)?;
                let angle = Vec2::new(px, py).direction().to_degrees();
                Ok((Value::Numeric(angle), Type::Known))
            }
            UnaryOp::UniformDeviate => {
                let v = value_to_scalar(input)?;
                Ok((
                    Value::Numeric(math::uniform_deviate(v, random_seed)),
                    Type::Known,
                ))
            }
            UnaryOp::Length => {
                let n = match input {
                    Value::Path(p) => {
                        #[expect(clippy::cast_precision_loss, reason = "segment count fits in f64")]
                        {
                            p.num_segments() as f64
                        }
                    }
                    Value::String(s) => {
                        #[expect(
                            clippy::cast_precision_loss,
                            reason = "string length in chars fits in f64 for practical inputs"
                        )]
                        {
                            s.chars().count() as f64
                        }
                    }
                    Value::Pair(x, y) => x.hypot(*y),
                    _ => {
                        return Err(InterpreterError::new(
                            ErrorKind::TypeError,
                            "length requires path, string, or pair",
                        ));
                    }
                };
                Ok((Value::Numeric(n), Type::Known))
            }
            UnaryOp::Decimal => {
                let v = value_to_scalar(input)?;
                Ok((
                    Value::String(Arc::from(format!("{v}").as_str())),
                    Type::String,
                ))
            }
            UnaryOp::Reverse => {
                if let Value::Path(p) = input {
                    Ok((Value::Path(path::reverse(p)), Type::Path))
                } else {
                    Err(InterpreterError::new(
                        ErrorKind::TypeError,
                        "reverse requires a path",
                    ))
                }
            }
            UnaryOp::RedPart => Self::extract_color_part(input, 0),
            UnaryOp::GreenPart => Self::extract_color_part(input, 1),
            UnaryOp::BluePart => Self::extract_color_part(input, 2),
            UnaryOp::MakePath => {
                if let Value::Pen(p) = input {
                    Ok((Value::Path(pen::makepath(p)), Type::Path))
                } else {
                    Err(InterpreterError::new(
                        ErrorKind::TypeError,
                        "makepath requires a pen",
                    ))
                }
            }
            UnaryOp::MakePen => {
                // mp.web §16987: pair_to_path before makepen
                let owned_path;
                let path_ref = match input {
                    Value::Path(p) => p,
                    Value::Pair(x, y) => {
                        use postmeta_graphics::types::Knot;
                        owned_path = postmeta_graphics::path::Path {
                            knots: vec![Knot::new(Point::new(*x, *y))],
                            is_cyclic: true,
                        };
                        &owned_path
                    }
                    _ => {
                        return Err(InterpreterError::new(
                            ErrorKind::TypeError,
                            "makepen requires a path or pair",
                        ));
                    }
                };
                let result = pen::makepen(path_ref).map_err(|e| {
                    InterpreterError::new(ErrorKind::TypeError, format!("makepen: {e}"))
                })?;
                Ok((Value::Pen(result), Type::Pen))
            }
            UnaryOp::CycleOp => {
                let is_cyclic = matches!(input, Value::Path(p) if p.is_cyclic);
                Ok((Value::Boolean(is_cyclic), Type::Boolean))
            }
            UnaryOp::LLCorner | UnaryOp::LRCorner | UnaryOp::ULCorner | UnaryOp::URCorner => {
                let bb = match input {
                    Value::Picture(pic) => bbox::picture_bbox(pic, false),
                    Value::Path(p) => bbox::path_bbox(p),
                    Value::Pen(p) => {
                        let mut bb = bbox::BoundingBox::EMPTY;
                        match p {
                            postmeta_graphics::types::Pen::Elliptical(t) => {
                                for pt in [
                                    t.apply(Point::new(1.0, 0.0)),
                                    t.apply(Point::new(-1.0, 0.0)),
                                    t.apply(Point::new(0.0, 1.0)),
                                    t.apply(Point::new(0.0, -1.0)),
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
                                input.ty()
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
                Ok((Value::Pair(px, py), Type::PairType))
            }
            UnaryOp::ArcLength => {
                let p = value_to_path(input)?;
                let len = path::arc_length(p);
                Ok((Value::Numeric(len), Type::Known))
            }
            // Part-extraction ops are handled in do_unary before calling this.
            _ => Err(InterpreterError::new(
                ErrorKind::InvalidExpression,
                format!("Unimplemented unary operator: {op:?}"),
            )),
        }
    }

    /// Execute an "X of Y" binary operator.
    pub(super) fn do_primary_binary(
        op: PrimaryBinaryOp,
        first: &Value,
        second: &Value,
    ) -> InterpResult<(Value, Type)> {
        match op {
            PrimaryBinaryOp::PointOf => {
                let t = value_to_scalar(first)?;
                let p = value_to_path(second)?;
                let pt = p.point_at(t);
                Ok((Value::Pair(pt.x, pt.y), Type::PairType))
            }
            PrimaryBinaryOp::PrecontrolOf => {
                let t = value_to_scalar(first)?;
                let p = value_to_path(second)?;
                let pt = path::precontrol_of(p, t);
                Ok((Value::Pair(pt.x, pt.y), Type::PairType))
            }
            PrimaryBinaryOp::PostcontrolOf => {
                let t = value_to_scalar(first)?;
                let p = value_to_path(second)?;
                let pt = path::postcontrol_of(p, t);
                Ok((Value::Pair(pt.x, pt.y), Type::PairType))
            }
            PrimaryBinaryOp::SubpathOf => {
                let (t1, t2) = value_to_pair(first)?;
                let p = value_to_path(second)?;
                Ok((Value::Path(path::subpath(p, t1, t2)), Type::Path))
            }
            PrimaryBinaryOp::PenOffsetOf => {
                let (dx, dy) = value_to_pair(first)?;
                let p = value_to_pen(second)?;
                let pt = pen::penoffset(p, Vec2::new(dx, dy));
                Ok((Value::Pair(pt.x, pt.y), Type::PairType))
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

                Ok((Value::String(Arc::from(substr)), Type::String))
            }
            PrimaryBinaryOp::ArcTimeOf => {
                let target_len = value_to_scalar(first)?;
                let p = value_to_path(second)?;
                let t = path::arc_time(p, target_len);
                Ok((Value::Numeric(t), Type::Known))
            }
            PrimaryBinaryOp::DirectionTimeOf => Err(InterpreterError::new(
                ErrorKind::InvalidExpression,
                "Unimplemented primary binary: directiontime",
            )),
        }
    }

    /// Execute a secondary binary operator.
    pub(super) fn do_secondary_binary(
        op: SecondaryBinaryOp,
        left: &Value,
        right: &Value,
    ) -> InterpResult<(Value, Type)> {
        match op {
            SecondaryBinaryOp::Times => {
                // Scalar * scalar, scalar * pair, pair * scalar,
                // scalar * color, color * scalar.
                match (left, right) {
                    (Value::Numeric(a), Value::Numeric(b)) => {
                        Ok((Value::Numeric(a * b), Type::Known))
                    }
                    (Value::Numeric(a), Value::Pair(bx, by)) => {
                        Ok((Value::Pair(a * bx, a * by), Type::PairType))
                    }
                    (Value::Pair(ax, ay), Value::Numeric(b)) => {
                        Ok((Value::Pair(ax * b, ay * b), Type::PairType))
                    }
                    (Value::Numeric(a), Value::Color(c)) => Ok((
                        Value::Color(Color::new(a * c.r, a * c.g, a * c.b)),
                        Type::ColorType,
                    )),
                    (Value::Color(c), Value::Numeric(a)) => Ok((
                        Value::Color(Color::new(c.r * a, c.g * a, c.b * a)),
                        Type::ColorType,
                    )),
                    _ => Err(InterpreterError::new(
                        ErrorKind::TypeError,
                        "Invalid types for *",
                    )),
                }
            }
            SecondaryBinaryOp::Scaled => {
                let factor = value_to_scalar(right)?;
                Self::apply_transform(left, &transform::scaled(factor))
            }
            SecondaryBinaryOp::Shifted => {
                let (dx, dy) = value_to_pair(right)?;
                Self::apply_transform(left, &transform::shifted(dx, dy))
            }
            SecondaryBinaryOp::Rotated => {
                let angle = value_to_scalar(right)?;
                Self::apply_transform(left, &transform::rotated(angle))
            }
            SecondaryBinaryOp::XScaled => {
                let factor = value_to_scalar(right)?;
                Self::apply_transform(left, &transform::xscaled(factor))
            }
            SecondaryBinaryOp::YScaled => {
                let factor = value_to_scalar(right)?;
                Self::apply_transform(left, &transform::yscaled(factor))
            }
            SecondaryBinaryOp::Slanted => {
                let factor = value_to_scalar(right)?;
                Self::apply_transform(left, &transform::slanted(factor))
            }
            SecondaryBinaryOp::ZScaled => {
                let (a, b) = value_to_pair(right)?;
                Self::apply_transform(left, &transform::zscaled(a, b))
            }
            SecondaryBinaryOp::Transformed => {
                let t = value_to_transform(right)?;
                Self::apply_transform(left, &t)
            }
            SecondaryBinaryOp::Infont => {
                let text = value_to_string(left)?;
                let font_name = value_to_string(right)?;
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
                Ok((Value::Picture(pic), Type::Picture))
            }
            SecondaryBinaryOp::Over => Err(InterpreterError::new(
                ErrorKind::InvalidExpression,
                "Unimplemented secondary binary: over",
            )),
        }
    }

    /// Apply a transform to a value, returning the transformed `(Value, Type)`.
    fn apply_transform(val: &Value, t: &Transform) -> InterpResult<(Value, Type)> {
        match val {
            Value::Pair(x, y) => {
                let pt = Point::new(*x, *y).transformed(t);
                Ok((Value::Pair(pt.x, pt.y), Type::PairType))
            }
            Value::Path(p) => Ok((Value::Path(p.transformed(t)), Type::Path)),
            Value::Pen(p) => Ok((Value::Pen(p.transformed(t)), Type::Pen)),
            Value::Picture(p) => Ok((Value::Picture(p.transformed(t)), Type::Picture)),
            Value::Transform(existing) => Ok((
                Value::Transform(existing.transformed(t)),
                Type::TransformType,
            )),
            _ => Err(InterpreterError::new(
                ErrorKind::TypeError,
                format!("Cannot transform {}", val.ty()),
            )),
        }
    }

    /// Execute plus or minus on two operands.
    pub(super) fn do_plus_minus(
        op: PlusMinusOp,
        left: &Value,
        right: &Value,
    ) -> InterpResult<(Value, Type)> {
        plus_minus_value(op, left, right)
    }

    /// Perform implicit multiplication (e.g., `3x`, `2bp`, `.5(1,2)`).
    ///
    /// The `factor` is the numeric value on the left; `cur_exp`/`cur_type`
    /// hold the right operand (the result of the recursive `scan_primary`).
    pub(super) fn do_implicit_mul(factor: &Value, right: &Value) -> InterpResult<(Value, Type)> {
        let a = value_to_scalar(factor)?;
        match right {
            Value::Numeric(b) => Ok((Value::Numeric(a * b), Type::Known)),
            Value::Pair(bx, by) => Ok((Value::Pair(a * bx, a * by), Type::PairType)),
            Value::Color(c) => Ok((
                Value::Color(Color::new(a * c.r, a * c.g, a * c.b)),
                Type::ColorType,
            )),
            _ => Err(InterpreterError::new(
                ErrorKind::TypeError,
                format!("Cannot multiply numeric by {}", right.ty()),
            )),
        }
    }

    /// Execute a tertiary binary operator.
    pub(super) fn do_tertiary_binary(
        op: TertiaryBinaryOp,
        left: &Value,
        right: &Value,
    ) -> InterpResult<(Value, Type)> {
        tertiary_binary_value(op, left, right)
    }

    /// Execute an expression binary operator.
    pub(super) fn do_expression_binary(
        op: ExpressionBinaryOp,
        left: &Value,
        right: &Value,
    ) -> InterpResult<(Value, Type)> {
        expression_binary_value(op, left, right)
    }

    // =======================================================================
    // Part extractors
    // =======================================================================

    /// Extract a part from a pair or transform.
    ///
    /// When the operand has a pair dependency list (i.e. the pair variable
    /// is not fully known), the extracted component's dependency is
    /// propagated to the returned result's `dep` and to
    /// `last_lhs_binding` so that it can participate in linear equation
    /// solving (e.g. `xpart A = 0`).
    ///
    /// For transform variables, `operand_binding` carries the variable
    /// binding from before the unary operator cleared it, allowing us to
    /// look up the sub-part `VarId` for equation solving (e.g.
    /// `xxpart T = 1`).
    fn extract_part(
        &mut self,
        input: &Value,
        part: usize,
        pair_dep: Option<(crate::equation::DepList, crate::equation::DepList)>,
        operand_binding: Option<LhsBinding>,
    ) -> InterpResult<super::ExprResultValue> {
        match input {
            Value::Pair(x, y) => {
                let v = match part {
                    0 => *x,
                    1 => *y,
                    _ => {
                        return Err(InterpreterError::new(
                            ErrorKind::TypeError,
                            "Pair only has xpart and ypart",
                        ));
                    }
                };
                // Propagate the component's dependency so equations work.
                if let Some((dx, dy)) = pair_dep {
                    let dep = if part == 0 { dx } else { dy };
                    if crate::equation::is_constant(&dep) {
                        // Fully known component — no dependency to track.
                        Ok(super::ExprResultValue {
                            exp: Value::Numeric(v),
                            ty: Type::Known,
                            dep: Some(dep),
                            pair_dep: None,
                        })
                    } else {
                        // Extract the primary VarId from the dep for LHS binding.
                        let primary_var = dep.iter().find_map(|t| t.var_id);
                        if let Some(vid) = primary_var {
                            self.lhs_tracking.last_lhs_binding = Some(LhsBinding::Variable {
                                id: vid,
                                negated: false,
                            });
                        }
                        Ok(super::ExprResultValue {
                            exp: Value::Numeric(v),
                            ty: Type::Dependent,
                            dep: Some(dep),
                            pair_dep: None,
                        })
                    }
                } else {
                    Ok(super::ExprResultValue::numeric_known(v))
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
                        ));
                    }
                };
                // If the operand was a transform variable, look up the
                // sub-part VarId so the result can participate in equation
                // solving (e.g. `xxpart T = 1`).
                if let Some(LhsBinding::Variable { id, .. }) = operand_binding {
                    if let VarValue::Transform {
                        tx,
                        ty,
                        txx,
                        txy,
                        tyx,
                        tyy,
                    } = self.variables.get(id).clone()
                    {
                        let sub_id = match part {
                            0 => tx,
                            1 => ty,
                            2 => txx,
                            3 => txy,
                            4 => tyx,
                            5 => tyy,
                            _ => unreachable!(),
                        };
                        let dep = self.numeric_dep_for_var(sub_id);
                        if crate::equation::is_constant(&dep) {
                            return Ok(super::ExprResultValue {
                                exp: Value::Numeric(v),
                                ty: Type::Known,
                                dep: Some(dep),
                                pair_dep: None,
                            });
                        }
                        let primary_var = dep.iter().find_map(|t| t.var_id);
                        if let Some(vid) = primary_var {
                            self.lhs_tracking.last_lhs_binding = Some(LhsBinding::Variable {
                                id: vid,
                                negated: false,
                            });
                        }
                        return Ok(super::ExprResultValue {
                            exp: Value::Numeric(crate::equation::constant_value(&dep).unwrap_or(v)),
                            ty: Type::Dependent,
                            dep: Some(dep),
                            pair_dep: None,
                        });
                    }
                }
                Ok(super::ExprResultValue::numeric_known(v))
            }
            _ => Err(InterpreterError::new(
                ErrorKind::TypeError,
                format!("{} has no xpart/ypart", input.ty()),
            )),
        }
    }

    /// Extract a color part, returning `(Value::Numeric, Type::Known)`.
    fn extract_color_part(val: &Value, part: usize) -> InterpResult<(Value, Type)> {
        if let Value::Color(c) = val {
            let v = match part {
                0 => c.r,
                1 => c.g,
                2 => c.b,
                _ => {
                    return Err(InterpreterError::new(
                        ErrorKind::TypeError,
                        "Invalid color part",
                    ));
                }
            };
            Ok((Value::Numeric(v), Type::Known))
        } else {
            Err(InterpreterError::new(
                ErrorKind::TypeError,
                format!("{} has no color parts", val.ty()),
            ))
        }
    }
}

fn plus_minus_value(op: PlusMinusOp, left: &Value, right: &Value) -> InterpResult<(Value, Type)> {
    let is_plus = op == PlusMinusOp::Plus;

    match (left, right) {
        (Value::Numeric(a), Value::Numeric(b)) => Ok((
            Value::Numeric(if is_plus { a + b } else { a - b }),
            Type::Known,
        )),
        (Value::Pair(ax, ay), Value::Pair(bx, by)) => Ok((
            if is_plus {
                Value::Pair(ax + bx, ay + by)
            } else {
                Value::Pair(ax - bx, ay - by)
            },
            Type::PairType,
        )),
        (Value::Color(a), Value::Color(b)) => Ok((
            Value::Color(if is_plus {
                Color::new(a.r + b.r, a.g + b.g, a.b + b.b)
            } else {
                Color::new(a.r - b.r, a.g - b.g, a.b - b.b)
            }),
            Type::ColorType,
        )),
        (Value::String(a), Value::String(b)) if is_plus => Err(InterpreterError::new(
            ErrorKind::TypeError,
            format!("Cannot add strings (use & for concatenation): \"{a}\" + \"{b}\""),
        )),
        _ => Err(InterpreterError::new(
            ErrorKind::TypeError,
            format!(
                "Incompatible types for {}: {} and {}",
                if is_plus { "+" } else { "-" },
                left.ty(),
                right.ty()
            ),
        )),
    }
}

fn tertiary_binary_value(
    op: TertiaryBinaryOp,
    left: &Value,
    right: &Value,
) -> InterpResult<(Value, Type)> {
    match op {
        // Pythagorean addition: `a ++ b = sqrt(a² + b²)`.
        TertiaryBinaryOp::PythagAdd => {
            let a = value_to_scalar(left)?;
            let b = value_to_scalar(right)?;
            Ok((Value::Numeric(a.hypot(b)), Type::Known))
        }
        TertiaryBinaryOp::PythagSub => {
            let a = value_to_scalar(left)?;
            let b = value_to_scalar(right)?;
            Ok((Value::Numeric(math::pyth_sub(a, b)), Type::Known))
        }
        TertiaryBinaryOp::Or => {
            let a = value_to_bool(left)?;
            let b = value_to_bool(right)?;
            Ok((Value::Boolean(a || b), Type::Boolean))
        }
    }
}

fn expression_binary_value(
    op: ExpressionBinaryOp,
    left: &Value,
    right: &Value,
) -> InterpResult<(Value, Type)> {
    match op {
        ExpressionBinaryOp::LessThan => Ok((
            Value::Boolean(Interpreter::compare_values(left, right, |ord| {
                ord == Ordering::Less
            })?),
            Type::Boolean,
        )),
        ExpressionBinaryOp::LessOrEqual => Ok((
            Value::Boolean(Interpreter::compare_values(left, right, |ord| {
                ord != Ordering::Greater
            })?),
            Type::Boolean,
        )),
        ExpressionBinaryOp::GreaterThan => Ok((
            Value::Boolean(Interpreter::compare_values(left, right, |ord| {
                ord == Ordering::Greater
            })?),
            Type::Boolean,
        )),
        ExpressionBinaryOp::GreaterOrEqual => Ok((
            Value::Boolean(Interpreter::compare_values(left, right, |ord| {
                ord != Ordering::Less
            })?),
            Type::Boolean,
        )),
        ExpressionBinaryOp::EqualTo => Ok((Value::Boolean(left == right), Type::Boolean)),
        ExpressionBinaryOp::UnequalTo => Ok((Value::Boolean(left != right), Type::Boolean)),
        ExpressionBinaryOp::Concatenate => {
            let a = value_to_string(left)?;
            let b = value_to_string(right)?;
            let result = format!("{a}{b}");
            Ok((Value::String(Arc::from(result)), Type::String))
        }
        ExpressionBinaryOp::IntersectionTimes => {
            let p1 = value_to_path(left)?;
            let p2 = value_to_path(right)?;
            let value = postmeta_graphics::intersection::intersection_times(p1, p2).map_or_else(
                || Value::Pair(-1.0, -1.0),
                |isect| Value::Pair(isect.t1, isect.t2),
            );
            Ok((value, Type::PairType))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn compare_values_nan_is_not_comparable() {
        let is_less_or_equal =
            Interpreter::compare_values(&Value::Numeric(f64::NAN), &Value::Numeric(1.0), |ord| {
                ord != Ordering::Greater
            })
            .expect("comparison should not error");
        assert!(!is_less_or_equal);
    }

    #[test]
    fn unary_char_from_numeric_code() {
        let mut seed = 0_u64;
        let (val, ty) = Interpreter::eval_unary(UnaryOp::Char, &Value::Numeric(34.0), &mut seed)
            .expect("char should evaluate");
        assert_eq!(ty, Type::String);
        assert_eq!(val, Value::String(Arc::from("\"")));
    }
}
