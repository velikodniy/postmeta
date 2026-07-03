//! Operator dispatch.
//!
//! Implements all nullary, unary, and binary operators at each precedence
//! level.  This module keeps the thin dispatch `match`es; the per-domain
//! evaluation functions live in the submodules.

mod arithmetic;
mod paths;
mod pictures;
mod strings;
mod text;
mod transforms;

pub(in crate::interpreter) use text::compute_text_metrics;

use std::cmp::Ordering;
use std::sync::Arc;

use postmeta_fonts::FontProvider;
use postmeta_graphics::math;
use postmeta_graphics::types::{Pen, Picture, Transform};

use crate::command::{
    ExpressionBinaryOp, NullaryOp, PlusMinusOp, PrimaryBinaryOp, SecondaryBinaryOp,
    TertiaryBinaryOp, UnaryOp,
};
use crate::error::{ErrorKind, InterpResult, InterpreterError};
use crate::types::{Type, Value};

use super::Interpreter;
use super::helpers::{
    value_to_bool, value_to_pair, value_to_scalar, value_to_string, value_to_transform,
};

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
                Value::Numeric(math::normal_deviate(&mut self.state.random_seed)),
                Type::Known,
            ),
            NullaryOp::JobName => (
                Value::String(Arc::from(self.state.job_name.as_str())),
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
        input: &Value,
        pair_dep: Option<(crate::equation::DepList, crate::equation::DepList)>,
    ) -> InterpResult<super::ExprResultValue> {
        // Save the operand binding before clearing — part-extraction operators
        // need it to find transform sub-part VarIds for equation solving.
        let operand_binding = self.lhs_tracking.last_lhs_binding.take();

        // Part-extraction operators need pair_dep access — handle them here.
        match op {
            UnaryOp::XPart => {
                return self.extract_part(input, 0, pair_dep, operand_binding.as_ref());
            }
            UnaryOp::YPart => {
                return self.extract_part(input, 1, pair_dep, operand_binding.as_ref());
            }
            UnaryOp::XXPart => {
                return self.extract_part(input, 2, pair_dep, operand_binding.as_ref());
            }
            UnaryOp::XYPart => {
                return self.extract_part(input, 3, pair_dep, operand_binding.as_ref());
            }
            UnaryOp::YXPart => {
                return self.extract_part(input, 4, pair_dep, operand_binding.as_ref());
            }
            UnaryOp::YYPart => {
                return self.extract_part(input, 5, pair_dep, operand_binding.as_ref());
            }
            UnaryOp::ReadFrom => {
                let name = value_to_string(input)?;
                let text = self
                    .state
                    .fs
                    .read_line(&name)
                    .unwrap_or_else(|| "\0".to_string());
                return Ok(super::ExprResultValue {
                    exp: Value::String(Arc::from(text.as_str())),
                    ty: Type::String,
                    dep: None,
                    pair_dep: None,
                });
            }
            _ => {}
        }

        // All remaining unary operators are pure value transformations.
        // Access both fields through `self.state` so the borrow checker can
        // see they are disjoint (Deref would borrow all of `self`).
        let fonts = self.state.font_provider.as_deref();
        let (val, ty) = Self::eval_unary(op, input, &mut self.state.random_seed, fonts)?;
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
        fonts: Option<&dyn FontProvider>,
    ) -> InterpResult<(Value, Type)> {
        match op {
            UnaryOp::Not => {
                let b = value_to_bool(input)?;
                Ok((Value::Boolean(!b), Type::Boolean))
            }
            UnaryOp::Sqrt => arithmetic::sqrt(input),
            UnaryOp::SinD => arithmetic::sind(input),
            UnaryOp::CosD => arithmetic::cosd(input),
            UnaryOp::Floor => arithmetic::floor(input),
            UnaryOp::Odd => arithmetic::odd(input),
            UnaryOp::MExp => arithmetic::mexp(input),
            UnaryOp::MLog => arithmetic::mlog(input),
            UnaryOp::Angle => arithmetic::angle(input),
            UnaryOp::UniformDeviate => arithmetic::uniform_deviate(input, random_seed),
            UnaryOp::Length => arithmetic::length(input),
            UnaryOp::Oct => strings::oct(input),
            UnaryOp::Hex => strings::hex(input),
            UnaryOp::ASCII => strings::ascii(input),
            UnaryOp::Char => strings::char_op(input),
            UnaryOp::Decimal => strings::decimal(input),
            UnaryOp::Reverse => paths::reverse(input),
            UnaryOp::MakePath => paths::make_path(input),
            UnaryOp::MakePen => paths::make_pen(input),
            UnaryOp::ArcLength => paths::arc_length(input),
            UnaryOp::TurningNumber => paths::turning_number(input),
            UnaryOp::CycleOp => {
                let is_cyclic = matches!(input, Value::Path(p) if p.is_cyclic());
                Ok((Value::Boolean(is_cyclic), Type::Boolean))
            }
            UnaryOp::RedPart => Self::extract_color_part(input, 0),
            UnaryOp::GreenPart => Self::extract_color_part(input, 1),
            UnaryOp::BluePart => Self::extract_color_part(input, 2),
            UnaryOp::ColorModel => Self::extract_color_model(input),
            UnaryOp::GreyPart => Self::extract_grey_part(input),
            UnaryOp::CyanPart | UnaryOp::MagentaPart | UnaryOp::YellowPart | UnaryOp::BlackPart => {
                // CMYK not supported — always return 0.
                // For color values (non-picture), this is still 0.
                Ok((Value::Numeric(0.0), Type::Known))
            }
            UnaryOp::LLCorner | UnaryOp::LRCorner | UnaryOp::ULCorner | UnaryOp::URCorner => {
                pictures::corner(op, input)
            }
            // TODO: Load actual font metrics (.tfm or hardcoded CMR) for accurate results.
            UnaryOp::CharExists => {
                // Stub: assume all byte-range character codes exist.
                let code = value_to_scalar(input)?;
                let exists = (0.0..=255.0).contains(&code) && (code - code.floor()).abs() < 0.001;
                Ok((Value::Boolean(exists), Type::Boolean))
            }
            UnaryOp::FontSize => text::font_size(input, fonts),
            UnaryOp::TextPart => pictures::text_part(input),
            UnaryOp::FontPart => pictures::font_part(input),
            UnaryOp::PathPart => pictures::path_part(input),
            UnaryOp::PenPart => pictures::pen_part(input),
            UnaryOp::DashPart => pictures::dash_part(input),
            UnaryOp::FilledOp => pictures::is_filled(input),
            UnaryOp::StrokedOp => pictures::is_stroked(input),
            UnaryOp::TextualOp => pictures::is_textual(input),
            UnaryOp::ClippedOp => pictures::is_clipped(input),
            UnaryOp::BoundedOp => pictures::is_bounded(input),
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
            PrimaryBinaryOp::PointOf => paths::point_of(first, second),
            PrimaryBinaryOp::PrecontrolOf => paths::precontrol_of(first, second),
            PrimaryBinaryOp::PostcontrolOf => paths::postcontrol_of(first, second),
            PrimaryBinaryOp::SubpathOf => paths::subpath_of(first, second),
            PrimaryBinaryOp::PenOffsetOf => paths::pen_offset_of(first, second),
            PrimaryBinaryOp::SubstringOf => strings::substring_of(first, second),
            PrimaryBinaryOp::ArcTimeOf => paths::arc_time_of(first, second),
            PrimaryBinaryOp::DirectionTimeOf => paths::direction_time_of(first, second),
        }
    }

    /// Execute a secondary binary operator.
    pub(super) fn do_secondary_binary(
        op: SecondaryBinaryOp,
        left: &Value,
        right: &Value,
        fonts: Option<&dyn FontProvider>,
    ) -> InterpResult<(Value, Type)> {
        match op {
            SecondaryBinaryOp::Times => arithmetic::times(left, right),
            SecondaryBinaryOp::Scaled => {
                let factor = value_to_scalar(right)?;
                transforms::apply_transform(left, &Transform::scaled(factor))
            }
            SecondaryBinaryOp::Shifted => {
                let (dx, dy) = value_to_pair(right)?;
                transforms::apply_transform(left, &Transform::shifted(dx, dy))
            }
            SecondaryBinaryOp::Rotated => {
                let angle = value_to_scalar(right)?;
                transforms::apply_transform(left, &Transform::rotated(angle))
            }
            SecondaryBinaryOp::XScaled => {
                let factor = value_to_scalar(right)?;
                transforms::apply_transform(left, &Transform::xscaled(factor))
            }
            SecondaryBinaryOp::YScaled => {
                let factor = value_to_scalar(right)?;
                transforms::apply_transform(left, &Transform::yscaled(factor))
            }
            SecondaryBinaryOp::Slanted => {
                let factor = value_to_scalar(right)?;
                transforms::apply_transform(left, &Transform::slanted(factor))
            }
            SecondaryBinaryOp::ZScaled => {
                let (a, b) = value_to_pair(right)?;
                transforms::apply_transform(left, &Transform::zscaled(a, b))
            }
            SecondaryBinaryOp::Transformed => {
                let t = value_to_transform(right)?;
                transforms::apply_transform(left, &t)
            }
            SecondaryBinaryOp::Infont => text::infont(left, right, fonts),
            SecondaryBinaryOp::Over => Err(InterpreterError::new(
                ErrorKind::InvalidExpression,
                "Unimplemented secondary binary: over",
            )),
        }
    }

    /// Execute plus or minus on two operands.
    pub(super) fn do_plus_minus(
        op: PlusMinusOp,
        left: &Value,
        right: &Value,
    ) -> InterpResult<(Value, Type)> {
        arithmetic::plus_minus_value(op, left, right)
    }

    /// Perform implicit multiplication (e.g., `3x`, `2bp`, `.5(1,2)`).
    ///
    /// The `factor` is the numeric value on the left; `cur_exp`/`cur_type`
    /// hold the right operand (the result of the recursive `scan_primary`).
    pub(super) fn do_implicit_mul(factor: &Value, right: &Value) -> InterpResult<(Value, Type)> {
        arithmetic::implicit_mul(factor, right)
    }

    /// Execute a tertiary binary operator.
    pub(super) fn do_tertiary_binary(
        op: TertiaryBinaryOp,
        left: &Value,
        right: &Value,
    ) -> InterpResult<(Value, Type)> {
        arithmetic::tertiary_binary_value(op, left, right)
    }

    /// Execute an expression binary operator.
    pub(super) fn do_expression_binary(
        op: ExpressionBinaryOp,
        left: &Value,
        right: &Value,
    ) -> InterpResult<(Value, Type)> {
        arithmetic::expression_binary_value(op, left, right)
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
        let (val, ty) =
            Interpreter::eval_unary(UnaryOp::Char, &Value::Numeric(34.0), &mut seed, None)
                .expect("char should evaluate");
        assert_eq!(ty, Type::String);
        assert_eq!(val, Value::String(Arc::from("\"")));
    }
}
