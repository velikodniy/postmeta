//! Expression parser — four precedence levels.
//!
//! The recursive-descent parser follows `MetaPost`'s four precedence levels:
//! - `scan_primary`: atoms, unary operators, grouping
//! - `scan_secondary`: `*`, `/`, `scaled`, `rotated`, etc.
//! - `scan_tertiary`: `+`, `-`, `++`, `+-+`
//! - `scan_expression`: `=`, `<`, `>`, path construction

use std::fmt::Write;
use std::sync::Arc;

use crate::command::{
    Command, ExpressionBinaryOp, NullaryOp, PlusMinusOp, PrimaryBinaryOp, SecondaryBinaryOp,
    StrOpOp, TertiaryBinaryOp, TypeNameOp, UnaryOp,
};
use crate::equation::{const_dep, constant_value, dep_add_scaled, dep_scale};
use crate::error::{ErrorKind, InterpResult, InterpreterError};
use crate::types::{Type, Value};
use crate::variables::{SuffixSegment, VarValue};

use super::helpers::{value_to_bool, value_to_pair, value_to_scalar, value_to_transform};
use super::{ExprResultValue, Interpreter, LhsBinding};

impl Interpreter {
    /// Parse and evaluate a primary expression, returning the result.
    pub(super) fn scan_primary(&mut self) -> InterpResult<ExprResultValue> {
        self.cur_expr.pair_dep = None;
        match self.cur.command {
            Command::NumericToken => {
                if let crate::token::TokenKind::Numeric(v) = self.cur.token.kind {
                    self.cur_expr.exp = Value::Numeric(v);
                    self.cur_expr.ty = Type::Known;
                    self.cur_expr.dep = Some(const_dep(v));
                }
                self.lhs_tracking.last_lhs_binding = None;
                self.get_x_next();
                // Check for fraction: 3/4 as a primary
                if self.cur.command == Command::Slash {
                    self.get_x_next();
                    if let crate::token::TokenKind::Numeric(denom) = self.cur.token.kind {
                        if let Value::Numeric(numer) = self.cur_expr.exp {
                            if denom.abs() > f64::EPSILON {
                                let frac = numer / denom;
                                self.cur_expr.exp = Value::Numeric(frac);
                                self.cur_expr.dep = Some(const_dep(frac));
                            } else {
                                self.report_error(ErrorKind::ArithmeticError, "Division by zero");
                            }
                        }
                        self.get_x_next();
                    } else {
                        // Not a fraction — restore `/` for the secondary
                        // level to handle as division (mp.web §15371-15374).
                        self.back_input();
                        self.cur.command = Command::Slash;
                        self.cur.modifier =
                            crate::command::SecondaryBinaryOp::Over as u16;
                        return Ok(self.take_cur_result());
                    }
                }
                // Implicit multiplication: `3x`, `2bp`, `.5(1,2)`, etc.
                // Triggers when a numeric is followed by a token in
                // [min_primary_command..numeric_token) — i.e., anything
                // that can start a primary EXCEPT +/- and another number.
                if self.cur.command.can_start_implicit_mul() {
                    let factor_result = self.take_cur_result();
                    let factor_dep = factor_result.dep;
                    let factor = factor_result.exp;
                    let right_result = self.scan_primary()?;
                    self.lhs_tracking.last_lhs_binding = None;
                    let (val, ty) = Self::do_implicit_mul(&factor, &right_result.exp)?;
                    self.cur_expr.exp = val;
                    self.cur_expr.ty = ty;
                    let factor_val = factor_dep
                        .as_ref()
                        .and_then(constant_value)
                        .unwrap_or_else(|| value_to_scalar(&factor).unwrap_or(1.0));
                    self.cur_expr.dep = right_result.dep.map(|mut d| {
                        dep_scale(&mut d, factor_val);
                        d
                    });
                    if let Some((mut dx, mut dy)) = right_result.pair_dep {
                        dep_scale(&mut dx, factor_val);
                        dep_scale(&mut dy, factor_val);
                        self.cur_expr.pair_dep = Some((dx, dy));
                    }
                }
                Ok(())
            }

            Command::StringToken => {
                if let crate::token::TokenKind::StringLit(ref s) = self.cur.token.kind {
                    self.cur_expr.exp = Value::String(Arc::from(s.as_str()));
                    self.cur_expr.ty = Type::String;
                }
                self.cur_expr.dep = None;
                self.lhs_tracking.last_lhs_binding = None;
                self.get_x_next();
                Ok(())
            }

            Command::Nullary => {
                let Some(op) = NullaryOp::from_modifier(self.cur.modifier) else {
                    return Err(InterpreterError::new(
                        ErrorKind::UnexpectedToken,
                        "Invalid nullary operator modifier",
                    ));
                };
                self.get_x_next();
                self.lhs_tracking.last_lhs_binding = None;
                let (val, ty) = self.eval_nullary(op);
                self.cur_expr.dep = if let Value::Numeric(v) = &val {
                    Some(const_dep(*v))
                } else {
                    None
                };
                self.cur_expr.exp = val;
                self.cur_expr.ty = ty;
                Ok(())
            }

            Command::Unary => {
                let Some(op) = UnaryOp::from_modifier(self.cur.modifier) else {
                    return Err(InterpreterError::new(
                        ErrorKind::UnexpectedToken,
                        "Invalid unary operator modifier",
                    ));
                };
                self.get_x_next();
                // Take the operand, but preserve pair_dep for part-extraction
                // ops that propagate it into the equation solver.
                let operand_result = self.scan_primary()?;
                self.cur_expr.pair_dep = operand_result.pair_dep;
                self.do_unary(op, operand_result.exp)?;
                // Part-extraction ops (xpart, ypart, etc.) set up cur_dep
                // themselves for equation solving; don't clear it for those.
                // For all other unary ops the result is a known scalar,
                // so any stale dep must be dropped.
                if self.cur_expr.pair_dep.is_none() && self.cur_expr.ty == Type::Known {
                    self.cur_expr.dep = None;
                }
                Ok(())
            }

            Command::PlusOrMinus => {
                // Unary plus or minus
                let is_minus = PlusMinusOp::from_modifier(self.cur.modifier)
                    == Some(PlusMinusOp::Minus);
                self.get_x_next();
                let result = self.scan_primary()?;
                self.set_cur_result(result);
                if is_minus {
                    self.negate_cur_exp();
                }
                Ok(())
            }

            Command::LeftDelimiter => {
                // ( expr ) or ( expr , expr ) for pair/color
                let expected_delimiter = self.cur.modifier;
                self.get_x_next();
                let first_result = self.scan_expression()?;

                if self.cur.command == Command::Comma {
                    // Pair or color
                    let first = first_result.exp;
                    let first_binding = self.lhs_tracking.last_lhs_binding.clone();
                    self.get_x_next();
                    let second_result = self.scan_expression()?;
                    let second = second_result.exp;
                    let second_binding = self.lhs_tracking.last_lhs_binding.clone();

                if self.cur.command == Command::Comma {
                    // `first_result` consumed in pair/color branch below.
                        // Color: (r, g, b)
                        self.get_x_next();
                        let third_result = self.scan_expression()?;
                        let third = third_result.exp;
                        let third_binding = self.lhs_tracking.last_lhs_binding.clone();

                        let r = value_to_scalar(&first)?;
                        let g = value_to_scalar(&second)?;
                        let b = value_to_scalar(&third)?;
                        self.cur_expr.exp = Value::Color(postmeta_graphics::types::Color::new(r, g, b));
                        self.cur_expr.ty = Type::ColorType;
                        let _ = (first_result.dep, second_result.dep, third_result.dep);
                        self.lhs_tracking.last_lhs_binding = if first_binding.is_some()
                            || second_binding.is_some()
                            || third_binding.is_some()
                        {
                            Some(LhsBinding::Color {
                                r: first_binding.map(Box::new),
                                g: second_binding.map(Box::new),
                                b: third_binding.map(Box::new),
                            })
                        } else {
                            None
                        };
                    } else {
                        // Pair: (x, y)
                        let x = value_to_scalar(&first)?;
                        let y = value_to_scalar(&second)?;
                        self.cur_expr.exp = Value::Pair(x, y);
                        self.cur_expr.ty = Type::PairType;
                        self.cur_expr.pair_dep = Some((
                            first_result.dep.unwrap_or_else(|| const_dep(x)),
                            second_result.dep.unwrap_or_else(|| const_dep(y)),
                        ));
                        self.lhs_tracking.last_lhs_binding =
                            if first_binding.is_some() || second_binding.is_some() {
                                Some(LhsBinding::Pair {
                                    x: first_binding.map(Box::new),
                                    y: second_binding.map(Box::new),
                                })
                            } else {
                                None
                            };
                    }
                    self.cur_expr.dep = None;
                } else {
                    // Single expression in parens — restore result
                    self.set_cur_result(first_result);
                }

                // Expect closing delimiter
                if self.cur.command == Command::RightDelimiter
                    && self.cur.modifier == expected_delimiter
                {
                    self.get_x_next();
                } else {
                    let message = if expected_delimiter == 0 {
                        "Expected `)`"
                    } else {
                        "Expected matching right delimiter"
                    };
                    self.report_error(ErrorKind::MissingToken, message);
                }
                Ok(())
            }

            Command::BeginGroup => {
                self.save_stack.push_boundary();
                self.get_x_next();
                // Execute statements until endgroup
                while self.cur.command != Command::EndGroup && self.cur.command != Command::Stop {
                    self.do_statement()?;
                }
                // Restore scope — but preserve cur_exp/cur_type/cur_dep from
                // the last expression in the group (the group's return value).
                self.do_endgroup();
                self.get_x_next();
                self.lhs_tracking.last_lhs_binding = None;
                // Intentionally keep cur_dep: the group result's dependency
                // info must survive so that unknown numerics (e.g. from
                // `whatever`) can participate in equations after the group.
                Ok(())
            }

            Command::TagToken => {
                let result = self.scan_tag_token()?;
                self.set_cur_result(result);
                Ok(())
            }

            Command::InternalQuantity => {
                let idx = self.cur.modifier;
                self.cur_expr.exp = Value::Numeric(self.internals.get(idx));
                self.cur_expr.ty = Type::Known;
                self.cur_expr.dep = Some(const_dep(self.internals.get(idx)));
                // Track for assignment LHS
                self.lhs_tracking.last_lhs_binding = Some(LhsBinding::Internal { idx });
                self.get_x_next();
                Ok(())
            }

            Command::PrimaryBinary => {
                // "expr X of Y" pattern
                let op = self.cur.modifier;
                self.get_x_next();
                let first_result = self.scan_expression()?;
                // Expect "of"
                if self.cur.command != Command::OfToken {
                    return Err(InterpreterError::new(
                        ErrorKind::MissingToken,
                        "Missing `of`",
                    ));
                }
                let first = first_result.exp;
                self.get_x_next();
                let second_result = self.scan_primary()?;
                self.lhs_tracking.last_lhs_binding = None;
                let Some(op) = PrimaryBinaryOp::from_modifier(op) else {
                    return Err(InterpreterError::new(
                        ErrorKind::UnexpectedToken,
                        "Invalid primary binary operator modifier",
                    ));
                };
                let second = second_result.exp;
                let (val, ty) = Self::do_primary_binary(op, &first, &second)?;
                self.cur_expr.exp = val;
                self.cur_expr.ty = ty;
                Ok(())
            }

            Command::Cycle => {
                // The `cycle` keyword in an expression context evaluates to true
                // if the current expression is a cyclic path. But as a primary
                // it's used in path construction — handle that at expression level.
                self.cur_expr.exp = Value::Boolean(false);
                self.cur_expr.ty = Type::Boolean;
                self.lhs_tracking.last_lhs_binding = None;
                self.cur_expr.dep = None;
                self.get_x_next();
                Ok(())
            }

            Command::StrOp => {
                let op = StrOpOp::from_modifier(self.cur.modifier);
                self.get_x_next();
                if op == Some(StrOpOp::Str) {
                    // `str` <suffix> — converts suffix to string
                    let name = if let crate::token::TokenKind::Symbolic(ref s) = self.cur.token.kind
                    {
                        s.clone()
                    } else {
                        String::new()
                    };
                    self.get_x_next();
                    self.cur_expr.exp = Value::String(Arc::from(name.as_str()));
                } else {
                    // readfrom etc. — not yet implemented
                    self.cur_expr.exp = Value::String(Arc::from(""));
                }
                self.cur_expr.ty = Type::String;
                self.lhs_tracking.last_lhs_binding = None;
                self.cur_expr.dep = None;
                Ok(())
            }

            Command::CapsuleToken => {
                // A capsule: an already-evaluated expression pushed back
                // via back_expr. Extract the payload directly.
                if let Some((val, ty, dep, pair_dep)) = self.cur.capsule.take() {
                    self.cur_expr.exp = val;
                    self.cur_expr.ty = ty;
                    self.cur_expr.dep = dep;
                    self.cur_expr.pair_dep = pair_dep;
                } else {
                    // CapsuleToken without payload — shouldn't happen, treat as vacuous
                    self.cur_expr.exp = Value::Vacuous;
                    self.cur_expr.ty = Type::Vacuous;
                    self.cur_expr.dep = None;
                    self.cur_expr.pair_dep = None;
                }
                self.lhs_tracking.last_lhs_binding = None;
                self.get_x_next();
                Ok(())
            }

            Command::TypeName => {
                // Type name as unary operator — type test.
                // `numeric <primary>` → boolean, true if the primary is a known numeric.
                // Same for `boolean`, `string`, `pen`, `path`, `picture`,
                // `transform`, `color`, `pair`.
                //
                // See mp.web §740: each type_name acts as a type_range test.
                let op = TypeNameOp::from_modifier(self.cur.modifier);
                self.get_x_next();
                let primary_result = self.scan_primary()?;
                let ty = primary_result.ty;
                let result = match op {
                    Some(TypeNameOp::Numeric) => {
                        // numeric: type_range(known)(independent)
                        ty >= Type::Known && ty <= Type::Independent
                    }
                    Some(TypeNameOp::Boolean) => {
                        ty == Type::Boolean || ty == Type::UnknownBoolean
                    }
                    Some(TypeNameOp::String) => {
                        ty == Type::String || ty == Type::UnknownString
                    }
                    Some(TypeNameOp::Pen) => ty == Type::Pen || ty == Type::UnknownPen,
                    Some(TypeNameOp::Path) => {
                        ty == Type::Path || ty == Type::UnknownPath
                    }
                    Some(TypeNameOp::Picture) => {
                        ty == Type::Picture || ty == Type::UnknownPicture
                    }
                    Some(TypeNameOp::Transform) => ty == Type::TransformType,
                    Some(TypeNameOp::Color) => ty == Type::ColorType,
                    Some(TypeNameOp::Pair) => ty == Type::PairType,
                    Some(TypeNameOp::Known) => {
                        // mp.web §746: known if cur_type < dependent
                        (ty as u8) < (Type::Dependent as u8)
                    }
                    Some(TypeNameOp::Unknown) => {
                        // mp.web §746: unknown if cur_type >= dependent
                        (ty as u8) >= (Type::Dependent as u8)
                    }
                    _ => false,
                };
                self.cur_expr.exp = Value::Boolean(result);
                self.cur_expr.ty = Type::Boolean;
                self.lhs_tracking.last_lhs_binding = None;
                self.cur_expr.dep = None;
                Ok(())
            }

            _ => {
                // Missing primary — set to vacuous
                self.cur_expr.exp = Value::Vacuous;
                self.cur_expr.ty = Type::Vacuous;
                self.lhs_tracking.last_lhs_binding = None;
                self.cur_expr.dep = None;
                Ok(())
            }
        }?;

        // Check for mediation: a[b,c] = (1-a)*b + a*c
        if self.cur.command == Command::LeftBracket {
            if let Value::Numeric(a) = self.cur_expr.exp {
                let a_dep = self.cur_expr.dep.clone().unwrap_or_else(|| const_dep(a));
                self.get_x_next();
                let b_result = self.scan_expression()?;
                let b_binding = self.lhs_tracking.last_lhs_binding.clone();
                let b_dep = b_result.dep.or_else(|| {
                    if let Some(LhsBinding::Variable { id, .. }) = b_binding {
                        Some(self.numeric_dep_for_var(id))
                    } else {
                        None
                    }
                });
                let b_pair_dep = b_result.pair_dep;
                let b = b_result.exp;
                if self.cur.command == Command::Comma {
                    self.get_x_next();
                } else {
                    return Err(InterpreterError::new(
                        ErrorKind::MissingToken,
                        "Expected `,` in mediation a[b,c]",
                    ));
                }
                let c_result = self.scan_expression()?;
                let c_binding = self.lhs_tracking.last_lhs_binding.clone();
                let c_dep = c_result.dep.or_else(|| {
                    if let Some(LhsBinding::Variable { id, .. }) = c_binding {
                        Some(self.numeric_dep_for_var(id))
                    } else {
                        None
                    }
                });
                let c_pair_dep = c_result.pair_dep;
                let c = c_result.exp;
                if self.cur.command == Command::RightBracket {
                    self.get_x_next();
                } else {
                    self.report_error(ErrorKind::MissingToken, "Expected `]` in mediation a[b,c]");
                }

                // a[b,c] = b + a*(c-b) = (1-a)*b + a*c
                let one_minus_a = 1.0 - a;
                match (b, c) {
                    (Value::Numeric(bn), Value::Numeric(cn)) => {
                        self.cur_expr.exp = Value::Numeric(a.mul_add(cn - bn, bn));
                        self.cur_expr.ty = Type::Known;
                        let b_dep = b_dep.unwrap_or_else(|| const_dep(bn));
                        let c_dep = c_dep.unwrap_or_else(|| const_dep(cn));
                        let a_is_linear = constant_value(&a_dep).is_none();
                        let bc_have_linear =
                            constant_value(&b_dep).is_none() || constant_value(&c_dep).is_none();

                        self.cur_expr.dep = if a_is_linear && bc_have_linear {
                            None
                        } else if a_is_linear {
                            Some(dep_add_scaled(&b_dep, &a_dep, cn - bn))
                        } else {
                            let mut dep = b_dep;
                            dep_scale(&mut dep, one_minus_a);
                            Some(dep_add_scaled(&dep, &c_dep, a))
                        };
                        self.cur_expr.pair_dep = None;
                    }
                    (Value::Pair(bx, by), Value::Pair(cx, cy)) => {
                        self.cur_expr.exp =
                            Value::Pair(one_minus_a * bx + a * cx, one_minus_a * by + a * cy);
                        self.cur_expr.ty = Type::PairType;
                        self.cur_expr.dep = None;
                        let (b_dep_x, b_dep_y) =
                            b_pair_dep.unwrap_or_else(|| (const_dep(bx), const_dep(by)));
                        let (c_dep_x, c_dep_y) =
                            c_pair_dep.unwrap_or_else(|| (const_dep(cx), const_dep(cy)));
                        let a_is_linear = constant_value(&a_dep).is_none();
                        let pair_has_linear = constant_value(&b_dep_x).is_none()
                            || constant_value(&b_dep_y).is_none()
                            || constant_value(&c_dep_x).is_none()
                            || constant_value(&c_dep_y).is_none();

                        self.cur_expr.pair_dep = if a_is_linear && pair_has_linear {
                            None
                        } else if a_is_linear {
                            Some((
                                dep_add_scaled(&b_dep_x, &a_dep, cx - bx),
                                dep_add_scaled(&b_dep_y, &a_dep, cy - by),
                            ))
                        } else {
                            let mut dep_x = b_dep_x;
                            dep_scale(&mut dep_x, one_minus_a);
                            dep_x = dep_add_scaled(&dep_x, &c_dep_x, a);

                            let mut dep_y = b_dep_y;
                            dep_scale(&mut dep_y, one_minus_a);
                            dep_y = dep_add_scaled(&dep_y, &c_dep_y, a);

                            Some((dep_x, dep_y))
                        };
                    }
                    (Value::Color(bc), Value::Color(cc)) => {
                        self.cur_expr.exp = Value::Color(postmeta_graphics::types::Color::new(
                            one_minus_a * bc.r + a * cc.r,
                            one_minus_a * bc.g + a * cc.g,
                            one_minus_a * bc.b + a * cc.b,
                        ));
                        self.cur_expr.ty = Type::ColorType;
                        self.cur_expr.dep = None;
                        self.cur_expr.pair_dep = None;
                    }
                    (Value::Transform(bt), Value::Transform(ct)) => {
                        self.cur_expr.exp = Value::Transform(postmeta_graphics::types::Transform {
                            tx: one_minus_a * bt.tx + a * ct.tx,
                            ty: one_minus_a * bt.ty + a * ct.ty,
                            txx: one_minus_a * bt.txx + a * ct.txx,
                            txy: one_minus_a * bt.txy + a * ct.txy,
                            tyx: one_minus_a * bt.tyx + a * ct.tyx,
                            tyy: one_minus_a * bt.tyy + a * ct.tyy,
                        });
                        self.cur_expr.ty = Type::TransformType;
                        self.cur_expr.dep = None;
                        self.cur_expr.pair_dep = None;
                    }
                    (bv, cv) => {
                        return Err(InterpreterError::new(
                            ErrorKind::TypeError,
                            format!(
                                "Mediation requires matching types, got {} and {}",
                                bv.ty(),
                                cv.ty()
                            ),
                        ));
                    }
                }

                self.lhs_tracking.last_lhs_binding = None;
            }
        }

        Ok(self.take_cur_result())
    }

    fn scan_tag_token(&mut self) -> InterpResult<ExprResultValue> {
        // Variable reference — scan suffix parts to form compound name.
        //
        // MetaPost variable names are structured: `laboff.lft`, `z.r`,
        // etc. The scanner drops `.` separators, so suffixes appear as
        // consecutive tokens.
        //
        // The suffix loop accepts only tokens with command codes in the
        // range [`InternalQuantity`..`NumericToken`] (42..44 in mp.web).
        // This is how `vardef` macros like `lft` can appear as suffixes:
        // vardefs keep `TagToken` (43) as their command code, unlike
        // regular `def` macros which use `DefinedMacro` (13).
        //
        // After suffix collection, if the result is a standalone root
        // that has a vardef in `self.macros`, we trigger macro expansion
        // instead of variable lookup.
        let root_sym = self.cur.sym;
        let mut name = self
            .cur_symbolic_name()
            .map_or_else(String::new, std::borrow::ToOwned::to_owned);

        let mut has_suffixes = false;
        let mut suffix_segs: Vec<SuffixSegment> = Vec::new();

        // Check early if this is a standalone vardef macro.
        let is_root_vardef = root_sym.is_some_and(|s| self.macros.get(&s).is_some_and(|m| m.is_vardef));

        // Advance to next token. We use `get_x_next` (expanding) as
        // mp.web does — since vardefs keep `TagToken`, they won't be
        // expanded by `get_x_next`.
        self.get_x_next();

        // Suffix loop: collect symbolic suffixes, numeric subscripts,
        // and bracketed subscript expressions `[expr]`.
        //
        // For vardef roots, do NOT collect suffix tokens here; following
        // tokens belong to undelimited macro arguments (e.g. `foo p`).
        loop {
            if !is_root_vardef
                && (self.cur.command == Command::TagToken
                    || self.cur.command == Command::InternalQuantity)
            {
                if let crate::token::TokenKind::Symbolic(ref s) = self.cur.token.kind {
                    if let Some(sym) = self.cur.sym {
                        suffix_segs.push(SuffixSegment::Attr(sym));
                    }
                    name.push('.');
                    name.push_str(s);
                }
                has_suffixes = true;
                self.get_x_next();
            } else if !is_root_vardef && self.cur.command == Command::NumericToken {
                // Bare numeric subscript: pen_3
                if let crate::token::TokenKind::Numeric(v) = self.cur.token.kind {
                    let _ = write!(name, "[{}]", v as i64);
                    suffix_segs.push(SuffixSegment::Subscript);
                }
                has_suffixes = true;
                self.get_x_next();
                } else if !is_root_vardef && self.cur.command == Command::LeftBracket {
                // Speculatively scan for a bracketed subscript: var[expr].
                // If the expression is followed by `]`, this is a subscript.
                // Otherwise (e.g. `,` in `lambda[A,B]`), back up and let
                // the mediation handler deal with it (mp.web §1489-1506).
                self.get_x_next(); // skip `[`
                let subscript_result = self.scan_expression()?;
                if self.cur.command == Command::RightBracket {
                    // Subscript: var[expr]
                    let subscript = match &subscript_result.exp {
                        Value::Numeric(v) => *v as i64,
                        _ => 0,
                    };
                    let _ = write!(name, "[{subscript}]");
                    suffix_segs.push(SuffixSegment::Subscript);
                    self.get_x_next();
                    has_suffixes = true;
                } else {
                    // Not a subscript — put the expression and
                    // the current token back, then restore `[`
                    // as the current command so the mediation
                    // check after variable resolution can see it
                    // (mp.web §1498-1506).
                    //
                    // Build a token list [capsule(expr), cur_tok]
                    // so they are re-read in the right order.
                    use crate::input::StoredToken;
                    let result = subscript_result;
                    let mut tl = vec![StoredToken::Capsule(
                        result.exp,
                        result.ty,
                        result.dep,
                        result.pair_dep,
                    )];
                    self.store_current_token(&mut tl);
                    self.input
                        .push_token_list(tl, Vec::new(), "mediation backtrack".into());
                    self.cur.command = Command::LeftBracket;
                    break;
                }
            } else {
                break;
            }
        }

        // Check if this is a vardef macro call (standalone root or
        // root with only symbolic suffixes that don't have a variable
        // entry, and the symbol has a vardef entry in the macro table).
        let is_vardef_call = !has_suffixes && is_root_vardef;

        if is_vardef_call {
            // Trigger vardef macro expansion.
            // `self.cur` is the token AFTER the macro name (e.g. `(`
            // or `;`). We push it as a token-list level so that
            // `expand_defined_macro` can read it with `get_next`.
            // Using back_input() would put it in the priority slot,
            // which is read BEFORE any token-list level — including
            // the body that expand_defined_macro is about to push.
            let mut trailing = crate::input::TokenList::new();
            self.store_current_token(&mut trailing);
            if !trailing.is_empty() {
                self.input
                    .push_token_list(trailing, Vec::new(), "vardef trailing".into());
            }
            self.cur.command = Command::DefinedMacro;
            self.cur.sym = root_sym;
            self.expand_defined_macro();
            // After expansion, re-enter scan_primary to parse the
            // expanded result (mp.web's `goto restart`).
            return self.scan_primary();
        }

        self.resolve_variable(root_sym, &name, &suffix_segs)?;
        Ok(self.take_cur_result())
    }

    fn scan_rhs_for_infix_command(&mut self, cmd: Command) -> InterpResult<()> {
        let Some(bp) = cmd.infix_binding_power() else {
            return Err(InterpreterError::new(
                ErrorKind::UnexpectedToken,
                "Expected infix command",
            ));
        };
        self.scan_infix_bp(bp + 1, false)
    }

    fn scan_current_infix_op(&mut self, equals_is_equation: bool) -> InterpResult<bool> {
        match self.cur.command {
            Command::SecondaryPrimaryMacro
            | Command::SecondaryBinary
            | Command::Slash
            | Command::And => self.scan_secondary_infix_op(),
            Command::TertiarySecondaryMacro | Command::PlusOrMinus | Command::TertiaryBinary => {
                self.scan_tertiary_infix_op()
            }
            Command::Equals
            | Command::PathJoin
            | Command::Ampersand
            | Command::ExpressionTertiaryMacro
            | Command::ExpressionBinary
            | Command::LeftBrace => self.scan_expression_infix_op(equals_is_equation),
            _ => Err(InterpreterError::new(
                ErrorKind::UnexpectedToken,
                "Expected infix command",
            )),
        }
    }

    fn scan_infix_bp(&mut self, min_bp: u8, equals_is_equation: bool) -> InterpResult<()> {
        let result = self.scan_primary()?;
        self.set_cur_result(result);
        while let Some(bp) = self.cur.command.infix_binding_power() {
            if bp < min_bp {
                break;
            }

            let should_break = self.scan_current_infix_op(equals_is_equation)?;
            if should_break {
                break;
            }
        }
        Ok(())
    }

    /// Parse and evaluate a secondary expression, returning the result.
    pub(super) fn scan_secondary(&mut self) -> InterpResult<ExprResultValue> {
        self.scan_infix_bp(Command::BP_SECONDARY, false)?;
        Ok(self.take_cur_result())
    }

    /// Parse and evaluate a tertiary expression, returning the result.
    pub(super) fn scan_tertiary(&mut self) -> InterpResult<ExprResultValue> {
        self.scan_infix_bp(Command::BP_TERTIARY, false)?;
        Ok(self.take_cur_result())
    }

    /// Parse and evaluate an expression, returning the result.
    ///
    /// Handles expression-level binary operators and path construction.
    pub(crate) fn scan_expression(&mut self) -> InterpResult<ExprResultValue> {
        // Capture and reset the flag (mp.web: my_var_flag := var_flag; var_flag := 0).
        let equals_is_equation = self.lhs_tracking.equals_means_equation;
        self.lhs_tracking.equals_means_equation = false;
        self.scan_infix_bp(Command::BP_EXPRESSION, equals_is_equation)?;
        Ok(self.take_cur_result())
    }

    fn scan_secondary_infix_op(&mut self) -> InterpResult<bool> {
        let cmd = self.cur.command;

        if cmd == Command::SecondaryPrimaryMacro {
            // User-defined primarydef operator
            let left = self.take_cur_result().exp;
            self.expand_binary_macro(&left)?;
            return Ok(true);
        }

            let op = self.cur.modifier;
            let left_result = self.take_cur_result();
            let left_dep = left_result.dep.clone();
            let left_pair_dep = left_result.pair_dep.clone();
            let left = left_result.exp;
            self.get_x_next();
            self.scan_rhs_for_infix_command(cmd)?;
            let right_result = self.cur_expr.snapshot();
            let right_val = right_result.exp.clone();
            let right_dep = right_result.dep.clone();
            let right_pair_dep = right_result.pair_dep.clone();
            let right_binding = self.lhs_tracking.last_lhs_binding.clone();

        match cmd {
                Command::SecondaryBinary => {
                    let Some(op) = SecondaryBinaryOp::from_modifier(op) else {
                        return Err(InterpreterError::new(
                            ErrorKind::UnexpectedToken,
                            "Invalid secondary binary operator modifier",
                        ));
                    };
                    self.lhs_tracking.last_lhs_binding = None;
                    let (val, ty) = Self::do_secondary_binary(op, &left, &right_val)?;
                    self.cur_expr.exp = val;
                    self.cur_expr.ty = ty;
                    if op == SecondaryBinaryOp::Times {
                        let left_const = left_dep.as_ref().and_then(constant_value);
                        let right_const = right_dep.as_ref().and_then(constant_value);

                        match self.cur_expr.exp {
                            Value::Numeric(_) => {
                                self.cur_expr.dep = left_const.map_or_else(
                                    || {
                                        right_const.and_then(|factor| {
                                            left_dep.map(|mut d| {
                                                dep_scale(&mut d, factor);
                                                d
                                            })
                                        })
                                    },
                                    |factor| {
                                        right_dep.clone().map(|mut d| {
                                            dep_scale(&mut d, factor);
                                            d
                                        })
                                    },
                                );
                                self.cur_expr.pair_dep = None;
                            }
                            Value::Pair(_, _) => {
                                self.cur_expr.dep = None;

                                let pair_deps = match (&left, &right_val) {
                                    (Value::Numeric(_), Value::Pair(rx, ry)) => {
                                        let left_linear = left_dep
                                            .as_ref()
                                            .is_some_and(|d| constant_value(d).is_none());
                                        let right_linear = right_pair_dep.as_ref().is_some_and(
                                            |(dx, dy)| {
                                                constant_value(dx).is_none()
                                                    || constant_value(dy).is_none()
                                            },
                                        );

                                        if left_linear && right_linear {
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
                                                .unwrap_or_else(|| value_to_scalar(&left).unwrap_or(0.0));
                                            let (mut dx, mut dy) = right_pair_dep
                                                .unwrap_or_else(|| (const_dep(*rx), const_dep(*ry)));
                                            dep_scale(&mut dx, scalar);
                                            dep_scale(&mut dy, scalar);
                                            Some((dx, dy))
                                        }
                                    }
                                    (Value::Pair(lx, ly), Value::Numeric(_)) => {
                                        let left_linear = left_pair_dep.as_ref().is_some_and(
                                            |(dx, dy)| {
                                                constant_value(dx).is_none()
                                                    || constant_value(dy).is_none()
                                            },
                                        );
                                        let right_linear = right_dep
                                            .as_ref()
                                            .is_some_and(|d| constant_value(d).is_none());

                                        if left_linear && right_linear {
                                            None
                                        } else if right_linear {
                                            let dep = right_dep.unwrap_or_else(|| const_dep(0.0));
                                            let mut dx = dep.clone();
                                            let mut dy = dep;
                                            dep_scale(&mut dx, *lx);
                                            dep_scale(&mut dy, *ly);
                                            Some((dx, dy))
                                        } else {
                                            let scalar = right_const
                                                .unwrap_or_else(|| value_to_scalar(&right_val).unwrap_or(0.0));
                                            let (mut dx, mut dy) = left_pair_dep
                                                .unwrap_or_else(|| (const_dep(*lx), const_dep(*ly)));
                                            dep_scale(&mut dx, scalar);
                                            dep_scale(&mut dy, scalar);
                                            Some((dx, dy))
                                        }
                                    }
                                    _ => None,
                                };

                                self.cur_expr.pair_dep = pair_deps;
                            }
                            _ => {
                                self.cur_expr.dep = None;
                                self.cur_expr.pair_dep = None;
                            }
                        }
                    } else {
                        self.cur_expr.dep = None;
                        if matches!(self.cur_expr.exp, Value::Pair(_, _)) {
                            let base_dep = left_pair_dep.or_else(|| {
                                if let Value::Pair(lx, ly) = left {
                                    Some((const_dep(lx), const_dep(ly)))
                                } else {
                                    None
                                }
                            });

                            self.cur_expr.pair_dep = base_dep.map(|(ldx, ldy)| {
                                if op == SecondaryBinaryOp::Transformed
                                    && let Some(LhsBinding::Variable { id, .. }) = right_binding.clone()
                                    && let VarValue::Transform {
                                        tx,
                                        ty,
                                        txx,
                                        txy,
                                        tyx,
                                        tyy,
                                    } = self.variables.get(id).clone()
                                {
                                    let (lx, ly) = if let Value::Pair(lx, ly) = left {
                                        (lx, ly)
                                    } else {
                                        (0.0, 0.0)
                                    };

                                    let mut dep_x = self.numeric_dep_for_var(tx);
                                    dep_x = dep_add_scaled(&dep_x, &self.numeric_dep_for_var(txx), lx);
                                    dep_x = dep_add_scaled(&dep_x, &self.numeric_dep_for_var(txy), ly);

                                    let mut dep_y = self.numeric_dep_for_var(ty);
                                    dep_y = dep_add_scaled(&dep_y, &self.numeric_dep_for_var(tyx), lx);
                                    dep_y = dep_add_scaled(&dep_y, &self.numeric_dep_for_var(tyy), ly);

                                    return (dep_x, dep_y);
                                }

                                let t = match op {
                                    SecondaryBinaryOp::Scaled => {
                                        let f = value_to_scalar(&right_val).unwrap_or(1.0);
                                        postmeta_graphics::transform::scaled(f)
                                    }
                                    SecondaryBinaryOp::Shifted => {
                                        let (dx, dy) =
                                            value_to_pair(&right_val).unwrap_or((0.0, 0.0));
                                        postmeta_graphics::transform::shifted(dx, dy)
                                    }
                                    SecondaryBinaryOp::Rotated => {
                                        let a = value_to_scalar(&right_val).unwrap_or(0.0);
                                        postmeta_graphics::transform::rotated(a)
                                    }
                                    SecondaryBinaryOp::XScaled => {
                                        let f = value_to_scalar(&right_val).unwrap_or(1.0);
                                        postmeta_graphics::transform::xscaled(f)
                                    }
                                    SecondaryBinaryOp::YScaled => {
                                        let f = value_to_scalar(&right_val).unwrap_or(1.0);
                                        postmeta_graphics::transform::yscaled(f)
                                    }
                                    SecondaryBinaryOp::Slanted => {
                                        let f = value_to_scalar(&right_val).unwrap_or(0.0);
                                        postmeta_graphics::transform::slanted(f)
                                    }
                                    SecondaryBinaryOp::ZScaled => {
                                        let (a, b) =
                                            value_to_pair(&right_val).unwrap_or((1.0, 0.0));
                                        postmeta_graphics::transform::zscaled(a, b)
                                    }
                                    SecondaryBinaryOp::Transformed => {
                                        value_to_transform(&right_val).unwrap_or(
                                            postmeta_graphics::types::Transform::IDENTITY,
                                        )
                                    }
                                    SecondaryBinaryOp::Times
                                    | SecondaryBinaryOp::Over
                                    | SecondaryBinaryOp::DotProd
                                    | SecondaryBinaryOp::Infont => {
                                        postmeta_graphics::types::Transform::IDENTITY
                                    }
                                };

                                let mut new_x = ldx.clone();
                                dep_scale(&mut new_x, t.txx);
                                new_x = dep_add_scaled(&new_x, &ldy, t.txy);
                                new_x = dep_add_scaled(&new_x, &const_dep(t.tx), 1.0);

                                let mut new_y = ldx;
                                dep_scale(&mut new_y, t.tyx);
                                new_y = dep_add_scaled(&new_y, &ldy, t.tyy);
                                new_y = dep_add_scaled(&new_y, &const_dep(t.ty), 1.0);

                                (new_x, new_y)
                            });
                        } else {
                            self.cur_expr.pair_dep = None;
                        }
                    }
                }
                Command::Slash => {
                    // Division
                    let right = right_result.exp;
                    let b = value_to_scalar(&right)?;
                    if b.abs() < f64::EPSILON {
                        self.report_error(ErrorKind::ArithmeticError, "Division by zero");
                        match left {
                            Value::Numeric(_) => {
                                self.cur_expr.exp = Value::Numeric(0.0);
                                self.cur_expr.ty = Type::Known;
                                self.cur_expr.dep = Some(const_dep(0.0));
                                self.cur_expr.pair_dep = None;
                            }
                            Value::Pair(_, _) => {
                                self.cur_expr.exp = Value::Pair(0.0, 0.0);
                                self.cur_expr.ty = Type::PairType;
                                self.cur_expr.dep = None;
                                self.cur_expr.pair_dep = Some((const_dep(0.0), const_dep(0.0)));
                            }
                            _ => {
                                self.cur_expr.exp = Value::Numeric(0.0);
                                self.cur_expr.ty = Type::Known;
                                self.cur_expr.dep = Some(const_dep(0.0));
                                self.cur_expr.pair_dep = None;
                            }
                        }
                    } else {
                        match left {
                            Value::Numeric(a) => {
                                self.cur_expr.exp = Value::Numeric(a / b);
                                let divisor = right_dep
                                    .as_ref()
                                    .and_then(constant_value)
                                    .or_else(|| value_to_scalar(&right).ok());
                                self.cur_expr.dep = divisor.and_then(|c| {
                                    if c.abs() < f64::EPSILON {
                                        None
                                    } else {
                                        left_dep.map(|mut d| {
                                            dep_scale(&mut d, 1.0 / c);
                                            d
                                        })
                                    }
                                });
                                self.cur_expr.pair_dep = None;
                            }
                            Value::Pair(x, y) => {
                                self.cur_expr.exp = Value::Pair(x / b, y / b);
                                self.cur_expr.dep = None;
                                let (mut dx, mut dy) =
                                    left_pair_dep.unwrap_or_else(|| (const_dep(x), const_dep(y)));
                                dep_scale(&mut dx, 1.0 / b);
                                dep_scale(&mut dy, 1.0 / b);
                                self.cur_expr.pair_dep = Some((dx, dy));
                            }
                            _ => {
                                return Err(InterpreterError::new(
                                    ErrorKind::TypeError,
                                    format!(
                                        "Invalid types for /: {} and {}",
                                        left.ty(),
                                        right.ty()
                                    ),
                                ));
                            }
                        }
                    }
                    if !matches!(self.cur_expr.exp, Value::Pair(_, _)) {
                        self.cur_expr.ty = Type::Known;
                    }
                    self.lhs_tracking.last_lhs_binding = None;
                }
                Command::And => {
                    // Logical and
                    let right = right_result.exp;
                    let a = value_to_bool(&left)?;
                    let b = value_to_bool(&right)?;
                    self.cur_expr.exp = Value::Boolean(a && b);
                    self.cur_expr.ty = Type::Boolean;
                    self.lhs_tracking.last_lhs_binding = None;
                    self.cur_expr.dep = None;
                    self.cur_expr.pair_dep = None;
                }
            _ => {}
        }
        Ok(false)
    }

    fn scan_tertiary_infix_op(&mut self) -> InterpResult<bool> {
        let cmd = self.cur.command;

        if cmd == Command::TertiarySecondaryMacro {
            // User-defined tertiarydef operator
            let left = self.take_cur_result().exp;
            self.expand_binary_macro(&left)?;
            return Ok(true);
        }

            let op = self.cur.modifier;
            let left_result = self.take_cur_result();
            let left_dep = left_result.dep.clone();
            let left_pair_dep = left_result.pair_dep.clone();
            let left = left_result.exp;
            self.get_x_next();
            self.scan_rhs_for_infix_command(cmd)?;
            let right_result = self.take_cur_result();
            let right_dep = right_result.dep.clone();
            let right_pair_dep = right_result.pair_dep.clone();

        match cmd {
                Command::PlusOrMinus => {
                    let Some(op) = PlusMinusOp::from_modifier(op) else {
                        return Err(InterpreterError::new(
                            ErrorKind::UnexpectedToken,
                            "Invalid plus/minus modifier",
                        ));
                    };
                    let right = right_result.exp;
                    self.lhs_tracking.last_lhs_binding = None;
                    let (val, ty) = Self::do_plus_minus(op, &left, &right)?;
                    self.cur_expr.exp = val;
                    self.cur_expr.ty = ty;
                    let factor = if op == PlusMinusOp::Plus {
                        1.0
                    } else {
                        -1.0
                    };

                    if matches!(self.cur_expr.exp, Value::Pair(_, _)) {
                        self.cur_expr.dep = None;
                        let (lx, ly) = if let Value::Pair(x, y) = left {
                            (x, y)
                        } else {
                            (0.0, 0.0)
                        };
                        let (rx, ry) = if let Value::Pair(x, y) = right {
                            (x, y)
                        } else {
                            (0.0, 0.0)
                        };

                        let (ldx, ldy) =
                            left_pair_dep.unwrap_or_else(|| (const_dep(lx), const_dep(ly)));
                        let (rdx, rdy) = right_pair_dep
                            .unwrap_or_else(|| (const_dep(rx), const_dep(ry)));

                        self.cur_expr.pair_dep = Some((
                            dep_add_scaled(&ldx, &rdx, factor),
                            dep_add_scaled(&ldy, &rdy, factor),
                        ));
                    } else {
                        self.cur_expr.dep = match (left_dep.as_ref(), right_dep.as_ref()) {
                            (Some(ld), Some(rd)) => Some(dep_add_scaled(ld, rd, factor)),
                            _ => None,
                        };
                        self.cur_expr.pair_dep = None;
                    }
                }
                Command::TertiaryBinary => {
                    let Some(op) = TertiaryBinaryOp::from_modifier(op) else {
                        return Err(InterpreterError::new(
                            ErrorKind::UnexpectedToken,
                            "Invalid tertiary binary modifier",
                        ));
                    };
                    let right = right_result.exp;
                    self.lhs_tracking.last_lhs_binding = None;
                    let (val, ty) = Self::do_tertiary_binary(op, &left, &right)?;
                    self.cur_expr.exp = val;
                    self.cur_expr.ty = ty;
                    self.cur_expr.dep = None;
                    self.cur_expr.pair_dep = None;
                }
            _ => {}
        }
        Ok(false)
    }

    fn scan_expression_infix_op(&mut self, equals_is_equation: bool) -> InterpResult<bool> {
        let cmd = self.cur.command;
        let op = self.cur.modifier;

            match cmd {
            Command::Equals if equals_is_equation => {
                    // In statement context, `=` is an equation/assignment
                    // delimiter — don't consume it.
                return Ok(true);
            }
            Command::Equals => {
                    // In expression context (e.g. exitif, if), `=` is an
                    // equality comparison producing a boolean.
                    let left = self.take_cur_result().exp;
                    self.get_x_next();
                    self.scan_rhs_for_infix_command(cmd)?;
                    let right = self.take_cur_result().exp;
                    self.lhs_tracking.last_lhs_binding = None;
                    let (val, ty) = Self::do_expression_binary(ExpressionBinaryOp::EqualTo, &left, &right)?;
                    self.cur_expr.exp = val;
                    self.cur_expr.ty = ty;
                    self.cur_expr.dep = None;
                    self.cur_expr.pair_dep = None;
            }
            Command::PathJoin => {
                    // Path construction
                    let left = self.take_cur_result();
                    let result = self.scan_path_construction(left)?;
                    self.set_cur_result(result);
                return Ok(true);
            }
            Command::Ampersand => {
                    // & is path join for pairs/paths, string concat otherwise
                    if matches!(self.cur_expr.ty, Type::PairType | Type::Path) {
                        let left = self.take_cur_result();
                        let result = self.scan_path_construction(left)?;
                        self.set_cur_result(result);
                    } else {
                        // String concatenation
                        let left = self.take_cur_result().exp;
                        self.get_x_next();
                        self.scan_rhs_for_infix_command(cmd)?;
                        let right = self.take_cur_result().exp;
                        self.lhs_tracking.last_lhs_binding = None;
                        let (val, ty) = Self::do_expression_binary(
                            ExpressionBinaryOp::Concatenate,
                            &left,
                            &right,
                        )?;
                        self.cur_expr.exp = val;
                        self.cur_expr.ty = ty;
                        self.cur_expr.dep = None;
                        self.cur_expr.pair_dep = None;
                    }
                return Ok(true);
            }
            Command::ExpressionTertiaryMacro => {
                    // User-defined secondarydef operator
                    let left = self.take_cur_result().exp;
                    self.expand_binary_macro(&left)?;
                    self.cur_expr.dep = None;
                    self.cur_expr.pair_dep = None;
                return Ok(true);
            }
            Command::ExpressionBinary => {
                    let Some(op) = ExpressionBinaryOp::from_modifier(op) else {
                        return Err(InterpreterError::new(
                            ErrorKind::UnexpectedToken,
                            "Invalid expression binary modifier",
                        ));
                    };
                    let left = self.take_cur_result().exp;
                    self.get_x_next();
                    self.scan_rhs_for_infix_command(cmd)?;
                    let right = self.take_cur_result().exp;
                    self.lhs_tracking.last_lhs_binding = None;
                    let (val, ty) = Self::do_expression_binary(op, &left, &right)?;
                    self.cur_expr.exp = val;
                    self.cur_expr.ty = ty;
                    self.cur_expr.dep = None;
                    self.cur_expr.pair_dep = None;
                }
            Command::LeftBrace => {
                    // Direction specification — start of path construction
                    let left = self.take_cur_result();
                    let result = self.scan_path_construction(left)?;
                    self.set_cur_result(result);
                return Ok(true);
            }
            _ => return Ok(true),
        }
        Ok(false)
    }
}
