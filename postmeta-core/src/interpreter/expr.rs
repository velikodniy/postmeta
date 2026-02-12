//! Expression parser — Pratt-style with three binding power levels.
//!
//! The parser uses a single Pratt loop ([`Interpreter::scan_infix_bp`]) with:
//! - `scan_primary` as the nud (prefix/atom) handler
//! - `scan_infix_led` as the unified led (infix) handler
//!
//! Three binding power tiers match `MetaPost`'s grammar:
//! - **Secondary** (BP 30): `*`, `/`, `and`, `scaled`, `rotated`, etc.
//! - **Tertiary** (BP 20): `+`, `-`, `++`, `+-+`
//! - **Expression** (BP 10): `=`, `<`, `>`, `&`, path construction

use std::fmt::Write;
use std::sync::Arc;

use crate::command::{
    Command, ExpressionBinaryOp, NullaryOp, PlusMinusOp, PrimaryBinaryOp, SecondaryBinaryOp,
    StrOpOp, TertiaryBinaryOp, TypeNameOp, UnaryOp,
};
use crate::equation::{const_dep, constant_value, dep_add_scaled, dep_scale, DepList};
use crate::error::{ErrorKind, InterpResult, InterpreterError};
use crate::types::{Type, Value};
use crate::variables::{SuffixSegment, VarValue};

use super::helpers::{value_to_bool, value_to_pair, value_to_scalar, value_to_transform};
use super::{ExprResultValue, Interpreter, LhsBinding};

/// Result from an infix (led) handler — either continue the Pratt loop
/// or break out of it.
enum InfixAction {
    /// The operator was consumed; continue looking for more infix ops.
    Continue(ExprResultValue),
    /// The operator signals a mode switch or end of expression; stop the loop.
    Break(ExprResultValue),
}

impl Interpreter {
    /// Parse and evaluate a primary expression, returning the result.
    pub(super) fn scan_primary(&mut self) -> InterpResult<ExprResultValue> {
        let primary = match self.cur.command {
            Command::NumericToken => self.scan_primary_numeric()?,

            Command::StringToken => {
                let val = if let crate::token::TokenKind::StringLit(ref s) = self.cur.token.kind {
                    Value::String(Arc::from(s.as_str()))
                } else {
                    Value::Vacuous
                };
                self.lhs_tracking.last_lhs_binding = None;
                self.get_x_next();
                ExprResultValue {
                    exp: val,
                    ty: Type::String,
                    dep: None,
                    pair_dep: None,
                }
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
                let dep = if let Value::Numeric(v) = &val {
                    Some(const_dep(*v))
                } else {
                    None
                };
                ExprResultValue {
                    exp: val,
                    ty,
                    dep,
                    pair_dep: None,
                }
            }

            Command::Unary => {
                let Some(op) = UnaryOp::from_modifier(self.cur.modifier) else {
                    return Err(InterpreterError::new(
                        ErrorKind::UnexpectedToken,
                        "Invalid unary operator modifier",
                    ));
                };
                self.get_x_next();
                let operand_result = self.scan_primary()?;
                self.do_unary(op, operand_result.exp, operand_result.pair_dep)?
            }

            Command::PlusOrMinus => {
                // Unary plus or minus
                let is_minus = PlusMinusOp::from_modifier(self.cur.modifier)
                    == Some(PlusMinusOp::Minus);
                self.get_x_next();
                let mut result = self.scan_primary()?;
                if is_minus {
                    result = self.negate_value(result);
                }
                result
            }

            Command::LeftDelimiter => self.scan_primary_delimited()?,

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
                self.take_cur_result()
            }

            Command::TagToken => self.scan_tag_token()?,

            Command::InternalQuantity => {
                let idx = self.cur.modifier;
                let v = self.internals.get(idx);
                // Track for assignment LHS
                self.lhs_tracking.last_lhs_binding = Some(LhsBinding::Internal { idx });
                self.get_x_next();
                ExprResultValue {
                    exp: Value::Numeric(v),
                    ty: Type::Known,
                    dep: Some(const_dep(v)),
                    pair_dep: None,
                }
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
                ExprResultValue {
                    exp: val,
                    ty,
                    dep: None,
                    pair_dep: None,
                }
            }

            Command::Cycle => {
                self.lhs_tracking.last_lhs_binding = None;
                self.get_x_next();
                ExprResultValue {
                    exp: Value::Boolean(false),
                    ty: Type::Boolean,
                    dep: None,
                    pair_dep: None,
                }
            }

            Command::StrOp => {
                let op = StrOpOp::from_modifier(self.cur.modifier);
                self.get_x_next();
                let val = if op == Some(StrOpOp::Str) {
                    // `str` <suffix> — converts suffix to string
                    let name = if let crate::token::TokenKind::Symbolic(ref s) = self.cur.token.kind
                    {
                        s.clone()
                    } else {
                        String::new()
                    };
                    self.get_x_next();
                    Value::String(Arc::from(name.as_str()))
                } else {
                    // readfrom etc. — not yet implemented
                    Value::String(Arc::from(""))
                };
                self.lhs_tracking.last_lhs_binding = None;
                ExprResultValue {
                    exp: val,
                    ty: Type::String,
                    dep: None,
                    pair_dep: None,
                }
            }

            Command::CapsuleToken => {
                let result =
                    if let Some((val, ty, dep, pair_dep)) = self.cur.capsule.take() {
                        ExprResultValue {
                            exp: val,
                            ty,
                            dep,
                            pair_dep,
                        }
                    } else {
                        // CapsuleToken without payload — shouldn't happen, treat as vacuous
                        ExprResultValue {
                            exp: Value::Vacuous,
                            ty: Type::Vacuous,
                            dep: None,
                            pair_dep: None,
                        }
                    };
                self.lhs_tracking.last_lhs_binding = None;
                self.get_x_next();
                result
            }

            Command::TypeName => {
                // Type name as unary operator — type test.
                let op = TypeNameOp::from_modifier(self.cur.modifier);
                self.get_x_next();
                let primary_result = self.scan_primary()?;
                let ty = primary_result.ty;
                let result = match op {
                    Some(TypeNameOp::Numeric) => {
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
                        (ty as u8) < (Type::Dependent as u8)
                    }
                    Some(TypeNameOp::Unknown) => {
                        (ty as u8) >= (Type::Dependent as u8)
                    }
                    _ => false,
                };
                self.lhs_tracking.last_lhs_binding = None;
                ExprResultValue {
                    exp: Value::Boolean(result),
                    ty: Type::Boolean,
                    dep: None,
                    pair_dep: None,
                }
            }

            _ => {
                // Missing primary — set to vacuous
                self.lhs_tracking.last_lhs_binding = None;
                ExprResultValue {
                    exp: Value::Vacuous,
                    ty: Type::Vacuous,
                    dep: None,
                    pair_dep: None,
                }
            }
        };

        // Check for mediation: a[b,c] = (1-a)*b + a*c
        self.scan_mediation(primary)
    }

    /// Handle the `NumericToken` primary: literal, fraction, implicit multiplication.
    fn scan_primary_numeric(&mut self) -> InterpResult<ExprResultValue> {
        let v = if let crate::token::TokenKind::Numeric(v) = self.cur.token.kind {
            v
        } else {
            0.0
        };
        let mut result = ExprResultValue {
            exp: Value::Numeric(v),
            ty: Type::Known,
            dep: Some(const_dep(v)),
            pair_dep: None,
        };
        self.lhs_tracking.last_lhs_binding = None;
        self.get_x_next();

        // Check for fraction: 3/4 as a primary
        if self.cur.command == Command::Slash {
            self.get_x_next();
            if let crate::token::TokenKind::Numeric(denom) = self.cur.token.kind {
                if let Value::Numeric(numer) = result.exp {
                    if denom.abs() > f64::EPSILON {
                        let frac = numer / denom;
                        result.exp = Value::Numeric(frac);
                        result.dep = Some(const_dep(frac));
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
                self.cur.modifier = crate::command::SecondaryBinaryOp::Over as u16;
                return Ok(result);
            }
        }

        // Implicit multiplication: `3x`, `2bp`, `.5(1,2)`, etc.
        if self.cur.command.can_start_implicit_mul() {
            let factor_val = result
                .dep
                .as_ref()
                .and_then(constant_value)
                .unwrap_or_else(|| value_to_scalar(&result.exp).unwrap_or(1.0));
            let right_result = self.scan_primary()?;
            self.lhs_tracking.last_lhs_binding = None;
            let (val, ty) = Self::do_implicit_mul(&result.exp, &right_result.exp)?;
            let dep = right_result.dep.map(|mut d| {
                dep_scale(&mut d, factor_val);
                d
            });
            let pair_dep = right_result.pair_dep.map(|(mut dx, mut dy)| {
                dep_scale(&mut dx, factor_val);
                dep_scale(&mut dy, factor_val);
                (dx, dy)
            });
            result = ExprResultValue {
                exp: val,
                ty,
                dep,
                pair_dep,
            };
        }

        Ok(result)
    }

    /// Handle delimited primary: `(expr)`, `(x,y)`, `(r,g,b)`.
    fn scan_primary_delimited(&mut self) -> InterpResult<ExprResultValue> {
        let expected_delimiter = self.cur.modifier;
        self.get_x_next();
        let first_result = self.scan_expression()?;

        let result = if self.cur.command == Command::Comma {
            // Pair or color
            let first = first_result.exp;
            let first_dep = first_result.dep;
            let second_dep_backup = first_result.pair_dep;
            let _ = second_dep_backup; // unused in pair/color
            let first_binding = self.lhs_tracking.last_lhs_binding.clone();
            self.get_x_next();
            let second_result = self.scan_expression()?;
            let second = second_result.exp;
            let second_binding = self.lhs_tracking.last_lhs_binding.clone();

            if self.cur.command == Command::Comma {
                // Color: (r, g, b)
                self.get_x_next();
                let third_result = self.scan_expression()?;
                let third = third_result.exp;
                let third_binding = self.lhs_tracking.last_lhs_binding.clone();

                let r = value_to_scalar(&first)?;
                let g = value_to_scalar(&second)?;
                let b = value_to_scalar(&third)?;
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
                ExprResultValue {
                    exp: Value::Color(postmeta_graphics::types::Color::new(r, g, b)),
                    ty: Type::ColorType,
                    dep: None,
                    pair_dep: None,
                }
            } else {
                // Pair: (x, y)
                let x = value_to_scalar(&first)?;
                let y = value_to_scalar(&second)?;
                self.lhs_tracking.last_lhs_binding =
                    if first_binding.is_some() || second_binding.is_some() {
                        Some(LhsBinding::Pair {
                            x: first_binding.map(Box::new),
                            y: second_binding.map(Box::new),
                        })
                    } else {
                        None
                    };
                ExprResultValue {
                    exp: Value::Pair(x, y),
                    ty: Type::PairType,
                    dep: None,
                    pair_dep: Some((
                        first_dep.unwrap_or_else(|| const_dep(x)),
                        second_result.dep.unwrap_or_else(|| const_dep(y)),
                    )),
                }
            }
        } else {
            // Single expression in parens
            first_result
        };

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
        Ok(result)
    }

    /// Check for and evaluate mediation: `a[b,c] = (1-a)*b + a*c`.
    fn scan_mediation(&mut self, primary: ExprResultValue) -> InterpResult<ExprResultValue> {
        if self.cur.command != Command::LeftBracket {
            return Ok(primary);
        }
        let Value::Numeric(a) = primary.exp else {
            return Ok(primary);
        };

        let a_dep = primary.dep.unwrap_or_else(|| const_dep(a));
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
        let result = match (b, c) {
            (Value::Numeric(bn), Value::Numeric(cn)) => {
                let b_dep = b_dep.unwrap_or_else(|| const_dep(bn));
                let c_dep = c_dep.unwrap_or_else(|| const_dep(cn));
                let a_is_linear = constant_value(&a_dep).is_none();
                let bc_have_linear =
                    constant_value(&b_dep).is_none() || constant_value(&c_dep).is_none();

                let dep = if a_is_linear && bc_have_linear {
                    None
                } else if a_is_linear {
                    Some(dep_add_scaled(&b_dep, &a_dep, cn - bn))
                } else {
                    let mut dep = b_dep;
                    dep_scale(&mut dep, one_minus_a);
                    Some(dep_add_scaled(&dep, &c_dep, a))
                };
                ExprResultValue {
                    exp: Value::Numeric(a.mul_add(cn - bn, bn)),
                    ty: Type::Known,
                    dep,
                    pair_dep: None,
                }
            }
            (Value::Pair(bx, by), Value::Pair(cx, cy)) => {
                let (b_dep_x, b_dep_y) =
                    b_pair_dep.unwrap_or_else(|| (const_dep(bx), const_dep(by)));
                let (c_dep_x, c_dep_y) =
                    c_pair_dep.unwrap_or_else(|| (const_dep(cx), const_dep(cy)));
                let a_is_linear = constant_value(&a_dep).is_none();
                let pair_has_linear = constant_value(&b_dep_x).is_none()
                    || constant_value(&b_dep_y).is_none()
                    || constant_value(&c_dep_x).is_none()
                    || constant_value(&c_dep_y).is_none();

                let pair_dep = if a_is_linear && pair_has_linear {
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
                ExprResultValue {
                    exp: Value::Pair(one_minus_a * bx + a * cx, one_minus_a * by + a * cy),
                    ty: Type::PairType,
                    dep: None,
                    pair_dep,
                }
            }
            (Value::Color(bc), Value::Color(cc)) => ExprResultValue {
                exp: Value::Color(postmeta_graphics::types::Color::new(
                    one_minus_a * bc.r + a * cc.r,
                    one_minus_a * bc.g + a * cc.g,
                    one_minus_a * bc.b + a * cc.b,
                )),
                ty: Type::ColorType,
                dep: None,
                pair_dep: None,
            },
            (Value::Transform(bt), Value::Transform(ct)) => ExprResultValue {
                exp: Value::Transform(postmeta_graphics::types::Transform {
                    tx: one_minus_a * bt.tx + a * ct.tx,
                    ty: one_minus_a * bt.ty + a * ct.ty,
                    txx: one_minus_a * bt.txx + a * ct.txx,
                    txy: one_minus_a * bt.txy + a * ct.txy,
                    tyx: one_minus_a * bt.tyx + a * ct.tyx,
                    tyy: one_minus_a * bt.tyy + a * ct.tyy,
                }),
                ty: Type::TransformType,
                dep: None,
                pair_dep: None,
            },
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
        };

        self.lhs_tracking.last_lhs_binding = None;
        Ok(result)
    }

    fn scan_tag_token(&mut self) -> InterpResult<ExprResultValue> {
        // Variable reference — scan suffix parts to form compound name.
        let root_sym = self.cur.sym;
        let mut name = self
            .cur_symbolic_name()
            .map_or_else(String::new, std::borrow::ToOwned::to_owned);

        let mut has_suffixes = false;
        let mut suffix_segs: Vec<SuffixSegment> = Vec::new();

        // Check early if this is a standalone vardef macro.
        let is_root_vardef = root_sym.is_some_and(|s| self.macros.get(&s).is_some_and(|m| m.is_vardef));

        self.get_x_next();

        // Suffix loop: collect symbolic suffixes, numeric subscripts,
        // and bracketed subscript expressions `[expr]`.
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
                if let crate::token::TokenKind::Numeric(v) = self.cur.token.kind {
                    let _ = write!(name, "[{}]", v as i64);
                    suffix_segs.push(SuffixSegment::Subscript);
                }
                has_suffixes = true;
                self.get_x_next();
            } else if !is_root_vardef && self.cur.command == Command::LeftBracket {
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
                    // check after variable resolution can see it.
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

        let is_vardef_call = !has_suffixes && is_root_vardef;

        if is_vardef_call {
            let mut trailing = crate::input::TokenList::new();
            self.store_current_token(&mut trailing);
            if !trailing.is_empty() {
                self.input
                    .push_token_list(trailing, Vec::new(), "vardef trailing".into());
            }
            self.cur.command = Command::DefinedMacro;
            self.cur.sym = root_sym;
            self.expand_defined_macro();
            return self.scan_primary();
        }

        self.resolve_variable(root_sym, &name, &suffix_segs)
    }

    // =====================================================================
    // Pratt parser loop
    // =====================================================================

    /// Parse the RHS of an infix operator at one binding power level higher.
    fn scan_rhs(&mut self, cmd: Command) -> InterpResult<ExprResultValue> {
        let Some(bp) = cmd.infix_binding_power() else {
            return Err(InterpreterError::new(
                ErrorKind::UnexpectedToken,
                "Expected infix command",
            ));
        };
        self.scan_infix_bp(bp + 1, false)
    }

    /// Core Pratt loop: parse primary, then consume infix operators while
    /// their binding power meets the minimum.
    fn scan_infix_bp(
        &mut self,
        min_bp: u8,
        equals_is_equation: bool,
    ) -> InterpResult<ExprResultValue> {
        let mut accum = self.scan_primary()?;
        while let Some(bp) = self.cur.command.infix_binding_power() {
            if bp < min_bp {
                break;
            }
            match self.scan_infix_led(accum, equals_is_equation)? {
                InfixAction::Continue(result) => accum = result,
                InfixAction::Break(result) => return Ok(result),
            }
        }
        Ok(accum)
    }

    /// Parse and evaluate a secondary expression, returning the result.
    pub(super) fn scan_secondary(&mut self) -> InterpResult<ExprResultValue> {
        self.scan_infix_bp(Command::BP_SECONDARY, false)
    }

    /// Parse and evaluate a tertiary expression, returning the result.
    pub(super) fn scan_tertiary(&mut self) -> InterpResult<ExprResultValue> {
        self.scan_infix_bp(Command::BP_TERTIARY, false)
    }

    /// Parse and evaluate an expression, returning the result.
    ///
    /// Handles expression-level binary operators and path construction.
    pub(crate) fn scan_expression(&mut self) -> InterpResult<ExprResultValue> {
        let equals_is_equation = self.lhs_tracking.equals_means_equation;
        self.lhs_tracking.equals_means_equation = false;
        self.scan_infix_bp(Command::BP_EXPRESSION, equals_is_equation)
    }

    // =====================================================================
    // Unified infix (led) handler
    // =====================================================================

    /// Single led dispatch for all infix operators.
    fn scan_infix_led(
        &mut self,
        left: ExprResultValue,
        equals_is_equation: bool,
    ) -> InterpResult<InfixAction> {
        let cmd = self.cur.command;
        let modifier = self.cur.modifier;

        match cmd {
            // ----- User-defined binary macros (break after expansion) -----
            Command::SecondaryPrimaryMacro
            | Command::TertiarySecondaryMacro
            | Command::ExpressionTertiaryMacro => {
                let left_val = left.exp;
                let mut result = self.expand_binary_macro(&left_val)?;
                if cmd == Command::ExpressionTertiaryMacro {
                    result.dep = None;
                    result.pair_dep = None;
                }
                Ok(InfixAction::Break(result))
            }

            // ----- Secondary level: *, /, and, scaled, rotated, ... -----
            Command::SecondaryBinary => {
                let Some(op) = SecondaryBinaryOp::from_modifier(modifier) else {
                    return Err(InterpreterError::new(
                        ErrorKind::UnexpectedToken,
                        "Invalid secondary binary operator modifier",
                    ));
                };
                let left_dep = left.dep.clone();
                let left_pair_dep = left.pair_dep.clone();
                let left_val = left.exp;
                self.get_x_next();
                let right = self.scan_rhs(cmd)?;
                let right_binding = self.lhs_tracking.last_lhs_binding.clone();
                self.lhs_tracking.last_lhs_binding = None;
                let (val, ty) = Self::do_secondary_binary(op, &left_val, &right.exp)?;
                let result = if op == SecondaryBinaryOp::Times {
                    Self::mul_deps(val, ty, &left_val, left_dep, left_pair_dep, &right)
                } else {
                    self.transform_deps(
                        val,
                        ty,
                        op,
                        &left_val,
                        left_pair_dep,
                        &right,
                        right_binding,
                    )
                };
                Ok(InfixAction::Continue(result))
            }

            Command::Slash => {
                let left_dep = left.dep.clone();
                let left_pair_dep = left.pair_dep.clone();
                let left_val = left.exp;
                self.get_x_next();
                let right = self.scan_rhs(cmd)?;
                self.lhs_tracking.last_lhs_binding = None;
                let result = self.div_deps(left_val, left_dep, left_pair_dep, &right)?;
                Ok(InfixAction::Continue(result))
            }

            Command::And => {
                let left_val = left.exp;
                self.get_x_next();
                let right = self.scan_rhs(cmd)?;
                let a = value_to_bool(&left_val)?;
                let b = value_to_bool(&right.exp)?;
                self.lhs_tracking.last_lhs_binding = None;
                Ok(InfixAction::Continue(ExprResultValue {
                    exp: Value::Boolean(a && b),
                    ty: Type::Boolean,
                    dep: None,
                    pair_dep: None,
                }))
            }

            // ----- Tertiary level: +, -, ++, +-+ -----
            Command::PlusOrMinus => {
                let Some(op) = PlusMinusOp::from_modifier(modifier) else {
                    return Err(InterpreterError::new(
                        ErrorKind::UnexpectedToken,
                        "Invalid plus/minus modifier",
                    ));
                };
                let left_dep = left.dep.clone();
                let left_pair_dep = left.pair_dep.clone();
                let left_val = left.exp;
                self.get_x_next();
                let right = self.scan_rhs(cmd)?;
                self.lhs_tracking.last_lhs_binding = None;
                let (val, ty) = Self::do_plus_minus(op, &left_val, &right.exp)?;
                let factor = if op == PlusMinusOp::Plus {
                    1.0
                } else {
                    -1.0
                };
                let result =
                    Self::add_sub_deps(val, ty, factor, &left_val, left_dep, left_pair_dep, &right);
                Ok(InfixAction::Continue(result))
            }

            Command::TertiaryBinary => {
                let Some(op) = TertiaryBinaryOp::from_modifier(modifier) else {
                    return Err(InterpreterError::new(
                        ErrorKind::UnexpectedToken,
                        "Invalid tertiary binary modifier",
                    ));
                };
                let left_val = left.exp;
                self.get_x_next();
                let right = self.scan_rhs(cmd)?;
                self.lhs_tracking.last_lhs_binding = None;
                let (val, ty) = Self::do_tertiary_binary(op, &left_val, &right.exp)?;
                Ok(InfixAction::Continue(ExprResultValue {
                    exp: val,
                    ty,
                    dep: None,
                    pair_dep: None,
                }))
            }

            // ----- Expression level: =, <, >, path join, &, ... -----
            Command::Equals if equals_is_equation => {
                // In statement context, `=` is an equation/assignment — stop.
                Ok(InfixAction::Break(left))
            }

            Command::Equals => {
                // In expression context, `=` is equality comparison.
                let left_val = left.exp;
                self.get_x_next();
                let right = self.scan_rhs(cmd)?;
                self.lhs_tracking.last_lhs_binding = None;
                let (val, ty) =
                    Self::do_expression_binary(ExpressionBinaryOp::EqualTo, &left_val, &right.exp)?;
                Ok(InfixAction::Continue(ExprResultValue {
                    exp: val,
                    ty,
                    dep: None,
                    pair_dep: None,
                }))
            }

            Command::ExpressionBinary => {
                let Some(op) = ExpressionBinaryOp::from_modifier(modifier) else {
                    return Err(InterpreterError::new(
                        ErrorKind::UnexpectedToken,
                        "Invalid expression binary modifier",
                    ));
                };
                let left_val = left.exp;
                self.get_x_next();
                let right = self.scan_rhs(cmd)?;
                self.lhs_tracking.last_lhs_binding = None;
                let (val, ty) = Self::do_expression_binary(op, &left_val, &right.exp)?;
                Ok(InfixAction::Continue(ExprResultValue {
                    exp: val,
                    ty,
                    dep: None,
                    pair_dep: None,
                }))
            }

            // ----- Path construction and & -----
            Command::PathJoin | Command::LeftBrace => {
                let result = self.scan_path_construction(left)?;
                Ok(InfixAction::Break(result))
            }

            Command::Ampersand => {
                if matches!(left.ty, Type::PairType | Type::Path) {
                    let result = self.scan_path_construction(left)?;
                    Ok(InfixAction::Break(result))
                } else {
                    // String concatenation
                    let left_val = left.exp;
                    self.get_x_next();
                    let right = self.scan_rhs(cmd)?;
                    self.lhs_tracking.last_lhs_binding = None;
                    let (val, ty) = Self::do_expression_binary(
                        ExpressionBinaryOp::Concatenate,
                        &left_val,
                        &right.exp,
                    )?;
                    Ok(InfixAction::Break(ExprResultValue {
                        exp: val,
                        ty,
                        dep: None,
                        pair_dep: None,
                    }))
                }
            }

            _ => Ok(InfixAction::Break(left)),
        }
    }

    // =====================================================================
    // Dependency propagation helpers
    // =====================================================================

    /// Compute dependency info for multiplication (`*`).
    fn mul_deps(
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
                        right_const.and_then(|factor| {
                            left_dep.map(|mut d| {
                                dep_scale(&mut d, factor);
                                d
                            })
                        })
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
                        let left_linear =
                            left_dep.as_ref().is_some_and(|d| constant_value(d).is_none());
                        let right_linear = right.pair_dep.as_ref().is_some_and(|(dx, dy)| {
                            constant_value(dx).is_none() || constant_value(dy).is_none()
                        });
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
                            let (mut dx, mut dy) = left_pair_dep
                                .unwrap_or_else(|| (const_dep(*lx), const_dep(*ly)));
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
            _ => ExprResultValue {
                exp: val,
                ty,
                dep: None,
                pair_dep: None,
            },
        }
    }

    /// Compute dependency info for division (`/`).
    fn div_deps(
        &mut self,
        left_val: Value,
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
                _ => ExprResultValue {
                    exp: Value::Numeric(0.0),
                    ty: Type::Known,
                    dep: Some(const_dep(0.0)),
                    pair_dep: None,
                },
            });
        }
        Ok(match left_val {
            Value::Numeric(a) => {
                let divisor = right
                    .dep
                    .as_ref()
                    .and_then(constant_value)
                    .or_else(|| value_to_scalar(&right.exp).ok());
                let dep = divisor.and_then(|c| {
                    if c.abs() < f64::EPSILON {
                        None
                    } else {
                        left_dep.map(|mut d| {
                            dep_scale(&mut d, 1.0 / c);
                            d
                        })
                    }
                });
                ExprResultValue {
                    exp: Value::Numeric(a / b),
                    ty: Type::Known,
                    dep,
                    pair_dep: None,
                }
            }
            Value::Pair(x, y) => {
                let (mut dx, mut dy) =
                    left_pair_dep.unwrap_or_else(|| (const_dep(x), const_dep(y)));
                dep_scale(&mut dx, 1.0 / b);
                dep_scale(&mut dy, 1.0 / b);
                ExprResultValue {
                    exp: Value::Pair(x / b, y / b),
                    ty: Type::PairType,
                    dep: None,
                    pair_dep: Some((dx, dy)),
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
    fn add_sub_deps(
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
            let dep = match (left_dep.as_ref(), right.dep.as_ref()) {
                (Some(ld), Some(rd)) => Some(dep_add_scaled(ld, rd, factor)),
                _ => None,
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
    fn transform_deps(
        &mut self,
        val: Value,
        ty: Type,
        op: SecondaryBinaryOp,
        left_val: &Value,
        left_pair_dep: Option<(DepList, DepList)>,
        right: &ExprResultValue,
        right_binding: Option<LhsBinding>,
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
                    } = self.variables.get(id).clone()
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
        match op {
            SecondaryBinaryOp::Scaled => {
                postmeta_graphics::transform::scaled(value_to_scalar(right).unwrap_or(1.0))
            }
            SecondaryBinaryOp::Shifted => {
                let (dx, dy) = value_to_pair(right).unwrap_or((0.0, 0.0));
                postmeta_graphics::transform::shifted(dx, dy)
            }
            SecondaryBinaryOp::Rotated => {
                postmeta_graphics::transform::rotated(value_to_scalar(right).unwrap_or(0.0))
            }
            SecondaryBinaryOp::XScaled => {
                postmeta_graphics::transform::xscaled(value_to_scalar(right).unwrap_or(1.0))
            }
            SecondaryBinaryOp::YScaled => {
                postmeta_graphics::transform::yscaled(value_to_scalar(right).unwrap_or(1.0))
            }
            SecondaryBinaryOp::Slanted => {
                postmeta_graphics::transform::slanted(value_to_scalar(right).unwrap_or(0.0))
            }
            SecondaryBinaryOp::ZScaled => {
                let (a, b) = value_to_pair(right).unwrap_or((1.0, 0.0));
                postmeta_graphics::transform::zscaled(a, b)
            }
            SecondaryBinaryOp::Transformed => value_to_transform(right)
                .unwrap_or(postmeta_graphics::types::Transform::IDENTITY),
            SecondaryBinaryOp::Times
            | SecondaryBinaryOp::Over
            | SecondaryBinaryOp::DotProd
            | SecondaryBinaryOp::Infont => postmeta_graphics::types::Transform::IDENTITY,
        }
    }
}
