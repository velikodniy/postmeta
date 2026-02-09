//! Expression parser — four precedence levels.
//!
//! The recursive-descent parser follows `MetaPost`'s four precedence levels:
//! - `scan_primary`: atoms, unary operators, grouping
//! - `scan_secondary`: `*`, `/`, `scaled`, `rotated`, etc.
//! - `scan_tertiary`: `+`, `-`, `++`, `+-+`
//! - `scan_expression`: `=`, `<`, `>`, path construction

use std::fmt::Write;
use std::sync::Arc;

use crate::command::{Command, ExpressionBinaryOp, PlusMinusOp, StrOpOp};
use crate::equation::{const_dep, constant_value, dep_add_scaled, dep_scale};
use crate::error::{ErrorKind, InterpResult, InterpreterError};
use crate::types::{Type, Value};
use crate::variables::{SuffixSegment, VarValue};

use super::helpers::{value_to_bool, value_to_scalar};
use super::{Interpreter, LhsBinding};

impl Interpreter {
    /// Parse and evaluate a primary expression.
    pub(super) fn scan_primary(&mut self) -> InterpResult<()> {
        match self.cur.command {
            Command::NumericToken => {
                if let crate::token::TokenKind::Numeric(v) = self.cur.token.kind {
                    self.cur_exp = Value::Numeric(v);
                    self.cur_type = Type::Known;
                    self.cur_dep = Some(const_dep(v));
                }
                self.last_lhs_binding = None;
                self.get_x_next();
                // Check for fraction: 3/4 as a primary
                if self.cur.command == Command::Slash {
                    self.get_x_next();
                    if let crate::token::TokenKind::Numeric(denom) = self.cur.token.kind {
                        if let Value::Numeric(numer) = self.cur_exp {
                            if denom.abs() > f64::EPSILON {
                                self.cur_exp = Value::Numeric(numer / denom);
                            } else {
                                self.report_error(ErrorKind::ArithmeticError, "Division by zero");
                            }
                        }
                        self.get_x_next();
                    }
                }
                // Implicit multiplication: `3x`, `2bp`, `.5(1,2)`, etc.
                // Triggers when a numeric is followed by a token in
                // [min_primary_command..numeric_token) — i.e., anything
                // that can start a primary EXCEPT +/- and another number.
                if self.cur.command.can_start_implicit_mul() {
                    let factor_dep = self.take_cur_dep();
                    let factor = self.take_cur_exp();
                    self.scan_primary()?;
                    self.last_lhs_binding = None;
                    self.do_implicit_mul(&factor)?;
                    let factor_val = factor_dep
                        .as_ref()
                        .and_then(constant_value)
                        .unwrap_or_else(|| value_to_scalar(&factor).unwrap_or(1.0));
                    self.cur_dep = self.cur_dep.clone().map(|mut d| {
                        dep_scale(&mut d, factor_val);
                        d
                    });
                }
                Ok(())
            }

            Command::StringToken => {
                if let crate::token::TokenKind::StringLit(ref s) = self.cur.token.kind {
                    self.cur_exp = Value::String(Arc::from(s.as_str()));
                    self.cur_type = Type::String;
                }
                self.cur_dep = None;
                self.last_lhs_binding = None;
                self.get_x_next();
                Ok(())
            }

            Command::Nullary => {
                let op = self.cur.modifier;
                self.get_x_next();
                self.last_lhs_binding = None;
                self.do_nullary(op)?;
                self.cur_dep = if let Value::Numeric(v) = self.cur_exp {
                    Some(const_dep(v))
                } else {
                    None
                };
                Ok(())
            }

            Command::Unary => {
                let op = self.cur.modifier;
                self.get_x_next();
                self.scan_primary()?;
                self.do_unary(op)?;
                self.cur_dep = None;
                Ok(())
            }

            Command::PlusOrMinus => {
                // Unary plus or minus
                let is_minus = self.cur.modifier == PlusMinusOp::Minus as u16;
                self.get_x_next();
                self.scan_primary()?;
                if is_minus {
                    self.negate_cur_exp();
                }
                Ok(())
            }

            Command::LeftDelimiter => {
                // ( expr ) or ( expr , expr ) for pair/color
                self.get_x_next();
                self.scan_expression()?;

                if self.cur.command == Command::Comma {
                    // Pair or color
                    let first = self.take_cur_exp();
                    self.get_x_next();
                    self.scan_expression()?;

                    if self.cur.command == Command::Comma {
                        // Color: (r, g, b)
                        let second = self.take_cur_exp();
                        self.get_x_next();
                        self.scan_expression()?;
                        let third = self.take_cur_exp();

                        let r = value_to_scalar(&first)?;
                        let g = value_to_scalar(&second)?;
                        let b = value_to_scalar(&third)?;
                        self.cur_exp = Value::Color(postmeta_graphics::types::Color::new(r, g, b));
                        self.cur_type = Type::ColorType;
                    } else {
                        // Pair: (x, y)
                        let second = self.take_cur_exp();
                        let x = value_to_scalar(&first)?;
                        let y = value_to_scalar(&second)?;
                        self.cur_exp = Value::Pair(x, y);
                        self.cur_type = Type::PairType;
                    }
                    self.last_lhs_binding = None;
                    self.cur_dep = None;
                }

                // Expect closing delimiter
                if self.cur.command == Command::RightDelimiter {
                    self.get_x_next();
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
                self.last_lhs_binding = None;
                // Intentionally keep cur_dep: the group result's dependency
                // info must survive so that unknown numerics (e.g. from
                // `whatever`) can participate in equations after the group.
                Ok(())
            }

            Command::TagToken => {
                // Variable reference — scan suffix parts to form compound name.
                //
                // MetaPost variable names are structured: `laboff.lft`, `z.r`,
                // etc.  The scanner drops `.` separators, so suffixes appear as
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
                let mut name = if let crate::token::TokenKind::Symbolic(ref s) = self.cur.token.kind
                {
                    s.clone()
                } else {
                    String::new()
                };

                let mut has_suffixes = false;

                // Check early if this is a standalone vardef macro.
                let is_root_vardef =
                    root_sym.is_some_and(|s| self.macros.get(&s).is_some_and(|m| m.is_vardef));

                // Advance to next token. We use `get_x_next` (expanding) as
                // mp.web does — since vardefs keep `TagToken`, they won't be
                // expanded by `get_x_next`.
                self.get_x_next();

                // Suffix loop: collect symbolic suffixes, numeric subscripts,
                // and bracketed subscript expressions `[expr]`.
                //
                // For vardef roots, we only collect symbolic suffixes (to build
                // compound names like `laboff.lft`) — NOT subscripts, because
                // numeric tokens and brackets should be parsed as macro
                // arguments, not variable subscripts.
                loop {
                    if self.cur.command == Command::TagToken
                        || self.cur.command == Command::InternalQuantity
                    {
                        if let crate::token::TokenKind::Symbolic(ref s) = self.cur.token.kind {
                            name.push('.');
                            name.push_str(s);
                        }
                        has_suffixes = true;
                        self.get_x_next();
                    } else if !is_root_vardef && self.cur.command == Command::NumericToken {
                        // Bare numeric subscript: pen_3
                        if let crate::token::TokenKind::Numeric(v) = self.cur.token.kind {
                            let _ = write!(name, "[{}]", v as i64);
                        }
                        has_suffixes = true;
                        self.get_x_next();
                    } else if !is_root_vardef && self.cur.command == Command::LeftBracket {
                        // Bracketed subscript: var[expr]
                        self.get_x_next(); // skip `[`
                        self.scan_expression()?;
                        let subscript = match &self.cur_exp {
                            Value::Numeric(v) => *v as i64,
                            _ => 0,
                        };
                        let _ = write!(name, "[{subscript}]");
                        if self.cur.command == Command::RightBracket {
                            self.get_x_next();
                        }
                        has_suffixes = true;
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
                    // or `;`).  We push it as a token-list level so that
                    // `expand_defined_macro` can read it with `get_next`.
                    // Using back_input() would put it in the priority slot,
                    // which is read BEFORE any token-list level — including
                    // the body that expand_defined_macro is about to push.
                    {
                        let mut trailing = crate::input::TokenList::new();
                        self.store_current_token(&mut trailing);
                        if !trailing.is_empty() {
                            self.input.push_token_list(
                                trailing,
                                Vec::new(),
                                "vardef trailing".into(),
                            );
                        }
                    }
                    self.cur.command = Command::DefinedMacro;
                    self.cur.sym = root_sym;
                    self.expand_defined_macro();
                    // After expansion, re-enter scan_primary to parse the
                    // expanded result (mp.web's `goto restart`).
                    return self.scan_primary();
                }

                self.resolve_variable(root_sym, &name)
            }

            Command::InternalQuantity => {
                let idx = self.cur.modifier;
                self.cur_exp = Value::Numeric(self.internals.get(idx));
                self.cur_type = Type::Known;
                self.cur_dep = Some(const_dep(self.internals.get(idx)));
                // Track for assignment LHS
                self.last_internal_idx = Some(idx);
                self.last_var_id = None;
                self.last_lhs_binding = Some(LhsBinding::Internal { idx });
                self.get_x_next();
                Ok(())
            }

            Command::PrimaryBinary => {
                // "expr X of Y" pattern
                let op = self.cur.modifier;
                self.get_x_next();
                self.scan_expression()?;
                // Expect "of"
                if self.cur.command != Command::OfToken {
                    return Err(InterpreterError::new(
                        ErrorKind::MissingToken,
                        "Missing `of`",
                    ));
                }
                let first = self.take_cur_exp();
                self.get_x_next();
                self.scan_primary()?;
                self.last_lhs_binding = None;
                self.cur_dep = None;
                self.do_primary_binary(op, &first)
            }

            Command::Cycle => {
                // The `cycle` keyword in an expression context evaluates to true
                // if the current expression is a cyclic path. But as a primary
                // it's used in path construction — handle that at expression level.
                self.cur_exp = Value::Boolean(false);
                self.cur_type = Type::Boolean;
                self.last_lhs_binding = None;
                self.cur_dep = None;
                self.get_x_next();
                Ok(())
            }

            Command::StrOp => {
                let op = self.cur.modifier;
                self.get_x_next();
                if op == StrOpOp::Str as u16 {
                    // `str` <suffix> — converts suffix to string
                    let name = if let crate::token::TokenKind::Symbolic(ref s) = self.cur.token.kind
                    {
                        s.clone()
                    } else {
                        String::new()
                    };
                    self.get_x_next();
                    self.cur_exp = Value::String(Arc::from(name.as_str()));
                } else {
                    // readfrom etc. — not yet implemented
                    self.cur_exp = Value::String(Arc::from(""));
                }
                self.cur_type = Type::String;
                self.last_lhs_binding = None;
                self.cur_dep = None;
                Ok(())
            }

            Command::CapsuleToken => {
                // A capsule: an already-evaluated expression pushed back
                // via back_expr. Extract the payload directly.
                if let Some((val, ty)) = self.cur.capsule.take() {
                    self.cur_exp = val;
                    self.cur_type = ty;
                } else {
                    // CapsuleToken without payload — shouldn't happen, treat as vacuous
                    self.cur_exp = Value::Vacuous;
                    self.cur_type = Type::Vacuous;
                }
                self.last_lhs_binding = None;
                self.cur_dep = if let Value::Numeric(v) = self.cur_exp {
                    Some(const_dep(v))
                } else {
                    None
                };
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
                use crate::command::TypeNameOp;
                let op = self.cur.modifier;
                self.get_x_next();
                self.scan_primary()?;
                let ty = self.cur_type;
                let result = match op {
                    x if x == TypeNameOp::Numeric as u16 => {
                        // numeric: type_range(known)(independent)
                        ty >= Type::Known && ty <= Type::Independent
                    }
                    x if x == TypeNameOp::Boolean as u16 => {
                        ty == Type::Boolean || ty == Type::UnknownBoolean
                    }
                    x if x == TypeNameOp::String as u16 => {
                        ty == Type::String || ty == Type::UnknownString
                    }
                    x if x == TypeNameOp::Pen as u16 => ty == Type::Pen || ty == Type::UnknownPen,
                    x if x == TypeNameOp::Path as u16 => {
                        ty == Type::Path || ty == Type::UnknownPath
                    }
                    x if x == TypeNameOp::Picture as u16 => {
                        ty == Type::Picture || ty == Type::UnknownPicture
                    }
                    x if x == TypeNameOp::Transform as u16 => ty == Type::TransformType,
                    x if x == TypeNameOp::Color as u16 => ty == Type::ColorType,
                    x if x == TypeNameOp::Pair as u16 => ty == Type::PairType,
                    _ => false,
                };
                self.cur_exp = Value::Boolean(result);
                self.cur_type = Type::Boolean;
                self.last_lhs_binding = None;
                self.cur_dep = None;
                Ok(())
            }

            _ => {
                // Missing primary — set to vacuous
                self.cur_exp = Value::Vacuous;
                self.cur_type = Type::Vacuous;
                self.last_lhs_binding = None;
                self.cur_dep = None;
                Ok(())
            }
        }?;

        // Check for mediation: a[b,c] = (1-a)*b + a*c
        if self.cur.command == Command::LeftBracket {
            if let Value::Numeric(a) = self.cur_exp {
                self.get_x_next();
                self.scan_expression()?;
                let b = self.take_cur_exp();
                if self.cur.command == Command::Comma {
                    self.get_x_next();
                } else {
                    return Err(InterpreterError::new(
                        ErrorKind::MissingToken,
                        "Expected `,` in mediation a[b,c]",
                    ));
                }
                self.scan_expression()?;
                let c = self.take_cur_exp();
                if self.cur.command == Command::RightBracket {
                    self.get_x_next();
                }

                // a[b,c] = b + a*(c-b) = (1-a)*b + a*c
                let one_minus_a = 1.0 - a;
                match (b, c) {
                    (Value::Numeric(bn), Value::Numeric(cn)) => {
                        self.cur_exp = Value::Numeric(a.mul_add(cn - bn, bn));
                        self.cur_type = Type::Known;
                        self.cur_dep = Some(const_dep(a.mul_add(cn - bn, bn)));
                    }
                    (Value::Pair(bx, by), Value::Pair(cx, cy)) => {
                        self.cur_exp =
                            Value::Pair(one_minus_a * bx + a * cx, one_minus_a * by + a * cy);
                        self.cur_type = Type::PairType;
                        self.cur_dep = None;
                    }
                    (Value::Color(bc), Value::Color(cc)) => {
                        self.cur_exp = Value::Color(postmeta_graphics::types::Color::new(
                            one_minus_a * bc.r + a * cc.r,
                            one_minus_a * bc.g + a * cc.g,
                            one_minus_a * bc.b + a * cc.b,
                        ));
                        self.cur_type = Type::ColorType;
                        self.cur_dep = None;
                    }
                    (Value::Transform(bt), Value::Transform(ct)) => {
                        self.cur_exp = Value::Transform(postmeta_graphics::types::Transform {
                            tx: one_minus_a * bt.tx + a * ct.tx,
                            ty: one_minus_a * bt.ty + a * ct.ty,
                            txx: one_minus_a * bt.txx + a * ct.txx,
                            txy: one_minus_a * bt.txy + a * ct.txy,
                            tyx: one_minus_a * bt.tyx + a * ct.tyx,
                            tyy: one_minus_a * bt.tyy + a * ct.tyy,
                        });
                        self.cur_type = Type::TransformType;
                        self.cur_dep = None;
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

                self.last_lhs_binding = None;
            }
        }

        Ok(())
    }

    /// Parse and evaluate a secondary expression.
    pub(super) fn scan_secondary(&mut self) -> InterpResult<()> {
        self.scan_primary()?;

        while self.cur.command.is_secondary_op() {
            let cmd = self.cur.command;

            if cmd == Command::SecondaryPrimaryMacro {
                // User-defined primarydef operator
                let left = self.take_cur_exp();
                self.expand_binary_macro(&left)?;
                break;
            }

            let op = self.cur.modifier;
            let left_dep = self.take_cur_dep();
            let left = self.take_cur_exp();
            self.get_x_next();
            self.scan_primary()?;
            let right_dep = self.cur_dep.clone();

            match cmd {
                Command::SecondaryBinary => {
                    self.last_lhs_binding = None;
                    self.do_secondary_binary(op, &left)?;
                    if op == crate::command::SecondaryBinaryOp::Times as u16 {
                        let left_const = left_dep.as_ref().and_then(constant_value);
                        let right_const = right_dep.as_ref().and_then(constant_value);
                        self.cur_dep = left_const.map_or_else(
                            || {
                                right_const.and_then(|factor| {
                                    left_dep.map(|mut d| {
                                        dep_scale(&mut d, factor);
                                        d
                                    })
                                })
                            },
                            |factor| {
                                right_dep.map(|mut d| {
                                    dep_scale(&mut d, factor);
                                    d
                                })
                            },
                        );
                    } else {
                        self.cur_dep = None;
                    }
                }
                Command::Slash => {
                    // Division
                    let right = self.take_cur_exp();
                    let a = value_to_scalar(&left)?;
                    let b = value_to_scalar(&right)?;
                    if b.abs() < f64::EPSILON {
                        self.report_error(ErrorKind::ArithmeticError, "Division by zero");
                        self.cur_exp = Value::Numeric(0.0);
                        self.cur_dep = Some(const_dep(0.0));
                    } else {
                        self.cur_exp = Value::Numeric(a / b);
                        let right_const = right_dep.as_ref().and_then(constant_value);
                        self.cur_dep = right_const.and_then(|c| {
                            if c.abs() < f64::EPSILON {
                                None
                            } else {
                                left_dep.map(|mut d| {
                                    dep_scale(&mut d, 1.0 / c);
                                    d
                                })
                            }
                        });
                    }
                    self.cur_type = Type::Known;
                    self.last_lhs_binding = None;
                }
                Command::And => {
                    // Logical and
                    let right = self.take_cur_exp();
                    let a = value_to_bool(&left)?;
                    let b = value_to_bool(&right)?;
                    self.cur_exp = Value::Boolean(a && b);
                    self.cur_type = Type::Boolean;
                    self.last_lhs_binding = None;
                    self.cur_dep = None;
                }
                _ => {}
            }
        }
        Ok(())
    }

    /// Parse and evaluate a tertiary expression.
    pub(super) fn scan_tertiary(&mut self) -> InterpResult<()> {
        self.scan_secondary()?;

        while self.cur.command.is_tertiary_op() {
            let cmd = self.cur.command;

            if cmd == Command::TertiarySecondaryMacro {
                // User-defined tertiarydef operator
                let left = self.take_cur_exp();
                self.expand_binary_macro(&left)?;
                break;
            }

            let op = self.cur.modifier;
            let left_dep = self.take_cur_dep();
            let left = self.take_cur_exp();
            self.get_x_next();
            self.scan_secondary()?;
            let right_dep = self.cur_dep.clone();

            match cmd {
                Command::PlusOrMinus => {
                    let right = self.take_cur_exp();
                    self.last_lhs_binding = None;
                    self.do_plus_minus(op, &left, &right)?;
                    self.cur_dep = match (left_dep.as_ref(), right_dep.as_ref()) {
                        (Some(ld), Some(rd)) => {
                            let factor = if op == PlusMinusOp::Plus as u16 {
                                1.0
                            } else {
                                -1.0
                            };
                            Some(dep_add_scaled(ld, rd, factor))
                        }
                        _ => None,
                    };
                }
                Command::TertiaryBinary => {
                    let right = self.take_cur_exp();
                    self.last_lhs_binding = None;
                    self.do_tertiary_binary(op, &left, &right)?;
                    self.cur_dep = None;
                }
                _ => {}
            }
        }
        Ok(())
    }

    /// Parse and evaluate an expression.
    ///
    /// Handles expression-level binary operators and path construction.
    pub fn scan_expression(&mut self) -> InterpResult<()> {
        self.scan_tertiary()?;

        while self.cur.command.is_expression_op() {
            let cmd = self.cur.command;
            let op = self.cur.modifier;

            match cmd {
                Command::Equals => {
                    // This is either an equation or assignment
                    // Don't consume here — let the caller handle it
                    break;
                }
                Command::PathJoin => {
                    // Path construction
                    self.scan_path_construction()?;
                    self.cur_dep = None;
                    break;
                }
                Command::Ampersand => {
                    // & is path join for pairs/paths, string concat otherwise
                    if matches!(self.cur_type, Type::PairType | Type::Path) {
                        self.scan_path_construction()?;
                    } else {
                        // String concatenation
                        let left = self.take_cur_exp();
                        self.get_x_next();
                        self.scan_tertiary()?;
                        self.last_lhs_binding = None;
                        self.do_expression_binary(ExpressionBinaryOp::Concatenate as u16, &left)?;
                        self.cur_dep = None;
                    }
                    break;
                }
                Command::ExpressionTertiaryMacro => {
                    // User-defined secondarydef operator
                    let left = self.take_cur_exp();
                    self.expand_binary_macro(&left)?;
                    self.cur_dep = None;
                    break;
                }
                Command::ExpressionBinary => {
                    let left = self.take_cur_exp();
                    self.get_x_next();
                    self.scan_tertiary()?;
                    self.last_lhs_binding = None;
                    self.do_expression_binary(op, &left)?;
                    self.cur_dep = None;
                }
                Command::LeftBrace => {
                    // Direction specification — start of path construction
                    self.scan_path_construction()?;
                    self.cur_dep = None;
                    break;
                }
                _ => break,
            }
        }
        Ok(())
    }
}
