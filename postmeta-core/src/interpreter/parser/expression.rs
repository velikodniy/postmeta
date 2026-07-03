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
    TertiaryBinaryOp, TypeNameOp, UnaryOp,
};
use crate::equation::{const_dep, constant_value, dep_add_scaled, dep_scale};
use crate::error::{ErrorKind, InterpResult, InterpreterError};
use crate::symbols::SymbolId;
use crate::types::{Type, Value};
use crate::variables::SuffixSegment;

use crate::interpreter::EqualsMode;
use crate::interpreter::helpers::{value_to_bool, value_to_scalar};
use crate::interpreter::{ExprResultValue, Interpreter, LhsBinding};

/// Format a numeric subscript into a variable name string.
///
/// `MetaPost` supports fractional subscripts (e.g., `A[0.08]`). We need a
/// canonical string representation so that two evaluations of the same
/// numeric value always produce the same key. Integer values are formatted
/// without decimals (e.g., `[1]`) for backward compatibility; fractional
/// values use Rust's shortest round-trip representation (e.g., `[0.08]`).
///
/// This is the ONLY subscript formatter: variable identity and the `str`
/// operator both go through it, so a subscript always round-trips to the
/// same key/text.
fn write_subscript_key(name: &mut String, v: f64) {
    let rounded = v.round();
    if (v - rounded).abs() < 1e-10 {
        #[expect(
            clippy::cast_possible_truncation,
            reason = "subscript formatting uses rounded integer representation"
        )]
        let _ = write!(name, "[{}]", rounded as i64);
    } else {
        let _ = write!(name, "[{v}]");
    }
}

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
    #[allow(clippy::too_many_lines)]
    pub(in crate::interpreter) fn scan_primary(&mut self) -> InterpResult<ExprResultValue> {
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
                ExprResultValue::plain(val)
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
                // known/unknown need the operand's type, not its value.
                if op == UnaryOp::KnownOp || op == UnaryOp::UnknownOp {
                    let ty = operand_result.ty;
                    let is_known = (ty as u8) < (Type::Dependent as u8);
                    let result = if op == UnaryOp::KnownOp {
                        is_known
                    } else {
                        !is_known
                    };
                    self.lhs_tracking.last_lhs_binding = None;
                    ExprResultValue::plain(Value::Boolean(result))
                } else {
                    // `bad_unary` reports a diagnostic but keeps the
                    // operand unchanged. We catch type errors
                    // here so they don't abort the whole expression.
                    match self.do_unary(op, &operand_result.exp, operand_result.pair_dep.clone()) {
                        Ok(r) => r,
                        Err(e) => {
                            if op != UnaryOp::Reverse {
                                self.report_error(e.kind, e.message);
                            }
                            operand_result
                        }
                    }
                }
            }

            Command::PlusOrMinus => {
                // Unary plus or minus
                let is_minus =
                    PlusMinusOp::from_modifier(self.cur.modifier) == Some(PlusMinusOp::Minus);
                self.get_x_next();
                let mut result = self.scan_primary()?;
                if is_minus {
                    result = self.negate_value(result);
                }
                result
            }

            Command::LeftDelimiter => self.scan_primary_delimited()?,

            Command::BeginGroup => {
                self.state.scope_manager.begin_group(&mut self.state.macros);
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
                let v = self.state.internals.get(idx);
                // Track for assignment LHS
                self.lhs_tracking.last_lhs_binding = Some(LhsBinding::Internal { idx });
                self.get_x_next();
                ExprResultValue::numeric_known(v)
            }

            Command::PrimaryBinary => {
                // "expr X of Y" pattern
                let op = self.cur.modifier;
                self.get_x_next();
                let first_result = self.scan_expression(EqualsMode::Relation)?;
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
                ExprResultValue::typed(val, ty)
            }

            Command::Cycle => {
                self.lhs_tracking.last_lhs_binding = None;
                self.get_x_next();
                ExprResultValue::plain(Value::Boolean(false))
            }

            Command::StrOp => {
                // `str` <suffix> — converts suffix to string
                self.get_x_next();
                let name = self.scan_str_suffix()?;
                let val = Value::String(Arc::from(name.as_str()));
                self.lhs_tracking.last_lhs_binding = None;
                ExprResultValue::plain(val)
            }

            Command::CapsuleToken => {
                let result =
                    self.cur
                        .capsule
                        .take()
                        .map_or_else(ExprResultValue::vacuous, |arc_payload| {
                            // Try to unwrap the Arc to avoid cloning
                            // (O(1) when refcount is 1).
                            match Arc::try_unwrap(arc_payload) {
                                Ok(payload) => payload,
                                Err(arc) => arc.as_ref().clone(),
                            }
                        });
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
                    Some(TypeNameOp::Numeric) => ty >= Type::Known && ty <= Type::Independent,
                    Some(TypeNameOp::Boolean) => ty == Type::Boolean || ty == Type::UnknownBoolean,
                    Some(TypeNameOp::String) => ty == Type::String || ty == Type::UnknownString,
                    Some(TypeNameOp::Pen) => ty == Type::Pen || ty == Type::UnknownPen,
                    Some(TypeNameOp::Path) => ty == Type::Path || ty == Type::UnknownPath,
                    Some(TypeNameOp::Picture) => ty == Type::Picture || ty == Type::UnknownPicture,
                    Some(TypeNameOp::Transform) => ty == Type::TransformType,
                    Some(TypeNameOp::Color) => ty == Type::ColorType,
                    Some(TypeNameOp::Pair) => ty == Type::PairType,
                    _ => false,
                };
                self.lhs_tracking.last_lhs_binding = None;
                ExprResultValue::plain(Value::Boolean(result))
            }

            _ => {
                // Missing primary — set to vacuous
                self.lhs_tracking.last_lhs_binding = None;
                self.report_error(ErrorKind::MissingToken, "Missing primary expression");
                ExprResultValue::vacuous()
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
        let mut result = ExprResultValue::numeric_known(v);
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
        let first_result = self.scan_expression(EqualsMode::Relation)?;

        let result = if self.cur.command == Command::Comma {
            // Pair or color
            let first = first_result.exp;
            let first_dep = first_result.dep;
            let second_dep_backup = first_result.pair_dep;
            let _ = second_dep_backup; // unused in pair/color
            let first_binding = self.lhs_tracking.last_lhs_binding.clone();
            self.get_x_next();
            let second_result = self.scan_expression(EqualsMode::Relation)?;
            let second = second_result.exp;
            let second_binding = self.lhs_tracking.last_lhs_binding.clone();

            if self.cur.command == Command::Comma {
                // Color: (r, g, b)
                self.get_x_next();
                let third_result = self.scan_expression(EqualsMode::Relation)?;
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
                ExprResultValue::plain(Value::Color(postmeta_graphics::types::Color::new(r, g, b)))
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
        if self.cur.command == Command::RightDelimiter && self.cur.modifier == expected_delimiter {
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
    #[allow(clippy::too_many_lines)]
    fn scan_mediation(&mut self, primary: ExprResultValue) -> InterpResult<ExprResultValue> {
        if self.cur.command != Command::LeftBracket {
            return Ok(primary);
        }
        let Value::Numeric(a) = primary.exp else {
            return Ok(primary);
        };

        let a_dep = primary.dep.unwrap_or_else(|| const_dep(a));
        self.get_x_next();
        let b_result = self.scan_expression(EqualsMode::Relation)?;
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
        let c_result = self.scan_expression(EqualsMode::Relation)?;
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
        let lerp = |b: f64, c: f64| a.mul_add(c - b, b);
        let result = match (b, c) {
            (Value::Numeric(bn), Value::Numeric(cn)) => {
                let b_dep = b_dep.unwrap_or_else(|| const_dep(bn));
                let c_dep = c_dep.unwrap_or_else(|| const_dep(cn));
                let a_is_linear = constant_value(&a_dep).is_none();
                let bc_have_linear =
                    constant_value(&b_dep).is_none() || constant_value(&c_dep).is_none();

                let dep = if a_is_linear && bc_have_linear {
                    self.report_error(
                        ErrorKind::IncompatibleTypes,
                        "Nonlinear dependency in mediation",
                    );
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
                    self.report_error(
                        ErrorKind::IncompatibleTypes,
                        "Nonlinear dependency in mediation",
                    );
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
                    exp: Value::Pair(lerp(bx, cx), lerp(by, cy)),
                    ty: Type::PairType,
                    dep: None,
                    pair_dep,
                }
            }
            (Value::Color(bc), Value::Color(cc)) => {
                ExprResultValue::plain(Value::Color(postmeta_graphics::types::Color::new(
                    lerp(bc.r, cc.r),
                    lerp(bc.g, cc.g),
                    lerp(bc.b, cc.b),
                )))
            }
            (Value::Transform(bt), Value::Transform(ct)) => {
                ExprResultValue::plain(Value::Transform(postmeta_graphics::types::Transform {
                    tx: lerp(bt.tx, ct.tx),
                    ty: lerp(bt.ty, ct.ty),
                    txx: lerp(bt.txx, ct.txx),
                    txy: lerp(bt.txy, ct.txy),
                    tyx: lerp(bt.tyx, ct.tyx),
                    tyy: lerp(bt.tyy, ct.tyy),
                }))
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
        };

        self.lhs_tracking.last_lhs_binding = None;
        Ok(result)
    }

    fn scan_tag_token(&mut self) -> InterpResult<ExprResultValue> {
        // Variable reference — scan suffix parts to form compound name.
        let root_sym = self.cur.sym;

        // Defer String allocation: only build the name string when suffixes
        // are found. For root-only variables (the common case in tight loops),
        // resolve_variable uses lookup_by_sym which avoids string hashing.
        let mut name: Option<String> = None;
        let mut suffix_segs: Vec<SuffixSegment> = Vec::new();

        // Check early if this is a standalone vardef macro.
        let is_root_vardef = root_sym
            .and_then(|symbol| self.state.macros.get(symbol))
            .is_some_and(|info| info.is_vardef);

        self.get_x_next();

        // Suffix loop: collect symbolic suffixes, numeric subscripts,
        // and bracketed subscript expressions `[expr]`.
        loop {
            if !is_root_vardef
                && (self.cur.command == Command::TagToken
                    || self.cur.command == Command::InternalQuantity)
            {
                if let Some(sym) = self.cur.sym {
                    suffix_segs.push(SuffixSegment::Attr(sym));
                    let n = name.get_or_insert_with(|| self.cur_root_name(root_sym));
                    n.push('.');
                    n.push_str(self.state.symbols.name(sym));
                }
                self.get_x_next();
            } else if !is_root_vardef && self.cur.command == Command::NumericToken {
                if let crate::token::TokenKind::Numeric(v) = self.cur.token.kind {
                    let n = name.get_or_insert_with(|| self.cur_root_name(root_sym));
                    write_subscript_key(n, v);
                    suffix_segs.push(SuffixSegment::Subscript);
                }
                self.get_x_next();
            } else if !is_root_vardef && self.cur.command == Command::LeftBracket {
                self.get_x_next(); // skip `[`
                let subscript_result = self.scan_expression(EqualsMode::Relation)?;
                if self.cur.command == Command::RightBracket {
                    // Subscript: var[expr]
                    let subscript = match &subscript_result.exp {
                        Value::Numeric(v) => *v,
                        _ => 0.0,
                    };
                    let n = name.get_or_insert_with(|| self.cur_root_name(root_sym));
                    write_subscript_key(n, subscript);
                    suffix_segs.push(SuffixSegment::Subscript);
                    self.get_x_next();
                } else {
                    // Not a subscript — put the expression and
                    // the current token back, then restore `[`
                    // as the current command so the mediation
                    // check after variable resolution can see it.
                    use crate::input::StoredToken;
                    let result = subscript_result;
                    let mut tl = vec![StoredToken::Capsule(Arc::new(result))];
                    self.store_current_token(&mut tl);
                    self.state
                        .input
                        .push_token_list(tl, Vec::new(), "mediation backtrack");
                    self.cur.command = Command::LeftBracket;
                    break;
                }
            } else {
                break;
            }
        }

        let has_suffixes = name.is_some();
        let is_vardef_call = !has_suffixes && is_root_vardef;

        if is_vardef_call {
            let mut trailing = crate::input::TokenList::new();
            self.store_current_token(&mut trailing);
            if !trailing.is_empty() {
                self.state
                    .input
                    .push_token_list(trailing, Vec::new(), "vardef trailing");
            }
            self.cur.command = Command::DefinedMacro;
            self.cur.sym = root_sym;
            self.expand_defined_macro();
            return self.scan_primary();
        }

        if let Some(ref name_str) = name {
            // Suffixed variable — must use string-based lookup.
            Ok(self.resolve_variable(root_sym, name_str, &suffix_segs))
        } else {
            // Root-only variable — use resolve_variable_root which avoids
            // String allocation when the sym cache hits.
            Ok(self.resolve_variable_root(root_sym))
        }
    }

    /// Get the root variable name from a symbol, allocating a `String`.
    fn cur_root_name(&self, sym: Option<SymbolId>) -> String {
        sym.map_or_else(String::new, |s| self.state.symbols.name(s).to_owned())
    }

    fn scan_str_suffix(&mut self) -> InterpResult<String> {
        let mut name = String::new();
        let mut first = true;

        loop {
            if self.cur.command == Command::TagToken
                || self.cur.command == Command::InternalQuantity
            {
                if let Some(s) = self.cur_symbolic_name() {
                    if !first {
                        name.push('.');
                    }
                    name.push_str(s);
                }
                self.get_x_next();
                first = false;
            } else if self.cur.command == Command::NumericToken {
                if let crate::token::TokenKind::Numeric(v) = self.cur.token.kind {
                    write_subscript_key(&mut name, v);
                }
                self.get_x_next();
                first = false;
            } else if self.cur.command == Command::LeftBracket {
                self.get_x_next(); // skip `[`
                let subscript_result = self.scan_expression(EqualsMode::Relation)?;
                let subscript = match subscript_result.exp {
                    Value::Numeric(v) => v,
                    _ => 0.0,
                };
                write_subscript_key(&mut name, subscript);
                if self.cur.command == Command::RightBracket {
                    self.get_x_next();
                } else {
                    self.report_error(ErrorKind::MissingToken, "Expected `]` in suffix");
                    break;
                }
                first = false;
            } else {
                break;
            }
        }

        Ok(name)
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
    pub(in crate::interpreter) fn scan_secondary(&mut self) -> InterpResult<ExprResultValue> {
        self.scan_infix_bp(Command::BP_SECONDARY, false)
    }

    /// Parse and evaluate a tertiary expression, returning the result.
    pub(in crate::interpreter) fn scan_tertiary(&mut self) -> InterpResult<ExprResultValue> {
        self.scan_infix_bp(Command::BP_TERTIARY, false)
    }

    /// Parse and evaluate an expression, returning the result.
    ///
    /// Handles expression-level binary operators and path construction.
    pub(crate) fn scan_expression(
        &mut self,
        equals_mode: EqualsMode,
    ) -> InterpResult<ExprResultValue> {
        self.scan_infix_bp(Command::BP_EXPRESSION, equals_mode == EqualsMode::Equation)
    }

    // =====================================================================
    // Unified infix (led) handler
    // =====================================================================

    /// Single led dispatch for all infix operators.
    #[allow(clippy::too_many_lines)]
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
                let (val, ty) = Self::do_secondary_binary(
                    op,
                    &left_val,
                    &right.exp,
                    self.state.font_provider.as_deref(),
                )?;
                let result = if op == SecondaryBinaryOp::Times {
                    self.mul_deps(val, ty, &left_val, left_dep, left_pair_dep, &right)
                } else {
                    self.transform_deps(
                        val,
                        ty,
                        op,
                        &left_val,
                        left_pair_dep,
                        &right,
                        right_binding.as_ref(),
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
                let result = self.div_deps(&left_val, left_dep.as_ref(), left_pair_dep, &right)?;
                Ok(InfixAction::Continue(result))
            }

            Command::And => {
                let left_val = left.exp;
                self.get_x_next();
                let right = self.scan_rhs(cmd)?;
                let a = value_to_bool(&left_val)?;
                let b = value_to_bool(&right.exp)?;
                self.lhs_tracking.last_lhs_binding = None;
                Ok(InfixAction::Continue(ExprResultValue::plain(
                    Value::Boolean(a && b),
                )))
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
                let factor = if op == PlusMinusOp::Plus { 1.0 } else { -1.0 };
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
                let result = if op == TertiaryBinaryOp::IntersectionTimes {
                    if let Value::Pair(x, y) = val {
                        ExprResultValue {
                            exp: Value::Pair(x, y),
                            ty,
                            dep: None,
                            pair_dep: Some((const_dep(x), const_dep(y))),
                        }
                    } else {
                        ExprResultValue::typed(val, ty)
                    }
                } else {
                    ExprResultValue::typed(val, ty)
                };
                Ok(InfixAction::Continue(result))
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
                Ok(InfixAction::Continue(ExprResultValue::typed(val, ty)))
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
                Ok(InfixAction::Continue(ExprResultValue::typed(val, ty)))
            }

            // ----- Path construction and & -----
            Command::PathJoin | Command::LeftBrace => {
                let result = self.scan_path_construction(left)?;
                // Continue (not Break) so expression-level operators like
                // `cutbefore`/`cutafter` (tertiarydef macros) that follow
                // the path are picked up by the Pratt loop.
                Ok(InfixAction::Continue(result))
            }

            Command::Ampersand => {
                if matches!(left.ty, Type::PairType | Type::Path) {
                    let result = self.scan_path_construction(left)?;
                    Ok(InfixAction::Continue(result))
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
                    Ok(InfixAction::Continue(ExprResultValue::typed(val, ty)))
                }
            }

            _ => Ok(InfixAction::Break(left)),
        }
    }
}
