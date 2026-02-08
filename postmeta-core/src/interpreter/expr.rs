//! Expression parser — four precedence levels.
//!
//! The recursive-descent parser follows `MetaPost`'s four precedence levels:
//! - `scan_primary`: atoms, unary operators, grouping
//! - `scan_secondary`: `*`, `/`, `scaled`, `rotated`, etc.
//! - `scan_tertiary`: `+`, `-`, `++`, `+-+`
//! - `scan_expression`: `=`, `<`, `>`, path construction

use std::sync::Arc;

use crate::command::{Command, ExpressionBinaryOp, PlusMinusOp, StrOpOp};
use crate::error::{ErrorKind, InterpResult, InterpreterError};
use crate::types::{Type, Value};
use crate::variables::{SuffixSegment, VarValue};

use super::helpers::{value_to_bool, value_to_scalar};
use super::Interpreter;

impl Interpreter {
    /// Parse and evaluate a primary expression.
    pub(super) fn scan_primary(&mut self) -> InterpResult<()> {
        match self.cur.command {
            Command::NumericToken => {
                if let crate::token::TokenKind::Numeric(v) = self.cur.token.kind {
                    self.cur_exp = Value::Numeric(v);
                    self.cur_type = Type::Known;
                }
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
                Ok(())
            }

            Command::StringToken => {
                if let crate::token::TokenKind::StringLit(ref s) = self.cur.token.kind {
                    self.cur_exp = Value::String(Arc::from(s.as_str()));
                    self.cur_type = Type::String;
                }
                self.get_x_next();
                Ok(())
            }

            Command::Nullary => {
                let op = self.cur.modifier;
                self.get_x_next();
                self.do_nullary(op)
            }

            Command::Unary => {
                let op = self.cur.modifier;
                self.get_x_next();
                self.scan_primary()?;
                self.do_unary(op)
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
                // Restore scope
                self.do_endgroup();
                self.get_x_next();
                Ok(())
            }

            Command::TagToken => {
                // Variable reference — scan suffix parts to form compound name.
                //
                // MetaPost variable names are structured: `laboff.lft`, `z.r`,
                // etc.  The scanner drops `.` separators, so suffixes appear as
                // consecutive tokens.  A suffix part can be a `TagToken` or even
                // a `DefinedMacro` (e.g. `lft` is a vardef, but `laboff.lft` is
                // a declared pair variable).
                //
                // Two strategies for suffix collection:
                // 1. **Trie-guided** — if the root has entries in `var_trie`,
                //    use the trie to decide which suffix tokens to collect.
                //    This correctly handles `laboff.lft` (declared pair) vs
                //    calling the `lft` vardef macro.
                // 2. **Fallback** — if the root has no trie entry, fall back
                //    to the old `lookup_existing` approach for variables
                //    created by assignment (not type declaration).
                let sym = self.cur.sym;
                let mut name = if let crate::token::TokenKind::Symbolic(ref s) = self.cur.token.kind
                {
                    s.clone()
                } else {
                    String::new()
                };

                let has_trie_entry = sym.is_some_and(|s| self.var_trie.has_root(s));

                // Use get_next (non-expanding) so we can inspect tokens that
                // might be vardef macros before they get expanded.
                self.get_next();

                if has_trie_entry {
                    // Trie-guided suffix collection.
                    let root_sym = sym.unwrap_or(crate::symbols::SymbolId::INVALID);
                    let mut path: Vec<SuffixSegment> = Vec::new();

                    while self.cur.command == Command::TagToken
                        || self.cur.command == Command::DefinedMacro
                        || self.cur.command == Command::InternalQuantity
                    {
                        let Some(suffix_sym) = self.cur.sym else {
                            break;
                        };
                        let has = self.var_trie.has_suffix(root_sym, &path, suffix_sym);
                        if !has {
                            break;
                        }
                        // This suffix is part of the variable name.
                        if let crate::token::TokenKind::Symbolic(ref s) = self.cur.token.kind {
                            name.push('.');
                            name.push_str(s);
                        }
                        path.push(SuffixSegment::Attr(suffix_sym));
                        self.get_next();
                    }
                } else {
                    // Fallback: lookup_existing for variables without trie entries.
                    while self.cur.command == Command::TagToken
                        || self.cur.command == Command::DefinedMacro
                    {
                        let next_name =
                            if let crate::token::TokenKind::Symbolic(ref s) = self.cur.token.kind {
                                s.clone()
                            } else {
                                break;
                            };
                        let compound = format!("{name}.{next_name}");
                        let is_known =
                            self.variables.lookup_existing(&compound).is_some_and(|id| {
                                !matches!(self.variables.get(id), VarValue::Undefined)
                            });
                        if !is_known {
                            break;
                        }
                        name = compound;
                        self.get_next();
                    }
                }

                // Now expand whatever token follows the variable name.
                self.expand_current();

                self.resolve_variable(sym, &name)
            }

            Command::InternalQuantity => {
                let idx = self.cur.modifier;
                self.cur_exp = Value::Numeric(self.internals.get(idx));
                self.cur_type = Type::Known;
                // Track for assignment LHS
                self.last_internal_idx = Some(idx);
                self.last_var_id = None;
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
                self.do_primary_binary(op, &first)
            }

            Command::Cycle => {
                // The `cycle` keyword in an expression context evaluates to true
                // if the current expression is a cyclic path. But as a primary
                // it's used in path construction — handle that at expression level.
                self.cur_exp = Value::Boolean(false);
                self.cur_type = Type::Boolean;
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
                self.get_x_next();
                Ok(())
            }

            Command::TypeName => {
                // Type name as primary — used in type declarations
                // In expression context, this is an error
                Err(InterpreterError::new(
                    ErrorKind::InvalidExpression,
                    "Type name cannot be used as an expression",
                ))
            }

            _ => {
                // Missing primary — set to vacuous
                self.cur_exp = Value::Vacuous;
                self.cur_type = Type::Vacuous;
                Ok(())
            }
        }?;

        // Check for mediation: a[b,c] = (1-a)*b + a*c
        if self.cur.command == Command::LeftBracket {
            if let Value::Numeric(a) = self.cur_exp {
                self.get_x_next();
                self.scan_expression()?;
                let b = value_to_scalar(&self.take_cur_exp())?;
                if self.cur.command == Command::Comma {
                    self.get_x_next();
                } else {
                    return Err(InterpreterError::new(
                        ErrorKind::MissingToken,
                        "Expected `,` in mediation a[b,c]",
                    ));
                }
                self.scan_expression()?;
                let c = value_to_scalar(&self.take_cur_exp())?;
                if self.cur.command == Command::RightBracket {
                    self.get_x_next();
                }
                // a[b,c] = b + a*(c - b) = (1-a)*b + a*c
                self.cur_exp = Value::Numeric(a.mul_add(c - b, b));
                self.cur_type = Type::Known;
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
            let left = self.take_cur_exp();
            self.get_x_next();
            self.scan_primary()?;

            match cmd {
                Command::SecondaryBinary => {
                    self.do_secondary_binary(op, &left)?;
                }
                Command::Slash => {
                    // Division
                    let right = self.take_cur_exp();
                    let a = value_to_scalar(&left)?;
                    let b = value_to_scalar(&right)?;
                    if b.abs() < f64::EPSILON {
                        self.report_error(ErrorKind::ArithmeticError, "Division by zero");
                        self.cur_exp = Value::Numeric(0.0);
                    } else {
                        self.cur_exp = Value::Numeric(a / b);
                    }
                    self.cur_type = Type::Known;
                }
                Command::And => {
                    // Logical and
                    let right = self.take_cur_exp();
                    let a = value_to_bool(&left)?;
                    let b = value_to_bool(&right)?;
                    self.cur_exp = Value::Boolean(a && b);
                    self.cur_type = Type::Boolean;
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
            let left = self.take_cur_exp();
            self.get_x_next();
            self.scan_secondary()?;

            match cmd {
                Command::PlusOrMinus => {
                    let right = self.take_cur_exp();
                    self.do_plus_minus(op, &left, &right)?;
                }
                Command::TertiaryBinary => {
                    let right = self.take_cur_exp();
                    self.do_tertiary_binary(op, &left, &right)?;
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
                        self.do_expression_binary(ExpressionBinaryOp::Concatenate as u16, &left)?;
                    }
                    break;
                }
                Command::ExpressionTertiaryMacro => {
                    // User-defined secondarydef operator
                    let left = self.take_cur_exp();
                    self.expand_binary_macro(&left)?;
                    break;
                }
                Command::ExpressionBinary => {
                    let left = self.take_cur_exp();
                    self.get_x_next();
                    self.scan_tertiary()?;
                    self.do_expression_binary(op, &left)?;
                }
                Command::LeftBrace => {
                    // Direction specification — start of path construction
                    self.scan_path_construction()?;
                    break;
                }
                _ => break,
            }
        }
        Ok(())
    }
}
