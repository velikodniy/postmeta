//! Statement execution.
//!
//! Implements `do_statement` (the top-level statement dispatcher) and all
//! individual statement handlers: type declarations, `addto`, `clip`,
//! `setbounds`, `shipout`, `save`, `interim`, `let`, `delimiters`,
//! `newinternal`, `show`, `message`, and `endgroup`.

use std::sync::Arc;

use postmeta_graphics::picture;
use postmeta_graphics::types::{Color, LineCap, LineJoin, Path, Pen, Picture};

use crate::command::{BoundsOp, Command, MessageOp, ThingToAddOp, TypeNameOp, WithOptionOp};
use crate::error::{ErrorKind, InterpResult};
use crate::internals::InternalId;
use crate::types::{DrawingState, Type, Value};
use crate::variables::{NumericState, SaveEntry, SuffixSegment, VarValue};

use super::helpers::{value_to_path_owned, value_to_scalar};
use super::{Interpreter, LhsBinding};

impl Interpreter {
    /// Execute one statement.
    pub fn do_statement(&mut self) -> InterpResult<()> {
        match self.cur.command {
            Command::Semicolon => {
                // Empty statement
                self.get_x_next();
                Ok(())
            }
            Command::Stop => Ok(()), // End of input

            Command::TypeName => self.do_type_declaration(),
            Command::AddTo => self.do_addto(),
            Command::Bounds => self.do_bounds(),
            Command::ShipOut => self.do_shipout(),
            Command::Outer => self.do_outer(),
            Command::Save => self.do_save(),
            Command::Interim => self.do_interim(),
            Command::Let => self.do_let(),
            Command::MacroDef => self.do_macro_def(),
            Command::Delimiters => self.do_delimiters(),
            Command::NewInternal => self.do_new_internal(),
            Command::Show => self.do_show(),
            Command::MessageCommand => self.do_message(),
            Command::BeginGroup => {
                self.save_stack.push_boundary();
                self.get_x_next();
                Ok(())
            }
            Command::EndGroup => {
                self.do_endgroup();
                self.get_x_next();
                Ok(())
            }

            _ => {
                // Expression or equation
                self.scan_expression()?;

                if self.cur.command == Command::Equals {
                    // Equation chain: lhs = mid = ... = rhs.
                    // All left-hand sides are equated to the FINAL rightmost value.
                    let mut pending_lhs: Vec<(
                        Value,
                        Option<LhsBinding>,
                        Option<crate::equation::DepList>,
                    )> = Vec::new();
                    while self.cur.command == Command::Equals {
                        let lhs_dep = self.cur_dep.clone();
                        let lhs = self.take_cur_exp();
                        let lhs_binding = self.last_lhs_binding;
                        pending_lhs.push((lhs, lhs_binding, lhs_dep));
                        self.get_x_next();
                        self.scan_expression()?;
                    }

                    let rhs_clone = self.cur_exp.clone();
                    let rhs_dep = self.cur_dep.clone();
                    for (lhs, lhs_binding, lhs_dep) in &pending_lhs {
                        self.do_equation(
                            lhs,
                            &rhs_clone,
                            *lhs_binding,
                            lhs_dep.clone(),
                            rhs_dep.clone(),
                        )?;
                    }
                } else if self.cur.command == Command::Assignment {
                    // Assignment chain: a := b := ... := rhs
                    // All left-hand sides receive the final rhs value.
                    let mut pending_lhs: Vec<Option<LhsBinding>> = Vec::new();
                    while self.cur.command == Command::Assignment {
                        pending_lhs.push(self.last_lhs_binding);
                        self.get_x_next();
                        self.scan_expression()?;
                    }

                    let rhs = self.cur_exp.clone();
                    for lhs_binding in pending_lhs {
                        self.assign_binding(lhs_binding, &rhs)?;
                    }
                }

                // Expect statement terminator
                if self.cur.command == Command::Semicolon {
                    self.get_x_next();
                } else if self.cur.command == Command::EndGroup || self.cur.command == Command::Stop
                {
                    // OK — endgroup or end terminates too
                } else if self.cur.command == Command::MacroSpecial && self.cur.modifier == 0 {
                    // Allow an implicit terminator before `enddef` in macro bodies.
                    self.get_x_next();
                } else {
                    self.report_error(
                        ErrorKind::MissingToken,
                        format!(
                            "Missing `;` (got {:?} {:?})",
                            self.cur.command, self.cur.token.kind
                        ),
                    );
                    // Skip to the next semicolon (or end) to recover.
                    while self.cur.command != Command::Semicolon
                        && self.cur.command != Command::Stop
                        && self.cur.command != Command::EndGroup
                    {
                        self.get_x_next();
                    }
                    if self.cur.command == Command::Semicolon {
                        self.get_x_next();
                    }
                }
                Ok(())
            }
        }
    }

    /// Execute a type declaration (`numeric x, y;`).
    fn do_type_declaration(&mut self) -> InterpResult<()> {
        let type_op = self.cur.modifier;
        self.get_x_next();

        loop {
            // Expect a variable name (possibly compound with suffixes)
            if let crate::token::TokenKind::Symbolic(ref name) = self.cur.token.kind {
                let mut name = name.clone();
                let root_sym = self.cur.sym;
                let mut suffix_segs: Vec<SuffixSegment> = Vec::new();

                // Use get_next (non-expanding) to avoid expanding vardef
                // suffixes like `lft` in `pair laboff.lft`.
                self.get_next();

                // Collect suffix tokens (tag tokens, subscripts, and symbols
                // that might be macros but are suffix parts).  The scanner
                // drops `.` separators, so suffix parts appear as consecutive
                // tokens.  We use non-expanding reads to avoid triggering
                // vardef expansion on suffix names.
                loop {
                    if self.cur.command == Command::LeftBracket {
                        // Subscript array suffix `[]`
                        self.get_next();
                        if self.cur.command == Command::RightBracket {
                            suffix_segs.push(SuffixSegment::Subscript);
                            self.get_next();
                        } else {
                            // Not `[]` — push the bracket back and stop
                            self.back_input();
                            break;
                        }
                    } else if self.cur.command == Command::TagToken
                        || self.cur.command == Command::DefinedMacro
                        || self.cur.command == Command::InternalQuantity
                    {
                        // Suffix part (e.g. `l` in `path_.l`, `lft` in `laboff.lft`)
                        if let crate::token::TokenKind::Symbolic(ref s) = self.cur.token.kind {
                            if let Some(sym) = self.cur.sym {
                                suffix_segs.push(SuffixSegment::Attr(sym));
                            }
                            name.push('.');
                            name.push_str(s);
                        }
                        self.get_next();
                    } else {
                        break;
                    }
                }
                // Expand whatever follows the variable name.
                self.expand_current();

                let var_id = self.variables.lookup(&name);

                // Determine the MetaPost type for the trie registration
                let mp_type = Self::type_op_to_type(type_op);

                // Set the variable to the correct type
                let val = match type_op {
                    x if x == TypeNameOp::Numeric as u16 => {
                        VarValue::NumericVar(NumericState::Numeric)
                    }
                    x if x == TypeNameOp::Boolean as u16 => VarValue::Known(Value::Boolean(false)),
                    x if x == TypeNameOp::String as u16 => {
                        VarValue::Known(Value::String(Arc::from("")))
                    }
                    x if x == TypeNameOp::Path as u16 => {
                        VarValue::Known(Value::Path(Path::default()))
                    }
                    x if x == TypeNameOp::Pen as u16 => VarValue::Known(Value::Pen(Pen::default())),
                    x if x == TypeNameOp::Picture as u16 => {
                        VarValue::Known(Value::Picture(Picture::default()))
                    }
                    x if x == TypeNameOp::Pair as u16 => {
                        let x_id = self.variables.alloc();
                        let y_id = self.variables.alloc();
                        self.variables
                            .set(x_id, VarValue::NumericVar(NumericState::Numeric));
                        self.variables
                            .set(y_id, VarValue::NumericVar(NumericState::Numeric));
                        // Also register named sub-parts so xpart/ypart can find them
                        self.variables.register_name(&format!("{name}.x"), x_id);
                        self.variables.register_name(&format!("{name}.y"), y_id);
                        VarValue::Pair { x: x_id, y: y_id }
                    }
                    x if x == TypeNameOp::Color as u16 => {
                        let r_id = self.variables.alloc();
                        let g_id = self.variables.alloc();
                        let b_id = self.variables.alloc();
                        self.variables
                            .set(r_id, VarValue::NumericVar(NumericState::Numeric));
                        self.variables
                            .set(g_id, VarValue::NumericVar(NumericState::Numeric));
                        self.variables
                            .set(b_id, VarValue::NumericVar(NumericState::Numeric));
                        self.variables.register_name(&format!("{name}.r"), r_id);
                        self.variables.register_name(&format!("{name}.g"), g_id);
                        self.variables.register_name(&format!("{name}.b"), b_id);
                        VarValue::Color {
                            r: r_id,
                            g: g_id,
                            b: b_id,
                        }
                    }
                    x if x == TypeNameOp::Transform as u16 => {
                        let tx = self.variables.alloc();
                        let ty = self.variables.alloc();
                        let txx = self.variables.alloc();
                        let txy = self.variables.alloc();
                        let tyx = self.variables.alloc();
                        let tyy = self.variables.alloc();
                        for id in [tx, ty, txx, txy, tyx, tyy] {
                            self.variables
                                .set(id, VarValue::NumericVar(NumericState::Numeric));
                        }
                        self.variables.register_name(&format!("{name}.tx"), tx);
                        self.variables.register_name(&format!("{name}.ty"), ty);
                        self.variables.register_name(&format!("{name}.txx"), txx);
                        self.variables.register_name(&format!("{name}.txy"), txy);
                        self.variables.register_name(&format!("{name}.tyx"), tyx);
                        self.variables.register_name(&format!("{name}.tyy"), tyy);
                        VarValue::Transform {
                            tx,
                            ty,
                            txx,
                            txy,
                            tyx,
                            tyy,
                        }
                    }
                    _ => VarValue::Undefined,
                };
                self.variables.set(var_id, val);

                // Register in the variable type trie
                if let Some(root) = root_sym {
                    self.var_trie.declare(root, &suffix_segs, mp_type);
                }
            } else {
                // Non-symbolic token — skip it
                self.get_x_next();
            }

            if self.cur.command == Command::Comma {
                self.get_x_next();
                continue;
            }
            break;
        }

        if self.cur.command == Command::Semicolon {
            self.get_x_next();
        }
        Ok(())
    }

    /// Convert a `TypeNameOp` modifier to a `Type`.
    const fn type_op_to_type(type_op: u16) -> Type {
        match type_op {
            x if x == TypeNameOp::Numeric as u16 => Type::Numeric,
            x if x == TypeNameOp::Boolean as u16 => Type::Boolean,
            x if x == TypeNameOp::String as u16 => Type::String,
            x if x == TypeNameOp::Path as u16 => Type::Path,
            x if x == TypeNameOp::Pen as u16 => Type::Pen,
            x if x == TypeNameOp::Picture as u16 => Type::Picture,
            x if x == TypeNameOp::Pair as u16 => Type::PairType,
            x if x == TypeNameOp::Color as u16 => Type::ColorType,
            x if x == TypeNameOp::Transform as u16 => Type::TransformType,
            _ => Type::Undefined,
        }
    }

    /// Execute `addto` statement.
    fn do_addto(&mut self) -> InterpResult<()> {
        self.get_x_next();

        // Get the target picture variable name
        let pic_name = if let crate::token::TokenKind::Symbolic(ref s) = self.cur.token.kind {
            s.clone()
        } else {
            "currentpicture".to_owned()
        };
        self.get_x_next();

        // Expect contour / doublepath / also
        let thing = self.cur.modifier;
        self.get_x_next();

        match thing {
            x if x == ThingToAddOp::Contour as u16 => {
                self.scan_expression()?;
                let path_val = self.take_cur_exp();
                let path = value_to_path_owned(path_val)?;

                let ds = self.scan_with_options()?;

                picture::addto_contour(
                    &mut self.current_picture,
                    path,
                    ds.color,
                    if matches!(ds.pen, Pen::Elliptical(a) if a == kurbo::Affine::default()) {
                        None
                    } else {
                        Some(ds.pen)
                    },
                    ds.line_join,
                    ds.miter_limit,
                );
            }
            x if x == ThingToAddOp::DoublePath as u16 => {
                self.scan_expression()?;
                let path_val = self.take_cur_exp();
                let path = value_to_path_owned(path_val)?;

                let ds = self.scan_with_options()?;

                picture::addto_doublepath(
                    &mut self.current_picture,
                    path,
                    ds.pen,
                    ds.color,
                    ds.dash,
                    ds.line_cap,
                    ds.line_join,
                    ds.miter_limit,
                );
            }
            x if x == ThingToAddOp::Also as u16 => {
                self.scan_expression()?;
                let pic_val = self.take_cur_exp();
                if let Value::Picture(p) = pic_val {
                    picture::addto_also(&mut self.current_picture, &p);
                }
            }
            _ => {
                self.report_error(
                    ErrorKind::MissingToken,
                    "Expected `contour`, `doublepath`, or `also`",
                );
            }
        }

        let _ = pic_name; // TODO: support named pictures

        if self.cur.command == Command::Semicolon {
            self.get_x_next();
        }
        Ok(())
    }

    /// Scan `withpen`, `withcolor`, `dashed` options.
    fn scan_with_options(&mut self) -> InterpResult<DrawingState> {
        let mut ds = DrawingState {
            pen: Pen::default_pen(),
            color: Color::BLACK,
            dash: None,
            line_cap: LineCap::from_f64(self.internals.get(InternalId::LineCap as u16)),
            line_join: LineJoin::from_f64(self.internals.get(InternalId::LineJoin as u16)),
            miter_limit: self.internals.get(InternalId::MiterLimit as u16),
        };

        while self.cur.command == Command::WithOption {
            let opt = self.cur.modifier;
            self.get_x_next();
            self.scan_expression()?;
            let val = self.take_cur_exp();

            match opt {
                x if x == WithOptionOp::WithPen as u16 => {
                    if let Value::Pen(p) = val {
                        ds.pen = p;
                    }
                }
                x if x == WithOptionOp::WithColor as u16 => {
                    if let Value::Color(c) = val {
                        ds.color = c;
                    } else if let Value::Numeric(v) = val {
                        ds.color = Color::new(v, v, v);
                    }
                }
                x if x == WithOptionOp::Dashed as u16 => {
                    // For now, ignore dash pattern (complex to extract)
                }
                _ => {}
            }
        }

        Ok(ds)
    }

    /// Execute `clip`/`setbounds` statement.
    fn do_bounds(&mut self) -> InterpResult<()> {
        let is_clip = self.cur.modifier == BoundsOp::Clip as u16;
        self.get_x_next();

        // Get picture name
        let _pic_name = if let crate::token::TokenKind::Symbolic(ref s) = self.cur.token.kind {
            s.clone()
        } else {
            "currentpicture".to_owned()
        };
        self.get_x_next();

        // Expect "to"
        if self.cur.command == Command::ToToken {
            self.get_x_next();
        }

        self.scan_expression()?;
        let val = self.take_cur_exp();
        let clip_path = value_to_path_owned(val)?;

        if is_clip {
            picture::clip(&mut self.current_picture, clip_path);
        } else {
            picture::setbounds(&mut self.current_picture, clip_path);
        }

        if self.cur.command == Command::Semicolon {
            self.get_x_next();
        }
        Ok(())
    }

    /// Execute `shipout` statement.
    fn do_shipout(&mut self) -> InterpResult<()> {
        self.get_x_next();
        self.scan_expression()?;
        let val = self.take_cur_exp();

        let pic = if let Value::Picture(p) = val {
            p
        } else {
            self.current_picture.clone()
        };

        self.pictures.push(pic);

        if self.cur.command == Command::Semicolon {
            self.get_x_next();
        }
        Ok(())
    }

    /// Execute `outer` statement (no-op — skip the token list).
    ///
    /// In `MetaPost`, `outer` marks tokens so they cannot appear inside
    /// macro definitions.  We parse the comma-separated token list but
    /// do not enforce the restriction.
    ///
    /// Syntax: `outer <token> [, <token>]* ;`
    fn do_outer(&mut self) -> InterpResult<()> {
        // Read token names separated by commas until semicolon.
        // Use get_next (non-expanding) to avoid triggering `end`/`bye`.
        loop {
            self.get_next(); // read a token name (skip it)
            self.get_next(); // read separator (comma or semicolon)
            if self.cur.command != Command::Comma {
                break;
            }
        }
        if self.cur.command == Command::Semicolon {
            self.get_x_next();
        }
        Ok(())
    }

    /// Execute `save` statement.
    fn do_save(&mut self) -> InterpResult<()> {
        self.get_x_next();
        loop {
            if let Some(id) = self.cur.sym {
                let entry = self.symbols.get(id);
                self.save_stack.save_symbol(id, entry);
                self.symbols.clear(id);
            }
            self.get_x_next();
            if self.cur.command != Command::Comma {
                break;
            }
            self.get_x_next();
        }
        if self.cur.command == Command::Semicolon {
            self.get_x_next();
        }
        Ok(())
    }

    /// Execute `interim` statement.
    fn do_interim(&mut self) -> InterpResult<()> {
        self.get_x_next();
        if self.cur.command == Command::InternalQuantity {
            let idx = self.cur.modifier;
            self.save_stack.save_internal(idx, self.internals.get(idx));
            self.get_x_next();
            if self.cur.command == Command::Assignment {
                self.get_x_next();
                self.scan_expression()?;
                let val = value_to_scalar(&self.cur_exp)?;
                self.internals.set(idx, val);
            }
        }
        if self.cur.command == Command::Semicolon {
            self.get_x_next();
        }
        Ok(())
    }

    /// Execute `let` statement.
    fn do_let(&mut self) -> InterpResult<()> {
        // LHS: get_symbol (non-expanding), like mp.web's do_let
        self.get_next();
        let lhs = self.cur.sym;
        self.get_x_next();
        // Expect = or :=
        if self.cur.command == Command::Equals || self.cur.command == Command::Assignment {
            // RHS: get_symbol (non-expanding) — must not expand macros
            self.get_next();
        }
        let rhs = self.cur.sym;
        if let (Some(l), Some(r)) = (lhs, rhs) {
            let entry = self.symbols.get(r);
            self.symbols.set(l, entry);
            // Also copy macro info if the RHS is a macro
            if let Some(macro_info) = self.macros.get(&r).cloned() {
                self.macros.insert(l, macro_info);
            }
        }
        self.get_x_next();
        Ok(())
    }

    /// Execute `delimiters` statement.
    ///
    /// Syntax: `delimiters <left> <right>;`
    /// Declares a pair of matching delimiters (like `(` and `)`).
    /// Each pair gets a unique modifier so the parser can match them.
    fn do_delimiters(&mut self) -> InterpResult<()> {
        self.get_x_next();

        // Get left delimiter symbol
        let left_sym = self.cur.sym;
        self.get_x_next();

        // Get right delimiter symbol
        let right_sym = self.cur.sym;
        self.get_x_next();

        // Allocate a unique delimiter id for this pair
        let delim_id = self.next_delimiter_id;
        self.next_delimiter_id += 1;

        // Set the symbols as delimiter commands with matching modifier
        if let Some(l) = left_sym {
            self.symbols.set(
                l,
                crate::symbols::SymbolEntry {
                    command: Command::LeftDelimiter,
                    modifier: delim_id,
                },
            );
        }
        if let Some(r) = right_sym {
            self.symbols.set(
                r,
                crate::symbols::SymbolEntry {
                    command: Command::RightDelimiter,
                    modifier: delim_id,
                },
            );
        }

        if self.cur.command == Command::Semicolon {
            self.get_x_next();
        }
        Ok(())
    }

    /// Execute `newinternal` statement.
    ///
    /// Syntax: `newinternal <name>, <name>, ...;`
    /// Declares new internal numeric quantities.
    fn do_new_internal(&mut self) -> InterpResult<()> {
        self.get_x_next();

        loop {
            if let crate::token::TokenKind::Symbolic(ref name) = self.cur.token.kind {
                let name = name.clone();
                // Register the new internal
                let idx = self.internals.new_internal(&name);

                // Set the symbol to InternalQuantity
                if let Some(sym) = self.cur.sym {
                    self.symbols.set(
                        sym,
                        crate::symbols::SymbolEntry {
                            command: Command::InternalQuantity,
                            modifier: idx,
                        },
                    );
                }
            }
            self.get_x_next();

            if self.cur.command == Command::Comma {
                self.get_x_next();
                continue;
            }
            break;
        }

        if self.cur.command == Command::Semicolon {
            self.get_x_next();
        }
        Ok(())
    }

    /// Execute `show` statement.
    fn do_show(&mut self) -> InterpResult<()> {
        // show_type distinguishes show/showtoken/showdependencies — used later
        let _ = self.cur.modifier;
        self.get_x_next();
        self.scan_expression()?;
        // Print the value
        let val = &self.cur_exp;
        self.report_error(
            ErrorKind::Internal, // Not really an error, but using error channel for output
            format!(">> {val}"),
        );
        self.errors
            .last_mut()
            .map(|e| e.severity = crate::error::Severity::Info);
        if self.cur.command == Command::Semicolon {
            self.get_x_next();
        }
        Ok(())
    }

    /// Execute `message` / `errmessage` statement.
    fn do_message(&mut self) -> InterpResult<()> {
        let is_err = self.cur.modifier == MessageOp::ErrMessage as u16;
        self.get_x_next();
        self.scan_expression()?;
        let msg = match &self.cur_exp {
            Value::String(s) => s.to_string(),
            other => format!("{other}"),
        };
        let severity = if is_err {
            crate::error::Severity::Error
        } else {
            crate::error::Severity::Info
        };
        self.errors.push(
            crate::error::InterpreterError::new(ErrorKind::Internal, msg).with_severity(severity),
        );
        if self.cur.command == Command::Semicolon {
            self.get_x_next();
        }
        Ok(())
    }

    /// Restore scope at `endgroup`.
    pub(super) fn do_endgroup(&mut self) {
        let entries = self.save_stack.restore_to_boundary();
        for entry in entries {
            match entry {
                SaveEntry::Variable { id, value } => {
                    self.variables.set(id, value);
                }
                SaveEntry::Internal { index, value } => {
                    self.internals.set(index, value);
                }
                SaveEntry::Symbol { id, entry } => {
                    self.symbols.set(id, entry);
                }
                SaveEntry::Boundary => {} // shouldn't happen
            }
        }
    }
}
