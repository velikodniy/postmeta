//! Statement execution.
//!
//! Implements `do_statement` (the top-level statement dispatcher) and all
//! individual statement handlers: type declarations, `addto`, `clip`,
//! `setbounds`, `shipout`, `save`, `interim`, `let`, `delimiters`,
//! `newinternal`, `show`, `message`, and `endgroup`.

use std::sync::Arc;

use postmeta_graphics::picture;
use postmeta_graphics::transform;
use postmeta_graphics::transform::Transformable;
use postmeta_graphics::types::{
    Color, DashPattern, FillObject, GraphicsObject, LineCap, LineJoin, Path, Pen, Picture,
    StrokeObject,
};

use crate::command::{
    BoundsOp, Command, MacroSpecialOp, MessageOp, ThingToAddOp, TypeNameOp, WithOptionOp,
};
use crate::error::{ErrorKind, InterpResult};
use crate::internals::InternalId;
use crate::types::{DrawingState, Type, Value};
use crate::variables::{NumericState, SaveEntry, SuffixSegment, VarValue};

use super::helpers::{value_to_path_owned, value_to_scalar};
use super::{Interpreter, LhsBinding};

impl Interpreter {
    fn sync_currentpicture_variable(&mut self) {
        if let Some(var_id) = self.state.variables.lookup_existing("currentpicture") {
            let picture = self.state.picture_state.current_picture.clone();
            self.state
                .variables
                .set_known(var_id, Value::Picture(picture));
        }
    }

    fn eat_semicolon(&mut self) {
        if self.cur.command == Command::Semicolon {
            self.get_x_next();
        }
    }

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
                // Expression or equation — `=` should be treated as an
                // equation delimiter, not as comparison (mp.web: var_flag = assignment).
                self.lhs_tracking.equals_means_equation = true;
                self.scan_expression()?;

                if self.cur.command == Command::Equals {
                    // Equation chain: lhs = mid = ... = rhs.
                    // All left-hand sides are equated to the FINAL rightmost value.
                    type PendingEquationLhs = (
                        Value,
                        Option<LhsBinding>,
                        Option<crate::equation::DepList>,
                        Option<(crate::equation::DepList, crate::equation::DepList)>,
                    );

                    let mut pending_lhs: Vec<PendingEquationLhs> = Vec::new();
                    while self.cur.command == Command::Equals {
                        let lhs_dep = self.cur_expr.dep.clone();
                        let lhs_pair_dep = self.cur_expr.pair_dep.clone();
                        let lhs = self.take_cur_exp();
                        let lhs_binding = self.lhs_tracking.last_lhs_binding.clone();
                        pending_lhs.push((lhs, lhs_binding, lhs_dep, lhs_pair_dep));
                        self.get_x_next();
                        self.lhs_tracking.equals_means_equation = true;
                        self.scan_expression()?;
                    }

                    let rhs_clone = self.cur_expr.exp.clone();
                    let rhs_dep = self.cur_expr.dep.clone();
                    let rhs_pair_dep = self.cur_expr.pair_dep.clone();
                    for (lhs, lhs_binding, lhs_dep, lhs_pair_dep) in &pending_lhs {
                        self.do_equation(
                            lhs,
                            &rhs_clone,
                            lhs_binding.clone(),
                            (lhs_dep.clone(), lhs_pair_dep.clone()),
                            (rhs_dep.clone(), rhs_pair_dep.clone()),
                        )?;
                    }
                } else if self.cur.command == Command::Assignment {
                    // Assignment chain: a := b := ... := rhs
                    // All left-hand sides receive the final rhs value.
                    let mut pending_lhs: Vec<Option<LhsBinding>> = Vec::new();
                    while self.cur.command == Command::Assignment {
                        pending_lhs.push(self.lhs_tracking.last_lhs_binding.clone());
                        self.get_x_next();
                        self.lhs_tracking.equals_means_equation = true;
                        self.scan_expression()?;
                    }

                    let rhs = self.cur_expr.exp.clone();
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
                } else if self.cur.command == Command::MacroSpecial
                    && MacroSpecialOp::from_modifier(self.cur.modifier)
                        == Some(MacroSpecialOp::EndDef)
                {
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
                }
                Ok(())
            }
        }
    }

    /// Execute a type declaration (`numeric x, y;`).
    fn do_type_declaration(&mut self) -> InterpResult<()> {
        let Some(type_op) = TypeNameOp::from_modifier(self.cur.modifier) else {
            self.report_error(
                ErrorKind::UnexpectedToken,
                "Invalid type declaration modifier",
            );
            self.get_x_next();
            return Ok(());
        };
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
                    TypeNameOp::Numeric => VarValue::NumericVar(NumericState::Numeric),
                    TypeNameOp::Boolean => VarValue::Known(Value::Boolean(false)),
                    TypeNameOp::String => VarValue::Known(Value::String(Arc::from(""))),
                    TypeNameOp::Path => VarValue::Known(Value::Path(Path::default())),
                    TypeNameOp::Pen => VarValue::Known(Value::Pen(Pen::circle(0.0))),
                    TypeNameOp::Picture => VarValue::Known(Value::Picture(Picture::default())),
                    TypeNameOp::Pair => self.alloc_pair_value(&name),
                    TypeNameOp::Color => self.alloc_color_value(&name),
                    TypeNameOp::Transform => self.alloc_transform_value(&name),
                    TypeNameOp::Known | TypeNameOp::Unknown => VarValue::Undefined,
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

        self.eat_semicolon();
        Ok(())
    }

    /// Convert a `TypeNameOp` modifier to a `Type`.
    const fn type_op_to_type(type_op: TypeNameOp) -> Type {
        match type_op {
            TypeNameOp::Numeric => Type::Numeric,
            TypeNameOp::Boolean => Type::Boolean,
            TypeNameOp::String => Type::String,
            TypeNameOp::Path => Type::Path,
            TypeNameOp::Pen => Type::Pen,
            TypeNameOp::Picture => Type::Picture,
            TypeNameOp::Pair => Type::PairType,
            TypeNameOp::Color => Type::ColorType,
            TypeNameOp::Transform => Type::TransformType,
            TypeNameOp::Known | TypeNameOp::Unknown => Type::Undefined,
        }
    }

    /// Get a mutable reference to the target picture for `addto`/`clip`/`setbounds`.
    ///
    /// For `currentpicture`, returns `&mut self.picture_state.current_picture` directly.
    /// For named pictures, extracts the picture from the variable into
    /// `self.picture_state.named_pic_buf`, returning a mutable reference to it.
    /// After modification, call [`Self::flush_target_picture`] to write it back.
    fn get_target_picture(&mut self, pic_name: &str) -> &mut Picture {
        if pic_name == "currentpicture" {
            &mut self.picture_state.current_picture
        } else {
            // Extract picture from the named variable (or create empty).
            let pic = if let Some(var_id) = self.variables.lookup_existing(pic_name) {
                if let VarValue::Known(Value::Picture(p)) = self.variables.get(var_id) {
                    p.clone()
                } else {
                    Picture::default()
                }
            } else {
                Picture::default()
            };
            self.picture_state.named_pic_buf = Some(pic);
            // SAFETY: we just assigned `Some` above, so `unwrap` cannot fail.
            // This pattern avoids holding a borrow on `self.variables` across
            // the mutable return.
            #[allow(clippy::unwrap_used)]
            self.picture_state.named_pic_buf.as_mut().unwrap()
        }
    }

    /// Write the temporary named picture buffer back to the variable.
    fn flush_target_picture(&mut self, pic_name: &str) {
        if pic_name == "currentpicture" {
            self.sync_currentpicture_variable();
        } else if let Some(pic) = self.picture_state.named_pic_buf.take() {
            let var_id = self.variables.lookup(pic_name);
            self.variables.set_known(var_id, Value::Picture(pic));
        }
    }

    /// Execute `addto` statement.
    fn do_addto(&mut self) -> InterpResult<()> {
        self.get_x_next();

        // Optional target picture name. If omitted, default to currentpicture.
        let pic_name = if self.cur.command == Command::TagToken {
            let name = self
                .cur_symbolic_name()
                .map_or_else(|| "currentpicture".to_owned(), ToOwned::to_owned);
            self.get_x_next();
            name
        } else {
            "currentpicture".to_owned()
        };

        // Expect contour / doublepath / also
        let thing = ThingToAddOp::from_modifier(self.cur.modifier);
        self.get_x_next();

        // Parse expressions and options first, then apply to the target picture.
        match thing {
            Some(ThingToAddOp::Contour) => {
                self.scan_expression()?;
                let path_val = self.take_cur_exp();
                let path = value_to_path_owned(path_val)?;
                let (ds, pen_specified) = self.scan_with_options()?;

                let target = self.get_target_picture(&pic_name);
                picture::addto_contour(
                    target,
                    FillObject {
                        path,
                        color: ds.color,
                        pen: if pen_specified { Some(ds.pen) } else { None },
                        line_join: ds.line_join,
                        miter_limit: ds.miter_limit,
                    },
                );
            }
            Some(ThingToAddOp::DoublePath) => {
                self.scan_expression()?;
                let path_val = self.take_cur_exp();
                let (ds, _) = self.scan_with_options()?;

                let target = self.get_target_picture(&pic_name);
                match path_val {
                    Value::Pair(x, y) => {
                        // `draw <pair> withpen <pen>` draws a dot-like mark.
                        // Emulate this via the pen outline path shifted to the
                        // pair position, then filled.
                        let dot = postmeta_graphics::pen::makepath(&ds.pen);
                        let shifted = dot.transformed(&transform::shifted(x, y));
                        picture::addto_contour(
                            target,
                            FillObject {
                                path: shifted,
                                color: ds.color,
                                pen: None,
                                line_join: ds.line_join,
                                miter_limit: ds.miter_limit,
                            },
                        );
                    }
                    other => {
                        let path = value_to_path_owned(other)?;
                        picture::addto_doublepath(
                            target,
                            StrokeObject {
                                path,
                                pen: ds.pen,
                                color: ds.color,
                                dash: ds.dash,
                                line_cap: ds.line_cap,
                                line_join: ds.line_join,
                                miter_limit: ds.miter_limit,
                            },
                        );
                    }
                }
            }
            Some(ThingToAddOp::Also) => {
                self.scan_expression()?;
                let pic_val = self.take_cur_exp();
                if let Value::Picture(p) = pic_val {
                    let target = self.get_target_picture(&pic_name);
                    target.merge_from(p);
                }
            }
            _ => {
                self.report_error(
                    ErrorKind::MissingToken,
                    "Expected `contour`, `doublepath`, or `also`",
                );
            }
        }

        self.flush_target_picture(&pic_name);

        self.eat_semicolon();
        Ok(())
    }

    /// Scan `withpen`, `withcolor`, `dashed` options.
    fn scan_with_options(&mut self) -> InterpResult<(DrawingState, bool)> {
        let mut ds = DrawingState {
            pen: Pen::default_pen(),
            color: Color::BLACK,
            dash: None,
            line_cap: LineCap::from_f64(self.internals.get(InternalId::LineCap as u16)),
            line_join: LineJoin::from_f64(self.internals.get(InternalId::LineJoin as u16)),
            miter_limit: self.internals.get(InternalId::MiterLimit as u16),
        };
        let mut pen_specified = false;

        while self.cur.command == Command::WithOption {
            let opt = WithOptionOp::from_modifier(self.cur.modifier);
            self.get_x_next();
            self.scan_expression()?;
            let val = self.take_cur_exp();

            match opt {
                Some(WithOptionOp::WithPen) => {
                    if let Value::Pen(p) = val {
                        ds.pen = p;
                        pen_specified = true;
                    }
                }
                Some(WithOptionOp::WithColor) => {
                    if let Value::Color(c) = val {
                        ds.color = c;
                    } else if let Value::Numeric(v) = val {
                        ds.color = Color::new(v, v, v);
                    }
                }
                Some(WithOptionOp::Dashed) => {
                    if let Value::Picture(ref pic) = val {
                        ds.dash = extract_dash_pattern(pic);
                    }
                }
                _ => {}
            }
        }

        Ok((ds, pen_specified))
    }

    /// Execute `clip`/`setbounds` statement.
    fn do_bounds(&mut self) -> InterpResult<()> {
        let is_clip = BoundsOp::from_modifier(self.cur.modifier) == Some(BoundsOp::Clip);
        self.get_x_next();

        // Optional picture name before `to`. If omitted, target currentpicture.
        let pic_name = if self.cur.command == Command::TagToken {
            let name = self
                .cur_symbolic_name()
                .map_or_else(|| "currentpicture".to_owned(), ToOwned::to_owned);
            self.get_x_next();
            name
        } else {
            "currentpicture".to_owned()
        };

        // Expect "to"
        if self.cur.command == Command::ToToken {
            self.get_x_next();
        } else {
            self.report_error(ErrorKind::MissingToken, "Expected `to` in clip/setbounds");
        }

        self.scan_expression()?;
        let val = self.take_cur_exp();
        let clip_path = value_to_path_owned(val)?;

        let target = self.get_target_picture(&pic_name);
        if is_clip {
            picture::clip(target, clip_path);
        } else {
            picture::setbounds(target, clip_path);
        }

        self.flush_target_picture(&pic_name);

        self.eat_semicolon();
        Ok(())
    }

    /// Execute `shipout` statement.
    fn do_shipout(&mut self) -> InterpResult<()> {
        self.get_x_next();
        self.scan_expression()?;
        let val = self.take_cur_exp();

        let pic = match val {
            Value::Picture(p) => p,
            Value::Vacuous => self.picture_state.current_picture.clone(),
            other => {
                self.report_error(
                    ErrorKind::TypeError,
                    format!("shipout requires a picture, got {}", other.ty()),
                );
                self.eat_semicolon();
                return Ok(());
            }
        };

        self.picture_state.pictures.push(pic);

        self.eat_semicolon();
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
        self.eat_semicolon();
        Ok(())
    }

    /// Execute `save` statement.
    fn do_save(&mut self) -> InterpResult<()> {
        self.get_x_next();
        loop {
            if let Some(id) = self.cur.sym {
                let entry = self.symbols.get(id);
                self.save_stack.save_symbol(id, entry);
                let root = self.symbols.name(id).to_owned();
                let prev = self.variables.take_name_bindings_for_root(&root);
                self.save_stack.save_name_bindings(root, prev);
                self.symbols.clear(id);
            }
            self.get_x_next();
            if self.cur.command != Command::Comma {
                break;
            }
            self.get_x_next();
        }
        self.eat_semicolon();
        Ok(())
    }

    /// Execute `interim` statement.
    fn do_interim(&mut self) -> InterpResult<()> {
        self.get_x_next();
        if self.cur.command == Command::InternalQuantity {
            let idx = self.cur.modifier;
            let prev = self.state.internals.get(idx);
            self.state.save_stack.save_internal(idx, prev);
            self.get_x_next();
            if self.cur.command == Command::Assignment {
                self.get_x_next();
                self.scan_expression()?;
                let val = value_to_scalar(&self.cur_expr.exp)?;
                self.state.internals.set(idx, val);
            }
        }
        self.eat_semicolon();
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

        self.eat_semicolon();
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
                let Some(idx) = self.internals.new_internal(&name) else {
                    self.report_error(
                        ErrorKind::Overflow,
                        format!("Too many internal quantities while adding `{name}`"),
                    );
                    break;
                };

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

        self.eat_semicolon();
        Ok(())
    }

    /// Execute `show` statement.
    fn do_show(&mut self) -> InterpResult<()> {
        // show_type distinguishes show/showtoken/showdependencies — used later
        let _ = self.cur.modifier;
        self.get_x_next();
        self.scan_expression()?;
        // Print the value
        let val = &self.cur_expr.exp;
        self.report_error(
            ErrorKind::Internal, // Not really an error, but using error channel for output
            format!(">> {val}"),
        );
        if let Some(e) = self.errors.last_mut() {
            e.severity = crate::error::Severity::Info;
        }
        self.eat_semicolon();
        Ok(())
    }

    /// Execute `message` / `errmessage` statement.
    fn do_message(&mut self) -> InterpResult<()> {
        let is_err = MessageOp::from_modifier(self.cur.modifier) == Some(MessageOp::ErrMessage);
        self.get_x_next();
        self.scan_expression()?;
        let msg = match &self.cur_expr.exp {
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
        self.eat_semicolon();
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
                SaveEntry::NameBindings { root, prev } => {
                    self.variables.clear_name_bindings_for_root(&root);
                    for (name, id) in prev {
                        self.variables.register_name(&name, id);
                    }
                }
                SaveEntry::Boundary => {} // shouldn't happen
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Dash pattern extraction
// ---------------------------------------------------------------------------

/// Extract a [`DashPattern`] from a dash-pattern picture.
///
/// In `MetaPost`, `dashpattern(on a off b on c off d ...)` produces a
/// picture where each `_on_` segment is encoded as a horizontal stroke.
/// The x-range of each stroke gives the on-segment, and the y-coordinate
/// of every stroke equals the total pattern length (because each `_on_`
/// and `_off_` operation shifts the entire picture upward by its distance).
///
/// Returns `None` if the picture contains no strokes.
fn extract_dash_pattern(pic: &Picture) -> Option<DashPattern> {
    // Collect (xmin, xmax) of each stroke and the y-coordinate (total length).
    let mut on_segments: Vec<(f64, f64)> = Vec::new();
    let mut total_length: f64 = 0.0;

    for obj in &pic.objects {
        if let GraphicsObject::Stroke(stroke) = obj {
            let knots = &stroke.path.knots;
            if knots.is_empty() {
                continue;
            }
            // The x-range of this stroke path gives the on-segment.
            let mut xmin = f64::INFINITY;
            let mut xmax = f64::NEG_INFINITY;
            for k in knots {
                xmin = xmin.min(k.point.x);
                xmax = xmax.max(k.point.x);
            }
            // The y-coordinate is the total pattern length.
            total_length = total_length.max(knots[0].point.y);

            on_segments.push((xmin, xmax));
        }
    }

    if on_segments.is_empty() {
        return None;
    }

    // Sort by starting x position.
    on_segments.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap_or(std::cmp::Ordering::Equal));

    // Build alternating on/off dashes in cyclic order starting from the first
    // on-segment. A leading gap is represented via dash offset.
    let first_start = on_segments[0].0;
    let mut dashes: Vec<f64> = Vec::with_capacity(on_segments.len() * 2);

    for (idx, (xmin, xmax)) in on_segments.iter().enumerate() {
        let on_len = (xmax - xmin).max(0.0);
        dashes.push(on_len);

        let next_start = if let Some((nx, _)) = on_segments.get(idx + 1) {
            *nx
        } else {
            total_length + first_start
        };
        let off_len = (next_start - xmax).max(0.0);
        dashes.push(off_len);
    }

    let offset = if first_start.abs() < 1e-6 {
        0.0
    } else {
        first_start
    };

    Some(DashPattern { dashes, offset })
}
