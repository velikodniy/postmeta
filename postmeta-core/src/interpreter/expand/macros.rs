use std::sync::Arc;

use crate::command::{Command, MacroDefOp, MacroSpecialOp, ParamTypeOp};
use crate::error::{ErrorKind, InterpResult, InterpreterError};
use crate::input::{SharedTokenList, StoredToken, TokenList};
use crate::interpreter::ExprResultValue;
use crate::types::Value;

use super::{Interpreter, MacroInfo, ParamType};
use crate::interpreter::helpers::value_to_stored_tokens;

impl Interpreter {
    /// Handle `def`/`vardef`/`primarydef`/`secondarydef`/`tertiarydef`.
    ///
    /// Syntax:
    ///   `def <name>(param_list) = <body> enddef`
    ///   `vardef <name>(param_list) = <body> enddef`
    ///   `primarydef <lhs> <op> <rhs> = <body> enddef`
    ///   `secondarydef <lhs> <op> <rhs> = <body> enddef`
    ///   `tertiarydef <lhs> <op> <rhs> = <body> enddef`
    pub(in crate::interpreter) fn do_macro_def(&mut self) -> InterpResult<()> {
        let Some(def_op) = MacroDefOp::from_modifier(self.cur.modifier) else {
            self.report_error(ErrorKind::UnexpectedToken, "Invalid macro def modifier");
            return Ok(());
        };
        let is_vardef = def_op == MacroDefOp::VarDef;
        let is_binary_def = matches!(
            def_op,
            MacroDefOp::PrimaryDef | MacroDefOp::SecondaryDef | MacroDefOp::TertiaryDef
        );

        self.get_next(); // skip `def`/`vardef`/etc.

        if is_binary_def {
            // primarydef/secondarydef/tertiarydef: <param> <name> <param> = body enddef
            // e.g., `primarydef a dotprod b = ...`
            self.do_binary_macro_def(def_op)
        } else {
            // def/vardef: <name>(param_list) = body enddef
            self.do_normal_macro_def(is_vardef)
        }
    }

    /// Handle `def <name>(params) = body enddef` or `vardef <name>(params) = body enddef`.
    fn do_normal_macro_def(&mut self, is_vardef: bool) -> InterpResult<()> {
        // Get macro name
        let Some(macro_sym) = self.cur.sym else {
            self.report_error(ErrorKind::MissingToken, "Expected macro name after def");
            self.skip_to_enddef();
            return Ok(());
        };
        let macro_name = self.cur_symbolic_name().unwrap_or("").to_owned();

        self.get_next(); // skip macro name

        // For vardef: check for `@#` suffix parameter marker
        let mut has_at_suffix = false;
        if is_vardef
            && self.cur.command == Command::MacroSpecial
            && MacroSpecialOp::from_modifier(self.cur.modifier) == Some(MacroSpecialOp::MacroSuffix)
        {
            // `@#` suffix parameter — consume it
            has_at_suffix = true;
            self.get_next();
        }

        // Parse parameter list
        let params = self.scan_macro_params()?;

        // Expect `=`
        if self.cur.command == Command::Equals || self.cur.command == Command::Assignment {
            self.get_next();
        } else {
            self.report_error(ErrorKind::MissingToken, "Expected `=` in macro definition");
        }

        // Scan the body until `enddef`, replacing param names with Param(idx)
        let mut param_names: Vec<String> = params.iter().map(|(name, _, _)| name.clone()).collect();
        if has_at_suffix {
            // The `@#` suffix parameter gets the next parameter index
            param_names.push("@#".to_owned());
        }
        let body = self.scan_macro_body(&param_names);

        let mut param_types: Vec<ParamType> = params.iter().map(|(_, ty, _)| *ty).collect();
        let mut param_groups: Vec<u16> = params.iter().map(|(_, _, g)| *g).collect();
        if has_at_suffix {
            param_types.push(ParamType::UndelimitedSuffix);
            param_groups.push(u16::MAX);
        }

        // For vardefs, pre-bake begingroup/endgroup into the body.
        let body: SharedTokenList = if is_vardef {
            let bg = self.state.symbols.lookup("begingroup");
            let eg = self.state.symbols.lookup("endgroup");
            let mut wrapped = Vec::with_capacity(body.len() + 2);
            wrapped.push(StoredToken::Symbol(bg));
            wrapped.extend(body);
            wrapped.push(StoredToken::Symbol(eg));
            wrapped.into()
        } else {
            body.into()
        };

        // Store the macro
        let info = MacroInfo {
            params: param_types,
            param_groups,
            body,
            is_vardef,
            has_at_suffix,
        };
        self.state.macros.insert(macro_sym, info);

        // For regular `def`, set the symbol to `DefinedMacro` so that
        // `get_x_next` expands it (expandable = cmd < min_command = 14).
        // For `vardef`, keep the symbol as `TagToken` — the macro nature is
        // detected by `scan_primary` when it checks `self.state.macros` after
        // suffix collection.  This matches `mp.web`: vardef macros are stored
        // in the variable structure, not in `eq_type`.
        if !is_vardef {
            self.state.symbols.set(
                macro_sym,
                crate::symbols::SymbolEntry {
                    command: Command::DefinedMacro,
                    modifier: 0,
                },
            );
        }

        // Skip past enddef (scan_macro_body consumed it)
        // Get the next token
        self.get_x_next();

        // Consume trailing semicolon
        if self.cur.command == Command::Semicolon {
            self.get_x_next();
        }

        let _ = macro_name;
        Ok(())
    }

    /// Handle `primarydef`/`secondarydef`/`tertiarydef`.
    ///
    /// Syntax: `primarydef <lhs_param> <op_name> <rhs_param> = body enddef`
    #[allow(clippy::unnecessary_wraps)]
    fn do_binary_macro_def(&mut self, def_op: MacroDefOp) -> InterpResult<()> {
        // Parse: <lhs_param> <op_name> <rhs_param>
        let lhs_name = if let Some(s) = self.cur_symbolic_name() {
            s.to_owned()
        } else {
            self.report_error(
                ErrorKind::MissingToken,
                "Expected parameter name in binary macro def",
            );
            self.skip_to_enddef();
            return Ok(());
        };
        self.get_next(); // skip lhs param

        let Some(op_sym) = self.cur.sym else {
            self.report_error(
                ErrorKind::MissingToken,
                "Expected operator name in binary macro def",
            );
            self.skip_to_enddef();
            return Ok(());
        };
        self.get_next(); // skip op name

        let rhs_name = if let Some(s) = self.cur_symbolic_name() {
            s.to_owned()
        } else {
            self.report_error(
                ErrorKind::MissingToken,
                "Expected parameter name in binary macro def",
            );
            self.skip_to_enddef();
            return Ok(());
        };
        self.get_next(); // skip rhs param

        // Expect `=`
        if self.cur.command == Command::Equals || self.cur.command == Command::Assignment {
            self.get_next();
        }

        // Scan body with two parameter names
        let param_names = vec![lhs_name, rhs_name];
        let body = self.scan_macro_body(&param_names);

        let info = MacroInfo {
            params: vec![ParamType::Expr, ParamType::Expr],
            param_groups: vec![u16::MAX, u16::MAX],
            body: body.into(),
            is_vardef: false,
            has_at_suffix: false,
        };
        self.state.macros.insert(op_sym, info);

        // Set the symbol to the appropriate operator command
        let cmd = match def_op {
            MacroDefOp::PrimaryDef => Command::SecondaryPrimaryMacro,
            MacroDefOp::SecondaryDef => Command::TertiarySecondaryMacro,
            MacroDefOp::TertiaryDef => Command::ExpressionTertiaryMacro,
            _ => {
                self.report_error(
                    ErrorKind::UnexpectedToken,
                    "Non-binary macro def used in binary macro handler",
                );
                Command::TertiarySecondaryMacro
            }
        };
        self.state.symbols.set(
            op_sym,
            crate::symbols::SymbolEntry {
                command: cmd,
                modifier: 0,
            },
        );

        self.get_x_next();
        if self.cur.command == Command::Semicolon {
            self.get_x_next();
        }
        Ok(())
    }

    /// Scan macro parameter list: `(expr x, suffix s, text t)`.
    ///
    /// Returns a list of (name, type, group) tuples. Delimited parameters
    /// within the same `(…)` share a group number. Undelimited parameters
    /// get `u16::MAX`. If there are no parentheses, returns an empty list
    /// (parameterless macro).
    #[allow(clippy::unnecessary_wraps)]
    fn scan_macro_params(&mut self) -> InterpResult<Vec<(String, ParamType, u16)>> {
        let mut params: Vec<(String, ParamType, u16)> = Vec::new();
        let mut group_idx: u16 = 0;

        // Parse delimited parameters: (expr a, suffix b, text t)
        // Multiple delimited groups are allowed: (expr a)(text t)
        while self.cur.command == Command::LeftDelimiter {
            self.get_next(); // skip `(`

            // Empty param list: ()
            if self.cur.command == Command::RightDelimiter {
                self.get_next();
            } else {
                // Track the current type within a delimited group.
                // In MetaPost, `(suffix a, b)` means both a and b are suffix.
                // The type keyword applies to all following names until the next
                // type keyword or closing paren (mp.web §12882).
                let mut current_delimited_type = ParamType::Expr;
                loop {
                    // Expect a param type: expr, suffix, or text
                    let param_type = if self.cur.command == Command::ParamType {
                        let pt = Self::delimited_param_type(self.cur.modifier);
                        self.get_next(); // skip type keyword
                        current_delimited_type = pt;
                        pt
                    } else {
                        current_delimited_type
                    };

                    // Get the parameter name.
                    // Can't use map_or_else: cur_symbolic_name borrows self,
                    // but report_error needs &mut self.
                    #[allow(clippy::option_if_let_else)]
                    let name = if let Some(s) = self.cur_symbolic_name() {
                        s.to_owned()
                    } else {
                        self.report_error(ErrorKind::MissingToken, "Expected parameter name");
                        String::new()
                    };
                    self.get_next(); // skip param name

                    params.push((name, param_type, group_idx));

                    if self.cur.command == Command::Comma {
                        self.get_next();
                    } else if self.cur.command == Command::RightDelimiter {
                        self.get_next();
                        break;
                    } else {
                        break;
                    }
                }
            }
            group_idx += 1;
        }

        // Parse undelimited parameters: primary g, expr x, suffix s, text t
        // These appear between the closing `)` (or macro name) and `=`.
        // Special case: `expr t of p` adds both t (expr) and p (suffix).
        while self.cur.command == Command::ParamType {
            let pt = Self::undelimited_param_type(self.cur.modifier);
            self.get_next(); // skip type keyword

            let name = self.cur_symbolic_name().unwrap_or("").to_owned();
            if name.is_empty() {
                self.report_error(ErrorKind::MissingToken, "Expected parameter name");
            }
            self.get_next();

            params.push((name, pt, u16::MAX));

            // Check for `of <name>` pattern (e.g., `expr t of p`)
            if self.cur.command == Command::OfToken {
                self.get_next(); // skip `of`
                let of_name = self.cur_symbolic_name().unwrap_or("").to_owned();
                self.get_next();
                params.push((of_name, ParamType::OfPrimary, u16::MAX));
            }
        }

        Ok(params)
    }

    /// Convert a `ParamTypeOp` modifier to a delimited `ParamType`.
    const fn delimited_param_type(modifier: u16) -> ParamType {
        match ParamTypeOp::from_modifier(modifier) {
            Some(ParamTypeOp::Suffix) => ParamType::Suffix,
            Some(ParamTypeOp::Text) => ParamType::Text,
            // primary/secondary/tertiary inside delimiters are treated as expr
            _ => ParamType::Expr,
        }
    }

    /// Convert a `ParamTypeOp` modifier to an undelimited `ParamType`.
    const fn undelimited_param_type(modifier: u16) -> ParamType {
        match ParamTypeOp::from_modifier(modifier) {
            Some(ParamTypeOp::Primary) => ParamType::Primary,
            Some(ParamTypeOp::Secondary) => ParamType::Secondary,
            Some(ParamTypeOp::Tertiary) => ParamType::Tertiary,
            Some(ParamTypeOp::Suffix) => ParamType::UndelimitedSuffix,
            Some(ParamTypeOp::Text) => ParamType::UndelimitedText,
            _ => ParamType::UndelimitedExpr,
        }
    }

    /// Scan a suffix argument for macro expansion.
    ///
    /// Collects symbolic tokens (and bracket subscripts) until a non-suffix
    /// token is found.
    fn scan_suffix_arg(&mut self) -> TokenList {
        let mut suffix_tokens = TokenList::new();
        loop {
            if self.cur.command == Command::TagToken
                || self.cur.command == Command::InternalQuantity
                || self.cur.command == Command::NumericToken
            {
                self.store_current_token(&mut suffix_tokens);
                self.get_next();
                continue;
            }

            if self.cur.command == Command::LeftBracket {
                // Capture a full bracketed subscript, including nested brackets.
                let mut depth: u32 = 0;
                loop {
                    if self.cur.command == Command::LeftBracket {
                        depth += 1;
                    } else if self.cur.command == Command::RightBracket {
                        depth -= 1;
                    }

                    self.store_current_token(&mut suffix_tokens);
                    self.get_next();

                    if depth == 0 || self.cur.command == Command::Stop {
                        break;
                    }
                }
                continue;
            }

            break;
        }
        suffix_tokens
    }

    /// Scan a delimited text argument for macro expansion.
    ///
    /// Collects tokens until closing delimiter or comma (if not last param).
    fn scan_text_arg(&mut self, param_idx: usize, all_params: &[ParamType]) -> TokenList {
        let mut text_tokens = TokenList::new();
        let mut delim_depth: u32 = 0;
        loop {
            if delim_depth == 0 {
                if self.cur.command == Command::RightDelimiter {
                    break;
                }
                if self.cur.command == Command::Comma && param_idx < all_params.len() - 1 {
                    break;
                }
            }
            if self.cur.command == Command::LeftDelimiter {
                delim_depth += 1;
            } else if self.cur.command == Command::RightDelimiter {
                delim_depth -= 1;
            }
            if self.cur.command == Command::Stop {
                break;
            }
            self.store_current_token(&mut text_tokens);
            self.get_next();
        }
        text_tokens
    }

    /// Scan a macro body until `enddef`, tracking nested `def`/`enddef` pairs.
    ///
    /// Parameter names are replaced with `StoredToken::Param(idx)` references.
    fn scan_macro_body(&mut self, param_names: &[String]) -> TokenList {
        let mut body = TokenList::new();
        let mut depth: u32 = 0;

        loop {
            match self.cur.command {
                Command::MacroDef => {
                    // Nested def — store and increase depth
                    depth += 1;
                    self.store_current_token(&mut body);
                    self.get_next();
                }
                Command::MacroSpecial
                    if MacroSpecialOp::from_modifier(self.cur.modifier)
                        == Some(MacroSpecialOp::EndDef) =>
                {
                    // `enddef` — modifier 0 on MacroSpecial
                    if depth == 0 {
                        // Our enddef — don't store it, stop
                        return body;
                    }
                    depth -= 1;
                    self.store_current_token(&mut body);
                    self.get_next();
                }
                Command::Stop => {
                    self.report_error(ErrorKind::MissingToken, "Missing `enddef`");
                    return body;
                }
                _ => {
                    // Check if this token matches a parameter name.
                    // Parameter substitution applies at ALL nesting depths
                    // (inside nested def..enddef too), matching mp.web behaviour.
                    // The depth counter only tracks def/enddef pairs to find the
                    // outer body boundary.
                    if let Some(name) = self.cur_symbolic_name() {
                        if let Some(idx) = param_names.iter().position(|p| p == name) {
                            body.push(StoredToken::Param(idx));
                            self.get_next();
                            continue;
                        }
                    }
                    self.store_current_token(&mut body);
                    self.get_next();
                }
            }
        }
    }

    /// Expand a binary macro operator (from `primarydef`/`secondarydef`/`tertiarydef`).
    ///
    /// The left operand has already been evaluated and taken. The current
    /// token is the operator name. We need to scan the right operand at the
    /// next lower precedence level, then expand the body.
    pub(in crate::interpreter) fn expand_binary_macro(
        &mut self,
        left: &Value,
    ) -> InterpResult<ExprResultValue> {
        let Some(op_sym) = self.cur.sym else {
            return Err(InterpreterError::new(
                ErrorKind::Internal,
                "Binary macro without symbol",
            ));
        };

        let Some(macro_info) = self.state.macros.get_cloned(op_sym) else {
            return Err(InterpreterError::new(
                ErrorKind::Internal,
                "Undefined binary macro",
            ));
        };

        // Determine which precedence to scan the RHS at
        let cmd = self.cur.command;
        self.get_x_next();
        let rhs_result = match cmd {
            Command::SecondaryPrimaryMacro => self.scan_primary()?,
            Command::TertiarySecondaryMacro => self.scan_secondary()?,
            _ => self.scan_tertiary()?,
        };

        let right = rhs_result.exp;

        // Build param token lists — decompose compound values into tokens
        let args = vec![
            value_to_stored_tokens(left, &mut self.state.symbols),
            value_to_stored_tokens(&right, &mut self.state.symbols),
        ];

        // After scanning the RHS, `self.cur` holds the first token
        // beyond the operand (the look-ahead).  mp.web §15789 uses
        // `back_input` to push this token back BEFORE the body
        // expansion so it is naturally read after the body is consumed.
        //
        // In our architecture, `back_input` uses a single slot with
        // highest priority, so we instead push the look-ahead as a
        // one-token level below the body.
        let mut saved = TokenList::new();
        self.store_current_token(&mut saved);
        if !saved.is_empty() {
            self.state
                .input
                .push_token_list(saved, Vec::new(), "binary-mac-saved");
        }

        // Push the body on top — it will be read before the saved token.
        let args: Vec<SharedTokenList> = args.into_iter().map(Into::into).collect();
        self.state
            .input
            .push_token_list(Arc::clone(&macro_info.body), args, "binary macro");

        // Get next token from expansion and evaluate the body
        self.get_x_next();
        self.scan_expression()
    }

    /// Skip tokens until we reach `enddef` (for error recovery).
    fn skip_to_enddef(&mut self) {
        let mut depth: u32 = 0;
        loop {
            match self.cur.command {
                Command::MacroDef => {
                    depth += 1;
                    self.get_next();
                }
                Command::MacroSpecial
                    if MacroSpecialOp::from_modifier(self.cur.modifier)
                        == Some(MacroSpecialOp::EndDef) =>
                {
                    if depth == 0 {
                        return;
                    }
                    depth -= 1;
                    self.get_next();
                }
                Command::Stop => return,
                _ => self.get_next(),
            }
        }
    }

    /// Expand a user-defined macro.
    ///
    /// Scans arguments according to the macro's parameter types, then pushes
    /// the body as a token list with parameter bindings, and advances to
    /// the first token of the expansion.
    ///
    /// NOTE: `expand_current` uses `expand_defined_macro_push_only` instead
    /// so the central loop controls advancement.
    pub(in crate::interpreter) fn expand_defined_macro(&mut self) {
        self.expand_defined_macro_inner();
        self.get_next();
    }

    /// Core logic for expanding a user-defined macro: scan arguments and push
    /// the body expansion onto the input stack.  Returns `false` on error
    /// (caller decides whether to advance the token stream).
    #[allow(clippy::too_many_lines)]
    pub(super) fn expand_defined_macro_inner(&mut self) -> bool {
        let Some(macro_sym) = self.cur.sym else {
            self.report_error(ErrorKind::Internal, "DefinedMacro without symbol");
            return false;
        };

        let Some(macro_info) = self.state.macros.get_cloned(macro_sym) else {
            self.report_error(ErrorKind::Internal, "Undefined macro expansion");
            return false;
        };

        // Scan arguments — only advance past the macro name if there are params
        let mut args: Vec<TokenList> = Vec::new();

        if !macro_info.params.is_empty() {
            self.get_x_next(); // advance past the macro name, expanding conditionals/etc.

            // For vardefs with `@#`, the suffix tokens sit between the macro
            // name and the argument list `(`.  Collect them now, before the
            // regular param loop, and insert the arg at the `@#` position
            // (the last param) afterwards.
            let at_suffix_arg = if macro_info.has_at_suffix {
                Some(self.scan_suffix_arg())
            } else {
                None
            };

            let mut in_delimiters = false;

            // Number of regular params (excluding the trailing @# if present).
            let regular_param_count = if macro_info.has_at_suffix {
                macro_info.params.len() - 1
            } else {
                macro_info.params.len()
            };

            for i in 0..regular_param_count {
                let param_type = &macro_info.params[i];
                let current_group = macro_info.param_groups.get(i).copied().unwrap_or(u16::MAX);
                let next_group = macro_info
                    .param_groups
                    .get(i + 1)
                    .copied()
                    .unwrap_or(u16::MAX);
                match param_type {
                    // --- Delimited parameters (inside parentheses) ---
                    ParamType::Expr | ParamType::Suffix | ParamType::Text => {
                        if !in_delimiters {
                            if self.cur.command == Command::LeftDelimiter {
                                self.get_x_next(); // skip `(`
                                in_delimiters = true;
                            } else {
                                self.report_error(
                                    ErrorKind::MissingToken,
                                    "Expected `(` for delimited macro argument",
                                );
                            }
                        }
                        match param_type {
                            ParamType::Expr => {
                                if let Ok(result) = self.scan_expression() {
                                    args.push(expr_result_to_capsule(result));
                                } else {
                                    args.push(Vec::new());
                                }
                            }
                            ParamType::Suffix => {
                                args.push(self.scan_suffix_arg());
                            }
                            ParamType::Text => {
                                args.push(self.scan_text_arg(i, &macro_info.params));
                            }
                            _ => {}
                        }
                        // Determine if the next regular param is undelimited.
                        let next_regular_is_undelimited = if i + 1 < regular_param_count {
                            macro_info.params[i + 1].is_undelimited()
                        } else {
                            false
                        };
                        // After scanning the argument, we see either `,` or `)`.
                        //
                        // mp.web §13242: when we see `,` and the NEXT param is
                        // delimited but in a DIFFERENT group, the comma crosses
                        // the group boundary — no `)(`  pair is required.  We
                        // simply consume the comma and stay in_delimiters.
                        if self.cur.command == Command::Comma {
                            self.get_x_next();
                        }
                        // Close delimiters when we see `)` and either the next
                        // param is undelimited, in a different delimited group,
                        // or this is the last regular parameter.
                        if self.cur.command == Command::RightDelimiter
                            && (next_regular_is_undelimited
                                || i + 1 >= regular_param_count
                                || (next_group != current_group && next_group != u16::MAX))
                        {
                            // Only advance past `)` if there are more params to
                            // scan.  When this is the LAST parameter, leave
                            // `self.cur` at `)` so the token that follows the
                            // macro call (typically `;`) is not consumed before
                            // the body expansion is pushed.
                            if i + 1 < regular_param_count {
                                self.get_x_next();
                            }
                            in_delimiters = false;
                        }
                    }

                    // --- Undelimited parameters ---
                    ParamType::Primary => {
                        args.push(self.scan_undelimited_value_arg(Self::scan_primary));
                    }
                    ParamType::Secondary => {
                        args.push(self.scan_undelimited_value_arg(Self::scan_secondary));
                    }
                    ParamType::Tertiary => {
                        args.push(self.scan_undelimited_value_arg(Self::scan_tertiary));
                    }
                    ParamType::UndelimitedExpr => {
                        args.push(self.scan_undelimited_value_arg(Self::scan_expression));
                    }
                    ParamType::UndelimitedSuffix => {
                        args.push(self.scan_suffix_arg());
                    }
                    ParamType::OfPrimary => {
                        // `expr t of p` — consume the `of` delimiter, then
                        // scan the argument as a primary expression (mp.web
                        // §710: both sides of `of` are expr parameters).
                        if self.cur.command == Command::OfToken {
                            self.get_x_next();
                        }
                        args.push(self.scan_undelimited_value_arg(Self::scan_primary));
                    }
                    ParamType::UndelimitedText => {
                        // Collect tokens until semicolon/endgroup
                        let mut text_tokens = TokenList::new();
                        while self.cur.command != Command::Semicolon
                            && self.cur.command != Command::EndGroup
                            && self.cur.command != Command::Stop
                        {
                            self.store_current_token(&mut text_tokens);
                            self.get_next();
                        }
                        args.push(text_tokens);
                    }
                }
            }

            // Append the pre-collected @# suffix arg at the end (its param
            // index in the body matches the last position).
            if let Some(suffix_arg) = at_suffix_arg {
                args.push(suffix_arg);
            }
        }

        // When the last *regular* parameter is undelimited, `self.cur` holds
        // the first token AFTER the arguments (mp.web §389).  We must
        // preserve it by pushing it as a one-token input level BEFORE the
        // body expansion.  For `@#` vardefs the trailing `UndelimitedSuffix`
        // was already collected before the regular params, so check the last
        // regular param instead.
        let last_regular_param = if macro_info.has_at_suffix {
            let regular_count = macro_info.params.len().saturating_sub(1);
            macro_info
                .params
                .get(regular_count.saturating_sub(1))
                .copied()
        } else {
            macro_info.params.last().copied()
        };
        let last_param = last_regular_param.or_else(|| {
            if macro_info.has_at_suffix {
                macro_info.params.last().copied()
            } else {
                None
            }
        });
        let last_param_undelimited = last_param.is_some_and(ParamType::is_undelimited);
        if last_param_undelimited {
            let mut trailing = TokenList::new();
            self.store_current_token(&mut trailing);
            if !trailing.is_empty() {
                self.state
                    .input
                    .push_token_list(trailing, Vec::new(), "trailing token");
            }
        }

        // Push the body expansion on top of the trailing token level.
        // begingroup/endgroup are pre-baked for vardefs; Arc::clone is O(1).
        let args: Vec<SharedTokenList> = args.into_iter().map(Into::into).collect();
        self.state
            .input
            .push_token_list(Arc::clone(&macro_info.body), args, "macro expansion");

        true
    }

    fn scan_undelimited_value_arg(
        &mut self,
        scanner: fn(&mut Self) -> InterpResult<ExprResultValue>,
    ) -> TokenList {
        match scanner(self) {
            Ok(result) => expr_result_to_capsule(result),
            Err(err) => {
                self.state.errors.push(err);
                Vec::new()
            }
        }
    }
}

/// Convert an `ExprResultValue` to a single-element token list containing a
/// capsule that preserves dependency information. This is used for expr
/// arguments to macros so that the equation solver can still track unknown
/// variables passed through macro parameters.
fn expr_result_to_capsule(result: ExprResultValue) -> TokenList {
    vec![StoredToken::Capsule(Arc::new(result))]
}
