//! Macro definition and expansion: def/vardef/*def, let, scantokens, expandafter

use crate::command::Command;

use super::helpers::TestInterp;

#[test]
fn eval_def_simple() {
    let mut interp = TestInterp::new();
    interp.run("def double(expr x) = 2 * x enddef; show double(5);");
    let msg = interp.first_show();
    assert!(msg.contains("10"), "expected 10 in: {msg}");
}

#[test]
fn eval_def_no_params() {
    let mut interp = TestInterp::new();
    interp.run("def seven = 7 enddef; show seven;");
    let msg = interp.first_show();
    assert!(msg.contains("7"), "expected 7 in: {msg}");
}

#[test]
fn eval_def_two_params() {
    let mut interp = TestInterp::new();
    interp.run("def add(expr a, expr b) = a + b enddef; show add(3, 4);");
    let msg = interp.first_show();
    assert!(msg.contains("7"), "expected 7 in: {msg}");
}

#[test]
fn eval_def_multiple_calls() {
    let mut interp = TestInterp::new();
    interp.run("def sq(expr x) = x * x enddef; show sq(3); show sq(5);");
    assert_eq!(interp.shows().len(), 2);
    assert!(interp.shows()[0].contains("9"), "expected 9");
    assert!(interp.shows()[1].contains("25"), "expected 25");
}

#[test]
fn eval_def_nested_call() {
    let mut interp = TestInterp::new();
    interp.run("def double(expr x) = 2 * x enddef; show double(double(3));");
    let msg = interp.first_show();
    assert!(msg.contains("12"), "expected 12 in: {msg}");
}

#[test]
fn eval_vardef() {
    let mut interp = TestInterp::new();
    interp.run("vardef triple(expr x) = 3 * x enddef; show triple(4);");
    let msg = interp.first_show();
    assert!(msg.contains("12"), "expected 12 in: {msg}");
}

#[test]
fn eval_def_with_body_statements() {
    let mut interp = TestInterp::new();
    interp.run(
        "numeric result; def setresult(expr x) = result := x enddef; setresult(42); show result;",
    );
    let msg = interp.first_show();
    assert!(msg.contains("42"), "expected show 42, got: {msg}");
}

#[test]
fn eval_def_in_for_loop() {
    let mut interp = TestInterp::new();
    interp
        .run("def inc(expr x) = x + 1 enddef; numeric s; s := 0; for i = 1, 2, 3: s := s + inc(i); endfor; show s;");
    // inc(1) + inc(2) + inc(3) = 2 + 3 + 4 = 9
    let msg = interp.first_show();
    assert!(msg.contains("9"), "expected show 9, got: {msg}");
}

#[test]
fn eval_def_with_conditional() {
    let mut interp = TestInterp::new();
    interp
        .run("def myabs(expr x) = if x < 0: -x else: x fi enddef; show myabs(-5); show myabs(3);");
    assert_eq!(interp.shows().len(), 2);
    assert!(interp.shows()[0].contains("5"), "expected 5");
    assert!(interp.shows()[1].contains("3"), "expected 3");
}

#[test]
fn eval_scantokens_basic() {
    let mut interp = TestInterp::new();
    interp.run("show scantokens \"3 + 4\";");
    let msg = interp.first_show();
    assert!(msg.contains("7"), "expected show 7, got: {msg}");
}

#[test]
fn eval_scantokens_define_and_use() {
    let mut interp = TestInterp::new();
    interp.run("scantokens \"def foo = 99 enddef\"; show foo;");
    let msg = interp.first_show();
    assert!(msg.contains("99"), "expected show 99, got: {msg}");
}

#[test]
fn expandafter_text_macro_scantokens() {
    // `expandafter mymac scantokens "abc";` must not consume the following statement.
    // The `;` terminates the text parameter, so `message "B"` still executes.
    let mut interp = TestInterp::new();
    interp.run(concat!(
        "def mymac text t = message \"in mymac\"; enddef;\n",
        "message \"A\";\n",
        "expandafter mymac scantokens \"abc\";\n",
        "message \"B\";\n",
        "message \"C\";\n",
        "end\n",
    ));
    let msgs = interp.shows();
    assert_eq!(
        msgs,
        vec!["A", "in mymac", "B", "C"],
        "expandafter consumed a following statement: {msgs:?}"
    );
}

#[test]
fn expandafter_simple_token() {
    // expandafter with a non-expandable B just reorders the two tokens
    let mut interp = TestInterp::new();
    interp.run("expandafter message \"hello\"; end");
    let msgs = interp.shows();
    assert_eq!(msgs, vec!["hello"]);
}

#[test]
fn expandafter_triple_redefine_macro() {
    // The triple-expandafter pattern from boxes.mp appends to a macro body.
    // The expandafters defer `def clearboxes =` while `clearboxes` expands to its old body.
    // The scanner then sees `def clearboxes = <old body> message "hi"; enddef;`.
    let mut interp = TestInterp::new();
    interp.run(concat!(
        "def clearboxes = enddef;\n",
        "expandafter def expandafter clearboxes expandafter =\n",
        "  clearboxes message \"hi\";\n",
        "enddef;\n",
        "clearboxes;\n",
        "end\n",
    ));
    let msgs = interp.shows();
    assert_eq!(
        msgs,
        vec!["hi"],
        "triple expandafter should have appended 'message \"hi\"' to clearboxes: {msgs:?}"
    );
}

#[test]
fn expandafter_triple_accumulate() {
    let mut interp = TestInterp::new();
    interp.run(concat!(
        "def clearboxes = enddef;\n",
        "expandafter def expandafter clearboxes expandafter =\n",
        "  clearboxes message \"A\";\n",
        "enddef;\n",
        "expandafter def expandafter clearboxes expandafter =\n",
        "  clearboxes message \"B\";\n",
        "enddef;\n",
        "clearboxes;\n",
        "end\n",
    ));
    let msgs = interp.shows();
    assert_eq!(
        msgs,
        vec!["A", "B"],
        "triple expandafter should accumulate: {msgs:?}"
    );
}

#[test]
fn eval_primarydef() {
    let mut interp = TestInterp::new();
    interp
        .run("primarydef a dotprod b = xpart a * xpart b + ypart a * ypart b enddef; show (3,4) dotprod (1,2);");
    let msg = interp.first_show();
    // 3*1 + 4*2 = 11
    assert!(msg.contains("11"), "expected 11 in: {msg}");
}

// -----------------------------------------------------------------------
// Undelimited macro parameters
// -----------------------------------------------------------------------

#[test]
fn eval_def_undelimited_primary() {
    let mut interp = TestInterp::new();
    interp.run("vardef double primary x = 2*x enddef; show double 5;");
    let msg = interp.first_show();
    assert!(msg.contains("10"), "expected 10 in: {msg}");
}

#[test]
fn eval_def_undelimited_secondary() {
    let mut interp = TestInterp::new();
    interp.run("vardef neg secondary x = -x enddef; show neg 3;");
    let msg = interp.first_show();
    assert!(msg.contains("-3"), "expected -3 in: {msg}");
}

#[test]
fn eval_def_undelimited_expr() {
    let mut interp = TestInterp::new();
    interp.run("vardef id expr x = x enddef; show id 5+3;");
    let msg = interp.first_show();
    assert!(msg.contains("8"), "expected 8 in: {msg}");
}

// -----------------------------------------------------------------------
// let: must not expand RHS macro
// -----------------------------------------------------------------------

#[test]
fn let_does_not_expand_rhs() {
    let mut interp = TestInterp::new();
    // Without the fix, `let` expanded foo's body and crashed with "Expected pair, got known numeric"
    interp.run(
        "def foo(expr z, d) = shifted -z rotated d shifted z enddef; \
             let bar = foo; show 1;",
    );
    let msg = interp.first_show();
    assert!(msg.contains("1"), "expected 1 in: {msg}");
}

#[test]
fn let_copies_macro_info() {
    let mut interp = TestInterp::new();
    interp.run(
        "tertiarydef p _on_ d = d enddef; \
             let on = _on_; show 5 on 3;",
    );
    let msg = interp.first_show();
    assert!(msg.contains("3"), "expected 3 in: {msg}");
}

#[test]
fn let_rebinding_to_non_macro_clears_stale_vardef_metadata() {
    let mut interp = TestInterp::new();
    interp.run(
        "vardef f(expr x) = x + 1 enddef; \
             let g = mitered; \
             let f = g; \
             show f 2;",
    );

    let msg = interp
        .interp
        .state
        .errors
        .last()
        .expect("expected at least one diagnostic")
        .message
        .clone();
    assert!(
        !msg.contains("3"),
        "expected `f` to stop expanding as vardef, got: {msg}"
    );
}

// -----------------------------------------------------------------------
// vardef expansion from scan_primary (TagToken path)
// -----------------------------------------------------------------------

#[test]
fn vardef_suffix_in_equation() {
    // laboff.lft where lft is a vardef — should work as variable, not expand
    let mut interp = TestInterp::new();
    interp.run("vardef lft primary x = x enddef; pair laboff.lft; laboff.lft = (1,2); show 1;");
    let msg = interp.first_show();
    assert!(msg.contains("1"), "expected 1 in: {msg}");
}

#[test]
fn vardef_suffix_undeclared_equation() {
    // labxf.lft where labxf is undeclared and lft is a vardef
    let mut interp = TestInterp::new();
    interp.run("vardef lft primary x = x enddef; labxf.lft = 1; show 1;");
    let msg = interp.first_show();
    assert!(msg.contains("1"), "expected 1 in: {msg}");
}

#[test]
fn tertiarydef_with_picture() {
    // Simplified _on_: just shift a picture
    let mut interp = TestInterp::new();
    interp.run(
        r#"
        delimiters ();
        tertiarydef p _on_ d =
          begingroup
          p shifted (0,d)
          endgroup
        enddef;
        show nullpicture _on_ 3;
    "#,
    );
    let errors = interp.errors();
    for e in &errors {
        eprintln!("  tertiarydef error: {}", e.message);
    }
    assert!(errors.is_empty(), "had {} errors", errors.len());
}

#[test]
fn vardef_stays_tag_token() {
    let mut interp = TestInterp::new();
    interp.run("vardef foo primary x = x + 1 enddef;");
    let sym = interp.interp.state.symbols.lookup("foo");
    let entry = interp.interp.state.symbols.get(sym);
    assert_eq!(entry.command, Command::TagToken);
    assert!(interp.interp.state.macros.get(sym).is_some());
}

#[test]
fn vardef_expands_in_expression() {
    let mut interp = TestInterp::new();
    interp.run("vardef foo primary x = x + 1 enddef; show foo 5;");
    let msg = interp.first_show();
    assert!(msg.contains("6"), "expected 6 in: {msg}");
}

#[test]
fn vardef_suffix_not_expanded() {
    let mut interp = TestInterp::new();
    interp.run("pair p.foo; vardef foo primary x = x enddef; p.foo = (1,2);");
}

// -----------------------------------------------------------------------
// vardef with @# suffix parameter
// -----------------------------------------------------------------------

#[test]
fn vardef_at_suffix_parses() {
    let mut interp = TestInterp::new();
    interp.run("vardef foo@#(expr x) = x enddef; show 1;");
    let msg = interp.first_show();
    assert!(msg.contains("1"), "expected 1 in: {msg}");
}

// -----------------------------------------------------------------------
// vardef with expr..of parameter pattern
// -----------------------------------------------------------------------

#[test]
fn vardef_expr_of_pattern() {
    let mut interp = TestInterp::new();
    interp.run("vardef direction expr t of p = t enddef; show 1;");
    let msg = interp.first_show();
    assert!(msg.contains("1"), "expected 1 in: {msg}");
}

// -----------------------------------------------------------------------
// Multiple delimited parameter groups
// -----------------------------------------------------------------------

#[test]
fn multiple_delimited_param_groups() {
    let mut interp = TestInterp::new();
    interp.run("vardef foo(expr u)(expr v) = show u; show v enddef; foo(1)(2);");
    let infos = interp.shows();
    assert_eq!(infos.len(), 2, "expected 2 show outputs, got: {infos:?}");
    assert!(
        infos.iter().any(|m| m.contains('1')),
        "expected u=1 in: {infos:?}"
    );
    assert!(
        infos.iter().any(|m| m.contains('2')),
        "expected v=2 in: {infos:?}"
    );
}

#[test]
fn multiple_delimited_groups_allow_boundary_comma() {
    let mut interp = TestInterp::new();
    interp.run("vardef foo(expr u)(expr v)=show u; show v enddef; foo(4,5);");

    interp.assert_no_errors();

    let infos = interp.shows();
    assert!(
        infos.iter().any(|m| m.contains('4')),
        "expected u=4 in: {infos:?}"
    );
    assert!(
        infos.iter().any(|m| m.contains('5')),
        "expected v=5 in: {infos:?}"
    );
}

// -----------------------------------------------------------------------
// Trailing tokens after undelimited macro params
// -----------------------------------------------------------------------

#[test]
fn trailing_tokens_after_undelimited_expr() {
    // Scanning stops after the undelimited primary.
    // The trailing `;` must survive and terminate the statement.
    let mut interp = TestInterp::new();
    interp.run("def greet primary x = show x enddef; greet 42;");
    interp.assert_no_errors();
    let msg = interp.first_show();
    assert!(msg.contains("42"), "expected show 42, got: {msg}");
}

#[test]
fn vardef_returns_value() {
    let mut interp = TestInterp::new();
    interp.run("vardef triple(expr x) = 3 * x enddef; show triple(7);");
    let msg = interp.first_show();
    assert!(msg.contains("21"), "expected 21 in: {msg}");
}

#[test]
fn vardef_at_suffix_with_params() {
    let mut interp = TestInterp::new();
    interp.run(r#"vardef foo@#(expr s) = show str @#; show s enddef; foo.bar("hello");"#);
    let infos = interp.shows();
    assert_eq!(infos.len(), 2, "expected 2 show outputs, got: {infos:?}");
    assert!(
        infos[0].contains("bar"),
        "expected @# = bar, got: {}",
        infos[0]
    );
    assert!(
        infos[1].contains("hello"),
        "expected s = hello, got: {}",
        infos[1]
    );
}

#[test]
fn abs_of_numeric_via_plain_mp_let() {
    // plain.mp has `let abs = length;`, so abs must work on numerics like length
    let mut interp = TestInterp::new();
    interp.run("let abs = length; show abs(-42);");
    let msg = interp.first_show();
    assert!(msg.contains("42"), "expected 42 in: {msg}");
}

#[test]
fn delimited_suffix_comma_shares_type() {
    // (suffix a, b) — both a and b should be suffix params (mp.web §12882).
    // Previously, b was defaulting to expr.
    let mut interp = TestInterp::new();
    interp.run(concat!(
        "def mytwo(suffix aa, bb) =\n",
        "  message str aa;\n",
        "  message str bb;\n",
        "enddef;\n",
        "mytwo(foo, bar);\n",
    ));
    let msgs = interp.shows();
    assert_eq!(msgs, vec!["foo", "bar"], "both suffix params: {msgs:?}");
}

#[test]
fn delimited_suffix_in_def_endbox_pattern() {
    // The endbox_ pattern from boxes.mp: `def endbox_(suffix cl, $) = cl($); enddef`.
    // Both cl and $ are suffix params.
    // Expanding cl($) must call the macro named by cl with $ as its suffix argument.
    let mut interp = TestInterp::new();
    interp.run(concat!(
        "vardef myfunc(suffix $) = message str $; enddef;\n",
        "def wrapper(suffix cl, $) = cl($); enddef;\n",
        "wrapper(myfunc, hello);\n",
    ));
    let msgs = interp.shows();
    assert_eq!(msgs, vec!["hello"], "suffix passed through: {msgs:?}");
}

// -----------------------------------------------------------------------
// Binary macro lookahead fix (tertiarydef in text params)
// -----------------------------------------------------------------------

#[test]
fn tertiarydef_or_in_text_param() {
    // `or` is a tertiarydef.
    // Using it inside a text parameter must not duplicate the closing delimiter.
    let mut interp = TestInterp::new();
    interp.run(concat!(
        "tertiarydef a or b = if a: a else: b fi enddef;\n",
        "def test(text t) = t enddef;\n",
        "show test(false or true);\n",
    ));
    interp.assert_no_errors();
    let msg = interp.first_show();
    assert!(msg.contains("true"), "expected true in: {msg}");
}

#[test]
fn undelimited_macro_arg_parse_error_does_not_reuse_stale_cur_expr() {
    let mut interp = TestInterp::new();
    interp.run("def f primary p = show p; enddef; show 99; f;");

    let infos = interp.shows();

    let shows_99 = infos.iter().filter(|msg| msg.contains("99")).count();
    assert_eq!(
        shows_99, 1,
        "missing undelimited arg should not reuse stale expression value"
    );
}

// scantokens normal vs push-only parity

#[test]
fn scantokens_preserves_terminator() {
    // scantokens should not eat the `;` after the string expression
    let mut interp = TestInterp::new();
    interp.run(r#"scantokens "show 42"; show 99;"#);
    let infos = interp.shows();
    assert!(
        infos.iter().any(|m| m.contains("42")),
        "scantokens should show 42: {infos:?}"
    );
    assert!(
        infos.iter().any(|m| m.contains("99")),
        "statement after scantokens should run: {infos:?}"
    );
}

#[test]
fn expandafter_scantokens_same_as_direct() {
    let mut interp = TestInterp::new();
    interp.run(r#"expandafter show scantokens "42";"#);
    let infos = interp.shows();
    assert!(
        infos.iter().any(|m| m.contains("42")),
        "expandafter scantokens should show 42: {infos:?}"
    );
}

#[test]
fn undelimited_text_macro_stops_at_endgroup() {
    // Regression: undelimited text args must stop at endgroup as well as ';'
    let mut interp = TestInterp::new();
    interp.run(
        "def t text x = message \"in\" enddef; \
             begingroup t a endgroup; \
             message \"after\";",
    );

    let infos = interp.shows();
    assert!(infos.contains(&"in"), "expected message 'in': {infos:?}");
    assert!(
        infos.contains(&"after"),
        "expected message 'after': {infos:?}"
    );
}

#[test]
fn vardef_at_suffix_only_preserves_trailing_token() {
    // Regression: a vardef with only an @# suffix param must preserve the trailing token
    let mut interp = TestInterp::new();
    interp.run("vardef f@# = 1 enddef; show f.x; message \"after\";");

    let infos = interp.shows();
    assert!(
        infos.iter().any(|m| m.contains(">> 1")),
        "expected show output for f.x: {infos:?}"
    );
    assert!(
        infos.contains(&"after"),
        "expected trailing message after macro call: {infos:?}"
    );
}
