//! Declarations, assignment, subscripts, and save/begingroup scoping

use super::helpers::TestInterp;

#[test]
fn eval_assignment_numeric() {
    let mut interp = TestInterp::new();
    interp.run("numeric x; x := 42; show x;");
    let msg = interp.first_show();
    assert!(msg.contains("42"), "expected 42 in: {msg}");
}

#[test]
fn eval_assignment_string() {
    let mut interp = TestInterp::new();
    interp.run("string s; s := \"hello\"; show s;");
    let msg = interp.first_show();
    assert!(msg.contains("hello"), "expected hello in: {msg}");
}

#[test]
fn eval_assignment_overwrite() {
    let mut interp = TestInterp::new();
    interp.run("numeric x; x := 10; x := 20; show x;");
    let msg = interp.first_show();
    assert!(msg.contains("20"), "expected 20 in: {msg}");
}

#[test]
fn eval_assignment_internal() {
    let mut interp = TestInterp::new();
    interp.run("linecap := 0; show linecap;");
    let msg = interp.first_show();
    assert!(msg.contains("0"), "expected 0 in: {msg}");
}

#[test]
fn eval_assignment_expr() {
    let mut interp = TestInterp::new();
    interp.run("numeric x; x := 3 + 4; show x;");
    let msg = interp.first_show();
    assert!(msg.contains("7"), "expected 7 in: {msg}");
}

#[test]
fn known_unknown_operators() {
    let mut interp = TestInterp::new();
    interp.run(concat!(
        "numeric x;\n",
        "if unknown x: message \"x unknown\"; fi\n",
        "x := 5;\n",
        "if known x: message \"x known\"; fi\n",
        "pair p;\n",
        "if unknown xpart p: message \"xpart p unknown\"; fi\n",
        "p := (1,2);\n",
        "if known xpart p: message \"xpart p known\"; fi\n",
        "end\n",
    ));
    let msgs = interp.shows();
    assert_eq!(
        msgs,
        vec!["x unknown", "x known", "xpart p unknown", "xpart p known"]
    );
}

// -----------------------------------------------------------------------
// Type declarations
// -----------------------------------------------------------------------

#[test]
fn type_declaration_numeric() {
    let mut interp = TestInterp::new();
    interp.run("numeric x; x := 42; show x;");
    let msg = interp.first_show();
    assert!(msg.contains("42"), "expected 42 in: {msg}");
}

#[test]
fn type_declaration_string() {
    let mut interp = TestInterp::new();
    interp.run("string s; s := \"hello\"; show s;");
    let msg = interp.first_show();
    assert!(msg.contains("hello"), "expected hello in: {msg}");
}

#[test]
fn type_declaration_boolean() {
    let mut interp = TestInterp::new();
    interp.run("boolean b; b := true; show b;");
    let msg = interp.first_show();
    assert!(msg.contains("true"), "expected true in: {msg}");
}

#[test]
fn type_declaration_pair() {
    let mut interp = TestInterp::new();
    interp.run("pair p; p := (3, 7); show p;");
    let msg = interp.first_show();
    assert!(msg.contains("(3,7)"), "expected (3,7) in: {msg}");
}

#[test]
fn type_declaration_color() {
    let mut interp = TestInterp::new();
    interp.run("color c; c := (1, 0, 0); show c;");
    let msg = interp.first_show();
    assert!(msg.contains("(1,0,0)"), "expected (1,0,0) in: {msg}");
}

#[test]
fn type_declaration_multiple() {
    let mut interp = TestInterp::new();
    interp.run("numeric a, b; a := 10; b := 20; show a + b;");
    let msg = interp.first_show();
    assert!(msg.contains("30"), "expected 30 in: {msg}");
}

// -----------------------------------------------------------------------
// Newinternal
// -----------------------------------------------------------------------

#[test]
fn newinternal_basic() {
    let mut interp = TestInterp::new();
    interp.run("newinternal myvar; myvar := 7; show myvar;");
    let msg = interp.first_show();
    assert!(msg.contains("7"), "expected 7 in: {msg}");
}

#[test]
fn newinternal_multiple() {
    let mut interp = TestInterp::new();
    interp.run("newinternal a, b; a := 3; b := 5; show a + b;");
    let msg = interp.first_show();
    assert!(msg.contains("8"), "expected 8 in: {msg}");
}

// -----------------------------------------------------------------------
// Type declaration with subscripts and suffixes
// -----------------------------------------------------------------------

#[test]
fn type_declaration_subscript_array() {
    let mut interp = TestInterp::new();
    interp.run("pair z_[];");
}

#[test]
fn type_declaration_compound_suffix() {
    let mut interp = TestInterp::new();
    interp.run("path path_.l, path_.r;");
}

#[test]
fn type_declaration_clears_subscripted_descendants() {
    let mut interp = TestInterp::new();
    interp.run("numeric t[]; t[0] := 10; t[1] := 20; show t[0];");
    assert!(
        interp.shows()[0].contains("10"),
        "first assignment: expected 10 in {:?}",
        interp.shows()[0]
    );
    // Re-declaring clears old subscripted values
    interp.run("numeric t[]; t[0] := 99; show t[0];");
    let msg = interp.shows()[1];
    assert!(
        msg.contains("99"),
        "after re-declaration: expected 99, got: {msg}"
    );
}

#[test]
fn type_declaration_generic_subscript_clears_existing() {
    // Declaring `pair a[].off` must clear any pre-existing `a[N].off`
    // that was auto-created as numeric by prior reference
    let mut interp = TestInterp::new();
    interp.run(concat!(
        "show (pair a1.off);\n", // false: a1.off auto-created as numeric
        "pair a[].off;\n",       // clears a[1].off and redeclares as pair
        "show (pair a1.off);\n", // true now
    ));
    assert!(
        interp.shows()[0].contains("false"),
        "before: expected false, got {:?}",
        interp.shows()[0]
    );
    assert!(
        interp.shows()[1].contains("true"),
        "after: expected true, got {:?}",
        interp.shows()[1]
    );
}

// -----------------------------------------------------------------------
// Subscript variables
// -----------------------------------------------------------------------

#[test]
fn subscript_bracket() {
    let mut interp = TestInterp::new();
    interp.run("numeric a[]; a[1] := 42; show a[1];");
    let msg = interp.first_show();
    assert!(msg.contains("42"), "expected 42 in: {msg}");
}

#[test]
fn save_restores_variable_binding() {
    let mut interp = TestInterp::new();
    interp.run("numeric x; x := 1; begingroup save x; x := 2; endgroup; show x;");

    interp.assert_no_errors();

    let msg = interp.first_show();
    assert!(msg.contains("1"), "expected x to restore to 1, got: {msg}");
}

#[test]
fn save_localizes_suffix_bindings_in_recursive_vardef() {
    let mut interp = TestInterp::new();
    interp.run(
        "vardef test(expr n) = \
               save a; numeric a[]; \
               a[1] := n; \
               if n>0: \
                 test(n-1); \
               else: \
               fi; \
               show a[1]; \
             enddef; \
             test(3);",
    );

    interp.assert_no_errors();

    let infos = interp.shows();

    assert_eq!(
        infos.len(),
        4,
        "expected 4 recursive samples, got: {infos:?}"
    );
    for i in 0..4 {
        assert!(
            infos.iter().any(|m| m.contains(&format!(">> {i}"))),
            "missing sample {i} in {infos:?}"
        );
    }
}

#[test]
fn collective_pair_subscript_is_pair_typed() {
    // Regression: `pair A[]` must make `A[1]` a pair, not a numeric
    let mut interp = TestInterp::new();
    interp.run("pair A[]; show pair A[1]; show numeric A[1];");

    let infos = interp.shows();

    assert_eq!(infos.len(), 2, "expected 2 show outputs, got: {infos:?}");
    assert!(
        infos[0].contains("true"),
        "expected pair test true, got: {}",
        infos[0]
    );
    assert!(
        infos[1].contains("false"),
        "expected numeric test false, got: {}",
        infos[1]
    );
}

#[test]
fn save_root_does_not_affect_similar_prefix() {
    let mut interp = TestInterp::new();
    interp.run(
        "numeric a, ab; a := 1; ab := 2; \
             begingroup save a; a := 99; endgroup; \
             show a; show ab;",
    );
    let infos = interp.shows();
    assert!(
        infos.iter().any(|m| m.contains(">> 1")),
        "a should restore to 1: {infos:?}"
    );
    assert!(
        infos.iter().any(|m| m.contains(">> 2")),
        "ab should remain 2: {infos:?}"
    );
}

#[test]
fn refactor_guard_save_hides_and_restores_vardef_across_group() {
    let mut interp = TestInterp::new();
    interp.run(
        "vardef f = 42 enddef; \
             show f; \
             begingroup save f; numeric f; f := 99; show f; endgroup; \
             show f;",
    );

    interp.assert_no_errors();

    let show_outputs: Vec<_> = interp
        .shows()
        .into_iter()
        .filter(|m| m.contains(">>"))
        .collect();
    assert_eq!(
        show_outputs.len(),
        3,
        "expected 3 show outputs: {show_outputs:?}"
    );
    assert!(
        show_outputs[0].contains(">> 42"),
        "before group f should be 42: {}",
        show_outputs[0]
    );
    assert!(
        show_outputs[1].contains(">> 99"),
        "inside group f should be 99: {}",
        show_outputs[1]
    );
    assert!(
        show_outputs[2].contains(">> 42"),
        "after endgroup, f should be restored to vardef: {}",
        show_outputs[2]
    );
}

#[test]
fn refactor_guard_save_hides_and_restores_macro_across_group() {
    let mut interp = TestInterp::new();
    interp.run(
        "def greet = show 77 enddef; \
             greet; \
             begingroup save greet; greet; endgroup; \
             greet;",
    );

    interp.assert_no_errors();

    let show_outputs: Vec<_> = interp
        .shows()
        .into_iter()
        .filter(|m| m.contains(">>"))
        .collect();
    assert_eq!(
        show_outputs.len(),
        2,
        "expected only outer greet calls to show output; inside-group greet after `save greet` must not show: {show_outputs:?}"
    );
    assert!(
        show_outputs[0].contains("77"),
        "before group greet macro should run: {}",
        show_outputs[0]
    );
    assert!(
        show_outputs[1].contains("77"),
        "after endgroup greet macro should be restored: {}",
        show_outputs[1]
    );
}

#[test]
fn refactor_guard_begingroup_expression_value_survives_endgroup() {
    let mut interp = TestInterp::new();
    interp.run(
        "numeric y; \
             y := begingroup numeric x; x := 4; x + 5 endgroup; \
             show y;",
    );

    interp.assert_no_errors();

    let show_outputs: Vec<_> = interp
        .shows()
        .into_iter()
        .filter(|m| m.contains(">>"))
        .collect();
    assert_eq!(
        show_outputs.len(),
        1,
        "expected exactly one show output, got: {show_outputs:?}"
    );
    assert!(
        show_outputs[0].contains("9"),
        "expected y=9 from group expression, got: {}",
        show_outputs[0]
    );
}

#[test]
fn refactor_guard_nested_group_restore_order() {
    let mut interp = TestInterp::new();
    interp.run(
        "numeric x; x := 1; \
             begingroup \
               save x; \
               x := 2; \
               show x; \
               begingroup \
                 save x; \
                 x := 3; \
                 show x; \
               endgroup; \
               show x; \
             endgroup; \
             show x;",
    );

    interp.assert_no_errors();

    let show_outputs: Vec<_> = interp
        .shows()
        .into_iter()
        .filter(|m| m.contains(">>"))
        .collect();

    assert_eq!(
        show_outputs.len(),
        4,
        "expected 4 show outputs: {show_outputs:?}"
    );
    assert!(
        show_outputs[0].contains(">> 2"),
        "outer x should be 2: {}",
        show_outputs[0]
    );
    assert!(
        show_outputs[1].contains(">> 3"),
        "inner x should be 3: {}",
        show_outputs[1]
    );
    assert!(
        show_outputs[2].contains(">> 2"),
        "outer x should restore to 2: {}",
        show_outputs[2]
    );
    assert!(
        show_outputs[3].contains(">> 1"),
        "global x should restore to 1: {}",
        show_outputs[3]
    );
}

#[test]
fn refactor_guard_root_fast_save_discards_group_descendants() {
    let mut interp = TestInterp::new();
    interp.run(
        "numeric x; x := 1; \
             begingroup \
               save x; \
               x := 2; \
               x.foo := 3; \
             endgroup; \
             show x; \
             show known x.foo;",
    );

    interp.assert_no_errors();

    let show_outputs: Vec<_> = interp
        .shows()
        .into_iter()
        .filter(|m| m.contains(">>"))
        .collect();

    assert_eq!(
        show_outputs.len(),
        2,
        "expected 2 show outputs: {show_outputs:?}"
    );
    assert!(
        show_outputs[0].contains(">> 1"),
        "x should restore to 1 after endgroup: {}",
        show_outputs[0]
    );
    assert!(
        show_outputs[1].contains(">> false"),
        "x.foo should be discarded after endgroup: {}",
        show_outputs[1]
    );
}

#[test]
fn randomseed_statement_sets_seed() {
    let mut interp = TestInterp::new();
    interp.run("randomseed := 123;");
    assert_eq!(interp.interp.state.random_seed, 123);
}

// -----------------------------------------------------------------------
// save hides macro definitions (especially vardefs)
// -----------------------------------------------------------------------

#[test]
fn save_hides_vardef_in_group() {
    // Regression: `save pic` must hide the vardef `pic` so `picture pic; pic=p;`
    // treats `pic` as a plain variable, not the vardef
    let mut interp = TestInterp::new();
    interp.run(
        "vardef pic suffix $ = $ enddef; \
             begingroup \
               save pic; \
               picture pic; \
               pic := nullpicture; \
               show pic; \
             endgroup;",
    );

    interp.assert_no_errors();

    let msg = interp.first_show();
    assert!(
        msg.contains("(picture)"),
        "expected pic to be a picture, got: {msg}"
    );
}

#[test]
fn save_restores_vardef_after_endgroup() {
    let mut interp = TestInterp::new();
    interp.run(
        "vardef f = 42 enddef; \
             show f; \
             begingroup save f; numeric f; f := 99; show f; endgroup; \
             show f;",
    );

    interp.assert_no_errors();

    let infos = interp.shows();
    assert_eq!(infos.len(), 3, "expected 3 show outputs: {infos:?}");
    assert!(
        infos[0].contains("42"),
        "before save, f should be 42: {}",
        infos[0]
    );
    assert!(
        infos[1].contains("99"),
        "inside group, f should be 99: {}",
        infos[1]
    );
    assert!(
        infos[2].contains("42"),
        "after endgroup, f should be vardef again (42): {}",
        infos[2]
    );
}

#[test]
fn save_hides_defined_macro_in_group() {
    // `save` also hides non-vardef macros (def/primarydef/etc).
    // Inside the group, `greet` becomes an unknown tag, so its body does not fire.
    // After endgroup the macro is restored.
    let mut interp = TestInterp::new();
    interp.run(
        "def greet = show 99 enddef; \
             greet; \
             begingroup save greet; endgroup; \
             greet;",
    );

    interp.assert_no_errors();

    let infos = interp.shows();
    assert_eq!(infos.len(), 2, "expected 2 show outputs: {infos:?}");
    assert!(infos[0].contains("99"), "first greet: {}", infos[0]);
    assert!(infos[1].contains("99"), "restored greet: {}", infos[1]);
}
