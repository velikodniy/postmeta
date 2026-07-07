//! Numeric evaluation, operators, comparisons, and mediation.

use super::helpers::TestInterp;

#[test]
fn eval_numeric_literal() {
    let mut interp = TestInterp::new();
    interp.run("show 42;");
    // Should have a show message
    let msg = interp.first_show();
    assert!(msg.contains("42"), "expected 42 in: {msg}");
}

#[test]
fn eval_arithmetic() {
    let mut interp = TestInterp::new();
    interp.run("show 3 + 4;");
    let msg = interp.first_show();
    assert!(msg.contains("7"), "expected 7 in: {msg}");
}

#[test]
fn eval_multiplication() {
    let mut interp = TestInterp::new();
    interp.run("show 3 * 5;");
    let msg = interp.first_show();
    assert!(msg.contains("15"), "expected 15 in: {msg}");
}

#[test]
fn division_by_variable() {
    // Regression: `360/n` was miscomputed as `360*n` because the
    // fraction check in scan_primary consumed `/` without restoring
    // it when the denominator was a variable (not a numeric literal).
    let mut interp = TestInterp::new();
    interp.run("numeric n; n := 5; show 360/n;");
    let msg = interp.first_show();
    assert!(msg.contains("72"), "expected 72 in: {msg}");
}

#[test]
fn eval_boolean() {
    let mut interp = TestInterp::new();
    interp.run("show true;");
    let msg = interp.first_show();
    assert!(msg.contains("true"), "expected true in: {msg}");
}

#[test]
fn eval_pair() {
    let mut interp = TestInterp::new();
    interp.run("show (3, 4);");
    let msg = interp.first_show();
    assert!(msg.contains("(3,4)"), "expected (3,4) in: {msg}");
}

#[test]
fn eval_unary_minus() {
    let mut interp = TestInterp::new();
    interp.run("show -5;");
    let msg = interp.first_show();
    assert!(msg.contains("-5"), "expected -5 in: {msg}");
}

#[test]
fn eval_sqrt() {
    let mut interp = TestInterp::new();
    interp.run("show sqrt 9;");
    let msg = interp.first_show();
    assert!(msg.contains("3"), "expected 3 in: {msg}");
}

#[test]
fn eval_sind() {
    let mut interp = TestInterp::new();
    interp.run("show sind 90;");
    let msg = interp.first_show();
    assert!(msg.contains("1"), "expected 1 in: {msg}");
}

#[test]
fn eval_comparison() {
    let mut interp = TestInterp::new();
    interp.run("show 3 < 5;");
    let msg = interp.first_show();
    assert!(msg.contains("true"), "expected true in: {msg}");
}

#[test]
fn eval_operator_precedence_layers() {
    let mut interp = TestInterp::new();
    interp.run("show 1 + 2 * 3 = 7; show 1 + 2 * 3 > 6; show (1 + 2) * 3 = 9;");
    assert_eq!(interp.shows().len(), 3);
    assert!(
        interp.shows()[0].contains("true"),
        "expected true in: {}",
        interp.shows()[0]
    );
    assert!(
        interp.shows()[1].contains("true"),
        "expected true in: {}",
        interp.shows()[1]
    );
    assert!(
        interp.shows()[2].contains("true"),
        "expected true in: {}",
        interp.shows()[2]
    );
}

#[test]
fn eval_left_associative_infix_ops() {
    let mut interp = TestInterp::new();
    interp.run("show 10 - 3 - 2; show 20 / 5 / 2;");
    assert_eq!(interp.shows().len(), 2);
    assert!(
        interp.shows()[0].contains("5"),
        "expected 5 in: {}",
        interp.shows()[0]
    );
    assert!(
        interp.shows()[1].contains("2"),
        "expected 2 in: {}",
        interp.shows()[1]
    );
}

#[test]
fn eval_expression_rhs_parses_tighter_precedence() {
    let mut interp = TestInterp::new();
    interp.run("show 1 = 1 + 0; show 1 < 2 + 3 * 4;");
    assert_eq!(interp.shows().len(), 2);
    assert!(
        interp.shows()[0].contains("true"),
        "expected true in: {}",
        interp.shows()[0]
    );
    assert!(
        interp.shows()[1].contains("true"),
        "expected true in: {}",
        interp.shows()[1]
    );
}

#[test]
fn eval_expression_operators_are_left_associative() {
    let mut interp = TestInterp::new();
    interp.run("show 1 < 2 = true; show 3 > 2 = true;");
    assert_eq!(interp.shows().len(), 2);
    assert!(
        interp.shows()[0].contains("true"),
        "expected true in: {}",
        interp.shows()[0]
    );
    assert!(
        interp.shows()[1].contains("true"),
        "expected true in: {}",
        interp.shows()[1]
    );
}

#[test]
fn eval_multiple_statements() {
    let mut interp = TestInterp::new();
    interp.run("show 1; show 2; show 3;");
    assert_eq!(interp.shows().len(), 3);
}

#[test]
fn eval_internal_quantity() {
    let mut interp = TestInterp::new();
    interp.run("show linecap;");
    let msg = interp.first_show();
    assert!(msg.contains("1"), "expected 1 (round) in: {msg}");
}

#[test]
fn eval_xpart_ypart_pair() {
    let mut interp = TestInterp::new();
    interp.run("show xpart (3, 7);");
    let msg = interp.first_show();
    assert!(msg.contains("3"), "expected 3 in: {msg}");

    let mut interp = TestInterp::new();
    interp.run("show ypart (3, 7);");
    let msg = interp.first_show();
    assert!(msg.contains("7"), "expected 7 in: {msg}");
}

#[test]
fn eval_xpart_shifted_pair() {
    // (3, 7) shifted (10, 20) = (13, 27)
    let mut interp = TestInterp::new();
    interp.run("show xpart ((3,7) shifted (10,20));");
    let msg = interp.first_show();
    assert!(msg.contains("13"), "expected 13 in: {msg}");

    let mut interp = TestInterp::new();
    interp.run("show ypart ((3,7) shifted (10,20));");
    let msg = interp.first_show();
    assert!(msg.contains("27"), "expected 27 in: {msg}");
}

// -----------------------------------------------------------------------
// Mediation
// -----------------------------------------------------------------------

#[test]
fn mediation_basic() {
    let mut interp = TestInterp::new();
    // 0.5[10,20] = 15
    interp.run("show 0.5[10, 20];");
    let msg = interp.first_show();
    assert!(msg.contains("15"), "expected 15 in: {msg}");
}

#[test]
fn mediation_endpoints() {
    let mut interp = TestInterp::new();
    // 0[a,b] = a
    interp.run("show 0[3, 7];");
    let msg = interp.first_show();
    assert!(msg.contains("3"), "expected 3 in: {msg}");

    let mut interp = TestInterp::new();
    // 1[a,b] = b
    interp.run("show 1[3, 7];");
    let msg = interp.first_show();
    assert!(msg.contains("7"), "expected 7 in: {msg}");
}

#[test]
fn mediation_fraction() {
    let mut interp = TestInterp::new();
    // 1/4[0,100] = 25
    interp.run("show 1/4[0, 100];");
    let msg = interp.first_show();
    assert!(msg.contains("25"), "expected 25 in: {msg}");
}

#[test]
fn implicit_multiplication() {
    let mut interp = TestInterp::new();
    interp.run("bp := 1; show 3bp;");
    let msg = interp.first_show();
    assert!(msg.contains("3"), "expected 3 in: {msg}");
}

#[test]
fn implicit_multiplication_pair() {
    let mut interp = TestInterp::new();
    interp.run("show 2(3,4);");
    let msg = interp.first_show();
    assert!(msg.contains("(6,8)"), "expected (6,8) in: {msg}");
}

// -----------------------------------------------------------------------
// Type tests (numeric, pen, etc. as unary operators)
// -----------------------------------------------------------------------

#[test]
fn type_test_numeric() {
    let mut interp = TestInterp::new();
    interp.run("show numeric 5;");
    let msg = interp.first_show();
    assert!(msg.contains("true"), "expected true in: {msg}");
}

#[test]
fn type_test_pen() {
    let mut interp = TestInterp::new();
    interp.run("show pen pencircle;");
    let msg = interp.first_show();
    assert!(msg.contains("true"), "expected true in: {msg}");
}

#[test]
fn type_test_numeric_on_pen() {
    let mut interp = TestInterp::new();
    interp.run("show numeric pencircle;");
    let msg = interp.first_show();
    assert!(msg.contains("false"), "expected false in: {msg}");
}

#[test]
fn length_of_numeric_returns_abs() {
    let mut interp = TestInterp::new();
    interp.run("show length -5;");
    let msg = interp.first_show();
    assert!(msg.contains('5'), "expected abs value 5 in: {msg}");

    let mut interp2 = TestInterp::new();
    interp2.run("show length 3.7;");
    let msg2 = interp2.first_show();
    assert!(msg2.contains("3.7"), "expected 3.7 in: {msg2}");
}

// -----------------------------------------------------------------------
// Equals-means-equation flag (= as comparison vs equation)
// -----------------------------------------------------------------------

#[test]
fn equals_as_comparison_in_if() {
    // Inside `if`, `=` should be a comparison, not an equation
    let mut interp = TestInterp::new();
    interp.run("if 3 = 3: message \"yes\"; fi");
    let msgs = interp.shows();
    assert_eq!(msgs, vec!["yes"]);
}

#[test]
fn equals_as_comparison_in_exitif() {
    // `exitif n = 3` — the `=` must be comparison, not equation.
    // `exitif` finishes the current iteration body; loop stops at endfor.
    let mut interp = TestInterp::new();
    interp.run(concat!(
        "numeric n, s; n := 0; s := 0;\n",
        "forever: s := s + 1; n := n + 1; exitif n = 3; endfor;\n",
        "show n;\n",
    ));
    let msg = interp.first_show();
    // Loop runs 3 times (n=1,2,3), exits when n=3
    assert!(msg.contains("3"), "expected 3 in: {msg}");
}

#[test]
fn equals_as_equation_in_statement() {
    // At statement level, `=` should be an equation
    let mut interp = TestInterp::new();
    interp.run("numeric x; x = 42; show x;");
    let msg = interp.first_show();
    assert!(msg.contains("42"), "expected 42 in: {msg}");
}

// ===================================================================
// Regression tests for equality, step loops, scantokens, equations
// ===================================================================

// Lock down the interpreter's comparison tolerance behavior.
// Value::PartialEq uses NUMERIC_TOLERANCE (1e-4).

#[test]
fn equality_comparison_uses_interpreter_tolerance() {
    // 1 = 1.00005 should be true (diff < 1e-4) in MetaPost semantics
    let mut interp = TestInterp::new();
    interp.run("if 1 = 1.00005: show 1; fi;");
    let infos = interp.shows();
    assert!(!infos.is_empty(), "expected equality to hold for diff 5e-5");
}

#[test]
fn equality_comparison_detects_large_diff() {
    // 1 = 1.001 should be false (diff > 1e-4 threshold for equation consistency)
    let mut interp = TestInterp::new();
    interp.run("if 1 = 1.001: show 1; fi;");
    // Should NOT have any info messages if comparison is false
    let infos = interp.shows();
    assert!(
        infos.is_empty(),
        "1 = 1.001 should be false, but show executed"
    );
}
