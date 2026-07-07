//! Path construction, path operators, and pens made from paths.

use crate::interpreter::Interpreter;

use super::helpers::TestInterp;

#[test]
fn directiontime_east_on_right_path() {
    // Path going right: direction (1,0) should be found at time ~0
    let mut interp = TestInterp::new();
    interp.run("path p; p := (0,0)..(10,0); show directiontime (1,0) of p;");
    let msg = interp.first_show();
    assert!(msg.contains("0"), "expected 0 in: {msg}");
}

#[test]
fn directiontime_not_found() {
    // Path going right: direction (-1,0) should return -1
    let mut interp = TestInterp::new();
    interp.run("path p; p := (0,0)..(10,0); show directiontime (-1,0) of p;");
    let msg = interp.first_show();
    assert!(msg.contains("-1"), "expected -1 in: {msg}");
}

#[test]
fn turningnumber_counterclockwise() {
    // A counterclockwise triangle should have turningnumber = 1
    // Use `..` (primitive path join), not `--` (plain.mp macro)
    let mut interp = TestInterp::new();
    interp.run("path p; p := (0,0)..(10,0)..(5,10)..cycle; show turningnumber p;");
    let msg = interp.first_show();
    assert!(msg.contains("1"), "expected 1 in: {msg}");
}

#[test]
fn turningnumber_pair_returns_zero() {
    let mut interp = TestInterp::new();
    interp.run("show turningnumber (3,4);");
    let msg = interp.first_show();
    assert!(msg.contains("0"), "expected 0 in: {msg}");
}

#[test]
fn turningnumber_open_path_returns_zero() {
    let mut interp = TestInterp::new();
    interp.run("path p; p := (0,0)..(10,0); show turningnumber p;");
    let msg = interp.first_show();
    assert!(msg.contains("0"), "expected 0 in: {msg}");
}

// -----------------------------------------------------------------------
// Curl direction in path construction
// -----------------------------------------------------------------------

#[test]
fn curl_direction_in_def() {
    let mut interp = TestInterp::new();
    // This should define -- as a macro without error
    interp.run(
        "def -- = {curl 1}..{curl 1} enddef; \
             path p; p = (0,0)--(1,0); show p;",
    );
    let msg = interp.first_show();
    assert!(msg.contains("path"), "expected path in: {msg}");
}

#[test]
fn cutbefore_after_path_construction() {
    // `tertiarydef a cutbefore b` from plain.mp must work after
    // inline path construction: `(0,0)--(1cm,0) cutbefore fullcircle`
    // Previously, path construction returned Break from the Pratt loop,
    // so `cutbefore` was never reached.
    let mut interp = TestInterp::with_plain_mp();
    interp.run(concat!(
        "input plain;\n",
        "beginfig(1)\n",
        "  draw (0,0)--(28.34645,0) cutbefore fullcircle scaled 5;\n",
        "endfig;\n",
    ));
    interp.assert_no_errors();
}

#[test]
fn empty_path_cycle_reports_error_without_panic() {
    let mut interp = TestInterp::new();
    interp.run("path p; p := p .. cycle; show 1;");

    let errors = interp.errors();
    assert!(!errors.is_empty(), "expected an error for empty-path cycle");
}

#[test]
fn ampersand_requires_pair_or_path_rhs() {
    let mut interp = Interpreter::new();
    let run_err = interp
        .run("path p; p := (0,0) & 1;")
        .expect_err("expected `&` with non-path/pair RHS to fail");

    assert_eq!(run_err.kind, crate::error::ErrorKind::TypeError);
}

#[test]
fn path_tension_rejects_non_primary_expression() {
    let mut interp = Interpreter::new();
    let run_result = interp.run("path p; p := (0,0) .. tension 1+1 .. (10,0);");

    assert!(
        run_result.is_err(),
        "expected parse failure for tension 1+1"
    );
    if let Err(err) = run_result {
        assert_eq!(err.kind, crate::error::ErrorKind::UnexpectedToken);
    }
}

/// mp.web §302: makepen auto-closes non-cyclic paths.
#[test]
fn makepen_accepts_non_cyclic_path() {
    let mut interp = TestInterp::new();
    interp.run("pen p; p := makepen ((0,0)..(100,0));");

    interp.assert_no_errors();
}

/// mp.web §16987: makepen accepts a pair (pair_to_path).
#[test]
fn makepen_accepts_pair() {
    let mut interp = TestInterp::new();
    interp.run("pen p; p := makepen (5,3);");

    interp.assert_no_errors();
}
