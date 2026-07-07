//! Scanner/parser edge cases, error recovery, and interpreter internals.

use crate::command::Command;
use crate::interpreter::{ExprResultValue, Interpreter};
use crate::types::{Type, Value};

use super::helpers::TestInterp;
use crate::interpreter::EqualsMode;

// -----------------------------------------------------------------------
// Delimiters
// -----------------------------------------------------------------------

#[test]
fn delimiters_custom() {
    let mut interp = TestInterp::new();
    interp.run("delimiters {{ }}; show {{ 3 + 4 }};");
    let msg = interp.first_show();
    assert!(msg.contains("7"), "expected 7 in: {msg}");
}

#[test]
fn delimiters_pair() {
    let mut interp = TestInterp::new();
    interp.run("delimiters {{ }}; show {{ 2, 5 }};");
    let msg = interp.first_show();
    assert!(msg.contains("(2,5)"), "expected (2,5) in: {msg}");
}

// -----------------------------------------------------------------------
// back_input / back_expr integration
// -----------------------------------------------------------------------

#[test]
fn back_input_rescans_token() {
    let mut interp = Interpreter::new();
    interp.state.input.push_source("+ 3;");
    // Read "+"
    interp.get_next();
    assert_eq!(interp.cur.command, Command::PlusOrMinus);
    // Push it back
    interp.back_input();
    // Read again — should get "+" again
    interp.get_next();
    assert_eq!(interp.cur.command, Command::PlusOrMinus);
}

#[test]
fn back_expr_capsule_roundtrip() {
    let mut interp = Interpreter::new();
    // Push source first (it goes on the bottom of the stack)
    interp.state.input.push_source(";");
    // Set up a capsule with a pair value and push it back
    interp.back_expr_value(ExprResultValue {
        exp: Value::Pair(5.0, 10.0),
        ty: Type::PairType,
        dep: None,
        pair_dep: None,
    });
    // Now get_x_next reads from the capsule token list (top of stack)
    interp.get_x_next();
    assert_eq!(interp.cur.command, Command::CapsuleToken);
    let result = interp.scan_primary().unwrap();
    assert_eq!(result.ty, Type::PairType);
    assert_eq!(result.exp.as_pair(), Some((5.0, 10.0)));
}

#[test]
fn expr_value_capsule_roundtrip_preserves_dependency_state() {
    let mut interp = Interpreter::new();
    interp.state.input.push_source(";");

    let dep_x = crate::equation::const_dep(5.0);
    let dep_y = crate::equation::const_dep(10.0);
    interp.back_expr_value(ExprResultValue {
        exp: Value::Pair(5.0, 10.0),
        ty: Type::PairType,
        dep: None,
        pair_dep: Some((dep_x.clone(), dep_y.clone())),
    });

    interp.get_x_next();
    assert_eq!(interp.cur.command, Command::CapsuleToken);

    let result = interp.scan_primary().unwrap();
    assert_eq!(result.ty, Type::PairType);
    assert_eq!(result.exp.as_pair(), Some((5.0, 10.0)));
    assert!(result.dep.is_none());
    let (actual_x, actual_y) = result
        .pair_dep
        .as_ref()
        .expect("expected pair dependency payload");
    assert_eq!(crate::equation::constant_value(actual_x), Some(5.0));
    assert_eq!(crate::equation::constant_value(actual_y), Some(10.0));
    assert_eq!(crate::equation::constant_value(&dep_x), Some(5.0));
    assert_eq!(crate::equation::constant_value(&dep_y), Some(10.0));
}

#[test]
fn back_expr_numeric_in_expression() {
    // Push a numeric capsule and verify it can participate in arithmetic
    let mut interp = Interpreter::new();
    // Push source first (bottom of stack)
    interp.state.input.push_source("+ 3;");
    // Then push capsule (top of stack)
    interp.back_expr_value(ExprResultValue {
        exp: Value::Numeric(7.0),
        ty: Type::Known,
        dep: None,
        pair_dep: None,
    });
    interp.get_x_next();
    let result = interp.scan_expression(EqualsMode::Relation).unwrap();
    // Should evaluate to 7 + 3 = 10
    assert_eq!(result.exp, Value::Numeric(10.0));
}

#[test]
fn error_recovery_skips_to_semicolon() {
    // Statement with unexpected comma should skip to ; and continue
    let mut interp = TestInterp::new();
    interp.run(",,,; show 1;");
    // Should have errors for the commas but still process "show 1"
    let show_msgs: Vec<_> = interp
        .interp
        .state
        .errors
        .iter()
        .filter(|e| e.message.contains("1"))
        .collect();
    assert!(!show_msgs.is_empty(), "show 1 should have been processed");
}

#[test]
fn reports_missing_right_paren_in_parenthesized_expression() {
    let mut interp = TestInterp::new();
    interp.run("show (1+2; show 7;");

    let errors = interp.errors();
    assert!(
        errors.iter().any(|e| {
            e.kind == crate::error::ErrorKind::MissingToken && e.message.contains("Expected `)`")
        }),
        "expected missing right paren diagnostic, got: {errors:?}"
    );
}

#[test]
fn reports_missing_right_bracket_in_mediation() {
    let mut interp = TestInterp::new();
    interp.run("show 0.5[(0,0),(2,2); show 9;");

    let errors = interp.errors();
    assert!(
        errors.iter().any(|e| {
            e.kind == crate::error::ErrorKind::MissingToken && e.message.contains("Expected `]`")
        }),
        "expected missing right bracket diagnostic, got: {errors:?}"
    );
}

#[test]
fn reports_missing_right_brace_in_path_direction() {
    let mut interp = TestInterp::new();
    interp.run("path p; p := (0,0){curl 1..(1,0); show 1;");

    let errors = interp.errors();
    assert!(
        errors.iter().any(|e| {
            e.kind == crate::error::ErrorKind::MissingToken && e.message.contains("Expected `}`")
        }),
        "expected missing right brace diagnostic, got: {errors:?}"
    );
}

#[test]
fn scanner_unterminated_string_is_reported() {
    let mut interp = TestInterp::new();
    interp.run("show \"unterminated");

    let errors = interp.errors();
    assert!(
        errors
            .iter()
            .any(|e| e.kind == crate::error::ErrorKind::UnterminatedString),
        "expected unterminated-string scanner diagnostic, got: {errors:?}"
    );
}

#[test]
fn scanner_invalid_character_is_reported() {
    let mut interp = TestInterp::new();
    let src = format!("show 1;{}show 2;", '\u{1f}');
    interp.run(&src);

    let errors = interp.errors();
    assert!(
        errors
            .iter()
            .any(|e| e.kind == crate::error::ErrorKind::InvalidCharacter),
        "expected invalid-character scanner diagnostic, got: {errors:?}"
    );
}

// Input source push/pop ordering

#[test]
fn nested_source_levels_lifo_order() {
    // Verify that multiple push_source calls work in LIFO order
    let mut interp = Interpreter::new();
    // Push two source levels manually, then run the top-level source
    interp.state.input.push_source("show 2;");
    interp.state.input.push_source("show 1;");
    interp.get_x_next();
    while interp.cur.command != Command::Stop {
        interp.do_statement().unwrap();
    }
    let infos: Vec<_> = interp
        .state
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Info)
        .map(|e| e.message.clone())
        .collect();
    assert_eq!(infos.len(), 2, "expected 2 shows, got: {infos:?}");
    // LIFO: "show 1" runs first (top of stack), then "show 2"
    assert!(infos[0].contains("1"), "first should be 1: {}", infos[0]);
    assert!(infos[1].contains("2"), "second should be 2: {}", infos[1]);
}

// scan_expression is currently pub; this test works from inside the
// crate and will survive a visibility narrowing to pub(crate).

#[test]
fn scan_expression_internal_usage() {
    let mut interp = Interpreter::new();
    interp.state.input.push_source("3 + 4;");
    interp.get_x_next();
    let result = interp.scan_expression(EqualsMode::Relation).unwrap();
    assert_eq!(result.exp, Value::Numeric(7.0));
}

#[test]
fn mismatched_custom_delimiters_report_error() {
    let mut interp = Interpreter::new();
    let _ = interp.run("delimiters {{ }}; show {{ 3 + 4 );");

    let errors: Vec<_> = interp
        .state
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Error)
        .collect();
    assert!(
        errors
            .iter()
            .any(|e| e.kind == crate::error::ErrorKind::MissingToken),
        "expected missing-token error for mismatched delimiters, got: {errors:?}"
    );
}

#[test]
fn relax_command_is_accepted_as_noop() {
    let mut interp = TestInterp::new();
    interp.run("relax; show 1;");

    interp.assert_no_errors();

    let infos = interp.shows();
    assert!(
        infos.iter().any(|m| m.contains(">> 1")),
        "show output: {infos:?}"
    );
}

#[test]
fn special_statement_is_accepted_as_noop() {
    let mut interp = TestInterp::new();
    interp.run("special \"x\";");

    interp.assert_no_errors();
}

#[test]
fn reported_errors_carry_source_spans() {
    let mut interp = TestInterp::new();
    interp.run("show 1 / 0;");
    let errors = interp.errors();
    assert!(!errors.is_empty(), "expected a division-by-zero error");
    let err = errors[0];
    let span = err.span.expect("error should carry a span");
    assert!(
        span.end > span.start,
        "span should be non-degenerate: {span:?}"
    );
    // The span must point inside the source text.
    assert!(
        span.end <= "show 1 / 0;".len(),
        "span out of range: {span:?}"
    );
}
