use super::*;
use crate::filesystem::FileSystem;

struct PlainMpFs;

fn read_plain_mp() -> Option<String> {
    std::fs::read_to_string(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("workspace root")
            .join("lib/plain.mp"),
    )
    .ok()
}

impl FileSystem for PlainMpFs {
    fn read_file(&self, name: &str) -> Option<String> {
        if name == "plain" || name == "plain.mp" {
            read_plain_mp()
        } else {
            None
        }
    }
}

#[test]
fn eval_numeric_literal() {
    let mut interp = Interpreter::new();
    interp.run("show 42;").unwrap();
    // Should have a show message
    assert!(!interp.errors.is_empty());
    let msg = &interp.errors[0].message;
    assert!(msg.contains("42"), "expected 42 in: {msg}");
}

#[test]
fn eval_arithmetic() {
    let mut interp = Interpreter::new();
    interp.run("show 3 + 4;").unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("7"), "expected 7 in: {msg}");
}

#[test]
fn eval_multiplication() {
    let mut interp = Interpreter::new();
    interp.run("show 3 * 5;").unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("15"), "expected 15 in: {msg}");
}

#[test]
fn division_by_variable() {
    // Regression: `360/n` was miscomputed as `360*n` because the
    // fraction check in scan_primary consumed `/` without restoring
    // it when the denominator was a variable (not a numeric literal).
    let mut interp = Interpreter::new();
    interp.run("numeric n; n := 5; show 360/n;").unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("72"), "expected 72 in: {msg}");
}

#[test]
fn eval_string() {
    let mut interp = Interpreter::new();
    interp.run("show \"hello\";").unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("hello"), "expected hello in: {msg}");
}

#[test]
fn eval_boolean() {
    let mut interp = Interpreter::new();
    interp.run("show true;").unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("true"), "expected true in: {msg}");
}

#[test]
fn eval_pair() {
    let mut interp = Interpreter::new();
    interp.run("show (3, 4);").unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("(3,4)"), "expected (3,4) in: {msg}");
}

#[test]
fn eval_unary_minus() {
    let mut interp = Interpreter::new();
    interp.run("show -5;").unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("-5"), "expected -5 in: {msg}");
}

#[test]
fn eval_sqrt() {
    let mut interp = Interpreter::new();
    interp.run("show sqrt 9;").unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("3"), "expected 3 in: {msg}");
}

#[test]
fn eval_sind() {
    let mut interp = Interpreter::new();
    interp.run("show sind 90;").unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("1"), "expected 1 in: {msg}");
}

#[test]
fn eval_comparison() {
    let mut interp = Interpreter::new();
    interp.run("show 3 < 5;").unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("true"), "expected true in: {msg}");
}

#[test]
fn eval_operator_precedence_layers() {
    let mut interp = Interpreter::new();
    interp
        .run("show 1 + 2 * 3 = 7; show 1 + 2 * 3 > 6; show (1 + 2) * 3 = 9;")
        .unwrap();
    assert_eq!(interp.errors.len(), 3);
    assert!(
        interp.errors[0].message.contains("true"),
        "expected true in: {}",
        interp.errors[0].message
    );
    assert!(
        interp.errors[1].message.contains("true"),
        "expected true in: {}",
        interp.errors[1].message
    );
    assert!(
        interp.errors[2].message.contains("true"),
        "expected true in: {}",
        interp.errors[2].message
    );
}

#[test]
fn eval_left_associative_infix_ops() {
    let mut interp = Interpreter::new();
    interp.run("show 10 - 3 - 2; show 20 / 5 / 2;").unwrap();
    assert_eq!(interp.errors.len(), 2);
    assert!(
        interp.errors[0].message.contains("5"),
        "expected 5 in: {}",
        interp.errors[0].message
    );
    assert!(
        interp.errors[1].message.contains("2"),
        "expected 2 in: {}",
        interp.errors[1].message
    );
}

#[test]
fn eval_expression_rhs_parses_tighter_precedence() {
    let mut interp = Interpreter::new();
    interp.run("show 1 = 1 + 0; show 1 < 2 + 3 * 4;").unwrap();
    assert_eq!(interp.errors.len(), 2);
    assert!(
        interp.errors[0].message.contains("true"),
        "expected true in: {}",
        interp.errors[0].message
    );
    assert!(
        interp.errors[1].message.contains("true"),
        "expected true in: {}",
        interp.errors[1].message
    );
}

#[test]
fn eval_expression_operators_are_left_associative() {
    let mut interp = Interpreter::new();
    interp.run("show 1 < 2 = true; show 3 > 2 = true;").unwrap();
    assert_eq!(interp.errors.len(), 2);
    assert!(
        interp.errors[0].message.contains("true"),
        "expected true in: {}",
        interp.errors[0].message
    );
    assert!(
        interp.errors[1].message.contains("true"),
        "expected true in: {}",
        interp.errors[1].message
    );
}

#[test]
fn eval_string_concat() {
    let mut interp = Interpreter::new();
    interp.run("show \"hello\" & \" world\";").unwrap();
    let msg = &interp.errors[0].message;
    assert!(
        msg.contains("hello world"),
        "expected 'hello world' in: {msg}"
    );
}

#[test]
fn chained_string_concat() {
    let mut interp = Interpreter::new();
    interp.run("show \"a\" & \"b\" & \"c\" & \"d\";").unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("abcd"), "expected 'abcd' in: {msg}");
}

#[test]
fn eval_multiple_statements() {
    let mut interp = Interpreter::new();
    interp.run("show 1; show 2; show 3;").unwrap();
    assert_eq!(interp.errors.len(), 3);
}

#[test]
fn eval_internal_quantity() {
    let mut interp = Interpreter::new();
    interp.run("show linecap;").unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("1"), "expected 1 (round) in: {msg}");
}

#[test]
fn eval_pencircle() {
    let mut interp = Interpreter::new();
    interp.run("show pencircle;").unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("pen"), "expected pen in: {msg}");
}

#[test]
fn eval_if_true() {
    let mut interp = Interpreter::new();
    interp.run("show if true: 42 fi;").unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("42"), "expected 42 in: {msg}");
}

#[test]
fn eval_if_false_else() {
    let mut interp = Interpreter::new();
    interp.run("show if false: 1 else: 2 fi;").unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("2"), "expected 2 in: {msg}");
}

#[test]
fn eval_if_false_no_else() {
    let mut interp = Interpreter::new();
    // `if false: show 1; fi; show 2;` — only show 2 should execute
    interp.run("if false: show 1; fi; show 2;").unwrap();
    assert_eq!(
        interp.errors.len(),
        1,
        "expected only 1 show, got {:?}",
        interp.errors
    );
    let msg = &interp.errors[0].message;
    assert!(msg.contains("2"), "expected 2 in: {msg}");
}

#[test]
fn eval_if_elseif() {
    let mut interp = Interpreter::new();
    interp
        .run("if false: show 1; elseif true: show 2; fi;")
        .unwrap();
    assert_eq!(interp.errors.len(), 1);
    let msg = &interp.errors[0].message;
    assert!(msg.contains("2"), "expected 2 in: {msg}");
}

#[test]
fn eval_if_nested() {
    let mut interp = Interpreter::new();
    interp.run("if true: if true: show 42; fi; fi;").unwrap();
    assert_eq!(interp.errors.len(), 1);
    let msg = &interp.errors[0].message;
    assert!(msg.contains("42"), "expected 42 in: {msg}");
}

#[test]
fn eval_for_loop() {
    let mut interp = Interpreter::new();
    interp.run("for i = 1, 2, 3: show i; endfor;").unwrap();
    assert_eq!(
        interp.errors.len(),
        3,
        "expected 3 shows: {:?}",
        interp.errors
    );
    assert!(interp.errors[0].message.contains("1"));
    assert!(interp.errors[1].message.contains("2"));
    assert!(interp.errors[2].message.contains("3"));
}

#[test]
fn eval_for_loop_step() {
    // Accumulate sum inside a for loop
    let mut interp = Interpreter::new();
    interp
        .run("numeric s; s := 0; for i = 1, 2, 3: s := s + i; endfor; show s;")
        .unwrap();
    // s should be 1+2+3 = 6
    let msg = &interp.errors[0].message;
    assert!(msg.contains("6"), "expected 6 in: {msg}");
}

#[test]
fn eval_forever_exitif() {
    let mut interp = Interpreter::new();
    interp
        .run("numeric n; n := 0; forever: n := n + 1; exitif n > 3; endfor; show n;")
        .unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("4"), "expected 4 in: {msg}");
}

#[test]
fn exitif_outside_loop_reports_error() {
    let mut interp = Interpreter::new();
    interp.run("exitif true;").unwrap();

    let errs: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Error)
        .collect();
    assert!(
        errs.iter()
            .any(|e| e.kind == crate::error::ErrorKind::BadExitIf),
        "expected BadExitIf, got: {errs:?}"
    );
}

#[test]
fn exitif_outside_loop_does_not_leak_into_future_forever() {
    let mut interp = Interpreter::new();
    interp
        .run(concat!(
            "numeric n; n := 0;\n",
            "exitif true;\n",
            "forever: n := n + 1; exitif n = 2; endfor;\n",
            "show n;\n",
        ))
        .unwrap();

    let errs: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Error)
        .collect();
    assert!(
        errs.iter()
            .any(|e| e.kind == crate::error::ErrorKind::BadExitIf),
        "expected BadExitIf from top-level exitif, got: {errs:?}"
    );

    let infos: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Info)
        .map(|e| e.message.clone())
        .collect();
    assert!(
        infos.iter().any(|m| m.contains('2')),
        "expected loop to reach n=2, got infos: {infos:?}"
    );
}

#[test]
fn exitif_in_for_step_until_stops_loop() {
    // `exitif` inside a `for step until` loop must stop iteration.
    // Regression: previously, `for` pre-pushed all iterations so `exitif`
    // had no loop frame to set the exit flag on.
    let mut interp = Interpreter::new();
    interp
        .run(concat!(
            "numeric t;\n",
            "for i:=0 step 1 until 10:\n",
            "  t := i;\n",
            "  exitif i > 2;\n",
            "endfor;\n",
            "show t;\n",
        ))
        .unwrap();
    let errors: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Error)
        .collect();
    assert!(
        errors.is_empty(),
        "exitif in for-step-until should not produce errors: {errors:?}"
    );
    let msg = interp
        .errors
        .iter()
        .find(|e| e.severity == crate::error::Severity::Info)
        .map(|e| e.message.as_str())
        .unwrap_or("");
    assert!(msg.contains('3'), "expected t=3 in: {msg}");
}

#[test]
fn nested_forever_loops_keep_outer_replay_state() {
    // Regression: nested `forever` loops used a single pending body slot,
    // so an inner loop could clobber outer replay state.
    let mut interp = Interpreter::new();
    interp
        .run(concat!(
            "numeric nouter; nouter := 0;\n",
            "forever:\n",
            "  nouter := nouter + 1;\n",
            "  forever: exitif true; endfor;\n",
            "  exitif nouter > 2;\n",
            "endfor;\n",
            "show nouter;\n",
        ))
        .unwrap();

    let errors: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Error)
        .collect();
    assert!(errors.is_empty(), "unexpected errors: {errors:?}");
}

#[test]
fn filled_returns_true_for_fill_picture() {
    let mut interp = Interpreter::new();
    interp
        .run("picture p; addto p contour ((0,0)..(1,0)..(1,1)..cycle); show filled p;")
        .unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("true"), "expected true in: {msg}");
}

#[test]
fn stroked_returns_true_for_stroke_picture() {
    let mut interp = Interpreter::new();
    interp
        .run("picture p; addto p doublepath ((0,0)..(10,0)); show stroked p;")
        .unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("true"), "expected true in: {msg}");
}

#[test]
fn clipped_returns_false_for_empty_picture() {
    let mut interp = Interpreter::new();
    interp.run("picture p; show clipped p;").unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("false"), "expected false in: {msg}");
}

#[test]
fn textpart_extracts_text_from_picture() {
    let mut interp = Interpreter::new();
    interp
        .run(r#"picture p; p = "hello" infont "cmr10"; show textpart p;"#)
        .unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("hello"), "expected hello in: {msg}");
}

#[test]
fn fontpart_extracts_font_from_picture() {
    let mut interp = Interpreter::new();
    interp
        .run(r#"picture p; p = "abc" infont "cmr10"; show fontpart p;"#)
        .unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("cmr10"), "expected cmr10 in: {msg}");
}

#[test]
fn textpart_returns_empty_for_non_text_picture() {
    let mut interp = Interpreter::new();
    interp
        .run("picture p; addto p contour ((0,0)..(1,0)..(1,1)..cycle); show textpart p;")
        .unwrap();
    let msg = &interp.errors[0].message;
    // Empty string shows as ""
    assert!(msg.contains("\"\""), "expected empty string in: {msg}");
}

#[test]
fn pathpart_extracts_path_from_fill() {
    let mut interp = Interpreter::new();
    interp
        .run("picture p; addto p contour ((0,0)..(1,0)..(1,1)..cycle); show pathpart p;")
        .unwrap();
    let msg = &interp.errors[0].message;
    // Should show a path, not an error
    assert!(
        !msg.contains("Unimplemented"),
        "pathpart should not error: {msg}"
    );
}

#[test]
fn penpart_returns_pen_for_stroke() {
    let mut interp = Interpreter::new();
    interp
        .run("picture p; addto p doublepath ((0,0)..(10,0)); show penpart p;")
        .unwrap();
    let msg = &interp.errors[0].message;
    assert!(
        !msg.contains("Unimplemented"),
        "penpart should not error: {msg}"
    );
}

#[test]
fn dashpart_returns_picture_for_stroke() {
    let mut interp = Interpreter::new();
    interp
        .run("picture p; addto p doublepath ((0,0)..(10,0)); show dashpart p;")
        .unwrap();
    let msg = &interp.errors[0].message;
    assert!(
        !msg.contains("Unimplemented"),
        "dashpart should not error: {msg}"
    );
}

#[test]
fn charexists_valid_code() {
    let mut interp = Interpreter::new();
    interp.run("show charexists 65;").unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("true"), "expected true in: {msg}");
}

#[test]
fn charexists_out_of_range() {
    let mut interp = Interpreter::new();
    interp.run("show charexists 256;").unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("false"), "expected false in: {msg}");
}

#[test]
fn charexists_negative() {
    let mut interp = Interpreter::new();
    interp.run("show charexists -1;").unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("false"), "expected false in: {msg}");
}

#[test]
fn fontsize_returns_ten() {
    let mut interp = Interpreter::new();
    interp.run(r#"show fontsize "cmr10";"#).unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("10"), "expected 10 in: {msg}");
}

#[test]
fn directiontime_east_on_right_path() {
    // Path going right: direction (1,0) should be found at time ~0
    let mut interp = Interpreter::new();
    interp
        .run("path p; p := (0,0)..(10,0); show directiontime (1,0) of p;")
        .unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("0"), "expected 0 in: {msg}");
}

#[test]
fn directiontime_not_found() {
    // Path going right: direction (-1,0) should return -1
    let mut interp = Interpreter::new();
    interp
        .run("path p; p := (0,0)..(10,0); show directiontime (-1,0) of p;")
        .unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("-1"), "expected -1 in: {msg}");
}

#[test]
fn turningnumber_counterclockwise() {
    // A counterclockwise triangle should have turningnumber = 1
    // Use `..` (primitive path join), not `--` (plain.mp macro)
    let mut interp = Interpreter::new();
    interp
        .run("path p; p := (0,0)..(10,0)..(5,10)..cycle; show turningnumber p;")
        .unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("1"), "expected 1 in: {msg}");
}

#[test]
fn turningnumber_pair_returns_zero() {
    let mut interp = Interpreter::new();
    interp.run("show turningnumber (3,4);").unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("0"), "expected 0 in: {msg}");
}

#[test]
fn turningnumber_open_path_returns_zero() {
    let mut interp = Interpreter::new();
    interp
        .run("path p; p := (0,0)..(10,0); show turningnumber p;")
        .unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("0"), "expected 0 in: {msg}");
}

#[test]
fn nested_forever_exitif_equals_is_comparison() {
    // Regression: `exitif i = 2` inside expansion context must be parsed
    // as a boolean comparison, not statement equation semantics.
    let mut interp = Interpreter::new();
    interp
        .run(concat!(
            "numeric nouter, i;\n",
            "nouter := 0;\n",
            "forever:\n",
            "  nouter := nouter + 1;\n",
            "  i := 0;\n",
            "  forever: i := i + 1; exitif i = 2; endfor;\n",
            "  exitif nouter = 2;\n",
            "endfor;\n",
            "show nouter; show i;\n",
        ))
        .unwrap();

    let errors: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Error)
        .collect();
    assert!(errors.is_empty(), "unexpected errors: {errors:?}");

    let infos: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Info)
        .map(|e| e.message.clone())
        .collect();
    assert!(
        infos.iter().any(|m| m.contains('2')),
        "expected show outputs containing 2, got infos: {infos:?}"
    );
}

#[test]
fn eval_xpart_ypart_pair() {
    let mut interp = Interpreter::new();
    interp.run("show xpart (3, 7);").unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("3"), "expected 3 in: {msg}");

    let mut interp = Interpreter::new();
    interp.run("show ypart (3, 7);").unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("7"), "expected 7 in: {msg}");
}

#[test]
fn eval_assignment_numeric() {
    let mut interp = Interpreter::new();
    interp.run("numeric x; x := 42; show x;").unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("42"), "expected 42 in: {msg}");
}

#[test]
fn eval_assignment_string() {
    let mut interp = Interpreter::new();
    interp.run("string s; s := \"hello\"; show s;").unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("hello"), "expected hello in: {msg}");
}

#[test]
fn eval_assignment_overwrite() {
    let mut interp = Interpreter::new();
    interp.run("numeric x; x := 10; x := 20; show x;").unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("20"), "expected 20 in: {msg}");
}

#[test]
fn eval_assignment_internal() {
    let mut interp = Interpreter::new();
    interp.run("linecap := 0; show linecap;").unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("0"), "expected 0 in: {msg}");
}

#[test]
fn eval_assignment_expr() {
    let mut interp = Interpreter::new();
    interp.run("numeric x; x := 3 + 4; show x;").unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("7"), "expected 7 in: {msg}");
}

#[test]
fn eval_def_simple() {
    let mut interp = Interpreter::new();
    interp
        .run("def double(expr x) = 2 * x enddef; show double(5);")
        .unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("10"), "expected 10 in: {msg}");
}

#[test]
fn eval_def_no_params() {
    let mut interp = Interpreter::new();
    interp.run("def seven = 7 enddef; show seven;").unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("7"), "expected 7 in: {msg}");
}

#[test]
fn eval_def_two_params() {
    let mut interp = Interpreter::new();
    interp
        .run("def add(expr a, expr b) = a + b enddef; show add(3, 4);")
        .unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("7"), "expected 7 in: {msg}");
}

#[test]
fn eval_def_multiple_calls() {
    let mut interp = Interpreter::new();
    interp
        .run("def sq(expr x) = x * x enddef; show sq(3); show sq(5);")
        .unwrap();
    assert_eq!(interp.errors.len(), 2);
    assert!(interp.errors[0].message.contains("9"), "expected 9");
    assert!(interp.errors[1].message.contains("25"), "expected 25");
}

#[test]
fn eval_def_nested_call() {
    let mut interp = Interpreter::new();
    interp
        .run("def double(expr x) = 2 * x enddef; show double(double(3));")
        .unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("12"), "expected 12 in: {msg}");
}

#[test]
fn eval_vardef() {
    let mut interp = Interpreter::new();
    interp
        .run("vardef triple(expr x) = 3 * x enddef; show triple(4);")
        .unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("12"), "expected 12 in: {msg}");
}

#[test]
fn eval_def_with_body_statements() {
    // A macro that assigns to a variable
    let mut interp = Interpreter::new();
    interp
        .run("numeric result; def setresult(expr x) = result := x enddef; setresult(42); show result;")
        .unwrap();
    // Find the show message (skip any info/error messages before it)
    let show_msg = interp
        .errors
        .iter()
        .find(|e| e.message.contains(">>"))
        .map(|e| &e.message);
    assert!(
        show_msg.is_some() && show_msg.unwrap().contains("42"),
        "expected show 42, got errors: {:?}",
        interp.errors.iter().map(|e| &e.message).collect::<Vec<_>>()
    );
}

#[test]
fn eval_def_in_for_loop() {
    let mut interp = Interpreter::new();
    interp
        .run("def inc(expr x) = x + 1 enddef; numeric s; s := 0; for i = 1, 2, 3: s := s + inc(i); endfor; show s;")
        .unwrap();
    // inc(1) + inc(2) + inc(3) = 2 + 3 + 4 = 9
    let show_msg = interp
        .errors
        .iter()
        .find(|e| e.message.contains(">>"))
        .map(|e| &e.message);
    assert!(
        show_msg.is_some() && show_msg.unwrap().contains("9"),
        "expected show 9, got errors: {:?}",
        interp.errors.iter().map(|e| &e.message).collect::<Vec<_>>()
    );
}

#[test]
fn eval_def_with_conditional() {
    let mut interp = Interpreter::new();
    interp
        .run("def myabs(expr x) = if x < 0: -x else: x fi enddef; show myabs(-5); show myabs(3);")
        .unwrap();
    assert_eq!(interp.errors.len(), 2);
    assert!(interp.errors[0].message.contains("5"), "expected 5");
    assert!(interp.errors[1].message.contains("3"), "expected 3");
}

#[test]
fn eval_scantokens_basic() {
    let mut interp = Interpreter::new();
    interp.run("show scantokens \"3 + 4\";").unwrap();
    let show_msg = interp
        .errors
        .iter()
        .find(|e| e.message.contains(">>"))
        .map(|e| &e.message);
    assert!(
        show_msg.is_some() && show_msg.unwrap().contains("7"),
        "expected show 7, got: {:?}",
        interp.errors.iter().map(|e| &e.message).collect::<Vec<_>>()
    );
}

#[test]
fn eval_scantokens_define_and_use() {
    let mut interp = Interpreter::new();
    interp
        .run("scantokens \"def foo = 99 enddef\"; show foo;")
        .unwrap();
    let show_msg = interp
        .errors
        .iter()
        .find(|e| e.message.contains(">>"))
        .map(|e| &e.message);
    assert!(
        show_msg.is_some() && show_msg.unwrap().contains("99"),
        "expected show 99, got: {:?}",
        interp.errors.iter().map(|e| &e.message).collect::<Vec<_>>()
    );
}

#[test]
fn expandafter_text_macro_scantokens() {
    // expandafter mymac scantokens "abc"; should NOT consume the
    // statement after it.  The `;` terminates the text parameter,
    // and `message "B"` must still execute.
    let mut interp = Interpreter::new();
    interp
        .run(concat!(
            "def mymac text t = message \"in mymac\"; enddef;\n",
            "message \"A\";\n",
            "expandafter mymac scantokens \"abc\";\n",
            "message \"B\";\n",
            "message \"C\";\n",
            "end\n",
        ))
        .unwrap();
    let msgs: Vec<&str> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Info)
        .map(|e| e.message.as_str())
        .collect();
    assert_eq!(
        msgs,
        vec!["A", "in mymac", "B", "C"],
        "expandafter consumed a following statement: {msgs:?}"
    );
}

#[test]
fn expandafter_simple_token() {
    // expandafter with a non-expandable B should just reorder.
    let mut interp = Interpreter::new();
    interp.run("expandafter message \"hello\"; end").unwrap();
    let msgs: Vec<&str> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Info)
        .map(|e| e.message.as_str())
        .collect();
    assert_eq!(msgs, vec!["hello"]);
}

#[test]
fn expandafter_triple_redefine_macro() {
    // The triple-expandafter pattern from boxes.mp:
    //   expandafter def expandafter clearboxes expandafter =
    //     clearboxes message "hi";
    //   enddef;
    // This should APPEND `message "hi"` to clearboxes' body.
    // Step by step:
    //   1. expandafter reads A=`def`, reads B=`expandafter`, B is expandable
    //   2. Inner expandafter reads A=`clearboxes`, reads B=`expandafter`, B is expandable
    //   3. Innermost expandafter reads A=`=`, reads B=`clearboxes` (a defined macro)
    //   4. One-step expand of clearboxes pushes its body (empty at first)
    //   5. `=` is placed in front → scanner sees `= <old body>`
    //   6. Back in step 2: `clearboxes` is placed in front → `clearboxes = <old body>`
    //   7. Back in step 1: `def` is placed in front → `def clearboxes = <old body> message "hi"; enddef;`
    let mut interp = Interpreter::new();
    interp
        .run(concat!(
            "def clearboxes = enddef;\n",
            "expandafter def expandafter clearboxes expandafter =\n",
            "  clearboxes message \"hi\";\n",
            "enddef;\n",
            "clearboxes;\n",
            "end\n",
        ))
        .unwrap();
    let msgs: Vec<&str> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Info)
        .map(|e| e.message.as_str())
        .collect();
    assert_eq!(
        msgs,
        vec!["hi"],
        "triple expandafter should have appended 'message \"hi\"' to clearboxes: {msgs:?}"
    );
}

#[test]
fn expandafter_triple_accumulate() {
    // Multiple rounds of triple-expandafter accumulation.
    let mut interp = Interpreter::new();
    interp
        .run(concat!(
            "def clearboxes = enddef;\n",
            "expandafter def expandafter clearboxes expandafter =\n",
            "  clearboxes message \"A\";\n",
            "enddef;\n",
            "expandafter def expandafter clearboxes expandafter =\n",
            "  clearboxes message \"B\";\n",
            "enddef;\n",
            "clearboxes;\n",
            "end\n",
        ))
        .unwrap();
    let msgs: Vec<&str> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Info)
        .map(|e| e.message.as_str())
        .collect();
    assert_eq!(
        msgs,
        vec!["A", "B"],
        "triple expandafter should accumulate: {msgs:?}"
    );
}

#[test]
fn known_unknown_operators() {
    let mut interp = Interpreter::new();
    interp
        .run(concat!(
            "numeric x;\n",
            "if unknown x: message \"x unknown\"; fi\n",
            "x := 5;\n",
            "if known x: message \"x known\"; fi\n",
            "pair p;\n",
            "if unknown xpart p: message \"xpart p unknown\"; fi\n",
            "p := (1,2);\n",
            "if known xpart p: message \"xpart p known\"; fi\n",
            "end\n",
        ))
        .unwrap();
    let msgs: Vec<&str> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Info)
        .map(|e| e.message.as_str())
        .collect();
    assert_eq!(
        msgs,
        vec!["x unknown", "x known", "xpart p unknown", "xpart p known"]
    );
}

#[test]
fn eval_input_file_not_found() {
    let mut interp = Interpreter::new();
    // Should report error but not crash
    interp.run("input nonexistent;").unwrap();
    assert!(
        interp
            .errors
            .iter()
            .any(|e| e.message.contains("not found")),
        "expected file-not-found error: {:?}",
        interp.errors.iter().map(|e| &e.message).collect::<Vec<_>>()
    );
}

#[test]
fn eval_input_with_filesystem() {
    use crate::filesystem::FileSystem;

    struct TestFs;
    impl FileSystem for TestFs {
        fn read_file(&self, name: &str) -> Option<String> {
            if name == "testlib" || name == "testlib.mp" {
                Some("def tripleplus(expr x) = 3 * x + 1 enddef;".to_owned())
            } else {
                None
            }
        }
    }

    let mut interp = Interpreter::new();
    interp.set_filesystem(Box::new(TestFs));
    interp.run("input testlib; show tripleplus(10);").unwrap();
    let show_msg = interp
        .errors
        .iter()
        .find(|e| e.message.contains(">>"))
        .map(|e| &e.message);
    assert!(
        show_msg.is_some() && show_msg.unwrap().contains("31"),
        "expected show 31, got: {:?}",
        interp.errors.iter().map(|e| &e.message).collect::<Vec<_>>()
    );
}

#[test]
fn eval_primarydef() {
    let mut interp = Interpreter::new();
    interp
        .run("primarydef a dotprod b = xpart a * xpart b + ypart a * ypart b enddef; show (3,4) dotprod (1,2);")
        .unwrap();
    let msg = &interp.errors[0].message;
    // 3*1 + 4*2 = 11
    assert!(msg.contains("11"), "expected 11 in: {msg}");
}

#[test]
fn eval_xpart_shifted_pair() {
    // (3, 7) shifted (10, 20) = (13, 27)
    let mut interp = Interpreter::new();
    interp.run("show xpart ((3,7) shifted (10,20));").unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("13"), "expected 13 in: {msg}");

    let mut interp = Interpreter::new();
    interp.run("show ypart ((3,7) shifted (10,20));").unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("27"), "expected 27 in: {msg}");
}

// -----------------------------------------------------------------------
// Type declarations
// -----------------------------------------------------------------------

#[test]
fn type_declaration_numeric() {
    let mut interp = Interpreter::new();
    interp.run("numeric x; x := 42; show x;").unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("42"), "expected 42 in: {msg}");
}

#[test]
fn type_declaration_string() {
    let mut interp = Interpreter::new();
    interp.run("string s; s := \"hello\"; show s;").unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("hello"), "expected hello in: {msg}");
}

#[test]
fn type_declaration_boolean() {
    let mut interp = Interpreter::new();
    interp.run("boolean b; b := true; show b;").unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("true"), "expected true in: {msg}");
}

#[test]
fn type_declaration_pair() {
    let mut interp = Interpreter::new();
    interp.run("pair p; p := (3, 7); show p;").unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("(3,7)"), "expected (3,7) in: {msg}");
}

#[test]
fn type_declaration_color() {
    let mut interp = Interpreter::new();
    interp.run("color c; c := (1, 0, 0); show c;").unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("(1,0,0)"), "expected (1,0,0) in: {msg}");
}

#[test]
fn type_declaration_multiple() {
    let mut interp = Interpreter::new();
    interp
        .run("numeric a, b; a := 10; b := 20; show a + b;")
        .unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("30"), "expected 30 in: {msg}");
}

// -----------------------------------------------------------------------
// Delimiters
// -----------------------------------------------------------------------

#[test]
fn delimiters_custom() {
    let mut interp = Interpreter::new();
    interp.run("delimiters {{ }}; show {{ 3 + 4 }};").unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("7"), "expected 7 in: {msg}");
}

#[test]
fn delimiters_pair() {
    let mut interp = Interpreter::new();
    interp.run("delimiters {{ }}; show {{ 2, 5 }};").unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("(2,5)"), "expected (2,5) in: {msg}");
}

// -----------------------------------------------------------------------
// Newinternal
// -----------------------------------------------------------------------

#[test]
fn newinternal_basic() {
    let mut interp = Interpreter::new();
    interp
        .run("newinternal myvar; myvar := 7; show myvar;")
        .unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("7"), "expected 7 in: {msg}");
}

#[test]
fn newinternal_multiple() {
    let mut interp = Interpreter::new();
    interp
        .run("newinternal a, b; a := 3; b := 5; show a + b;")
        .unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("8"), "expected 8 in: {msg}");
}

// -----------------------------------------------------------------------
// Mediation
// -----------------------------------------------------------------------

#[test]
fn mediation_basic() {
    let mut interp = Interpreter::new();
    // 0.5[10,20] = 15
    interp.run("show 0.5[10, 20];").unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("15"), "expected 15 in: {msg}");
}

#[test]
fn mediation_endpoints() {
    let mut interp = Interpreter::new();
    // 0[a,b] = a
    interp.run("show 0[3, 7];").unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("3"), "expected 3 in: {msg}");

    let mut interp = Interpreter::new();
    // 1[a,b] = b
    interp.run("show 1[3, 7];").unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("7"), "expected 7 in: {msg}");
}

#[test]
fn mediation_fraction() {
    let mut interp = Interpreter::new();
    // 1/4[0,100] = 25
    interp.run("show 1/4[0, 100];").unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("25"), "expected 25 in: {msg}");
}

#[test]
fn mediation_preserves_numeric_endpoint_dependencies() {
    let mut interp = Interpreter::new();
    interp
        .run("numeric a,b,c,x; a := 0.25; x = a[b,c]; b = 2; c = 10; show x;")
        .unwrap();

    let infos: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Info)
        .map(|e| e.message.clone())
        .collect();
    assert!(
        infos.iter().any(|m| m.contains('4')),
        "expected x=4 in: {infos:?}"
    );
}

#[test]
fn mediation_preserves_pair_endpoint_dependencies() {
    let mut interp = Interpreter::new();
    interp
        .run("numeric a; pair b,c,p; a := 0.5; p = a[b,c]; b = (2,4); c = (6,8); show p;")
        .unwrap();

    let infos: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Info)
        .map(|e| e.message.clone())
        .collect();
    assert!(
        infos.iter().any(|m| m.contains("(4,6)")),
        "expected p=(4,6) in: {infos:?}"
    );
}

// -----------------------------------------------------------------------
// For step/until
// -----------------------------------------------------------------------

#[test]
fn for_step_until() {
    let mut interp = Interpreter::new();
    // Sum 1 through 5
    interp
        .run("numeric s; s := 0; for k=1 step 1 until 5: s := s + k; endfor; show s;")
        .unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("15"), "expected 15 in: {msg}");
}

#[test]
fn for_step_until_by_two() {
    let mut interp = Interpreter::new();
    // Sum 0, 2, 4, 6, 8, 10 = 30
    interp
        .run("numeric s; s := 0; for k=0 step 2 until 10: s := s + k; endfor; show s;")
        .unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("30"), "expected 30 in: {msg}");
}

#[test]
fn for_step_until_negative() {
    let mut interp = Interpreter::new();
    // Count down: 5, 4, 3, 2, 1 = 15
    interp
        .run("numeric s; s := 0; for k=5 step -1 until 1: s := s + k; endfor; show s;")
        .unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("15"), "expected 15 in: {msg}");
}

#[test]
fn for_step_until_accepts_assignment_syntax() {
    let mut interp = Interpreter::new();
    // MetaPost allows both `for k=...` and `for k:=...`.
    interp
        .run("numeric s; s := 0; for k:=1 step 1 until 5: s := s + k; endfor; show s;")
        .unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("15"), "expected 15 in: {msg}");
}

// -----------------------------------------------------------------------
// Str operator
// -----------------------------------------------------------------------

#[test]
fn str_operator() {
    let mut interp = Interpreter::new();
    interp.run("show str x;").unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("x"), "expected x in: {msg}");
}

#[test]
fn str_operator_multi_char() {
    let mut interp = Interpreter::new();
    interp.run("show str foo;").unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("foo"), "expected foo in: {msg}");
}

#[test]
fn str_operator_collects_suffix_chain() {
    let mut interp = Interpreter::new();
    interp.run("show str foo.bar.baz;").unwrap();
    let msg = &interp.errors[0].message;
    assert!(
        msg.contains("foo.bar.baz"),
        "expected suffix chain in: {msg}"
    );
}

#[test]
fn str_operator_collects_subscript_suffix() {
    let mut interp = Interpreter::new();
    interp.run("show str z[1+1].x;").unwrap();
    let msg = &interp.errors[0].message;
    assert!(
        msg.contains("z[2].x"),
        "expected subscript suffix in: {msg}"
    );
}

// -----------------------------------------------------------------------
// Undelimited macro parameters
// -----------------------------------------------------------------------

#[test]
fn eval_def_undelimited_primary() {
    let mut interp = Interpreter::new();
    interp
        .run("vardef double primary x = 2*x enddef; show double 5;")
        .unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("10"), "expected 10 in: {msg}");
}

#[test]
fn eval_def_undelimited_secondary() {
    let mut interp = Interpreter::new();
    interp
        .run("vardef neg secondary x = -x enddef; show neg 3;")
        .unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("-3"), "expected -3 in: {msg}");
}

#[test]
fn eval_def_undelimited_expr() {
    let mut interp = Interpreter::new();
    interp
        .run("vardef id expr x = x enddef; show id 5+3;")
        .unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("8"), "expected 8 in: {msg}");
}

// -----------------------------------------------------------------------
// Curl direction in path construction
// -----------------------------------------------------------------------

#[test]
fn curl_direction_in_def() {
    let mut interp = Interpreter::new();
    // This should define -- as a macro without error
    interp
        .run(
            "def -- = {curl 1}..{curl 1} enddef; \
             path p; p = (0,0)--(1,0); show p;",
        )
        .unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("path"), "expected path in: {msg}");
}

// -----------------------------------------------------------------------
// let: must not expand RHS macro
// -----------------------------------------------------------------------

#[test]
fn let_does_not_expand_rhs() {
    let mut interp = Interpreter::new();
    // Without fix, this crashes with "Expected pair, got known numeric"
    // because the let would try to expand foo's body
    interp
        .run(
            "def foo(expr z, d) = shifted -z rotated d shifted z enddef; \
             let bar = foo; show 1;",
        )
        .unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("1"), "expected 1 in: {msg}");
}

#[test]
fn let_copies_macro_info() {
    let mut interp = Interpreter::new();
    interp
        .run(
            "tertiarydef p _on_ d = d enddef; \
             let on = _on_; show 5 on 3;",
        )
        .unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("3"), "expected 3 in: {msg}");
}

// -----------------------------------------------------------------------
// Chained equations
// -----------------------------------------------------------------------

#[test]
fn chained_equation() {
    let mut interp = Interpreter::new();
    // Chained equation with unary-minus LHS: right = -left = (1,0)
    interp
        .run("pair right,left; right=-left=(1,0); show right; show left;")
        .unwrap();
    assert!(
        interp
            .errors
            .iter()
            .any(|e| e.message.contains(">> (1,0)") || e.message.contains(">> (1,-0)")),
        "expected right=(1,0), got: {:?}",
        interp.errors.iter().map(|e| &e.message).collect::<Vec<_>>()
    );
    assert!(
        interp
            .errors
            .iter()
            .any(|e| e.message.contains(">> (-1,0)") || e.message.contains(">> (-1,-0)")),
        "expected left=(-1,0), got: {:?}",
        interp.errors.iter().map(|e| &e.message).collect::<Vec<_>>()
    );
}

#[test]
fn linear_equation_system_solves() {
    let mut interp = Interpreter::new();
    interp
        .run("numeric x,y; x+y=5; x-y=1; show x; show y;")
        .unwrap();

    let messages: Vec<_> = interp.errors.iter().map(|e| e.message.as_str()).collect();
    assert!(
        messages.iter().any(|m| m.contains(">> 3")),
        "expected x=3, got: {:?}",
        messages
    );
    assert!(
        messages.iter().any(|m| m.contains(">> 2")),
        "expected y=2, got: {:?}",
        messages
    );
}

#[test]
fn chained_assignment() {
    let mut interp = Interpreter::new();
    interp
        .run("newinternal a,b,c; a:=b:=c:=0; show a; show b; show c;")
        .unwrap();

    let error_count = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Error)
        .count();
    assert!(error_count == 0, "expected 0 errors, got {error_count}");

    let shows: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.message.contains(">>"))
        .map(|e| e.message.as_str())
        .collect();
    assert!(
        shows.iter().filter(|m| m.contains(">> 0")).count() >= 3,
        "expected all values to be 0, got: {:?}",
        shows
    );
}

// -----------------------------------------------------------------------
// Type declaration with subscripts and suffixes
// -----------------------------------------------------------------------

#[test]
fn type_declaration_subscript_array() {
    let mut interp = Interpreter::new();
    // Should not hang
    interp.run("pair z_[];").unwrap();
}

#[test]
fn type_declaration_compound_suffix() {
    let mut interp = Interpreter::new();
    // Should not hang
    interp.run("path path_.l, path_.r;").unwrap();
}

#[test]
fn type_declaration_clears_subscripted_descendants() {
    let mut interp = Interpreter::new();
    // First pass: assign t[0] and t[1]
    interp
        .run("numeric t[]; t[0] := 10; t[1] := 20; show t[0];")
        .unwrap();
    assert!(
        interp.errors[0].message.contains("10"),
        "first assignment: expected 10 in {:?}",
        interp.errors[0].message
    );
    // Re-declare: clears old subscripted values
    interp.run("numeric t[]; t[0] := 99; show t[0];").unwrap();
    let msg = &interp.errors[1].message;
    assert!(
        msg.contains("99"),
        "after re-declaration: expected 99, got: {msg}"
    );
}

// -----------------------------------------------------------------------
// back_input / back_expr integration
// -----------------------------------------------------------------------

#[test]
fn back_input_rescans_token() {
    let mut interp = Interpreter::new();
    interp.input.push_source("+ 3;");
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
    interp.input.push_source(";");
    // Set up a capsule with a pair value and push it back
    interp.back_expr_value(super::ExprResultValue {
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
fn back_expr_numeric_in_expression() {
    // Push a numeric capsule and verify it can participate in arithmetic
    let mut interp = Interpreter::new();
    // Push source first (bottom of stack)
    interp.input.push_source("+ 3;");
    // Then push capsule (top of stack)
    interp.back_expr_value(super::ExprResultValue {
        exp: Value::Numeric(7.0),
        ty: Type::Known,
        dep: None,
        pair_dep: None,
    });
    interp.get_x_next();
    let result = interp.scan_expression().unwrap();
    // Should evaluate to 7 + 3 = 10
    assert_eq!(result.exp, Value::Numeric(10.0));
}

// -----------------------------------------------------------------------
// vardef expansion from scan_primary (TagToken path)
// -----------------------------------------------------------------------

#[test]
fn vardef_suffix_in_equation() {
    // laboff.lft where lft is a vardef — should work as variable, not expand
    let mut interp = Interpreter::new();
    interp
        .run("vardef lft primary x = x enddef; pair laboff.lft; laboff.lft = (1,2); show 1;")
        .unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("1"), "expected 1 in: {msg}");
}

#[test]
fn vardef_suffix_undeclared_equation() {
    // labxf.lft where labxf is undeclared and lft is a vardef
    let mut interp = Interpreter::new();
    interp
        .run("vardef lft primary x = x enddef; labxf.lft = 1; show 1;")
        .unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("1"), "expected 1 in: {msg}");
}

#[test]
fn tertiarydef_with_picture() {
    // Simplified _on_: just shift a picture
    let mut interp = Interpreter::new();
    interp
        .run(
            r#"
        delimiters ();
        tertiarydef p _on_ d =
          begingroup
          p shifted (0,d)
          endgroup
        enddef;
        show nullpicture _on_ 3;
    "#,
        )
        .unwrap();
    let errors: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Error)
        .collect();
    for e in &errors {
        eprintln!("  tertiarydef error: {}", e.message);
    }
    assert!(errors.is_empty(), "had {} errors", errors.len());
}

#[test]
fn error_recovery_skips_to_semicolon() {
    // Statement with unexpected comma should skip to ; and continue
    let mut interp = Interpreter::new();
    interp.run(",,,; show 1;").unwrap();
    // Should have errors for the commas but still process "show 1"
    let show_msgs: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.message.contains("1"))
        .collect();
    assert!(!show_msgs.is_empty(), "show 1 should have been processed");
}

#[test]
fn reports_missing_right_paren_in_parenthesized_expression() {
    let mut interp = Interpreter::new();
    interp.run("show (1+2; show 7;").unwrap();

    let errors: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Error)
        .collect();
    assert!(
        errors.iter().any(|e| {
            e.kind == crate::error::ErrorKind::MissingToken && e.message.contains("Expected `)`")
        }),
        "expected missing right paren diagnostic, got: {errors:?}"
    );
}

#[test]
fn reports_missing_right_bracket_in_mediation() {
    let mut interp = Interpreter::new();
    interp.run("show 0.5[(0,0),(2,2); show 9;").unwrap();

    let errors: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Error)
        .collect();
    assert!(
        errors.iter().any(|e| {
            e.kind == crate::error::ErrorKind::MissingToken && e.message.contains("Expected `]`")
        }),
        "expected missing right bracket diagnostic, got: {errors:?}"
    );
}

#[test]
fn reports_missing_right_brace_in_path_direction() {
    let mut interp = Interpreter::new();
    interp
        .run("path p; p := (0,0){curl 1..(1,0); show 1;")
        .unwrap();

    let errors: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Error)
        .collect();
    assert!(
        errors.iter().any(|e| {
            e.kind == crate::error::ErrorKind::MissingToken && e.message.contains("Expected `}`")
        }),
        "expected missing right brace diagnostic, got: {errors:?}"
    );
}

#[test]
fn scanner_unterminated_string_is_reported() {
    let mut interp = Interpreter::new();
    interp.run("show \"unterminated").unwrap();

    let errors: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Error)
        .collect();
    assert!(
        errors
            .iter()
            .any(|e| e.kind == crate::error::ErrorKind::UnterminatedString),
        "expected unterminated-string scanner diagnostic, got: {errors:?}"
    );
}

#[test]
fn scanner_invalid_character_is_reported() {
    let mut interp = Interpreter::new();
    let src = format!("show 1;{}show 2;", '\u{1f}');
    interp.run(&src).unwrap();

    let errors: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Error)
        .collect();
    assert!(
        errors
            .iter()
            .any(|e| e.kind == crate::error::ErrorKind::InvalidCharacter),
        "expected invalid-character scanner diagnostic, got: {errors:?}"
    );
}

#[test]
fn dashpattern_basic() {
    let mut interp = Interpreter::new();
    interp
        .run(
            r#"
        delimiters ();
        tertiarydef p _on_ d =
          begingroup save pic;
          picture pic; pic=p;
          addto pic doublepath (w,w)..(w+d,w);
          w := w+d;
          pic shifted (0,d)
          endgroup
        enddef;
        tertiarydef p _off_ d =
          begingroup w:=w+d;
          p shifted (0,d)
          endgroup
        enddef;
        vardef dashpattern(text t) =
          save on, off, w;
          let on=_on_;
          let off=_off_;
          w = 0;
          nullpicture t
        enddef;
        show dashpattern(on 3 off 3);
    "#,
        )
        .unwrap();
    // Should produce a picture, not a "Cannot transform" error
    let errors: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Error)
        .collect();
    for e in &errors {
        eprintln!("  dashpattern error: {}", e.message);
    }
    assert!(errors.is_empty(), "dashpattern had {} errors", errors.len());
}

#[test]
fn dashed_line_produces_dash_pattern() {
    // Verify that `dashed dashpattern(...)` applies stroke-dasharray to the
    // output picture and doesn't leak intermediate strokes.
    let mut interp = Interpreter::new();
    interp
        .run(
            r#"
        delimiters ();
        tertiarydef p _on_ d =
          begingroup save pic;
          picture pic; pic=p;
          addto pic doublepath (w,w)..(w+d,w);
          w := w+d;
          pic shifted (0,d)
          endgroup
        enddef;
        tertiarydef p _off_ d =
          begingroup w:=w+d;
          p shifted (0,d)
          endgroup
        enddef;
        vardef dashpattern(text t) =
          save on, off, w;
          let on=_on_;
          let off=_off_;
          w = 0;
          nullpicture t
        enddef;
        addto currentpicture doublepath (0,0)..(30,0)
          dashed dashpattern(on 2 off 3);
    "#,
        )
        .unwrap();

    let errors: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Error)
        .collect();
    assert!(errors.is_empty(), "errors: {errors:?}");

    // The picture should have exactly one Stroke object (the dashed line).
    let objects = &interp.current_picture().objects;
    assert_eq!(
        objects.len(),
        1,
        "expected 1 object, got {}: {:?}",
        objects.len(),
        objects
    );

    if let postmeta_graphics::types::GraphicsObject::Stroke(ref stroke) = objects[0] {
        let dash = stroke.dash.as_ref().expect("expected dash pattern");
        // on 2, off 3 → dashes = [2.0, 3.0]
        assert_eq!(dash.dashes.len(), 2, "dashes: {:?}", dash.dashes);
        assert!((dash.dashes[0] - 2.0).abs() < 0.01, "on={}", dash.dashes[0]);
        assert!(
            (dash.dashes[1] - 3.0).abs() < 0.01,
            "off={}",
            dash.dashes[1]
        );
    } else {
        panic!("expected Stroke, got {:?}", objects[0]);
    }
}

#[test]
fn dashed_withdots_uses_leading_offset() {
    // `dashpattern(off 2.5 on 0 off 2.5)` should produce one zero-length
    // dash every 5 units, offset by 2.5 from the path start.
    let mut interp = Interpreter::new();
    interp
        .run(
            r#"
        delimiters ();
        tertiarydef p _on_ d =
          begingroup save pic;
          picture pic; pic=p;
          addto pic doublepath (w,w)..(w+d,w);
          w := w+d;
          pic shifted (0,d)
          endgroup
        enddef;
        tertiarydef p _off_ d =
          begingroup w:=w+d;
          p shifted (0,d)
          endgroup
        enddef;
        vardef dashpattern(text t) =
          save on, off, w;
          let on=_on_;
          let off=_off_;
          w = 0;
          nullpicture t
        enddef;
        addto currentpicture doublepath (0,0)..(30,0)
          dashed dashpattern(off 2.5 on 0 off 2.5);
    "#,
        )
        .unwrap();

    let errors: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Error)
        .collect();
    assert!(errors.is_empty(), "errors: {errors:?}");

    let objects = &interp.current_picture().objects;
    assert_eq!(objects.len(), 1, "expected 1 object, got {}", objects.len());

    if let postmeta_graphics::types::GraphicsObject::Stroke(ref stroke) = objects[0] {
        let dash = stroke.dash.as_ref().expect("expected dash pattern");
        assert_eq!(dash.dashes.len(), 2, "dashes: {:?}", dash.dashes);
        assert!((dash.dashes[0] - 0.0).abs() < 0.01, "on={}", dash.dashes[0]);
        assert!(
            (dash.dashes[1] - 5.0).abs() < 0.01,
            "off={}",
            dash.dashes[1]
        );
        assert!((dash.offset - 2.5).abs() < 0.01, "offset={}", dash.offset);
    } else {
        panic!("expected Stroke, got {:?}", objects[0]);
    }
}

#[test]
fn vardef_stays_tag_token() {
    // After defining a vardef, the symbol should remain TagToken
    let mut interp = Interpreter::new();
    interp.run("vardef foo primary x = x + 1 enddef;").unwrap();
    let sym = interp.symbols.lookup("foo");
    let entry = interp.symbols.get(sym);
    assert_eq!(entry.command, Command::TagToken);
    assert!(interp.macros.contains_key(&sym));
}

#[test]
fn implicit_multiplication() {
    let mut interp = Interpreter::new();
    interp.run("bp := 1; show 3bp;").unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("3"), "expected 3 in: {msg}");
}

#[test]
fn implicit_multiplication_pair() {
    let mut interp = Interpreter::new();
    interp.run("show 2(3,4);").unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("(6,8)"), "expected (6,8) in: {msg}");
}

#[test]
fn vardef_expands_in_expression() {
    // vardef macro should expand when used as standalone primary
    let mut interp = Interpreter::new();
    interp
        .run("vardef foo primary x = x + 1 enddef; show foo 5;")
        .unwrap();
    // show produces an error with the value
    let msg = &interp.errors[0].message;
    assert!(msg.contains("6"), "expected 6 in: {msg}");
}

#[test]
fn vardef_suffix_not_expanded() {
    // A vardef symbol appearing as a suffix should NOT be expanded
    let mut interp = Interpreter::new();
    interp
        .run("pair p.foo; vardef foo primary x = x enddef; p.foo = (1,2);")
        .unwrap();
}

// -----------------------------------------------------------------------
// vardef with @# suffix parameter
// -----------------------------------------------------------------------

#[test]
fn vardef_at_suffix_parses() {
    let mut interp = Interpreter::new();
    interp
        .run("vardef foo@#(expr x) = x enddef; show 1;")
        .unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("1"), "expected 1 in: {msg}");
}

// -----------------------------------------------------------------------
// vardef with expr..of parameter pattern
// -----------------------------------------------------------------------

#[test]
fn vardef_expr_of_pattern() {
    let mut interp = Interpreter::new();
    interp
        .run("vardef direction expr t of p = t enddef; show 1;")
        .unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("1"), "expected 1 in: {msg}");
}

// -----------------------------------------------------------------------
// Multiple delimited parameter groups
// -----------------------------------------------------------------------

#[test]
fn multiple_delimited_param_groups() {
    let mut interp = Interpreter::new();
    interp
        .run("vardef foo(expr u)(expr v) = show u; show v enddef; foo(1)(2);")
        .unwrap();
    let infos: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Info)
        .map(|e| e.message.clone())
        .collect();
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
    let mut interp = Interpreter::new();
    interp
        .run("vardef foo(expr u)(expr v)=show u; show v enddef; foo(4,5);")
        .unwrap();

    let errors: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Error)
        .collect();
    assert!(errors.is_empty(), "unexpected errors: {errors:?}");

    let infos: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Info)
        .map(|e| e.message.clone())
        .collect();
    assert!(
        infos.iter().any(|m| m.contains('4')),
        "expected u=4 in: {infos:?}"
    );
    assert!(
        infos.iter().any(|m| m.contains('5')),
        "expected v=5 in: {infos:?}"
    );
}

#[test]
fn pair_equation_assigns_components() {
    let mut interp = Interpreter::new();
    interp
        .run("numeric t, u; (t,u) = (3.5, -2); show t; show u;")
        .unwrap();

    let messages: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Info)
        .map(|e| e.message.clone())
        .collect();
    assert!(
        messages.iter().any(|m| m.contains("3.5")),
        "expected t=3.5 in messages: {messages:?}"
    );
    assert!(
        messages.iter().any(|m| m.contains("-2")),
        "expected u=-2 in messages: {messages:?}"
    );
}

#[test]
fn pair_equation_preserves_dep_when_length_minus_unknown() {
    let mut interp = Interpreter::new();
    interp.set_filesystem(Box::new(PlainMpFs));
    interp
        .run(
            "input plain;
             path p;
             p := fullcircle;
             numeric t, u;
             (t, length p - u) = (1, 2);
             show u;",
        )
        .unwrap();

    let infos: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Info)
        .map(|e| e.message.clone())
        .collect();

    assert!(
        infos.iter().any(|m| m.contains('6')),
        "expected u=6 in info messages: {infos:?}"
    );
}

#[test]
fn vardef_expr_param_preserves_pair_deps() {
    // Regression: passing an unknown pair through a vardef expr parameter
    // must preserve equation deps so the solver can determine the variable.
    let mut interp = Interpreter::new();
    interp
        .run(
            "vardef assign(expr m, v) = m = v enddef;
             pair A; assign(A, (3,7)); show A;",
        )
        .unwrap();

    let errors: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Error)
        .collect();
    assert!(errors.is_empty(), "unexpected errors: {errors:?}");

    let infos: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Info)
        .map(|e| e.message.clone())
        .collect();
    assert!(
        infos.iter().any(|m| m.contains("(3,7)")),
        "expected A=(3,7), got: {infos:?}"
    );
}

#[test]
fn vardef_expr_param_preserves_numeric_deps() {
    // Passing an unknown numeric through a vardef expr parameter must
    // preserve its dependency so the equation solver can determine it.
    let mut interp = Interpreter::new();
    interp
        .run(
            "vardef assign(expr m, v) = m = v enddef;
             numeric x; assign(x, 42); show x;",
        )
        .unwrap();

    let errors: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Error)
        .collect();
    assert!(errors.is_empty(), "unexpected errors: {errors:?}");

    let infos: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Info)
        .map(|e| e.message.clone())
        .collect();
    assert!(
        infos.iter().any(|m| m.contains("42")),
        "expected x=42, got: {infos:?}"
    );
}

#[test]
fn vardef_expr_param_chained_pair_equations() {
    // Regression for example 177: a system of linear pair equations where
    // all unknowns pass through vardef expr parameters.
    //   bar(A, P0, P4, B)  =>  A = 1/3*P0 + 1/3*P4 + 1/3*B
    //   bar(B, A,  P1, C)  =>  B = 1/3*A  + 1/3*P1 + 1/3*C
    //   bar(C, B,  P2, P3) =>  C = 1/3*B  + 1/3*P2 + 1/3*P3
    // With P0..P4 known, the system is fully determined.
    let mut interp = Interpreter::new();
    interp
        .run(
            "vardef bar(expr m,a,b,c) = m = 1/3a + 1/3b + 1/3c enddef;
             pair A, B, C;
             bar(A, (9,0), (0,9), B);
             bar(B, A, (0,0), C);
             bar(C, B, (9,0), (0,9));
             show A; show B; show C;",
        )
        .unwrap();

    let errors: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Error)
        .collect();
    assert!(errors.is_empty(), "unexpected errors: {errors:?}");

    // Verify that all three pairs are known (not (0,0) placeholders).
    let infos: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Info)
        .map(|e| e.message.clone())
        .collect();
    assert_eq!(infos.len(), 3, "expected 3 show messages, got: {infos:?}");
    // None of the solved pairs should be (0,0) — that would indicate
    // deps were lost and the solver couldn't determine the variables.
    for info in &infos {
        assert!(
            !info.contains("(0,0)"),
            "pair should not be (0,0) — deps were likely lost: {infos:?}"
        );
    }
}

#[test]
fn def_expr_param_preserves_pair_deps() {
    // Same as the vardef test, but with `def` (no group scope).
    let mut interp = Interpreter::new();
    interp
        .run(
            "def assign(expr m, v) = m = v enddef;
             pair A; assign(A, (5,11)); show A;",
        )
        .unwrap();

    let errors: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Error)
        .collect();
    assert!(errors.is_empty(), "unexpected errors: {errors:?}");

    let infos: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Info)
        .map(|e| e.message.clone())
        .collect();
    assert!(
        infos.iter().any(|m| m.contains("(5,11)")),
        "expected A=(5,11), got: {infos:?}"
    );
}

#[test]
fn undelimited_expr_param_preserves_pair_deps() {
    // Undelimited primary/expr params also need dep preservation.
    let mut interp = Interpreter::new();
    interp
        .run(
            "def assign(expr m) primary v = m = v enddef;
             pair A; assign(A) (4,8); show A;",
        )
        .unwrap();

    let errors: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Error)
        .collect();
    assert!(errors.is_empty(), "unexpected errors: {errors:?}");

    let infos: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Info)
        .map(|e| e.message.clone())
        .collect();
    assert!(
        infos.iter().any(|m| m.contains("(4,8)")),
        "expected A=(4,8), got: {infos:?}"
    );
}

// -----------------------------------------------------------------------
// plain.mp loads without hard error
// -----------------------------------------------------------------------

#[test]
fn plain_mp_error_count() {
    let mut interp = Interpreter::new();
    interp.set_filesystem(Box::new(PlainMpFs));
    interp.run("input plain;").unwrap();

    let error_count = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Error)
        .count();
    // plain.mp should load without errors.
    assert!(error_count == 0, "expected 0 errors, got {error_count}");
}

#[test]
fn plain_mp_loads() {
    let mut interp = Interpreter::new();
    interp.set_filesystem(Box::new(PlainMpFs));
    // Should not return Err (hard error) — warnings are OK
    interp.run("input plain;").unwrap();
}

#[test]
fn plain_beginfig_draw_endfig() {
    let mut interp = Interpreter::new();
    interp.set_filesystem(Box::new(PlainMpFs));
    interp
        .run("input plain; beginfig(1); draw (0,0)..(10,10); endfig; end;")
        .unwrap();

    let errors = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Error)
        .count();
    assert!(errors == 0, "expected 0 errors, got {errors}");
    assert!(!interp.output().is_empty(), "expected shipped pictures");
}

#[test]
fn plain_path_examples_39_and_56() {
    let mut interp = Interpreter::new();
    interp.set_filesystem(Box::new(PlainMpFs));
    interp
        .run(
            "input plain;
             beginfig(39);
               draw (0,0) --- (0,1cm) .. (1cm,0) .. (1cm,1cm);
             endfig;
             beginfig(56);
               draw (0,0) .. tension 2 .. (1cm,1cm) .. (2cm,0);
             endfig;
             end;",
        )
        .unwrap();

    let errors = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Error)
        .count();
    assert!(errors == 0, "expected 0 errors, got {errors}");
    assert!(interp.output().len() >= 2, "expected shipped pictures");
}

#[test]
fn plain_fill_has_no_stroke_pen() {
    let mut interp = Interpreter::new();
    interp.set_filesystem(Box::new(PlainMpFs));
    interp
        .run("input plain; beginfig(1); fill fullcircle scaled 10bp; endfig; end;")
        .unwrap();

    let errors = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Error)
        .count();
    assert!(errors == 0, "expected 0 errors, got {errors}");

    let pic = interp.output().last().expect("expected shipped picture");
    let fill = match pic.objects.first().expect("expected one object") {
        postmeta_graphics::types::GraphicsObject::Fill(fill) => fill,
        other => panic!("expected Fill object, got {other:?}"),
    };
    assert!(fill.pen.is_none(), "fill should not carry stroke pen");
}

#[test]
fn plain_filldraw_withpen_sets_stroke_pen() {
    let mut interp = Interpreter::new();
    interp.set_filesystem(Box::new(PlainMpFs));
    interp
        .run(
            "input plain;
             beginfig(1);
               filldraw fullcircle scaled 10bp withpen pencircle scaled 2bp;
             endfig;
             end;",
        )
        .unwrap();

    let errors = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Error)
        .count();
    assert!(errors == 0, "expected 0 errors, got {errors}");

    let pic = interp.output().last().expect("expected shipped picture");
    let fill = match pic.objects.first().expect("expected one object") {
        postmeta_graphics::types::GraphicsObject::Fill(fill) => fill,
        other => panic!("expected Fill object, got {other:?}"),
    };

    let pen = fill.pen.as_ref().expect("filldraw should keep stroke pen");
    match pen {
        postmeta_graphics::types::Pen::Elliptical(t) => {
            assert!((t.txx - 1.0).abs() < 1e-9, "unexpected txx={}", t.txx);
            assert!((t.tyy - 1.0).abs() < 1e-9, "unexpected tyy={}", t.tyy);
        }
        other => panic!("expected elliptical pen, got {other:?}"),
    }
}

#[test]
fn plain_hide_postfix_preserves_left_expression() {
    use crate::variables::VarValue;
    let mut interp = Interpreter::new();
    interp.set_filesystem(Box::new(PlainMpFs));
    interp
        .run(
            "input plain;
             path p;
             cuttings := (0,0)--(1cm,0);
             p := ((0,0)--(1cm,0)) hide(cuttings:=reverse cuttings);
             end;",
        )
        .unwrap();

    let errors = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Error)
        .count();
    assert!(errors == 0, "expected 0 errors, got {errors}");

    let pid = interp
        .variables
        .lookup_existing("p")
        .expect("path variable p should exist");
    assert!(matches!(
        interp.variables.get(pid),
        VarValue::Known(crate::types::Value::Path(_))
    ));
}

#[test]
fn plain_drawarrow_example_17() {
    let mut interp = Interpreter::new();
    interp.set_filesystem(Box::new(PlainMpFs));
    interp
        .run(
            "input plain;
             beginfig(17);
               pair A, B, C;
               A := (0,0); B := (1cm,0); C := (0,1cm);
               drawarrow C--B--A;
               drawarrow A--C withpen pencircle scaled 2bp;
             endfig;
             end;",
        )
        .unwrap();

    let errors = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Error)
        .count();
    assert!(errors == 0, "expected 0 errors, got {errors}");
    assert!(!interp.output().is_empty(), "expected shipped pictures");
}

#[test]
fn plain_drawdblarrow_example_18() {
    let mut interp = Interpreter::new();
    interp.set_filesystem(Box::new(PlainMpFs));
    interp
        .run(
            "input plain;
             beginfig(18);
               pair A, B, C;
               A := (0,0); B := (1cm,0); C := (0,1cm);
               draw C--B--A--cycle;
               drawdblarrow A--C withpen pencircle scaled 2bp;
             endfig;
             end;",
        )
        .unwrap();

    let errors = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Error)
        .count();
    assert!(errors == 0, "expected 0 errors, got {errors}");
    assert!(!interp.output().is_empty(), "expected shipped pictures");
}

// -----------------------------------------------------------------------
// Type tests (numeric, pen, etc. as unary operators)
// -----------------------------------------------------------------------

#[test]
fn type_test_numeric() {
    let mut interp = Interpreter::new();
    interp.run("show numeric 5;").unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("true"), "expected true in: {msg}");
}

#[test]
fn type_test_pen() {
    let mut interp = Interpreter::new();
    interp.run("show pen pencircle;").unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("true"), "expected true in: {msg}");
}

#[test]
fn type_test_numeric_on_pen() {
    let mut interp = Interpreter::new();
    interp.run("show numeric pencircle;").unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("false"), "expected false in: {msg}");
}

// -----------------------------------------------------------------------
// Subscript variables
// -----------------------------------------------------------------------

#[test]
fn subscript_bracket() {
    let mut interp = Interpreter::new();
    interp.run("numeric a[]; a[1] := 42; show a[1];").unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("42"), "expected 42 in: {msg}");
}

// -----------------------------------------------------------------------
// Trailing tokens after undelimited macro params
// -----------------------------------------------------------------------

#[test]
fn trailing_tokens_after_undelimited_expr() {
    // A macro with undelimited `primary` param stops scanning after the
    // primary.  The trailing `;` must survive and terminate the statement.
    let mut interp = Interpreter::new();
    interp
        .run("def greet primary x = show x enddef; greet 42;")
        .unwrap();
    let errors: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Error)
        .collect();
    assert!(errors.is_empty(), "unexpected errors: {errors:?}");
    let show_msg = interp
        .errors
        .iter()
        .find(|e| e.severity == crate::error::Severity::Info);
    assert!(
        show_msg.is_some() && show_msg.unwrap().message.contains("42"),
        "expected show 42"
    );
}

#[test]
fn vardef_returns_value() {
    // A vardef should return the value of its last expression.
    let mut interp = Interpreter::new();
    interp
        .run("vardef triple(expr x) = 3 * x enddef; show triple(7);")
        .unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("21"), "expected 21 in: {msg}");
}

#[test]
fn save_restores_variable_binding() {
    let mut interp = Interpreter::new();
    interp
        .run("numeric x; x := 1; begingroup save x; x := 2; endgroup; show x;")
        .unwrap();

    let errors: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Error)
        .collect();
    assert!(errors.is_empty(), "unexpected errors: {errors:?}");

    let msg = interp
        .errors
        .iter()
        .find(|e| e.severity == crate::error::Severity::Info)
        .map(|e| e.message.clone())
        .unwrap_or_default();
    assert!(msg.contains("1"), "expected x to restore to 1, got: {msg}");
}

#[test]
fn whatever_calls_are_independent() {
    let mut interp = Interpreter::new();
    interp
        .run(
            "vardef whatever = save ?; ? enddef; \
             numeric a,b; \
             a=whatever; b=whatever; \
             a=0; b=1; \
             show a; show b;",
        )
        .unwrap();

    let errors: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Error)
        .collect();
    assert!(errors.is_empty(), "unexpected errors: {errors:?}");

    let infos: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Info)
        .map(|e| e.message.clone())
        .collect();
    assert!(
        infos
            .iter()
            .any(|m| m.contains(">> 0") || m.contains(">> -0")),
        "expected show a=0, got: {infos:?}"
    );
    assert!(
        infos.iter().any(|m| m.contains(">> 1")),
        "expected show b=1, got: {infos:?}"
    );
}

#[test]
fn whatever_times_pair_preserves_dependency() {
    let mut interp = Interpreter::new();
    interp
        .run(
            "vardef whatever = save ?; ? enddef; \
             pair o; \
             o-(1,2)=whatever*(3,4); \
             o-(5,6)=whatever*(7,8); \
             show o;",
        )
        .unwrap();

    let errors: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Error)
        .collect();
    assert!(errors.is_empty(), "unexpected errors: {errors:?}");
}

#[test]
fn whatever_line_intersection_solves_point() {
    let mut interp = Interpreter::new();
    interp
        .run(
            "vardef whatever = save ?; ? enddef; \
             pair A,B,C,D,M; \
             A=(0,0); B=(2,3); \
             C=(1,0); D=(-1,2); \
             M = whatever [A,B]; \
             M = whatever [C,D];",
        )
        .unwrap();

    let errors: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Error)
        .collect();
    assert!(errors.is_empty(), "unexpected errors: {errors:?}");

    let mid = interp
        .variables
        .lookup_existing("M")
        .expect("M should exist");
    let (xid, yid) = match interp.variables.get(mid) {
        crate::variables::VarValue::Pair { x, y } => (*x, *y),
        other => panic!("M should be a pair, got {other:?}"),
    };

    let mx = interp.variables.known_value(xid).unwrap_or(0.0);
    let my = interp.variables.known_value(yid).unwrap_or(0.0);

    assert!((mx - 0.4).abs() < 0.01, "mx={mx}");
    assert!((my - 0.6).abs() < 0.01, "my={my}");
}

#[test]
fn whatever_perpendicular_bisectors_solve_circumcenter() {
    let mut interp = Interpreter::new();
    interp
        .run(
            "vardef whatever = save ?; ? enddef; \
             pair A,B,C,O; \
             A=(0,0); B=(3,0); C=(1,2); \
             O - 1/2[B,C] = whatever * (B-C) rotated 90; \
             O - 1/2[A,B] = whatever * (A-B) rotated 90;",
        )
        .unwrap();

    let errors: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Error)
        .collect();
    assert!(errors.is_empty(), "unexpected errors: {errors:?}");

    let oid = interp
        .variables
        .lookup_existing("O")
        .expect("O should exist");
    let (xid, yid) = match interp.variables.get(oid) {
        crate::variables::VarValue::Pair { x, y } => (*x, *y),
        other => panic!("O should be a pair, got {other:?}"),
    };

    let ox = interp.variables.known_value(xid).unwrap_or(0.0);
    let oy = interp.variables.known_value(yid).unwrap_or(0.0);

    assert!((ox - 1.5).abs() < 0.01, "ox={ox}");
    assert!((oy - 0.5).abs() < 0.01, "oy={oy}");
}

#[test]
fn save_localizes_suffix_bindings_in_recursive_vardef() {
    let mut interp = Interpreter::new();
    interp
        .run(
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
        )
        .unwrap();

    let errors: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Error)
        .collect();
    assert!(errors.is_empty(), "unexpected errors: {errors:?}");

    let infos: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Info)
        .map(|e| e.message.clone())
        .collect();

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

// -----------------------------------------------------------------------
// btex/etex and infont
// -----------------------------------------------------------------------

#[test]
fn btex_etex_produces_picture() {
    // btex ... etex should produce a picture capsule (not a string).
    let mut interp = Interpreter::new();
    interp
        .run(r#"picture p; p = btex Hello World etex; show p;"#)
        .unwrap();
    let msg = &interp.errors[0].message;
    assert!(
        msg.contains("(picture)"),
        "expected picture type in show output: {msg}"
    );
}

#[test]
fn btex_etex_picture_is_transformable() {
    // btex...etex result can be shifted without error, since it's a picture.
    let mut interp = Interpreter::new();
    interp
        .run("picture p; p = btex test etex shifted (10,20);")
        .unwrap();
    let errors: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.message.contains("Cannot transform"))
        .collect();
    assert!(
        errors.is_empty(),
        "btex picture should be transformable, got: {:?}",
        errors
    );
}

#[test]
fn btex_etex_draw_shifted_no_error() {
    // `draw btex...etex shifted z` — the pattern from examples 203-207.
    // Should work with plain.mp loaded (addto currentpicture).
    let mut interp = Interpreter::new();
    interp.set_filesystem(Box::new(PlainMpFs));
    interp
        .run("input plain; beginfig(1); draw btex Q etex shifted (5,5); endfig; end;")
        .unwrap();
    let errors: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.message.contains("error") || e.message.contains("Cannot"))
        .collect();
    assert!(
        errors.is_empty(),
        "draw btex...etex shifted should not error: {:?}",
        errors
    );
    assert!(
        !interp.output().is_empty(),
        "should produce an output picture"
    );
}

#[test]
fn infont_produces_picture() {
    // "abc" infont "cmr10" should produce a picture
    let mut interp = Interpreter::new();
    interp
        .run(r#"picture p; p = "abc" infont "cmr10"; show p;"#)
        .unwrap();
    // The show output should indicate a picture value
    let msg = &interp.errors[0].message;
    // A picture show typically shows the type or contents
    assert!(
        !msg.contains("error"),
        "infont should not produce an error: {msg}"
    );
}

#[test]
fn infont_text_has_bbox() {
    // Corner operators on an infont picture should give non-zero bbox
    let mut interp = Interpreter::new();
    interp
        .run(r#"picture p; p = "Hello" infont "cmr10"; show lrcorner p;"#)
        .unwrap();
    let msg = &interp.errors[0].message;
    // lrcorner should have positive x and negative y (descender)
    assert!(msg.contains(','), "expected a pair in: {msg}");
}

#[test]
fn corner_operators_on_picture() {
    // Test all four corners on a simple filled picture
    let mut interp = Interpreter::new();
    interp
        .run("picture p; p = \"test\" infont \"cmr10\"; show llcorner p; show urcorner p;")
        .unwrap();
    let infos: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Info)
        .map(|e| e.message.clone())
        .collect();
    assert_eq!(infos.len(), 2, "expected 2 corner values, got: {infos:?}");
}

#[test]
fn corner_operators_on_path() {
    // Corner operators should work on paths too
    let mut interp = Interpreter::new();
    interp
        .run("path p; p = (0,0)..(10,20)..(30,5); show llcorner p; show urcorner p;")
        .unwrap();
    let infos: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Info)
        .map(|e| e.message.clone())
        .collect();
    assert_eq!(infos.len(), 2, "expected 2 corner values, got: {infos:?}");
}

#[test]
fn vardef_at_suffix_with_params() {
    // vardef foo@#(expr s) should bind @# to the suffix and s to the arg
    let mut interp = Interpreter::new();
    interp
        .run(r#"vardef foo@#(expr s) = show str @#; show s enddef; foo.bar("hello");"#)
        .unwrap();
    let infos: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Info)
        .map(|e| e.message.clone())
        .collect();
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

// -----------------------------------------------------------------------
// Substring reclassification (primary binary: substring X of Y)
// -----------------------------------------------------------------------

#[test]
fn substring_of_basic() {
    // substring (1,3) of "hello" = "el"
    let mut interp = Interpreter::new();
    interp.run(r#"show substring (1,3) of "hello";"#).unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("el"), "expected 'el' in: {msg}");
}

#[test]
fn substring_of_full_range() {
    // substring (0,5) of "hello" = "hello"
    let mut interp = Interpreter::new();
    interp.run(r#"show substring (0,5) of "hello";"#).unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("hello"), "expected 'hello' in: {msg}");
}

#[test]
fn substring_of_empty() {
    // substring (2,2) of "hello" = ""
    let mut interp = Interpreter::new();
    interp.run(r#"show substring (2,2) of "hello";"#).unwrap();
    let msg = &interp.errors[0].message;
    // Empty string shows as ""
    assert!(
        msg.contains("\"\"") || msg.contains(">>  ") || msg.ends_with(">> "),
        "expected empty string in: {msg}"
    );
}

#[test]
fn substring_of_utf8_is_char_boundary_safe() {
    // Regression: substring used byte slicing and could panic on UTF-8.
    let mut interp = Interpreter::new();
    interp.run("show substring (1,2) of \"a😊b\";").unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("😊"), "expected emoji substring in: {msg}");
}

#[test]
fn length_of_utf8_counts_characters() {
    let mut interp = Interpreter::new();
    interp.run("show length \"a😊b\";").unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains('3'), "expected length 3 in: {msg}");
}

#[test]
fn length_of_numeric_returns_abs() {
    let mut interp = Interpreter::new();
    interp.run("show length -5;").unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains('5'), "expected abs value 5 in: {msg}");

    let mut interp2 = Interpreter::new();
    interp2.run("show length 3.7;").unwrap();
    let msg2 = &interp2.errors[0].message;
    assert!(msg2.contains("3.7"), "expected 3.7 in: {msg2}");
}

#[test]
fn abs_of_numeric_via_plain_mp_let() {
    // plain.mp line 135: `let abs = length;`
    // abs should work on numerics since length does
    let mut interp = Interpreter::new();
    interp.run("let abs = length; show abs(-42);").unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("42"), "expected 42 in: {msg}");
}

// -----------------------------------------------------------------------
// Equals-means-equation flag (= as comparison vs equation)
// -----------------------------------------------------------------------

#[test]
fn equals_as_comparison_in_if() {
    // Inside `if`, `=` should be a comparison, not an equation
    let mut interp = Interpreter::new();
    interp.run("if 3 = 3: message \"yes\"; fi").unwrap();
    let msgs: Vec<&str> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Info)
        .map(|e| e.message.as_str())
        .collect();
    assert_eq!(msgs, vec!["yes"]);
}

#[test]
fn equals_as_comparison_in_exitif() {
    // `exitif n = 3` — the `=` must be comparison, not equation.
    // `exitif` finishes the current iteration body; loop stops at endfor.
    let mut interp = Interpreter::new();
    interp
        .run(concat!(
            "numeric n, s; n := 0; s := 0;\n",
            "forever: s := s + 1; n := n + 1; exitif n = 3; endfor;\n",
            "show n;\n",
        ))
        .unwrap();
    let msg = interp
        .errors
        .iter()
        .find(|e| e.severity == crate::error::Severity::Info)
        .map(|e| e.message.as_str())
        .unwrap_or("");
    // Loop runs 3 times (n=1,2,3), exits when n=3
    assert!(msg.contains("3"), "expected 3 in: {msg}");
}

#[test]
fn equals_as_equation_in_statement() {
    // At statement level, `=` should be an equation
    let mut interp = Interpreter::new();
    interp.run("numeric x; x = 42; show x;").unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("42"), "expected 42 in: {msg}");
}

// -----------------------------------------------------------------------
// Binary macro lookahead fix (tertiarydef in text params)
// -----------------------------------------------------------------------

#[test]
fn tertiarydef_or_in_text_param() {
    // `or` is a tertiarydef. Using it inside a text parameter of a macro
    // should not duplicate the closing delimiter.
    let mut interp = Interpreter::new();
    interp
        .run(concat!(
            "tertiarydef a or b = if a: a else: b fi enddef;\n",
            "def test(text t) = t enddef;\n",
            "show test(false or true);\n",
        ))
        .unwrap();
    let errors: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Error)
        .collect();
    assert!(errors.is_empty(), "unexpected errors: {errors:?}");
    let msg = interp
        .errors
        .iter()
        .find(|e| e.severity == crate::error::Severity::Info)
        .map(|e| e.message.as_str())
        .unwrap_or("");
    assert!(msg.contains("true"), "expected true in: {msg}");
}

// -----------------------------------------------------------------------
// String comparison operators
// -----------------------------------------------------------------------

#[test]
fn string_less_than() {
    let mut interp = Interpreter::new();
    interp.run(r#"show "a" < "b";"#).unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("true"), "expected true in: {msg}");
}

#[test]
fn string_greater_than() {
    let mut interp = Interpreter::new();
    interp.run(r#"show "z" > "a";"#).unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("true"), "expected true in: {msg}");
}

#[test]
fn string_less_equal() {
    let mut interp = Interpreter::new();
    interp.run(r#"show "abc" <= "abd";"#).unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("true"), "expected true in: {msg}");
}

#[test]
fn string_greater_equal_same() {
    let mut interp = Interpreter::new();
    interp.run(r#"show "abc" >= "abc";"#).unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("true"), "expected true in: {msg}");
}

#[test]
fn string_comparison_false() {
    let mut interp = Interpreter::new();
    interp.run(r#"show "b" < "a";"#).unwrap();
    let msg = &interp.errors[0].message;
    assert!(msg.contains("false"), "expected false in: {msg}");
}

// -----------------------------------------------------------------------
// For-loop token substitution (for-as-expression)
// -----------------------------------------------------------------------

#[test]
fn for_as_expression_sum() {
    // `for i=1,2,3: i + endfor 0` should evaluate to 6
    let mut interp = Interpreter::new();
    interp.run("show for i=1,2,3: i + endfor 0;").unwrap();
    let msg = interp
        .errors
        .iter()
        .find(|e| e.severity == crate::error::Severity::Info)
        .map(|e| e.message.as_str())
        .unwrap_or("");
    assert!(msg.contains("6"), "expected 6 in: {msg}");
}

#[test]
fn nested_for_substitutes_outer_loop_variable() {
    // Regression: outer `for` variables must substitute inside nested
    // loop bodies (example 132 relies on this).
    let mut interp = Interpreter::new();
    interp
        .run("for i=1 step 1 until 2: for j=1 step 1 until 2: show i; endfor; endfor;")
        .unwrap();

    let infos: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Info)
        .map(|e| e.message.clone())
        .collect();

    assert_eq!(infos.len(), 4, "expected 4 show outputs, got: {infos:?}");
    assert!(infos[0].contains("1"), "expected 1, got: {}", infos[0]);
    assert!(infos[1].contains("1"), "expected 1, got: {}", infos[1]);
    assert!(infos[2].contains("2"), "expected 2, got: {}", infos[2]);
    assert!(infos[3].contains("2"), "expected 2, got: {}", infos[3]);
}

#[test]
fn nested_for_same_name_shadows_outer_loop_variable() {
    // Guardrail: if an inner loop reuses the same variable name, it
    // should shadow the outer loop variable.
    let mut interp = Interpreter::new();
    interp
        .run("for i=1 step 1 until 2: for i=10 step 1 until 11: show i; endfor; endfor;")
        .unwrap();

    let infos: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Info)
        .map(|e| e.message.clone())
        .collect();

    assert_eq!(infos.len(), 4, "expected 4 show outputs, got: {infos:?}");
    assert!(infos[0].contains("10"), "expected 10, got: {}", infos[0]);
    assert!(infos[1].contains("11"), "expected 11, got: {}", infos[1]);
    assert!(infos[2].contains("10"), "expected 10, got: {}", infos[2]);
    assert!(infos[3].contains("11"), "expected 11, got: {}", infos[3]);
}

#[test]
fn collective_pair_subscript_is_pair_typed() {
    // Regression: `pair A[]` must make `A[1]` a pair, not a numeric.
    let mut interp = Interpreter::new();
    interp
        .run("pair A[]; show pair A[1]; show numeric A[1];")
        .unwrap();

    let infos: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Info)
        .map(|e| e.message.clone())
        .collect();

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
fn collective_pair_subscript_works_in_for_sum_expression() {
    // Regression from examples 133/134: summing A[i] must stay pair arithmetic.
    let mut interp = Interpreter::new();
    let result = interp.run(concat!(
        "numeric n; n := 3;\n",
        "pair A[];\n",
        "for i=1 step 1 until n-1: A[i+1] - A[i] = (0,1); endfor;\n",
        "show (0,0) for i=1 step 1 until n: + A[i] endfor;\n",
    ));

    assert!(result.is_ok(), "expected run to succeed, got: {result:?}");
}

#[test]
fn forsuffixes_iterates_suffixes() {
    // forsuffixes should iterate over suffix values
    let mut interp = Interpreter::new();
    interp
        .run(concat!(
            "numeric a.x, a.y, a.z;\n",
            "a.x := 10; a.y := 20; a.z := 30;\n",
            "numeric s; s := 0;\n",
            "forsuffixes $=x,y,z: s := s + a$; endfor;\n",
            "show s;\n",
        ))
        .unwrap();
    let msg = interp
        .errors
        .iter()
        .find(|e| e.severity == crate::error::Severity::Info)
        .map(|e| e.message.as_str())
        .unwrap_or("");
    assert!(msg.contains("60"), "expected 60 in: {msg}");
}

// -----------------------------------------------------------------------
// Implicit multiplication with capsule tokens in for loops
// -----------------------------------------------------------------------

#[test]
fn for_loop_implicit_multiplication() {
    // `for i=0 step 1 until 2: show 72i; endfor`
    // should produce 0, 72, 144 via implicit multiplication 72*i
    let mut interp = Interpreter::new();
    interp
        .run("for i=0 step 1 until 2: show 72i; endfor;")
        .unwrap();
    let infos: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Info)
        .map(|e| e.message.clone())
        .collect();
    assert_eq!(infos.len(), 3, "expected 3 show outputs, got: {infos:?}");
    assert!(infos[0].contains("0"), "expected 0, got: {}", infos[0]);
    assert!(infos[1].contains("72"), "expected 72, got: {}", infos[1]);
    assert!(infos[2].contains("144"), "expected 144, got: {}", infos[2]);
}

// ===================================================================
// Regression tests for equality, step loops, scantokens, equations
// ===================================================================

// Lock down the interpreter's comparison tolerance behavior.
// Value::PartialEq uses NUMERIC_TOLERANCE (1e-4).

#[test]
fn equality_comparison_uses_interpreter_tolerance() {
    // 1 = 1.00005 should be true (diff < 1e-4) in MetaPost semantics
    let mut interp = Interpreter::new();
    interp.run("if 1 = 1.00005: show 1; fi;").unwrap();
    let infos: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Info)
        .collect();
    assert!(!infos.is_empty(), "expected equality to hold for diff 5e-5");
}

#[test]
fn equality_comparison_detects_large_diff() {
    // 1 = 1.001 should be false (diff > 1e-4 threshold for equation consistency)
    let mut interp = Interpreter::new();
    interp.run("if 1 = 1.001: show 1; fi;").unwrap();
    // Should NOT have any info messages if comparison is false
    let infos: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Info)
        .collect();
    assert!(
        infos.is_empty(),
        "1 = 1.001 should be false, but show executed"
    );
}

#[test]
fn undelimited_macro_arg_parse_error_does_not_reuse_stale_cur_expr() {
    let mut interp = Interpreter::new();
    interp
        .run("def f primary p = show p; enddef; show 99; f;")
        .unwrap();

    let infos: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Info)
        .map(|e| e.message.as_str())
        .collect();

    let shows_99 = infos.iter().filter(|msg| msg.contains("99")).count();
    assert_eq!(
        shows_99, 1,
        "missing undelimited arg should not reuse stale expression value"
    );
}

// step/until loop edge cases

#[test]
fn for_step_until_zero_step_no_hang() {
    // Zero step should produce no iterations (avoids infinite loop)
    let mut interp = Interpreter::new();
    interp
        .run("for i=1 step 0 until 5: show i; endfor;")
        .unwrap();
    let infos: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Info)
        .collect();
    assert!(infos.is_empty(), "zero step should produce no iterations");
}

#[test]
fn for_step_until_inclusive_endpoint() {
    // `for i=0 step 1 until 3` should include i=3
    let mut interp = Interpreter::new();
    interp
        .run("for i=0 step 1 until 3: show i; endfor;")
        .unwrap();
    let infos: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Info)
        .map(|e| e.message.clone())
        .collect();
    assert_eq!(
        infos.len(),
        4,
        "expected 4 iterations (0,1,2,3), got: {infos:?}"
    );
}

#[test]
fn for_step_until_negative_direction() {
    // `for i=3 step -1 until 1` should produce 3,2,1
    let mut interp = Interpreter::new();
    interp
        .run("for i=3 step -1 until 1: show i; endfor;")
        .unwrap();
    let infos: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Info)
        .map(|e| e.message.clone())
        .collect();
    assert_eq!(
        infos.len(),
        3,
        "expected 3 iterations (3,2,1), got: {infos:?}"
    );
}

#[test]
fn for_step_until_fractional_inclusive() {
    // `for i=0 step 0.1 until 0.3` should include 0.3 (within tolerance)
    let mut interp = Interpreter::new();
    interp
        .run("for i=0 step 0.1 until 0.3: show i; endfor;")
        .unwrap();
    let infos: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Info)
        .map(|e| e.message.clone())
        .collect();
    assert!(
        infos.len() >= 4,
        "expected at least 4 iterations (0, 0.1, 0.2, 0.3), got {}: {infos:?}",
        infos.len()
    );
}

#[test]
fn for_step_until_wrong_direction_no_iterations() {
    // `for i=1 step -1 until 5` goes the wrong way: should produce no iterations
    let mut interp = Interpreter::new();
    interp
        .run("for i=1 step -1 until 5: show i; endfor;")
        .unwrap();
    let infos: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Info)
        .collect();
    assert!(
        infos.is_empty(),
        "wrong direction should produce no iterations, got: {infos:?}"
    );
}

// scantokens normal vs push-only parity

#[test]
fn scantokens_preserves_terminator() {
    // scantokens should not eat the `;` after the string expression
    let mut interp = Interpreter::new();
    interp.run(r#"scantokens "show 42"; show 99;"#).unwrap();
    let infos: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Info)
        .map(|e| e.message.clone())
        .collect();
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
    // expandafter scantokens should produce same result
    let mut interp = Interpreter::new();
    interp.run(r#"expandafter show scantokens "42";"#).unwrap();
    let infos: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Info)
        .map(|e| e.message.clone())
        .collect();
    assert!(
        infos.iter().any(|m| m.contains("42")),
        "expandafter scantokens should show 42: {infos:?}"
    );
}

// Input source push/pop ordering

#[test]
fn nested_source_levels_lifo_order() {
    // Verify that multiple push_source calls work in LIFO order
    let mut interp = Interpreter::new();
    // Push two source levels manually, then run the top-level source
    interp.input.push_source("show 2;");
    interp.input.push_source("show 1;");
    interp.get_x_next();
    while interp.cur.command != Command::Stop {
        interp.do_statement().unwrap();
    }
    let infos: Vec<_> = interp
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

// Equation solving with transitive dependencies

#[test]
fn nonlinear_equation_does_not_assign_bindable_lhs() {
    // Regression: nonlinear equations like `z = x*y` must not silently
    // degrade into assignment (`z := 0`) when dependency tracking is absent.
    let mut interp = Interpreter::new();
    interp.run("numeric x, y, z; z = x*y;").unwrap();

    let errors: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Error)
        .collect();
    assert!(
        errors.iter().any(|e| {
            e.kind == crate::error::ErrorKind::IncompatibleTypes && e.message.contains("Nonlinear")
        }),
        "expected nonlinear-equation diagnostic, got: {errors:?}"
    );

    let z_id = interp
        .variables
        .lookup_existing("z")
        .expect("z should exist after declaration");
    assert!(
        !matches!(
            interp.variables.get(z_id),
            crate::variables::VarValue::NumericVar(crate::variables::NumericState::Known(_))
        ),
        "nonlinear equation must not force z to known value"
    );
}

#[test]
fn transitive_equations_solve_correctly() {
    // x + y = 5; y + z = 7; x = 1 => y = 4, z = 3
    let mut interp = Interpreter::new();
    interp
        .run("numeric x, y, z; x + y = 5; y + z = 7; x = 1; show y; show z;")
        .unwrap();
    let infos: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Info)
        .map(|e| e.message.clone())
        .collect();
    assert!(
        infos.iter().any(|m| m.contains("4")),
        "expected y=4: {infos:?}"
    );
    assert!(
        infos.iter().any(|m| m.contains("3")),
        "expected z=3: {infos:?}"
    );
}

// save must not affect similar-prefix roots

#[test]
fn save_root_does_not_affect_similar_prefix() {
    let mut interp = Interpreter::new();
    interp
        .run(
            "numeric a, ab; a := 1; ab := 2; \
             begingroup save a; a := 99; endgroup; \
             show a; show ab;",
        )
        .unwrap();
    let infos: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Info)
        .map(|e| e.message.clone())
        .collect();
    assert!(
        infos.iter().any(|m| m.contains(">> 1")),
        "a should restore to 1: {infos:?}"
    );
    assert!(
        infos.iter().any(|m| m.contains(">> 2")),
        "ab should remain 2: {infos:?}"
    );
}

// scan_expression is currently pub; this test works from inside the
// crate and will survive a visibility narrowing to pub(crate).

#[test]
fn scan_expression_internal_usage() {
    let mut interp = Interpreter::new();
    interp.input.push_source("3 + 4;");
    interp.get_x_next();
    let result = interp.scan_expression().unwrap();
    assert_eq!(result.exp, Value::Numeric(7.0));
}

// -----------------------------------------------------------------------
// Regression tests for recent parser/interpreter bugs
// -----------------------------------------------------------------------

#[test]
fn implicit_mul_scales_pair_dependencies() {
    // Regression: implicit multiplication (3z) must scale pair dependencies,
    // not just the computed placeholder value.
    let mut interp = Interpreter::new();
    interp.run("pair z; 3z = (6,9); show z;").unwrap();

    let infos: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Info)
        .map(|e| e.message.clone())
        .collect();
    assert!(
        infos.iter().any(|m| m.contains("(2,3)")),
        "expected z=(2,3), got: {infos:?}"
    );
}

#[test]
fn addto_defaults_to_currentpicture_when_name_omitted() {
    let mut interp = Interpreter::new();
    interp
        .run("addto contour ((0,0)..(1,0)..(1,1)..cycle);")
        .unwrap();

    let errors: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Error)
        .collect();
    assert!(errors.is_empty(), "unexpected errors: {errors:?}");

    assert_eq!(
        interp.current_picture().objects.len(),
        1,
        "expected one object in currentpicture"
    );
    assert!(matches!(
        interp.current_picture().objects[0],
        postmeta_graphics::types::GraphicsObject::Fill(_)
    ));
}

#[test]
fn clip_defaults_to_currentpicture_when_name_omitted() {
    let mut interp = Interpreter::new();
    interp
        .run(
            "addto contour ((0,0)..(1,0)..(1,1)..cycle); \
             clip to ((-1,-1)..(2,-1)..(2,2)..(-1,2)..cycle);",
        )
        .unwrap();

    let errors: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Error)
        .collect();
    assert!(errors.is_empty(), "unexpected errors: {errors:?}");

    let objs = &interp.current_picture().objects;
    assert!(matches!(
        objs.first(),
        Some(postmeta_graphics::types::GraphicsObject::ClipStart(_))
    ));
    assert!(matches!(
        objs.last(),
        Some(postmeta_graphics::types::GraphicsObject::ClipEnd)
    ));
}

#[test]
fn shipout_non_picture_reports_type_error() {
    let mut interp = Interpreter::new();
    interp.run("shipout 123;").unwrap();

    let errors: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Error)
        .collect();
    assert!(
        errors
            .iter()
            .any(|e| e.kind == crate::error::ErrorKind::TypeError),
        "expected type error for non-picture shipout, got: {errors:?}"
    );
    assert!(interp.output().is_empty(), "shipout must not emit output");
}

#[test]
fn empty_path_cycle_reports_error_without_panic() {
    let mut interp = Interpreter::new();
    interp.run("path p; p := p .. cycle; show 1;").unwrap();

    let errors: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Error)
        .collect();
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
fn undelimited_text_macro_stops_at_endgroup() {
    // Regression: undelimited text args must stop at endgroup as well as ';'.
    let mut interp = Interpreter::new();
    interp
        .run(
            "def t text x = message \"in\" enddef; \
             begingroup t a endgroup; \
             message \"after\";",
        )
        .unwrap();

    let infos: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Info)
        .map(|e| e.message.clone())
        .collect();
    assert!(
        infos.iter().any(|m| m == "in"),
        "expected message 'in': {infos:?}"
    );
    assert!(
        infos.iter().any(|m| m == "after"),
        "expected message 'after': {infos:?}"
    );
}

#[test]
fn vardef_at_suffix_only_preserves_trailing_token() {
    // Regression: for vardef with only @# suffix param, the trailing token after
    // a macro call must still be preserved.
    let mut interp = Interpreter::new();
    interp
        .run("vardef f@# = 1 enddef; show f.x; message \"after\";")
        .unwrap();

    let infos: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Info)
        .map(|e| e.message.clone())
        .collect();
    assert!(
        infos.iter().any(|m| m.contains(">> 1")),
        "expected show output for f.x: {infos:?}"
    );
    assert!(
        infos.iter().any(|m| m == "after"),
        "expected trailing message after macro call: {infos:?}"
    );
}

#[test]
fn mismatched_custom_delimiters_report_error() {
    let mut interp = Interpreter::new();
    let _ = interp.run("delimiters {{ }}; show {{ 3 + 4 );");

    let errors: Vec<_> = interp
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
fn known_equation_reports_inconsistency_without_assignment() {
    let mut interp = Interpreter::new();
    interp.run("numeric x; x := 1; x = 2; show x;").unwrap();

    let errors: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Error)
        .collect();
    assert!(
        errors
            .iter()
            .any(|e| e.kind == crate::error::ErrorKind::InconsistentEquation),
        "expected inconsistent-equation error, got: {errors:?}"
    );

    let x_id = interp
        .variables
        .lookup_existing("x")
        .expect("x should exist after declaration");
    let x = interp.variables.known_value(x_id).unwrap_or(f64::NAN);
    assert!((x - 1.0).abs() < 1e-12, "x should remain 1, got {x}");
}

#[test]
fn addto_picture_target_accepts_symbolic_suffixes() {
    let mut interp = Interpreter::new();
    interp
        .run("picture pic.layer; addto pic.layer contour ((0,0)..(1,0)..(1,1)..cycle);")
        .unwrap();

    let layer_id = interp
        .variables
        .lookup_existing("pic.layer")
        .expect("pic.layer should exist");
    let layer_pic = match interp.variables.get(layer_id) {
        crate::variables::VarValue::Known(Value::Picture(p)) => p,
        other => panic!("pic.layer should be picture, got {other:?}"),
    };
    assert_eq!(
        layer_pic.objects.len(),
        1,
        "expected contour on pic.layer picture"
    );
}

#[test]
fn clip_picture_target_accepts_symbolic_suffixes() {
    let mut interp = Interpreter::new();
    interp
        .run(
            "picture pic.layer; \
             addto pic.layer contour ((0,0)..(1,0)..(1,1)..cycle); \
             clip pic.layer to ((-1,-1)..(2,-1)..(2,2)..(-1,2)..cycle);",
        )
        .unwrap();

    let layer_id = interp
        .variables
        .lookup_existing("pic.layer")
        .expect("pic.layer should exist");
    let layer_pic = match interp.variables.get(layer_id) {
        crate::variables::VarValue::Known(Value::Picture(p)) => p,
        other => panic!("pic.layer should be picture, got {other:?}"),
    };

    assert!(matches!(
        layer_pic.objects.first(),
        Some(postmeta_graphics::types::GraphicsObject::ClipStart(_))
    ));
    assert!(matches!(
        layer_pic.objects.last(),
        Some(postmeta_graphics::types::GraphicsObject::ClipEnd)
    ));
}

#[test]
fn nonlinear_equation_without_bindable_lhs_reports_error() {
    let mut interp = Interpreter::new();
    interp.run("numeric x, y; x*x = y;").unwrap();

    let errors: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Error)
        .collect();
    assert!(
        errors
            .iter()
            .any(|e| e.kind == crate::error::ErrorKind::IncompatibleTypes),
        "expected nonlinear-equation error, got: {errors:?}"
    );
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

#[test]
fn relax_command_is_accepted_as_noop() {
    let mut interp = Interpreter::new();
    interp.run("relax; show 1;").unwrap();

    let errors: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Error)
        .collect();
    assert!(errors.is_empty(), "unexpected errors: {errors:?}");

    let infos: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Info)
        .map(|e| e.message.clone())
        .collect();
    assert!(
        infos.iter().any(|m| m.contains(">> 1")),
        "show output: {infos:?}"
    );
}

#[test]
fn randomseed_statement_sets_seed() {
    let mut interp = Interpreter::new();
    interp.run("randomseed := 123;").unwrap();
    assert_eq!(interp.random_seed, 123);
}

#[test]
fn special_statement_reports_unimplemented() {
    let mut interp = Interpreter::new();
    interp.run("special \"x\";").unwrap();

    let errors: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Error)
        .collect();
    assert!(
        errors
            .iter()
            .any(|e| e.kind == crate::error::ErrorKind::InvalidExpression),
        "expected unimplemented diagnostic, got: {errors:?}"
    );
}

/// mp.web §302: makepen auto-closes non-cyclic paths.
#[test]
fn makepen_accepts_non_cyclic_path() {
    let mut interp = Interpreter::new();
    interp
        .run("pen p; p := makepen ((0,0)..(100,0));")
        .expect("makepen should accept non-cyclic path");

    let errors: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Error)
        .collect();
    assert!(errors.is_empty(), "unexpected errors: {errors:?}");
}

/// mp.web §16987: makepen accepts a pair (pair_to_path).
#[test]
fn makepen_accepts_pair() {
    let mut interp = Interpreter::new();
    interp
        .run("pen p; p := makepen (5,3);")
        .expect("makepen should accept a pair");

    let errors: Vec<_> = interp
        .errors
        .iter()
        .filter(|e| e.severity == crate::error::Severity::Error)
        .collect();
    assert!(errors.is_empty(), "unexpected errors: {errors:?}");
}
