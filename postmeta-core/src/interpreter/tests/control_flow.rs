//! Conditionals and loops: if/elseif, for, forever/exitif, forsuffixes

use super::helpers::TestInterp;

#[test]
fn eval_if_true() {
    let mut interp = TestInterp::new();
    interp.run("show if true: 42 fi;");
    let msg = interp.first_show();
    assert!(msg.contains("42"), "expected 42 in: {msg}");
}

#[test]
fn eval_if_false_else() {
    let mut interp = TestInterp::new();
    interp.run("show if false: 1 else: 2 fi;");
    let msg = interp.first_show();
    assert!(msg.contains("2"), "expected 2 in: {msg}");
}

#[test]
fn eval_if_false_no_else() {
    let mut interp = TestInterp::new();
    interp.run("if false: show 1; fi; show 2;");
    assert_eq!(
        interp.shows().len(),
        1,
        "expected only 1 show, got {:?}",
        interp.interp.state.errors
    );
    let msg = interp.first_show();
    assert!(msg.contains("2"), "expected 2 in: {msg}");
}

#[test]
fn eval_if_elseif() {
    let mut interp = TestInterp::new();
    interp.run("if false: show 1; elseif true: show 2; fi;");
    assert_eq!(interp.shows().len(), 1);
    let msg = interp.first_show();
    assert!(msg.contains("2"), "expected 2 in: {msg}");
}

#[test]
fn eval_if_nested() {
    let mut interp = TestInterp::new();
    interp.run("if true: if true: show 42; fi; fi;");
    assert_eq!(interp.shows().len(), 1);
    let msg = interp.first_show();
    assert!(msg.contains("42"), "expected 42 in: {msg}");
}

#[test]
fn eval_for_loop() {
    let mut interp = TestInterp::new();
    interp.run("for i = 1, 2, 3: show i; endfor;");
    assert_eq!(
        interp.shows().len(),
        3,
        "expected 3 shows: {:?}",
        interp.interp.state.errors
    );
    assert!(interp.shows()[0].contains("1"));
    assert!(interp.shows()[1].contains("2"));
    assert!(interp.shows()[2].contains("3"));
}

#[test]
fn eval_for_loop_step() {
    let mut interp = TestInterp::new();
    interp.run("numeric s; s := 0; for i = 1, 2, 3: s := s + i; endfor; show s;");
    let msg = interp.first_show();
    assert!(msg.contains("6"), "expected 6 in: {msg}");
}

#[test]
fn eval_forever_exitif() {
    let mut interp = TestInterp::new();
    interp.run("numeric n; n := 0; forever: n := n + 1; exitif n > 3; endfor; show n;");
    let msg = interp.first_show();
    assert!(msg.contains("4"), "expected 4 in: {msg}");
}

#[test]
fn exitif_outside_loop_reports_error() {
    let mut interp = TestInterp::new();
    interp.run("exitif true;");

    let errs = interp.errors();
    assert!(
        errs.iter()
            .any(|e| e.kind == crate::error::ErrorKind::BadExitIf),
        "expected BadExitIf, got: {errs:?}"
    );
}

#[test]
fn exitif_outside_loop_does_not_leak_into_future_forever() {
    let mut interp = TestInterp::new();
    interp.run(concat!(
        "numeric n; n := 0;\n",
        "exitif true;\n",
        "forever: n := n + 1; exitif n = 2; endfor;\n",
        "show n;\n",
    ));

    let errs = interp.errors();
    assert!(
        errs.iter()
            .any(|e| e.kind == crate::error::ErrorKind::BadExitIf),
        "expected BadExitIf from top-level exitif, got: {errs:?}"
    );

    let infos = interp.shows();
    assert!(
        infos.iter().any(|m| m.contains('2')),
        "expected loop to reach n=2, got infos: {infos:?}"
    );
}

#[test]
fn exitif_in_for_step_until_stops_loop() {
    // Regression: `for` pre-pushed all iterations.
    // `exitif` then had no loop frame to set the exit flag on.
    let mut interp = TestInterp::new();
    interp.run(concat!(
        "numeric t;\n",
        "for i:=0 step 1 until 10:\n",
        "  t := i;\n",
        "  exitif i > 2;\n",
        "endfor;\n",
        "show t;\n",
    ));
    interp.assert_no_errors();
    let msg = interp.first_show();
    assert!(msg.contains('3'), "expected t=3 in: {msg}");
}

#[test]
fn nested_forever_loops_keep_outer_replay_state() {
    // Regression: nested `forever` loops shared one pending body slot.
    // An inner loop could clobber outer replay state.
    let mut interp = TestInterp::new();
    interp.run(concat!(
        "numeric nouter; nouter := 0;\n",
        "forever:\n",
        "  nouter := nouter + 1;\n",
        "  forever: exitif true; endfor;\n",
        "  exitif nouter > 2;\n",
        "endfor;\n",
        "show nouter;\n",
    ));

    interp.assert_no_errors();
}

#[test]
fn nested_forever_exitif_equals_is_comparison() {
    // Regression: `exitif i = 2` must parse `=` as comparison, not equation
    let mut interp = TestInterp::new();
    interp.run(concat!(
        "numeric nouter, i;\n",
        "nouter := 0;\n",
        "forever:\n",
        "  nouter := nouter + 1;\n",
        "  i := 0;\n",
        "  forever: i := i + 1; exitif i = 2; endfor;\n",
        "  exitif nouter = 2;\n",
        "endfor;\n",
        "show nouter; show i;\n",
    ));

    interp.assert_no_errors();

    let infos = interp.shows();
    assert!(
        infos.iter().any(|m| m.contains('2')),
        "expected show outputs containing 2, got infos: {infos:?}"
    );
}

// -----------------------------------------------------------------------
// For step/until
// -----------------------------------------------------------------------

#[test]
fn for_step_until() {
    let mut interp = TestInterp::new();
    interp.run("numeric s; s := 0; for k=1 step 1 until 5: s := s + k; endfor; show s;");
    let msg = interp.first_show();
    assert!(msg.contains("15"), "expected 15 in: {msg}");
}

#[test]
fn for_step_until_by_two() {
    let mut interp = TestInterp::new();
    interp.run("numeric s; s := 0; for k=0 step 2 until 10: s := s + k; endfor; show s;");
    let msg = interp.first_show();
    assert!(msg.contains("30"), "expected 30 in: {msg}");
}

#[test]
fn for_step_until_negative() {
    let mut interp = TestInterp::new();
    interp.run("numeric s; s := 0; for k=5 step -1 until 1: s := s + k; endfor; show s;");
    let msg = interp.first_show();
    assert!(msg.contains("15"), "expected 15 in: {msg}");
}

#[test]
fn for_step_until_accepts_assignment_syntax() {
    let mut interp = TestInterp::new();
    // MetaPost allows both `for k=...` and `for k:=...`
    interp.run("numeric s; s := 0; for k:=1 step 1 until 5: s := s + k; endfor; show s;");
    let msg = interp.first_show();
    assert!(msg.contains("15"), "expected 15 in: {msg}");
}

// -----------------------------------------------------------------------
// For-loop token substitution (for-as-expression)
// -----------------------------------------------------------------------

#[test]
fn for_as_expression_sum() {
    let mut interp = TestInterp::new();
    interp.run("show for i=1,2,3: i + endfor 0;");
    let msg = interp.first_show();
    assert!(msg.contains("6"), "expected 6 in: {msg}");
}

#[test]
fn nested_for_substitutes_outer_loop_variable() {
    // Regression from example 132: outer loop variables must substitute in nested loop bodies
    let mut interp = TestInterp::new();
    interp.run("for i=1 step 1 until 2: for j=1 step 1 until 2: show i; endfor; endfor;");

    let infos = interp.shows();

    assert_eq!(infos.len(), 4, "expected 4 show outputs, got: {infos:?}");
    assert!(infos[0].contains("1"), "expected 1, got: {}", infos[0]);
    assert!(infos[1].contains("1"), "expected 1, got: {}", infos[1]);
    assert!(infos[2].contains("2"), "expected 2, got: {}", infos[2]);
    assert!(infos[3].contains("2"), "expected 2, got: {}", infos[3]);
}

#[test]
fn nested_for_same_name_shadows_outer_loop_variable() {
    let mut interp = TestInterp::new();
    interp.run("for i=1 step 1 until 2: for i=10 step 1 until 11: show i; endfor; endfor;");

    let infos = interp.shows();

    assert_eq!(infos.len(), 4, "expected 4 show outputs, got: {infos:?}");
    assert!(infos[0].contains("10"), "expected 10, got: {}", infos[0]);
    assert!(infos[1].contains("11"), "expected 11, got: {}", infos[1]);
    assert!(infos[2].contains("10"), "expected 10, got: {}", infos[2]);
    assert!(infos[3].contains("11"), "expected 11, got: {}", infos[3]);
}

#[test]
fn forsuffixes_iterates_suffixes() {
    let mut interp = TestInterp::new();
    interp.run(concat!(
        "numeric a.x, a.y, a.z;\n",
        "a.x := 10; a.y := 20; a.z := 30;\n",
        "numeric s; s := 0;\n",
        "forsuffixes $=x,y,z: s := s + a$; endfor;\n",
        "show s;\n",
    ));
    let msg = interp.first_show();
    assert!(msg.contains("60"), "expected 60 in: {msg}");
}

// -----------------------------------------------------------------------
// Implicit multiplication with capsule tokens in for loops
// -----------------------------------------------------------------------

#[test]
fn for_loop_implicit_multiplication() {
    let mut interp = TestInterp::new();
    interp.run("for i=0 step 1 until 2: show 72i; endfor;");
    let infos = interp.shows();
    assert_eq!(infos.len(), 3, "expected 3 show outputs, got: {infos:?}");
    assert!(infos[0].contains("0"), "expected 0, got: {}", infos[0]);
    assert!(infos[1].contains("72"), "expected 72, got: {}", infos[1]);
    assert!(infos[2].contains("144"), "expected 144, got: {}", infos[2]);
}

// step/until loop edge cases

#[test]
fn for_step_until_zero_step_no_hang() {
    let mut interp = TestInterp::new();
    interp.run("for i=1 step 0 until 5: show i; endfor;");
    let infos = interp.shows();
    assert!(infos.is_empty(), "zero step should produce no iterations");
}

#[test]
fn for_step_until_inclusive_endpoint() {
    let mut interp = TestInterp::new();
    interp.run("for i=0 step 1 until 3: show i; endfor;");
    let infos = interp.shows();
    assert_eq!(
        infos.len(),
        4,
        "expected 4 iterations (0,1,2,3), got: {infos:?}"
    );
}

#[test]
fn for_step_until_negative_direction() {
    let mut interp = TestInterp::new();
    interp.run("for i=3 step -1 until 1: show i; endfor;");
    let infos = interp.shows();
    assert_eq!(
        infos.len(),
        3,
        "expected 3 iterations (3,2,1), got: {infos:?}"
    );
}

#[test]
fn for_step_until_fractional_inclusive() {
    // The 0.3 endpoint must be included despite floating-point step accumulation
    let mut interp = TestInterp::new();
    interp.run("for i=0 step 0.1 until 0.3: show i; endfor;");
    let infos = interp.shows();
    assert!(
        infos.len() >= 4,
        "expected at least 4 iterations (0, 0.1, 0.2, 0.3), got {}: {infos:?}",
        infos.len()
    );
}

#[test]
fn for_step_until_wrong_direction_no_iterations() {
    let mut interp = TestInterp::new();
    interp.run("for i=1 step -1 until 5: show i; endfor;");
    let infos = interp.shows();
    assert!(
        infos.is_empty(),
        "wrong direction should produce no iterations, got: {infos:?}"
    );
}
