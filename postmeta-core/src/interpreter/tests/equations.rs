//! Linear equation solving, dependencies, and `whatever`-style systems.

use crate::interpreter::Interpreter;

use super::helpers::TestInterp;

#[test]
fn parser_split_keeps_equation_vs_assignment_behavior() {
    let mut interp = TestInterp::new();
    interp.run("numeric a, b, c; a = 7; b := c := 9;");

    let a_sym = interp.interp.state.symbols.lookup("a");
    let b_sym = interp.interp.state.symbols.lookup("b");
    let c_sym = interp.interp.state.symbols.lookup("c");

    let a_id = interp.interp.state.variables.lookup_by_sym(a_sym, "a");
    let b_id = interp.interp.state.variables.lookup_by_sym(b_sym, "b");
    let c_id = interp.interp.state.variables.lookup_by_sym(c_sym, "c");

    assert_eq!(interp.interp.state.variables.known_value(a_id), Some(7.0));
    assert_eq!(interp.interp.state.variables.known_value(b_id), Some(9.0));
    assert_eq!(interp.interp.state.variables.known_value(c_id), Some(9.0));
}

#[test]
fn mediation_preserves_numeric_endpoint_dependencies() {
    let mut interp = TestInterp::new();
    interp.run("numeric a,b,c,x; a := 0.25; x = a[b,c]; b = 2; c = 10; show x;");

    let infos = interp.shows();
    assert!(
        infos.iter().any(|m| m.contains('4')),
        "expected x=4 in: {infos:?}"
    );
}

#[test]
fn mediation_preserves_pair_endpoint_dependencies() {
    let mut interp = TestInterp::new();
    interp.run("numeric a; pair b,c,p; a := 0.5; p = a[b,c]; b = (2,4); c = (6,8); show p;");

    let infos = interp.shows();
    assert!(
        infos.iter().any(|m| m.contains("(4,6)")),
        "expected p=(4,6) in: {infos:?}"
    );
}

// -----------------------------------------------------------------------
// Chained equations
// -----------------------------------------------------------------------

#[test]
fn chained_equation() {
    let mut interp = TestInterp::new();
    // Chained equation with unary-minus LHS: right = -left = (1,0)
    interp.run("pair right,left; right=-left=(1,0); show right; show left;");
    assert!(
        interp
            .interp
            .state
            .errors
            .iter()
            .any(|e| e.message.contains(">> (1,0)") || e.message.contains(">> (1,-0)")),
        "expected right=(1,0), got: {:?}",
        interp
            .interp
            .state
            .errors
            .iter()
            .map(|e| &e.message)
            .collect::<Vec<_>>()
    );
    assert!(
        interp
            .interp
            .state
            .errors
            .iter()
            .any(|e| e.message.contains(">> (-1,0)") || e.message.contains(">> (-1,-0)")),
        "expected left=(-1,0), got: {:?}",
        interp
            .interp
            .state
            .errors
            .iter()
            .map(|e| &e.message)
            .collect::<Vec<_>>()
    );
}

#[test]
fn linear_equation_system_solves() {
    let mut interp = TestInterp::new();
    interp.run("numeric x,y; x+y=5; x-y=1; show x; show y;");

    let messages: Vec<_> = interp
        .interp
        .state
        .errors
        .iter()
        .map(|e| e.message.as_str())
        .collect();
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
    let mut interp = TestInterp::new();
    interp.run("newinternal a,b,c; a:=b:=c:=0; show a; show b; show c;");

    interp.assert_no_errors();

    let shows: Vec<_> = interp
        .shows()
        .into_iter()
        .filter(|m| m.contains(">>"))
        .collect();
    assert!(
        shows.iter().filter(|m| m.contains(">> 0")).count() >= 3,
        "expected all values to be 0, got: {:?}",
        shows
    );
}

#[test]
fn pair_equation_assigns_components() {
    let mut interp = TestInterp::new();
    interp.run("numeric t, u; (t,u) = (3.5, -2); show t; show u;");

    let messages = interp.shows();
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
    let mut interp = TestInterp::with_plain_mp();
    interp.run(
        "input plain;
             path p;
             p := fullcircle;
             numeric t, u;
             (t, length p - u) = (1, 2);
             show u;",
    );

    let infos = interp.shows();

    assert!(
        infos.iter().any(|m| m.contains('6')),
        "expected u=6 in info messages: {infos:?}"
    );
}

#[test]
fn vardef_expr_param_preserves_pair_deps() {
    // Regression: passing an unknown pair through a vardef expr parameter
    // must preserve equation deps so the solver can determine the variable.
    let mut interp = TestInterp::new();
    interp.run(
        "vardef assign(expr m, v) = m = v enddef;
             pair A; assign(A, (3,7)); show A;",
    );

    interp.assert_no_errors();

    let infos = interp.shows();
    assert!(
        infos.iter().any(|m| m.contains("(3,7)")),
        "expected A=(3,7), got: {infos:?}"
    );
}

#[test]
fn vardef_expr_param_preserves_numeric_deps() {
    // Passing an unknown numeric through a vardef expr parameter must
    // preserve its dependency so the equation solver can determine it.
    let mut interp = TestInterp::new();
    interp.run(
        "vardef assign(expr m, v) = m = v enddef;
             numeric x; assign(x, 42); show x;",
    );

    interp.assert_no_errors();

    let infos = interp.shows();
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
    let mut interp = TestInterp::new();
    interp.run(
        "vardef bar(expr m,a,b,c) = m = 1/3a + 1/3b + 1/3c enddef;
             pair A, B, C;
             bar(A, (9,0), (0,9), B);
             bar(B, A, (0,0), C);
             bar(C, B, (9,0), (0,9));
             show A; show B; show C;",
    );

    interp.assert_no_errors();

    // Verify that all three pairs are known (not (0,0) placeholders).
    let infos = interp.shows();
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
    let mut interp = TestInterp::new();
    interp.run(
        "def assign(expr m, v) = m = v enddef;
             pair A; assign(A, (5,11)); show A;",
    );

    interp.assert_no_errors();

    let infos = interp.shows();
    assert!(
        infos.iter().any(|m| m.contains("(5,11)")),
        "expected A=(5,11), got: {infos:?}"
    );
}

#[test]
fn undelimited_expr_param_preserves_pair_deps() {
    // Undelimited primary/expr params also need dep preservation.
    let mut interp = TestInterp::new();
    interp.run(
        "def assign(expr m) primary v = m = v enddef;
             pair A; assign(A) (4,8); show A;",
    );

    interp.assert_no_errors();

    let infos = interp.shows();
    assert!(
        infos.iter().any(|m| m.contains("(4,8)")),
        "expected A=(4,8), got: {infos:?}"
    );
}

#[test]
fn whatever_calls_are_independent() {
    let mut interp = TestInterp::new();
    interp.run(
        "vardef whatever = save ?; ? enddef; \
             numeric a,b; \
             a=whatever; b=whatever; \
             a=0; b=1; \
             show a; show b;",
    );

    interp.assert_no_errors();

    let infos = interp.shows();
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
    let mut interp = TestInterp::new();
    interp.run(
        "vardef whatever = save ?; ? enddef; \
             pair o; \
             o-(1,2)=whatever*(3,4); \
             o-(5,6)=whatever*(7,8); \
             show o;",
    );

    interp.assert_no_errors();
}

#[test]
fn whatever_line_intersection_solves_point() {
    let mut interp = TestInterp::new();
    interp.run(
        "vardef whatever = save ?; ? enddef; \
             pair A,B,C,D,M; \
             A=(0,0); B=(2,3); \
             C=(1,0); D=(-1,2); \
             M = whatever [A,B]; \
             M = whatever [C,D];",
    );

    interp.assert_no_errors();

    let mid = interp
        .interp
        .state
        .variables
        .lookup_existing("M")
        .expect("M should exist");
    let (xid, yid) = match interp.interp.state.variables.get(mid) {
        crate::variables::VarValue::Pair { x, y } => (*x, *y),
        other => panic!("M should be a pair, got {other:?}"),
    };

    let mx = interp
        .interp
        .state
        .variables
        .known_value(xid)
        .unwrap_or(0.0);
    let my = interp
        .interp
        .state
        .variables
        .known_value(yid)
        .unwrap_or(0.0);

    assert!((mx - 0.4).abs() < 0.01, "mx={mx}");
    assert!((my - 0.6).abs() < 0.01, "my={my}");
}

#[test]
fn whatever_perpendicular_bisectors_solve_circumcenter() {
    let mut interp = TestInterp::new();
    interp.run(
        "vardef whatever = save ?; ? enddef; \
             pair A,B,C,O; \
             A=(0,0); B=(3,0); C=(1,2); \
             O - 1/2[B,C] = whatever * (B-C) rotated 90; \
             O - 1/2[A,B] = whatever * (A-B) rotated 90;",
    );

    interp.assert_no_errors();

    let oid = interp
        .interp
        .state
        .variables
        .lookup_existing("O")
        .expect("O should exist");
    let (xid, yid) = match interp.interp.state.variables.get(oid) {
        crate::variables::VarValue::Pair { x, y } => (*x, *y),
        other => panic!("O should be a pair, got {other:?}"),
    };

    let ox = interp
        .interp
        .state
        .variables
        .known_value(xid)
        .unwrap_or(0.0);
    let oy = interp
        .interp
        .state
        .variables
        .known_value(yid)
        .unwrap_or(0.0);

    assert!((ox - 1.5).abs() < 0.01, "ox={ox}");
    assert!((oy - 0.5).abs() < 0.01, "oy={oy}");
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

// Equation solving with transitive dependencies

#[test]
fn nonlinear_equation_does_not_assign_bindable_lhs() {
    // Regression: nonlinear equations like `z = x*y` must not silently
    // degrade into assignment (`z := 0`) when dependency tracking is absent.
    let mut interp = TestInterp::new();
    interp.run("numeric x, y, z; z = x*y;");

    let errors = interp.errors();
    assert!(
        errors.iter().any(|e| {
            e.kind == crate::error::ErrorKind::IncompatibleTypes && e.message.contains("Nonlinear")
        }),
        "expected nonlinear-equation diagnostic, got: {errors:?}"
    );

    let z_id = interp
        .interp
        .state
        .variables
        .lookup_existing("z")
        .expect("z should exist after declaration");
    assert!(
        !matches!(
            interp.interp.state.variables.get(z_id),
            crate::variables::VarValue::NumericVar(crate::variables::NumericState::Known(_))
        ),
        "nonlinear equation must not force z to known value"
    );
}

#[test]
fn transitive_equations_solve_correctly() {
    // x + y = 5; y + z = 7; x = 1 => y = 4, z = 3
    let mut interp = TestInterp::new();
    interp.run("numeric x, y, z; x + y = 5; y + z = 7; x = 1; show y; show z;");
    let infos = interp.shows();
    assert!(
        infos.iter().any(|m| m.contains("4")),
        "expected y=4: {infos:?}"
    );
    assert!(
        infos.iter().any(|m| m.contains("3")),
        "expected z=3: {infos:?}"
    );
}

// -----------------------------------------------------------------------
// Regression tests for recent parser/interpreter bugs
// -----------------------------------------------------------------------

#[test]
fn implicit_mul_scales_pair_dependencies() {
    // Regression: implicit multiplication (3z) must scale pair dependencies,
    // not just the computed placeholder value.
    let mut interp = TestInterp::new();
    interp.run("pair z; 3z = (6,9); show z;");

    let infos = interp.shows();
    assert!(
        infos.iter().any(|m| m.contains("(2,3)")),
        "expected z=(2,3), got: {infos:?}"
    );
}

#[test]
fn known_equation_reports_inconsistency_without_assignment() {
    let mut interp = TestInterp::new();
    interp.run("numeric x; x := 1; x = 2; show x;");

    let errors = interp.errors();
    assert!(
        errors
            .iter()
            .any(|e| e.kind == crate::error::ErrorKind::InconsistentEquation),
        "expected inconsistent-equation error, got: {errors:?}"
    );

    let x_id = interp
        .interp
        .state
        .variables
        .lookup_existing("x")
        .expect("x should exist after declaration");
    let x = interp
        .interp
        .state
        .variables
        .known_value(x_id)
        .unwrap_or(f64::NAN);
    assert!((x - 1.0).abs() < 1e-12, "x should remain 1, got {x}");
}

#[test]
fn nonlinear_equation_without_bindable_lhs_reports_error() {
    let mut interp = TestInterp::new();
    interp.run("numeric x, y; x*x = y;");

    let errors = interp.errors();
    assert!(
        errors
            .iter()
            .any(|e| e.kind == crate::error::ErrorKind::IncompatibleTypes),
        "expected nonlinear-equation error, got: {errors:?}"
    );
}

// -----------------------------------------------------------------------
// Regression: numeric equations inside for-loops must work.
//
// For-loop variables stored as capsules previously had dep:None, causing
// the equation solver to silently skip `x = <loop-var>`.  Now capsules
// carry dep = const_dep(v) so equations resolve correctly.
// -----------------------------------------------------------------------

#[test]
fn for_loop_numeric_equation() {
    let mut interp = TestInterp::new();
    interp.run(
        "for p=3, 7, 11: \
               numeric a; a = p; \
               show a; \
             endfor;",
    );

    interp.assert_no_errors();

    let infos = interp.shows();
    assert_eq!(infos.len(), 3, "expected 3 show outputs: {infos:?}");
    assert!(infos[0].contains("3"), "first iteration: {}", infos[0]);
    assert!(infos[1].contains("7"), "second iteration: {}", infos[1]);
    assert!(infos[2].contains("11"), "third iteration: {}", infos[2]);
}

// ---------------------------------------------------------------------------
// Compound-type pins (pair/color/transform behavior guarded before the
// component-generic equation refactor)
// ---------------------------------------------------------------------------

#[test]
fn color_assignment_sets_components() {
    let mut interp = TestInterp::new();
    interp.run("color c; c := (0.1, 0.2, 0.3); show c;");
    interp.assert_no_errors();
    assert!(
        interp.first_show().contains("(0.1,0.2,0.3)"),
        "got: {}",
        interp.first_show()
    );
}

#[test]
fn color_equation_with_known_rhs_assigns_components() {
    let mut interp = TestInterp::new();
    interp.run("color c; c = (0.5, 0.25, 1); show c;");
    interp.assert_no_errors();
    assert!(
        interp.first_show().contains("(0.5,0.25,1)"),
        "got: {}",
        interp.first_show()
    );
}

#[test]
fn transform_componentwise_equations_solve() {
    let mut interp = TestInterp::new();
    interp.run(
        "transform T; xpart T = 1; ypart T = 2; xxpart T = 1; \
         xypart T = 0; yxpart T = 0; yypart T = 1; \
         show xpart T; show yypart T;",
    );
    interp.assert_no_errors();
    let shows = interp.shows();
    assert!(shows[0].contains('1'), "xpart: {}", shows[0]);
    assert!(shows[1].contains('1'), "yypart: {}", shows[1]);
}

#[test]
fn transform_equation_with_known_rhs_solves() {
    let mut interp = TestInterp::with_plain_mp();
    interp
        .run("input plain; transform T; T = identity shifted (1, 2); show xpart T; show yxpart T;");
    interp.assert_no_errors();
    // First show is plain.mp's preload banner; take the last two.
    let shows = interp.shows();
    let [xpart, yxpart] = shows[shows.len() - 2..] else {
        panic!("expected two shows, got {shows:?}");
    };
    assert!(xpart.contains('1'), "xpart: {xpart}");
    assert!(yxpart.contains('0'), "yxpart: {yxpart}");
}

#[test]
fn pair_inconsistent_equation_reports_residual_per_component() {
    let mut interp = TestInterp::new();
    interp.run("pair p; p = (1,2); p = (3,4); show p;");
    let errors = interp.errors();
    assert!(
        errors
            .iter()
            .any(|e| e.message.contains("Inconsistent") && e.message.contains("(x)")),
        "missing x-component inconsistency: {errors:?}"
    );
    assert!(
        errors
            .iter()
            .any(|e| e.message.contains("Inconsistent") && e.message.contains("(y)")),
        "missing y-component inconsistency: {errors:?}"
    );
    // First value wins; the second equation is rejected.
    assert!(interp.first_show().contains("(1,2)"));
}

#[test]
fn equation_chain_equates_all_lhs_to_final_rhs() {
    let mut interp = TestInterp::new();
    interp.run("numeric a, b; a = b = 3; show a; show b;");
    interp.assert_no_errors();
    assert!(interp.shows()[0].contains('3'));
    assert!(interp.shows()[1].contains('3'));
}

#[test]
fn color_ring_equation_links_components() {
    // Regression: `a = b` with both colors unknown used to yield (0,0,0)
    // silently; component-wise solving links the component variables.
    let mut interp = TestInterp::new();
    interp.run("color a, b; a = b; b = (0.1, 0.2, 0.3); show a;");
    interp.assert_no_errors();
    assert!(
        interp.first_show().contains("(0.1,0.2,0.3)"),
        "got: {}",
        interp.first_show()
    );
}

#[test]
fn transform_ring_equation_links_components() {
    // Regression: `S = T` with both transforms unknown used to yield an
    // all-zero transform silently.
    let mut interp = TestInterp::with_plain_mp();
    interp.run(
        "input plain; transform S, T; S = T; T = identity scaled 2; \
         show xxpart S; show yypart S;",
    );
    interp.assert_no_errors();
    let shows = interp.shows();
    let [xx, yy] = shows[shows.len() - 2..] else {
        panic!("expected two shows, got {shows:?}");
    };
    assert!(xx.contains('2'), "xxpart: {xx}");
    assert!(yy.contains('2'), "yypart: {yy}");
}

#[test]
fn negated_compound_variable_equation() {
    // `-a = b` must negate a's component dependencies.
    let mut interp = TestInterp::new();
    interp.run("color a, b; -a = b; b = (0.1, 0.2, 0.3); show a;");
    interp.assert_no_errors();
    assert!(
        interp.first_show().contains("(-0.1,-0.2,-0.3)"),
        "got: {}",
        interp.first_show()
    );
}
