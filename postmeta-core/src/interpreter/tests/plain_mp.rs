//! Loading plain.mp and exercising its macros end to end

use super::helpers::TestInterp;

// -----------------------------------------------------------------------
// plain.mp loads without hard error
// -----------------------------------------------------------------------

#[test]
fn plain_mp_error_count() {
    let mut interp = TestInterp::with_plain_mp();
    interp.run("input plain;");

    interp.assert_no_errors();
}

#[test]
fn plain_mp_loads() {
    let mut interp = TestInterp::with_plain_mp();
    // Should not return Err (hard error); warnings are OK
    interp.run("input plain;");
}

#[test]
fn plain_beginfig_draw_endfig() {
    let mut interp = TestInterp::with_plain_mp();
    interp.run("input plain; beginfig(1); draw (0,0)..(10,10); endfig; end;");

    interp.assert_no_errors();
    assert!(!interp.output().is_empty(), "expected shipped pictures");
}

#[test]
fn plain_path_examples_39_and_56() {
    let mut interp = TestInterp::with_plain_mp();
    interp.run(
        "input plain;
             beginfig(39);
               draw (0,0) --- (0,1cm) .. (1cm,0) .. (1cm,1cm);
             endfig;
             beginfig(56);
               draw (0,0) .. tension 2 .. (1cm,1cm) .. (2cm,0);
             endfig;
             end;",
    );

    interp.assert_no_errors();
    assert!(interp.output().len() >= 2, "expected shipped pictures");
}

#[test]
fn plain_fill_has_no_stroke_pen() {
    let mut interp = TestInterp::with_plain_mp();
    interp.run("input plain; beginfig(1); fill fullcircle scaled 10bp; endfig; end;");

    interp.assert_no_errors();

    let pic = interp.output().last().expect("expected shipped picture");
    let fill = match pic.objects().first().expect("expected one object") {
        postmeta_graphics::types::GraphicsObject::Fill(fill) => fill,
        other => panic!("expected Fill object, got {other:?}"),
    };
    assert!(fill.pen.is_none(), "fill should not carry stroke pen");
}

#[test]
fn plain_filldraw_withpen_sets_stroke_pen() {
    let mut interp = TestInterp::with_plain_mp();
    interp.run(
        "input plain;
             beginfig(1);
               filldraw fullcircle scaled 10bp withpen pencircle scaled 2bp;
             endfig;
             end;",
    );

    interp.assert_no_errors();

    let pic = interp.output().last().expect("expected shipped picture");
    let fill = match pic.objects().first().expect("expected one object") {
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
    let mut interp = TestInterp::with_plain_mp();
    interp.run(
        "input plain;
             path p;
             cuttings := (0,0)--(1cm,0);
             p := ((0,0)--(1cm,0)) hide(cuttings:=reverse cuttings);
             end;",
    );

    interp.assert_no_errors();

    let pid = interp
        .interp
        .state
        .variables
        .lookup_existing("p")
        .expect("path variable p should exist");
    assert!(matches!(
        interp.interp.state.variables.get(pid),
        VarValue::Known(crate::types::Value::Path(_))
    ));
}

#[test]
fn plain_drawarrow_example_17() {
    let mut interp = TestInterp::with_plain_mp();
    interp.run(
        "input plain;
             beginfig(17);
               pair A, B, C;
               A := (0,0); B := (1cm,0); C := (0,1cm);
               drawarrow C--B--A;
               drawarrow A--C withpen pencircle scaled 2bp;
             endfig;
             end;",
    );

    interp.assert_no_errors();
    assert!(!interp.output().is_empty(), "expected shipped pictures");
}

#[test]
fn plain_drawdblarrow_example_18() {
    let mut interp = TestInterp::with_plain_mp();
    interp.run(
        "input plain;
             beginfig(18);
               pair A, B, C;
               A := (0,0); B := (1cm,0); C := (0,1cm);
               draw C--B--A--cycle;
               drawdblarrow A--C withpen pencircle scaled 2bp;
             endfig;
             end;",
    );

    interp.assert_no_errors();
    assert!(!interp.output().is_empty(), "expected shipped pictures");
}
