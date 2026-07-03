//! Pictures: addto/clip, part extraction, btex/infont, dashes.

use crate::types::Value;

use super::helpers::TestInterp;

#[test]
fn eval_pencircle() {
    let mut interp = TestInterp::new();
    interp.run("show pencircle;");
    let msg = interp.first_show();
    assert!(msg.contains("pen"), "expected pen in: {msg}");
}

#[test]
fn filled_returns_true_for_fill_picture() {
    let mut interp = TestInterp::new();
    interp.run("picture p; addto p contour ((0,0)..(1,0)..(1,1)..cycle); show filled p;");
    let msg = interp.first_show();
    assert!(msg.contains("true"), "expected true in: {msg}");
}

#[test]
fn stroked_returns_true_for_stroke_picture() {
    let mut interp = TestInterp::new();
    interp.run("picture p; addto p doublepath ((0,0)..(10,0)); show stroked p;");
    let msg = interp.first_show();
    assert!(msg.contains("true"), "expected true in: {msg}");
}

#[test]
fn clipped_returns_false_for_empty_picture() {
    let mut interp = TestInterp::new();
    interp.run("picture p; show clipped p;");
    let msg = interp.first_show();
    assert!(msg.contains("false"), "expected false in: {msg}");
}

#[test]
fn textpart_extracts_text_from_picture() {
    let mut interp = TestInterp::new();
    interp.run(r#"picture p; p = "hello" infont "cmr10"; show textpart p;"#);
    let msg = interp.first_show();
    assert!(msg.contains("hello"), "expected hello in: {msg}");
}

#[test]
fn fontpart_extracts_font_from_picture() {
    let mut interp = TestInterp::new();
    interp.run(r#"picture p; p = "abc" infont "cmr10"; show fontpart p;"#);
    let msg = interp.first_show();
    assert!(msg.contains("cmr10"), "expected cmr10 in: {msg}");
}

#[test]
fn textpart_returns_empty_for_non_text_picture() {
    let mut interp = TestInterp::new();
    interp.run("picture p; addto p contour ((0,0)..(1,0)..(1,1)..cycle); show textpart p;");
    let msg = interp.first_show();
    // Empty string shows as ""
    assert!(msg.contains("\"\""), "expected empty string in: {msg}");
}

#[test]
fn pathpart_extracts_path_from_fill() {
    let mut interp = TestInterp::new();
    interp.run("picture p; addto p contour ((0,0)..(1,0)..(1,1)..cycle); show pathpart p;");
    let msg = interp.first_show();
    // Should show a path, not an error
    assert!(
        !msg.contains("Unimplemented"),
        "pathpart should not error: {msg}"
    );
}

#[test]
fn penpart_returns_pen_for_stroke() {
    let mut interp = TestInterp::new();
    interp.run("picture p; addto p doublepath ((0,0)..(10,0)); show penpart p;");
    let msg = interp.first_show();
    assert!(
        !msg.contains("Unimplemented"),
        "penpart should not error: {msg}"
    );
}

#[test]
fn dashpart_returns_picture_for_stroke() {
    let mut interp = TestInterp::new();
    interp.run("picture p; addto p doublepath ((0,0)..(10,0)); show dashpart p;");
    let msg = interp.first_show();
    assert!(
        !msg.contains("Unimplemented"),
        "dashpart should not error: {msg}"
    );
}

#[test]
fn dashpattern_basic() {
    let mut interp = TestInterp::new();
    interp.run(
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
    );
    // Should produce a picture, not a "Cannot transform" error
    let errors = interp.errors();
    for e in &errors {
        eprintln!("  dashpattern error: {}", e.message);
    }
    assert!(errors.is_empty(), "dashpattern had {} errors", errors.len());
}

#[test]
fn dashed_line_produces_dash_pattern() {
    // Verify that `dashed dashpattern(...)` applies stroke-dasharray to the
    // output picture and doesn't leak intermediate strokes.
    let mut interp = TestInterp::new();
    interp.run(
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
    );

    interp.assert_no_errors();

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
    let mut interp = TestInterp::new();
    interp.run(
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
    );

    interp.assert_no_errors();

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

// -----------------------------------------------------------------------
// btex/etex and infont
// -----------------------------------------------------------------------

#[test]
fn btex_etex_produces_picture() {
    // btex ... etex should produce a picture capsule (not a string).
    let mut interp = TestInterp::new();
    interp.run(r#"picture p; p = btex Hello World etex; show p;"#);
    let msg = interp.first_show();
    assert!(
        msg.contains("(picture)"),
        "expected picture type in show output: {msg}"
    );
}

#[test]
fn btex_etex_picture_is_transformable() {
    // btex...etex result can be shifted without error, since it's a picture.
    let mut interp = TestInterp::new();
    interp.run("picture p; p = btex test etex shifted (10,20);");
    let errors: Vec<_> = interp
        .interp
        .state
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
    let mut interp = TestInterp::with_plain_mp();
    interp.run("input plain; beginfig(1); draw btex Q etex shifted (5,5); endfig; end;");
    let errors: Vec<_> = interp
        .interp
        .state
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
    let mut interp = TestInterp::new();
    interp.run(r#"picture p; p = "abc" infont "cmr10"; show p;"#);
    // The show output should indicate a picture value
    let msg = interp.first_show();
    // A picture show typically shows the type or contents
    assert!(
        !msg.contains("error"),
        "infont should not produce an error: {msg}"
    );
}

#[test]
fn infont_text_has_bbox() {
    // Corner operators on an infont picture should give non-zero bbox
    let mut interp = TestInterp::new();
    interp.run(r#"picture p; p = "Hello" infont "cmr10"; show lrcorner p;"#);
    let msg = interp.first_show();
    // lrcorner should have positive x and negative y (descender)
    assert!(msg.contains(','), "expected a pair in: {msg}");
}

#[test]
fn corner_operators_on_picture() {
    // Test all four corners on a simple filled picture
    let mut interp = TestInterp::new();
    interp.run("picture p; p = \"test\" infont \"cmr10\"; show llcorner p; show urcorner p;");
    let infos = interp.shows();
    assert_eq!(infos.len(), 2, "expected 2 corner values, got: {infos:?}");
}

#[test]
fn corner_operators_on_path() {
    // Corner operators should work on paths too
    let mut interp = TestInterp::new();
    interp.run("path p; p = (0,0)..(10,20)..(30,5); show llcorner p; show urcorner p;");
    let infos = interp.shows();
    assert_eq!(infos.len(), 2, "expected 2 corner values, got: {infos:?}");
}

#[test]
fn addto_defaults_to_currentpicture_when_name_omitted() {
    let mut interp = TestInterp::new();
    interp.run("addto contour ((0,0)..(1,0)..(1,1)..cycle);");

    interp.assert_no_errors();

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
    let mut interp = TestInterp::new();
    interp.run(
        "addto contour ((0,0)..(1,0)..(1,1)..cycle); \
             clip to ((-1,-1)..(2,-1)..(2,2)..(-1,2)..cycle);",
    );

    interp.assert_no_errors();

    let objs = &interp.current_picture().objects;
    assert_eq!(objs.len(), 1);
    if let postmeta_graphics::types::GraphicsObject::Picture(nested) = &objs[0] {
        assert!(nested.clip_path.is_some());
    } else {
        panic!("Expected Picture");
    }
}

#[test]
fn refactor_guard_currentpicture_roundtrip_assignment_stays_stable() {
    let mut interp = TestInterp::new();
    interp.run("addto contour ((0,0)..(1,0)..(1,1)..cycle);");
    let original_picture = interp.current_picture().clone();
    assert!(
        !original_picture.objects.is_empty(),
        "precondition: currentpicture should be non-empty before roundtrip"
    );

    interp.run(
        "picture snap; \
             snap := currentpicture; \
             currentpicture := nullpicture; \
             currentpicture := snap;",
    );

    interp.assert_no_errors();

    assert!(
        interp.current_picture().objects.is_empty(),
        "current semantics are stable: after `snap := currentpicture; currentpicture := nullpicture; currentpicture := snap;`, currentpicture remains nullpicture"
    );
}

#[test]
fn shipout_non_picture_reports_type_error() {
    let mut interp = TestInterp::new();
    interp.run("shipout 123;");

    let errors = interp.errors();
    assert!(
        errors
            .iter()
            .any(|e| e.kind == crate::error::ErrorKind::TypeError),
        "expected type error for non-picture shipout, got: {errors:?}"
    );
    assert!(interp.output().is_empty(), "shipout must not emit output");
}

#[test]
fn addto_picture_target_accepts_symbolic_suffixes() {
    let mut interp = TestInterp::new();
    interp.run("picture pic.layer; addto pic.layer contour ((0,0)..(1,0)..(1,1)..cycle);");

    let layer_id = interp
        .interp
        .state
        .variables
        .lookup_existing("pic.layer")
        .expect("pic.layer should exist");
    let layer_pic = match interp.interp.state.variables.get(layer_id) {
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
    let mut interp = TestInterp::new();
    interp.run(
        "picture pic.layer; \
             addto pic.layer contour ((0,0)..(1,0)..(1,1)..cycle); \
             clip pic.layer to ((-1,-1)..(2,-1)..(2,2)..(-1,2)..cycle);",
    );

    let layer_id = interp
        .interp
        .state
        .variables
        .lookup_existing("pic.layer")
        .expect("pic.layer should exist");
    let layer_pic = match interp.interp.state.variables.get(layer_id) {
        crate::variables::VarValue::Known(Value::Picture(p)) => p,
        other => panic!("pic.layer should be picture, got {other:?}"),
    };

    assert_eq!(layer_pic.objects.len(), 1);
    if let postmeta_graphics::types::GraphicsObject::Picture(nested) = &layer_pic.objects[0] {
        assert!(nested.clip_path.is_some());
    } else {
        panic!("Expected Picture");
    }
}

// -----------------------------------------------------------------------
// verbatimtex ... etex
// -----------------------------------------------------------------------

#[test]
fn verbatimtex_is_skipped() {
    // verbatimtex ... etex should be silently skipped without errors.
    let mut interp = TestInterp::new();
    interp.run(r#"verbatimtex \documentstyle{article} \begin{document} etex show 42;"#);
    // The `show 42` after etex should execute normally.
    assert!(
        interp
            .interp
            .state
            .errors
            .iter()
            .any(|e| e.message.contains("42")),
        "show 42 should produce output after verbatimtex block"
    );
    // No errors about unexpected tokens from the TeX content.
    interp.assert_no_errors();
}

// -----------------------------------------------------------------------
// for ... within (picture iteration)
// -----------------------------------------------------------------------

#[test]
fn for_within_iterates_picture_components() {
    // Build a picture with two strokes, iterate with `for ... within`.
    // Use `..` (primitive path join) instead of `--` (plain.mp macro).
    let mut interp = TestInterp::new();
    interp.run(
        "picture pic; pic := nullpicture;
             addto pic doublepath (0,0)..(1,1);
             addto pic doublepath (2,2)..(3,3);
             numeric n; n := 0;
             for q within pic: n := n + 1; endfor
             show n;",
    );
    assert!(
        interp
            .interp
            .state
            .errors
            .iter()
            .any(|e| e.message.contains("2")),
        "should iterate over 2 components"
    );
}

#[test]
fn for_within_extracts_pathpart() {
    // Iterate and extract pathpart from each component.
    // Use `..` (primitive path join) instead of `--` (plain.mp macro).
    let mut interp = TestInterp::new();
    interp.run(
        "picture pic; pic := nullpicture;
             addto pic doublepath (10,20)..(30,40);
             for q within pic:
               show xpart point 0 of pathpart q;
               exitif true;
             endfor",
    );
    assert!(
        interp
            .interp
            .state
            .errors
            .iter()
            .any(|e| e.message.contains("10")),
        "pathpart should yield the original path's first point x=10"
    );
}

#[test]
fn for_within_empty_picture() {
    // Iterating over an empty picture should execute zero iterations.
    let mut interp = TestInterp::new();
    interp.run(
        "picture pic; pic := nullpicture;
             numeric n; n := 0;
             for q within pic: n := n + 1; endfor
             show n;",
    );
    assert!(
        interp
            .interp
            .state
            .errors
            .iter()
            .any(|e| e.message.contains("0")),
        "empty picture should produce 0 iterations"
    );
}

// -----------------------------------------------------------------------
// Picture part extraction on picture values
// -----------------------------------------------------------------------

#[test]
fn xxpart_of_text_picture() {
    // xxpart of a btex picture should return the xx component of the text transform.
    // For default btex output, the transform is identity, so xxpart = 1.
    let mut interp = TestInterp::new();
    interp.run("picture p; p = btex X etex; show xxpart p;");
    assert!(
        interp
            .interp
            .state
            .errors
            .iter()
            .any(|e| e.message.contains("1")),
        "xxpart of btex picture should be 1 (identity transform)"
    );
}

#[test]
fn colormodel_of_stroke() {
    // colormodel of an RGB stroked picture should return 5.
    // Use `..` (primitive path join) instead of `--` (plain.mp macro).
    let mut interp = TestInterp::new();
    interp.run(
        "picture pic; pic := nullpicture;
             addto pic doublepath (0,0)..(1,1) withcolor (1,0,0);
             for q within pic: show colormodel q; exitif true; endfor",
    );
    assert!(
        interp
            .interp
            .state
            .errors
            .iter()
            .any(|e| e.message.contains("5")),
        "colormodel of RGB stroke should be 5"
    );
}

#[test]
fn redpart_of_picture_component() {
    // redpart of a picture component should extract the red channel.
    // Use `..` (primitive path join) instead of `--` (plain.mp macro).
    let mut interp = TestInterp::new();
    interp.run(
        "picture pic; pic := nullpicture;
             addto pic doublepath (0,0)..(1,1) withcolor (0.75, 0.5, 0.25);
             for q within pic: show redpart q; exitif true; endfor",
    );
    assert!(
        interp
            .interp
            .state
            .errors
            .iter()
            .any(|e| e.message.contains("0.75")),
        "redpart should extract 0.75"
    );
}

#[test]
fn stroked_filled_textual_predicates() {
    // Use `..` (primitive path join) instead of `--` (plain.mp macro).
    let mut interp = TestInterp::new();
    interp.run(
        "picture pic; pic := nullpicture;
             addto pic doublepath (0,0)..(1,1);
             for q within pic:
               show stroked q;
               show filled q;
               show textual q;
               exitif true;
             endfor",
    );
    // stroked should be true, filled/textual should be false.
    let msgs: Vec<_> = interp
        .interp
        .state
        .errors
        .iter()
        .map(|e| &e.message)
        .collect();
    assert!(
        msgs.iter().any(|m| m.contains("true")),
        "stroked should be true: {msgs:?}"
    );
    // The two false results
    let false_count = msgs.iter().filter(|m| m.contains("false")).count();
    assert_eq!(
        false_count, 2,
        "filled and textual should be false: {msgs:?}"
    );
}
