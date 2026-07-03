//! String literals, operators, `str`, `substring`, and comparisons.

use super::helpers::TestInterp;

#[test]
fn eval_string() {
    let mut interp = TestInterp::new();
    interp.run("show \"hello\";");
    let msg = interp.first_show();
    assert!(msg.contains("hello"), "expected hello in: {msg}");
}

#[test]
fn eval_string_concat() {
    let mut interp = TestInterp::new();
    interp.run("show \"hello\" & \" world\";");
    let msg = interp.first_show();
    assert!(
        msg.contains("hello world"),
        "expected 'hello world' in: {msg}"
    );
}

#[test]
fn chained_string_concat() {
    let mut interp = TestInterp::new();
    interp.run("show \"a\" & \"b\" & \"c\" & \"d\";");
    let msg = interp.first_show();
    assert!(msg.contains("abcd"), "expected 'abcd' in: {msg}");
}

#[test]
fn charexists_valid_code() {
    let mut interp = TestInterp::new();
    interp.run("show charexists 65;");
    let msg = interp.first_show();
    assert!(msg.contains("true"), "expected true in: {msg}");
}

#[test]
fn charexists_out_of_range() {
    let mut interp = TestInterp::new();
    interp.run("show charexists 256;");
    let msg = interp.first_show();
    assert!(msg.contains("false"), "expected false in: {msg}");
}

#[test]
fn charexists_negative() {
    let mut interp = TestInterp::new();
    interp.run("show charexists -1;");
    let msg = interp.first_show();
    assert!(msg.contains("false"), "expected false in: {msg}");
}

#[test]
fn fontsize_returns_ten() {
    let mut interp = TestInterp::new();
    interp.run(r#"show fontsize "cmr10";"#);
    let msg = interp.first_show();
    assert!(msg.contains("10"), "expected 10 in: {msg}");
}

// -----------------------------------------------------------------------
// Str operator
// -----------------------------------------------------------------------

#[test]
fn str_operator() {
    let mut interp = TestInterp::new();
    interp.run("show str x;");
    let msg = interp.first_show();
    assert!(msg.contains("x"), "expected x in: {msg}");
}

#[test]
fn str_operator_multi_char() {
    let mut interp = TestInterp::new();
    interp.run("show str foo;");
    let msg = interp.first_show();
    assert!(msg.contains("foo"), "expected foo in: {msg}");
}

#[test]
fn str_operator_collects_suffix_chain() {
    let mut interp = TestInterp::new();
    interp.run("show str foo.bar.baz;");
    let msg = interp.first_show();
    assert!(
        msg.contains("foo.bar.baz"),
        "expected suffix chain in: {msg}"
    );
}

#[test]
fn str_operator_collects_subscript_suffix() {
    let mut interp = TestInterp::new();
    interp.run("show str z[1+1].x;");
    let msg = interp.first_show();
    assert!(
        msg.contains("z[2].x"),
        "expected subscript suffix in: {msg}"
    );
}

// -----------------------------------------------------------------------
// Substring reclassification (primary binary: substring X of Y)
// -----------------------------------------------------------------------

#[test]
fn substring_of_basic() {
    // substring (1,3) of "hello" = "el"
    let mut interp = TestInterp::new();
    interp.run(r#"show substring (1,3) of "hello";"#);
    let msg = interp.first_show();
    assert!(msg.contains("el"), "expected 'el' in: {msg}");
}

#[test]
fn substring_of_full_range() {
    // substring (0,5) of "hello" = "hello"
    let mut interp = TestInterp::new();
    interp.run(r#"show substring (0,5) of "hello";"#);
    let msg = interp.first_show();
    assert!(msg.contains("hello"), "expected 'hello' in: {msg}");
}

#[test]
fn substring_of_empty() {
    // substring (2,2) of "hello" = ""
    let mut interp = TestInterp::new();
    interp.run(r#"show substring (2,2) of "hello";"#);
    let msg = interp.first_show();
    // Empty string shows as ""
    assert!(
        msg.contains("\"\"") || msg.contains(">>  ") || msg.ends_with(">> "),
        "expected empty string in: {msg}"
    );
}

#[test]
fn substring_of_utf8_is_char_boundary_safe() {
    // Regression: substring used byte slicing and could panic on UTF-8.
    let mut interp = TestInterp::new();
    interp.run("show substring (1,2) of \"a😊b\";");
    let msg = interp.first_show();
    assert!(msg.contains("😊"), "expected emoji substring in: {msg}");
}

#[test]
fn length_of_utf8_counts_characters() {
    let mut interp = TestInterp::new();
    interp.run("show length \"a😊b\";");
    let msg = interp.first_show();
    assert!(msg.contains('3'), "expected length 3 in: {msg}");
}

// -----------------------------------------------------------------------
// String comparison operators
// -----------------------------------------------------------------------

#[test]
fn string_less_than() {
    let mut interp = TestInterp::new();
    interp.run(r#"show "a" < "b";"#);
    let msg = interp.first_show();
    assert!(msg.contains("true"), "expected true in: {msg}");
}

#[test]
fn string_greater_than() {
    let mut interp = TestInterp::new();
    interp.run(r#"show "z" > "a";"#);
    let msg = interp.first_show();
    assert!(msg.contains("true"), "expected true in: {msg}");
}

#[test]
fn string_less_equal() {
    let mut interp = TestInterp::new();
    interp.run(r#"show "abc" <= "abd";"#);
    let msg = interp.first_show();
    assert!(msg.contains("true"), "expected true in: {msg}");
}

#[test]
fn string_greater_equal_same() {
    let mut interp = TestInterp::new();
    interp.run(r#"show "abc" >= "abc";"#);
    let msg = interp.first_show();
    assert!(msg.contains("true"), "expected true in: {msg}");
}

#[test]
fn string_comparison_false() {
    let mut interp = TestInterp::new();
    interp.run(r#"show "b" < "a";"#);
    let msg = interp.first_show();
    assert!(msg.contains("false"), "expected false in: {msg}");
}

#[test]
fn str_fractional_subscript_matches_variable_identity() {
    // The str operator and variable-key formatting share one subscript
    // formatter: fractional subscripts keep their decimals.
    let mut interp = TestInterp::new();
    interp.run("numeric a[]; show str a[0.5];");
    assert!(
        interp.first_show().contains("a[0.5]"),
        "expected a[0.5] in: {}",
        interp.first_show()
    );
}
