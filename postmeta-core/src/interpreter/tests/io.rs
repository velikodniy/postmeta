//! The `input` statement and the FileSystem trait wiring.

use crate::interpreter::Interpreter;

use super::helpers::TestInterp;

#[test]
fn eval_input_file_not_found() {
    let mut interp = TestInterp::new();
    // Should report error but not crash
    interp.run("input nonexistent;");
    assert!(
        interp
            .interp
            .state
            .errors
            .iter()
            .any(|e| e.message.contains("not found")),
        "expected file-not-found error: {:?}",
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
        .state
        .errors
        .iter()
        .find(|e| e.message.contains(">>"))
        .map(|e| &e.message);
    assert!(
        show_msg.is_some() && show_msg.unwrap().contains("31"),
        "expected show 31, got: {:?}",
        interp
            .state
            .errors
            .iter()
            .map(|e| &e.message)
            .collect::<Vec<_>>()
    );
}
