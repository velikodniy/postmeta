use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::time::{SystemTime, UNIX_EPOCH};

struct TestDir {
    path: PathBuf,
}

impl TestDir {
    fn new(tag: &str) -> Self {
        let ts = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_or(0, |d| d.as_nanos());
        let path =
            std::env::temp_dir().join(format!("postmeta_cli_{tag}_{}_{}", std::process::id(), ts));
        fs::create_dir_all(&path).expect("create temp test dir");
        Self { path }
    }
}

impl Drop for TestDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

fn run_postmeta(args: &[&str], cwd: &Path) -> Output {
    Command::new(env!("CARGO_BIN_EXE_postmeta"))
        .args(args)
        .current_dir(cwd)
        .output()
        .expect("run postmeta")
}

#[test]
fn eval_expression_prints_show_output() {
    let dir = TestDir::new("eval_show");
    let output = run_postmeta(&["-e", "show 42; end;"], &dir.path);

    assert!(output.status.success(), "process failed: {output:?}");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains(">> 42"),
        "expected show output in stdout, got: {stdout}"
    );
}

#[test]
fn file_input_writes_svg_to_output_dir() {
    let dir = TestDir::new("file_svg");
    let source_file = dir.path.join("sample.mp");
    fs::write(
        &source_file,
        "delimiters (); addto currentpicture doublepath (0,0)..(10,10);",
    )
    .expect("write sample mp file");

    let out_dir = dir.path.join("out");
    fs::create_dir_all(&out_dir).expect("create output dir");

    let output = run_postmeta(&["sample.mp", "-o", "out"], &dir.path);
    assert!(output.status.success(), "process failed: {output:?}");

    let svg_path = out_dir.join("sample.svg");
    assert!(svg_path.is_file(), "expected output file at {svg_path:?}");
    let svg = fs::read_to_string(svg_path).expect("read svg output");
    assert!(svg.contains("<svg"), "expected svg root element");
    assert!(svg.contains("path"), "expected rendered path element");
}

#[test]
fn plain_mp_loads_and_eval_continues() {
    let dir = TestDir::new("plain_eval");
    let workspace_root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("workspace root from crate dir");
    let plain_src = workspace_root.join("lib/plain.mp");
    let plain_dst = dir.path.join("plain.mp");
    fs::copy(&plain_src, &plain_dst).expect("copy plain.mp into test dir");

    let output = run_postmeta(&["-e", "input plain; show 42; end;"], &dir.path);

    assert!(output.status.success(), "process failed: {output:?}");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains(">> 42"),
        "expected show output after input plain, got: {stdout}"
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !stderr.contains("Error:"),
        "did not expect runtime errors, got stderr: {stderr}"
    );
}
