/// Integration test that runs the e2e feature tests via `dylang test`.
/// These tests exercise core language features end-to-end (parse -> typecheck
/// -> elaborate -> lower -> BEAM), catching regressions that unit tests miss.
#[test]
fn e2e_test_suite() {
    let binary = env!("CARGO_BIN_EXE_dylang");
    let project_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/e2e");

    let output = std::process::Command::new(binary)
        .arg("test")
        .current_dir(&project_dir)
        .output()
        .expect("failed to run dylang test");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    print!("{stdout}");
    if !stderr.is_empty() {
        eprint!("{stderr}");
    }

    assert!(
        output.status.success(),
        "e2e tests failed:\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}
