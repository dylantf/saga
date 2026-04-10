/// Integration test that runs the stdlib test suite via `saga test`.
/// This compiles and executes .saga test files on the BEAM, providing
/// end-to-end coverage of the standard library.
#[test]
fn stdlib_test_suite() {
    let binary = env!("CARGO_BIN_EXE_saga");
    let project_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/stdlib");

    let output = std::process::Command::new(binary)
        .arg("test")
        .current_dir(&project_dir)
        .output()
        .expect("failed to run saga test");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    // Print test runner output (visible with `cargo test -- --nocapture`)
    print!("{stdout}");
    if !stderr.is_empty() {
        eprint!("{stderr}");
    }

    assert!(
        output.status.success(),
        "stdlib tests failed:\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}
