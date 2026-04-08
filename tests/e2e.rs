/// Integration test that runs the e2e feature tests via `dylang test`.
/// These tests exercise core language features end-to-end (parse -> typecheck
/// -> elaborate -> lower -> BEAM), catching regressions that unit tests miss.
#[test]
fn e2e_test_suite() {
    use std::io::Read;

    let binary = env!("CARGO_BIN_EXE_dylang");
    let project_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/e2e");
    let timeout = std::time::Duration::from_secs(45);

    let mut child = std::process::Command::new(binary)
        .arg("test")
        .current_dir(&project_dir)
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .expect("failed to run dylang test");

    let deadline = std::time::Instant::now() + timeout;
    let status = loop {
        if let Some(status) = child.try_wait().expect("failed while waiting for dylang test") {
            break status;
        }
        if std::time::Instant::now() >= deadline {
            let _ = child.kill();
            let _ = child.wait();
            panic!("e2e tests timed out after {}s", timeout.as_secs());
        }
        std::thread::sleep(std::time::Duration::from_millis(50));
    };

    let mut stdout = Vec::new();
    let mut stderr = Vec::new();
    child
        .stdout
        .take()
        .expect("missing dylang test stdout")
        .read_to_end(&mut stdout)
        .expect("failed reading dylang test stdout");
    child
        .stderr
        .take()
        .expect("missing dylang test stderr")
        .read_to_end(&mut stderr)
        .expect("failed reading dylang test stderr");

    let stdout = String::from_utf8_lossy(&stdout);
    let stderr = String::from_utf8_lossy(&stderr);

    print!("{stdout}");
    if !stderr.is_empty() {
        eprint!("{stderr}");
    }

    assert!(
        status.success(),
        "e2e tests failed:\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}
