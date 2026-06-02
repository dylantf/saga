#[test]
fn selective_core_lowers_imported_cps_adapter_call() {
    let binary = env!("CARGO_BIN_EXE_saga");
    let project_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("examples/optimization/selective-uniform/imported-cps-island-project");

    let output = std::process::Command::new(binary)
        .current_dir(&project_dir)
        .args(["inspect", "src/Main.saga", "--stage", "selective-core"])
        .output()
        .expect("run saga inspect selective-core");

    assert!(
        output.status.success(),
        "saga inspect failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("'read_plus_two'/3"), "{stdout}");
    assert!(
        stdout.contains(
            "call 'effects':'read_value'\n        ('unit', _Evidence, fun (_CpsBindArg0) ->"
        ),
        "{stdout}"
    );
    assert!(stdout.contains("let <Value>"), "{stdout}");
    assert!(
        stdout.contains("apply _ReturnK(call 'erlang':'+'"),
        "{stdout}"
    );
}

#[test]
fn selective_core_codegen_runs_handler_finally_fixtures() {
    let binary = env!("CARGO_BIN_EXE_saga");
    let manifest_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));

    let resume_fixture = manifest_dir
        .join("examples/optimization/selective-uniform/28-handler-finally-resume-e2e.saga");
    let resume_output = std::process::Command::new(binary)
        .current_dir(&manifest_dir)
        .args([
            "run",
            resume_fixture.to_str().expect("utf-8 fixture path"),
            "--selective-codegen",
        ])
        .output()
        .expect("run selective finally resume fixture");
    assert!(
        resume_output.status.success(),
        "saga run failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&resume_output.stdout),
        String::from_utf8_lossy(&resume_output.stderr)
    );
    let resume_stdout = String::from_utf8_lossy(&resume_output.stdout);
    assert!(
        resume_stdout.contains("body\ncleanup\nafter\n"),
        "{resume_stdout}"
    );

    let abort_fixture = manifest_dir
        .join("examples/optimization/selective-uniform/29-handler-finally-abort-e2e.saga");
    let abort_output = std::process::Command::new(binary)
        .current_dir(&manifest_dir)
        .args([
            "run",
            abort_fixture.to_str().expect("utf-8 fixture path"),
            "--selective-codegen",
        ])
        .output()
        .expect("run selective finally abort fixture");
    assert!(
        abort_output.status.success(),
        "saga run failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&abort_output.stdout),
        String::from_utf8_lossy(&abort_output.stderr)
    );
    let abort_stdout = String::from_utf8_lossy(&abort_output.stdout);
    assert!(abort_stdout.contains("cleanup\nafter\n"), "{abort_stdout}");
    assert!(!abort_stdout.contains("body\n"), "{abort_stdout}");
}

#[test]
fn selective_core_codegen_runs_higher_order_direct_callback_fixture() {
    let binary = env!("CARGO_BIN_EXE_saga");
    let manifest_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let fixture = manifest_dir
        .join("examples/optimization/selective-uniform/32-higher-order-direct-callback-e2e.saga");

    let output = std::process::Command::new(binary)
        .current_dir(&manifest_dir)
        .args([
            "run",
            fixture.to_str().expect("utf-8 fixture path"),
            "--selective-codegen",
        ])
        .output()
        .expect("run selective higher-order direct callback fixture");
    assert!(
        output.status.success(),
        "saga run failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("ok\n"), "{stdout}");
}
