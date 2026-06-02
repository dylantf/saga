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
