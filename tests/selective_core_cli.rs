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

#[test]
fn selective_core_no_fallback_cli_rejects_private_unplanned_function() {
    let binary = env!("CARGO_BIN_EXE_saga");
    let manifest_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let fixture = manifest_dir
        .join("examples/optimization/selective-uniform/33-no-fallback-private-unplanned.saga");

    let permissive = std::process::Command::new(binary)
        .current_dir(&manifest_dir)
        .args([
            "inspect",
            fixture.to_str().expect("utf-8 fixture path"),
            "--stage",
            "selective-core",
        ])
        .output()
        .expect("inspect permissive selective-core fixture");
    assert!(
        permissive.status.success(),
        "saga inspect failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&permissive.stdout),
        String::from_utf8_lossy(&permissive.stderr)
    );

    let strict = std::process::Command::new(binary)
        .current_dir(&manifest_dir)
        .args([
            "inspect",
            fixture.to_str().expect("utf-8 fixture path"),
            "--stage",
            "selective-core",
            "--selective-no-fallback",
        ])
        .output()
        .expect("inspect strict selective-core fixture");
    assert!(
        !strict.status.success(),
        "strict saga inspect should fail\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&strict.stdout),
        String::from_utf8_lossy(&strict.stderr)
    );
    let stderr = String::from_utf8_lossy(&strict.stderr);
    assert!(
        stderr.contains("function 'hidden' has no selective lowering plan with fallback disabled"),
        "{stderr}"
    );
}

#[test]
fn selective_core_codegen_runs_imported_higher_order_direct_callback_project() {
    let binary = env!("CARGO_BIN_EXE_saga");
    let project_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("examples/optimization/selective-uniform/imported-direct-callback-project");

    let inspect = std::process::Command::new(binary)
        .current_dir(&project_dir)
        .args(["inspect", "src/Main.saga", "--stage", "selective-core"])
        .output()
        .expect("inspect imported higher-order direct callback project");
    assert!(
        inspect.status.success(),
        "saga inspect failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&inspect.stdout),
        String::from_utf8_lossy(&inspect.stderr)
    );
    let inspect_stdout = String::from_utf8_lossy(&inspect.stdout);
    assert!(
        inspect_stdout.contains("call 'erlang':'make_fun'\n          ('helper', 'inc', 1)"),
        "{inspect_stdout}"
    );
    assert!(
        inspect_stdout.contains("apply 'apply_it'/1(call 'erlang':'make_fun'"),
        "{inspect_stdout}"
    );

    let run = std::process::Command::new(binary)
        .current_dir(&project_dir)
        .args(["run", "--selective-codegen"])
        .output()
        .expect("run imported higher-order direct callback project");
    assert!(
        run.status.success(),
        "saga run failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&run.stdout),
        String::from_utf8_lossy(&run.stderr)
    );
    let run_stdout = String::from_utf8_lossy(&run.stdout);
    assert!(run_stdout.contains("ok\n"), "{run_stdout}");
}

#[test]
fn selective_core_codegen_runs_imported_cps_callback_project() {
    let binary = env!("CARGO_BIN_EXE_saga");
    let project_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("examples/optimization/selective-uniform/imported-cps-callback-project");

    let monadic = std::process::Command::new(binary)
        .current_dir(&project_dir)
        .args(["inspect", "src/Main.saga", "--stage", "monadic"])
        .output()
        .expect("inspect imported CPS callback project monadic IR");
    assert!(
        monadic.status.success(),
        "saga inspect monadic failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&monadic.stdout),
        String::from_utf8_lossy(&monadic.stderr)
    );
    let monadic_stdout = String::from_utf8_lossy(&monadic.stdout);
    assert!(monadic_stdout.contains("bind f#"), "{monadic_stdout}");
    assert!(monadic_stdout.contains("bind g#"), "{monadic_stdout}");
    assert!(
        monadic_stdout.contains("Pure(Var(read_value"),
        "{monadic_stdout}"
    );
    assert!(
        monadic_stdout.contains("Pure(Var(pure_value"),
        "{monadic_stdout}"
    );
    assert!(
        monadic_stdout.contains("case Var(choose#"),
        "{monadic_stdout}"
    );
    assert!(
        monadic_stdout.contains("App(Var(apply_eff#"),
        "{monadic_stdout}"
    );
    assert!(monadic_stdout.contains("[Var(g#"), "{monadic_stdout}");

    let inspect = std::process::Command::new(binary)
        .current_dir(&project_dir)
        .args(["inspect", "src/Main.saga", "--stage", "selective-core"])
        .output()
        .expect("inspect imported CPS callback project selective Core");
    assert!(
        inspect.status.success(),
        "saga inspect selective-core failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&inspect.stdout),
        String::from_utf8_lossy(&inspect.stderr)
    );
    let inspect_stdout = String::from_utf8_lossy(&inspect.stdout);
    assert!(
        inspect_stdout.contains("call 'effects':'apply_eff'"),
        "{inspect_stdout}"
    );
    assert!(
        inspect_stdout.contains("fun (_CpsFnArg"),
        "{inspect_stdout}"
    );
    assert!(
        inspect_stdout.contains("call 'effects':'read_value'"),
        "{inspect_stdout}"
    );
    assert!(
        inspect_stdout.contains("call 'effects':'pure_value'"),
        "{inspect_stdout}"
    );
    assert!(
        inspect_stdout.contains("fun (_PureCpsArg"),
        "{inspect_stdout}"
    );
    assert!(
        inspect_stdout.contains("apply _PureCpsK"),
        "{inspect_stdout}"
    );
    assert!(
        inspect_stdout.contains("case Choose of"),
        "{inspect_stdout}"
    );
    assert!(!inspect_stdout.contains("make_fun"), "{inspect_stdout}");

    let effects_inspect = std::process::Command::new(binary)
        .current_dir(&project_dir)
        .args(["inspect", "src/Effects.saga", "--stage", "selective-core"])
        .output()
        .expect("inspect imported CPS callback effects module selective Core");
    assert!(
        effects_inspect.status.success(),
        "saga inspect Effects selective-core failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&effects_inspect.stdout),
        String::from_utf8_lossy(&effects_inspect.stderr)
    );
    let effects_stdout = String::from_utf8_lossy(&effects_inspect.stdout);
    assert!(
        effects_stdout.contains("'apply_eff'/3")
            && effects_stdout.contains("let <G>")
            && effects_stdout.contains("apply G('unit', _Evidence, _ReturnK)"),
        "{effects_stdout}"
    );

    let run = std::process::Command::new(binary)
        .current_dir(&project_dir)
        .args(["run", "--selective-codegen"])
        .output()
        .expect("run imported CPS callback project");
    assert!(
        run.status.success(),
        "saga run failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&run.stdout),
        String::from_utf8_lossy(&run.stderr)
    );
    let run_stdout = String::from_utf8_lossy(&run.stdout);
    assert!(run_stdout.contains("ok\n"), "{run_stdout}");
}

#[test]
fn selective_core_specializes_imported_static_handler_project() {
    let binary = env!("CARGO_BIN_EXE_saga");
    let project_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(
        "examples/optimization/selective-uniform/imported-static-handler-specialization-project",
    );

    let inspect = std::process::Command::new(binary)
        .current_dir(&project_dir)
        .args(["inspect", "src/Main.saga", "--stage", "selective-core"])
        .output()
        .expect("inspect imported static handler specialization project");
    assert!(
        inspect.status.success(),
        "saga inspect failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&inspect.stdout),
        String::from_utf8_lossy(&inspect.stderr)
    );
    let inspect_stdout = String::from_utf8_lossy(&inspect.stdout);
    assert!(
        !inspect_stdout.contains("call 'effects':'query'"),
        "{inspect_stdout}"
    );
    assert!(
        !inspect_stdout.contains("call 'std_evidence_bridge':'insert_canonical'"),
        "{inspect_stdout}"
    );
    assert!(inspect_stdout.contains("let <Config>"), "{inspect_stdout}");
    assert!(inspect_stdout.contains("let <Value>"), "{inspect_stdout}");
    assert!(
        inspect_stdout.contains("call 'erlang':'+'"),
        "{inspect_stdout}"
    );

    let run = std::process::Command::new(binary)
        .current_dir(&project_dir)
        .args(["run", "--selective-codegen"])
        .output()
        .expect("run imported static handler specialization project");
    assert!(
        run.status.success(),
        "saga run failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&run.stdout),
        String::from_utf8_lossy(&run.stderr)
    );
    let run_stdout = String::from_utf8_lossy(&run.stdout);
    assert!(run_stdout.contains("ok\n"), "{run_stdout}");
}

#[test]
fn selective_core_codegen_runs_imported_effectful_trait_project() {
    let binary = env!("CARGO_BIN_EXE_saga");
    let project_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("examples/optimization/selective-uniform/imported-effectful-trait-project");

    let lib_inspect = std::process::Command::new(binary)
        .current_dir(&project_dir)
        .args(["inspect", "src/Lib.saga", "--stage", "selective-core"])
        .output()
        .expect("inspect imported effectful trait lib selective Core");
    assert!(
        lib_inspect.status.success(),
        "saga inspect Lib selective-core failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&lib_inspect.stdout),
        String::from_utf8_lossy(&lib_inspect.stderr)
    );
    let lib_stdout = String::from_utf8_lossy(&lib_inspect.stdout);
    assert!(
        lib_stdout
            .contains("'__dict_Lib_Encodable_Std_Int_Int'/0, '__dict_Lib_Encodable_Lib_Boxed'/1"),
        "{lib_stdout}"
    );
    assert!(
        lib_stdout.contains("apply ___anf_v1(Value, _LambdaEvidence"),
        "{lib_stdout}"
    );

    let main_inspect = std::process::Command::new(binary)
        .current_dir(&project_dir)
        .args(["inspect", "src/Main.saga", "--stage", "selective-core"])
        .output()
        .expect("inspect imported effectful trait main selective Core");
    assert!(
        main_inspect.status.success(),
        "saga inspect Main selective-core failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&main_inspect.stdout),
        String::from_utf8_lossy(&main_inspect.stderr)
    );
    let main_stdout = String::from_utf8_lossy(&main_inspect.stdout);
    assert!(
        main_stdout.contains("call 'lib':'__dict_Lib_Encodable_lib_Std_Int_Int'"),
        "{main_stdout}"
    );
    assert!(
        main_stdout.contains("call 'lib':'__dict_Lib_Encodable_lib_Lib_Boxed'"),
        "{main_stdout}"
    );
    assert!(
        main_stdout.contains("apply ___anf_v2(___anf_v3, _CpsEvidence"),
        "{main_stdout}"
    );

    let run = std::process::Command::new(binary)
        .current_dir(&project_dir)
        .args(["run", "--selective-codegen"])
        .output()
        .expect("run imported effectful trait project");
    assert!(
        run.status.success(),
        "saga run failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&run.stdout),
        String::from_utf8_lossy(&run.stderr)
    );
    let run_stdout = String::from_utf8_lossy(&run.stdout);
    assert!(run_stdout.contains("ok\n"), "{run_stdout}");
}

#[test]
fn selective_core_codegen_specializes_imported_pure_callback_project() {
    let binary = env!("CARGO_BIN_EXE_saga");
    let project_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(
        "examples/optimization/selective-uniform/imported-pure-callback-specialization-project",
    );

    let run = std::process::Command::new(binary)
        .current_dir(&project_dir)
        .args(["run", "--selective-codegen"])
        .output()
        .expect("run imported pure callback specialization project");
    assert!(
        run.status.success(),
        "saga run failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&run.stdout),
        String::from_utf8_lossy(&run.stderr)
    );
    let run_stdout = String::from_utf8_lossy(&run.stdout);
    assert!(run_stdout.contains("ok\n"), "{run_stdout}");

    let effects_core =
        std::fs::read_to_string(project_dir.join("_build/dev/effects.core")).unwrap();
    assert!(
        effects_core.contains(
            "module 'effects' ['pure_value'/1, 'apply_eff'/3, '__saga_direct_hof_apply_eff'/1]"
        ),
        "{effects_core}"
    );

    let main_core = std::fs::read_to_string(project_dir.join("_build/dev/main.core")).unwrap();
    assert!(
        main_core.contains("call 'effects':'__saga_direct_hof_apply_eff'"),
        "{main_core}"
    );
    assert!(
        main_core.contains("call 'erlang':'make_fun'\n            ('effects', 'pure_value', 1)"),
        "{main_core}"
    );
    assert!(!main_core.contains("_PureCpsArg"), "{main_core}");
    assert!(
        !main_core.contains("call 'effects':'apply_eff'"),
        "{main_core}"
    );
}
