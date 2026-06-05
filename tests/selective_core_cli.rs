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
fn selective_core_codegen_handles_multi_clause_functions() {
    let binary = env!("CARGO_BIN_EXE_saga");
    let project_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("examples/optimization/selective-uniform/multi-clause-project");

    let fibonacci_inspect = std::process::Command::new(binary)
        .current_dir(&project_dir)
        .args(["inspect", "src/Main.saga", "--stage", "selective-core"])
        .output()
        .expect("inspect selective multi-clause fixture");
    assert!(
        fibonacci_inspect.status.success(),
        "saga inspect failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&fibonacci_inspect.stdout),
        String::from_utf8_lossy(&fibonacci_inspect.stderr)
    );
    let fibonacci_core = String::from_utf8_lossy(&fibonacci_inspect.stdout);
    assert!(fibonacci_core.contains("'fib'/1"), "{fibonacci_core}");
    assert!(fibonacci_core.contains("case {_Arg0}"), "{fibonacci_core}");

    let output = std::process::Command::new(binary)
        .current_dir(&project_dir)
        .args(["run"])
        .output()
        .expect("run selective multi-clause fixture");
    assert!(
        output.status.success(),
        "saga run failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let output_text = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(output_text.contains("55"), "{output_text}");
    assert!(output_text.contains("safe_div result: 25"), "{output_text}");
}

#[test]
fn selective_core_codegen_runs_deriving_example() {
    let binary = env!("CARGO_BIN_EXE_saga");
    let project_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("examples/optimization/selective-uniform/deriving-project");

    let output = std::process::Command::new(binary)
        .current_dir(&project_dir)
        .args(["run"])
        .output()
        .expect("run selective deriving example");
    assert!(
        output.status.success(),
        "saga run failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let output_text = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        output_text
            .contains("\"Scored(score: 10, value: first) vs Scored(score: 20, value: third): Lt\""),
        "{output_text}"
    );
}

#[test]
fn selective_core_codegen_adapts_pure_effect_callback_args() {
    let binary = env!("CARGO_BIN_EXE_saga");
    let project_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("examples/optimization/selective-uniform/async-project");

    let output = std::process::Command::new(binary)
        .current_dir(&project_dir)
        .args(["run"])
        .output()
        .expect("run selective async fixture");
    assert!(
        output.status.success(),
        "saga run failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let output_text = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(output_text.contains("[1, 2, 3]"), "{output_text}");
}

#[test]
fn selective_core_codegen_preserves_cps_callback_abi_for_public_entries() {
    let binary = env!("CARGO_BIN_EXE_saga");
    let project_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("examples/optimization/selective-uniform/atomic-ref-project");

    let output = std::process::Command::new(binary)
        .current_dir(&project_dir)
        .args(["run"])
        .output()
        .expect("run selective atomic-ref fixture");
    assert!(
        output.status.success(),
        "saga run failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let output_text = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        output_text.contains("\"after modify: 10\""),
        "{output_text}"
    );
    assert!(output_text.contains("\"after set: 42\""), "{output_text}");
}

#[test]
fn selective_core_codegen_adapts_pure_callbacks_for_local_cps_calls() {
    let binary = env!("CARGO_BIN_EXE_saga");
    let project_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("examples/optimization/selective-uniform/state-effect-project");

    let output = std::process::Command::new(binary)
        .current_dir(&project_dir)
        .args(["run"])
        .output()
        .expect("run selective state-effect fixture");
    assert!(
        output.status.success(),
        "saga run failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let output_text = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(output_text.contains("\"5\""), "{output_text}");
    assert!(output_text.contains("\"hello world\""), "{output_text}");
}

#[test]
fn selective_core_codegen_falls_back_when_static_handler_specialization_cannot_inline() {
    let binary = env!("CARGO_BIN_EXE_saga");
    let project_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("examples/optimization/selective-uniform/effect-row-polymorphism-project");

    let output = std::process::Command::new(binary)
        .current_dir(&project_dir)
        .args(["run"])
        .output()
        .expect("run selective effect-row polymorphism fixture");
    assert!(
        output.status.success(),
        "saga run failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let output_text = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        output_text.contains("\"5 doubled twice: 20\""),
        "{output_text}"
    );
    assert!(output_text.contains("\"hello, world\""), "{output_text}");
    assert!(
        output_text.contains("\"caught: empty name\""),
        "{output_text}"
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
        .args(["run", resume_fixture.to_str().expect("utf-8 fixture path")])
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
        .args(["run", abort_fixture.to_str().expect("utf-8 fixture path")])
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
fn selective_core_codegen_runs_multiarm_handler_finally_bug_fixture() {
    let binary = env!("CARGO_BIN_EXE_saga");
    let manifest_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let fixture = manifest_dir.join("examples/bugs/multiarm-finally/inline.saga");

    let output = std::process::Command::new(binary)
        .current_dir(&manifest_dir)
        .args(["run", fixture.to_str().expect("utf-8 fixture path")])
        .output()
        .expect("run selective multiarm finally fixture");
    assert!(
        output.status.success(),
        "saga run failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let output_text = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(output_text.contains("\"  cleanup n\""), "{output_text}");
    assert!(output_text.contains("\"  cleanup 0\""), "{output_text}");
    assert!(output_text.contains("\"result: 110\""), "{output_text}");
}

#[test]
fn selective_core_codegen_runs_higher_order_direct_callback_fixture() {
    let binary = env!("CARGO_BIN_EXE_saga");
    let project_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("examples/optimization/selective-uniform/higher-order-direct-callback-project");

    let output = std::process::Command::new(binary)
        .current_dir(&project_dir)
        .args(["run"])
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
fn selective_core_codegen_runs_stdlib_dict_fixture() {
    let binary = env!("CARGO_BIN_EXE_saga");
    let project_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("examples/optimization/selective-uniform/stdlib-dict-project");

    let output = std::process::Command::new(binary)
        .current_dir(&project_dir)
        .args(["run"])
        .output()
        .expect("run selective stdlib dict fixture");
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
fn selective_core_specializes_imported_monomorphic_trait_method() {
    let binary = env!("CARGO_BIN_EXE_saga");
    let project_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(
        "examples/optimization/selective-uniform/imported-stdlib-trait-specialization-project",
    );

    let inspect = std::process::Command::new(binary)
        .current_dir(&project_dir)
        .args(["inspect", "src/Main.saga", "--stage", "selective-core"])
        .output()
        .expect("inspect imported stdlib trait specialization fixture");
    assert!(
        inspect.status.success(),
        "saga inspect failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&inspect.stdout),
        String::from_utf8_lossy(&inspect.stderr)
    );
    let core = String::from_utf8_lossy(&inspect.stdout);
    assert!(!core.contains("call 'erlang':'element'"), "{core}");
    assert!(!core.contains("apply ___anf_v1"), "{core}");
    assert!(!core.contains("__dict_Std_Base_Show"), "{core}");
    assert!(core.contains("#{#<84>"), "{core}");
    assert!(core.contains("call 'erlang':'integer_to_binary'"), "{core}");

    let output = std::process::Command::new(binary)
        .current_dir(&project_dir)
        .args(["run"])
        .output()
        .expect("run imported stdlib trait specialization fixture");
    assert!(
        output.status.success(),
        "saga run failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let output_text = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(output_text.contains("True:42"), "{output_text}");
}

#[test]
fn selective_core_specializes_imported_generic_trait_method_chain() {
    let binary = env!("CARGO_BIN_EXE_saga");
    let project_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(
        "examples/optimization/selective-uniform/imported-generic-trait-specialization-project",
    );

    let inspect = std::process::Command::new(binary)
        .current_dir(&project_dir)
        .args(["inspect", "src/Main.saga", "--stage", "selective-core"])
        .output()
        .expect("inspect imported generic trait specialization fixture");
    assert!(
        inspect.status.success(),
        "saga inspect failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&inspect.stdout),
        String::from_utf8_lossy(&inspect.stderr)
    );
    let core = String::from_utf8_lossy(&inspect.stdout);
    assert!(!core.contains("call 'erlang':'element'"), "{core}");
    assert!(!core.contains("apply ___anf_v2"), "{core}");
    assert!(!core.contains("__dict_Lib_Size"), "{core}");
    assert!(core.contains("'__saga_direct_hof_apply_box'/1"), "{core}");
    assert!(core.contains("call 'erlang':'+'"), "{core}");
    assert!(core.contains("42"), "{core}");

    let output = std::process::Command::new(binary)
        .current_dir(&project_dir)
        .args(["run"])
        .output()
        .expect("run imported generic trait specialization fixture");
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
fn selective_core_runs_routed_derive_options_without_optimizer_variants() {
    let binary = env!("CARGO_BIN_EXE_saga");
    let manifest_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let fixture_src = manifest_dir
        .join("examples/optimization/routed-derive-options/01-routed-derive-options.saga");
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("system clock should be after unix epoch")
        .as_nanos();
    let isolated_dir = manifest_dir.join(format!(
        "target/selective-core-cli/routed-derive-options-{unique}"
    ));
    std::fs::create_dir_all(&isolated_dir).expect("create isolated selective fixture dir");
    let fixture = isolated_dir.join("01-routed-derive-options.saga");
    std::fs::copy(&fixture_src, &fixture).expect("copy routed derive fixture");

    let inspect = std::process::Command::new(binary)
        .args([
            "inspect",
            fixture.to_str().expect("fixture path should be utf-8"),
            "--stage",
            "selective-core",
            "--selective-no-fallback",
        ])
        .output()
        .expect("inspect routed derive options fixture");
    assert!(
        inspect.status.success(),
        "saga inspect failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&inspect.stdout),
        String::from_utf8_lossy(&inspect.stderr)
    );

    let core = String::from_utf8_lossy(&inspect.stdout);
    assert!(
        !core.contains("__saga_static_variant"),
        "selective-core should not depend on monadic optimizer static variants\n{core}"
    );
    assert!(
        core.contains("call 'erlang':'+'"),
        "fixture should still lower and expose the arithmetic leaf\n{core}"
    );

    let output = std::process::Command::new(binary)
        .args([
            "run",
            fixture.to_str().expect("fixture path should be utf-8"),
        ])
        .output()
        .expect("run routed derive options fixture");
    assert!(
        output.status.success(),
        "saga run failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let output_text = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(output_text.contains("\"15\""), "{output_text}");
}

#[test]
fn selective_core_specializes_known_generic_to_json_records() {
    let binary = env!("CARGO_BIN_EXE_saga");
    let manifest_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let fixture_src = manifest_dir.join("examples/99f-generic-derived-tojson.saga");
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("system clock should be after unix epoch")
        .as_nanos();
    let isolated_dir = manifest_dir.join(format!(
        "target/selective-core-cli/generic-derived-tojson-{unique}"
    ));
    std::fs::create_dir_all(&isolated_dir).expect("create isolated generic to_json fixture dir");
    let fixture = isolated_dir.join("99f-generic-derived-tojson.saga");
    std::fs::copy(&fixture_src, &fixture).expect("copy generic to_json fixture");

    let inspect = std::process::Command::new(binary)
        .args([
            "inspect",
            fixture.to_str().expect("fixture path should be utf-8"),
            "--stage",
            "selective-core",
            "--selective-no-fallback",
        ])
        .output()
        .expect("inspect generic to_json fixture");
    assert!(
        inspect.status.success(),
        "saga inspect failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&inspect.stdout),
        String::from_utf8_lossy(&inspect.stderr)
    );

    let core = String::from_utf8_lossy(&inspect.stdout);
    let start = core
        .find("\n'main'/1")
        .map(|index| index + 1)
        .expect("main should be emitted");
    let main_body = &core[start..];
    assert!(
        main_body.contains("call 'erlang':'integer_to_binary'\n                (42)"),
        "Box Int to_json should specialize through known Generic constructors\n{main_body}"
    );
    assert!(
        main_body.contains("#<104>(8,1,'integer',['unsigned'|['big']]),#<101>"),
        "Box String to_json should specialize through known Generic constructors\n{main_body}"
    );
    assert!(
        main_body.contains("#<83>(8,1,'integer',['unsigned'|['big']]),#<111>")
            && main_body.contains("call 'erlang':'integer_to_binary'\n              (7)"),
        "Some to_json should specialize through known Generic case constructors\n{main_body}"
    );
    assert!(
        main_body.contains("#<78>(8,1,'integer',['unsigned'|['big']]),#<97>")
            && main_body.contains("#<110>(8,1,'integer',['unsigned'|['big']]),#<117>"),
        "Nada to_json should specialize through known Generic case constructors\n{main_body}"
    );

    let output = std::process::Command::new(binary)
        .args([
            "run",
            "--selective-no-fallback",
            fixture.to_str().expect("fixture path should be utf-8"),
        ])
        .output()
        .expect("run generic to_json fixture");
    assert!(
        output.status.success(),
        "saga run failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let output_text = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(output_text.contains("\"{\"value\": 42}\""), "{output_text}");
    assert!(
        output_text.contains("\"{\"value\": \"hello\"}\""),
        "{output_text}"
    );
}

#[test]
fn selective_core_runs_known_split_trait_record_without_optimizer_variants() {
    let binary = env!("CARGO_BIN_EXE_saga");
    let manifest_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let fixture =
        manifest_dir.join("examples/optimization/routed-derive-options/03-split-trait-record.saga");

    let inspect = std::process::Command::new(binary)
        .args([
            "inspect",
            fixture.to_str().expect("fixture path should be utf-8"),
            "--stage",
            "selective-core",
            "--selective-no-fallback",
        ])
        .output()
        .expect("inspect split-trait routed derive options fixture");
    assert!(
        inspect.status.success(),
        "saga inspect failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&inspect.stdout),
        String::from_utf8_lossy(&inspect.stderr)
    );

    let core = String::from_utf8_lossy(&inspect.stdout);
    let start = core
        .find("\n'main'/1")
        .map(|index| index + 1)
        .expect("main should be emitted");
    let main_body = &core[start..];
    assert!(
        !main_body.contains("__saga_static_variant"),
        "selective-core should not depend on monadic optimizer static variants\n{main_body}"
    );

    let output = std::process::Command::new(binary)
        .args([
            "run",
            fixture.to_str().expect("fixture path should be utf-8"),
        ])
        .output()
        .expect("run split-trait routed derive options fixture");
    assert!(
        output.status.success(),
        "saga run failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let output_text = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(output_text.contains("\"33\""), "{output_text}");
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
        stderr.contains("direct function 'hidden' is outside the current direct subset"),
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
        inspect_stdout.contains("apply '__saga_direct_hof_apply_it'/1(call 'erlang':'make_fun'"),
        "{inspect_stdout}"
    );

    let run = std::process::Command::new(binary)
        .current_dir(&project_dir)
        .args(["run"])
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
    assert!(inspect_stdout.contains("module 'Main'"), "{inspect_stdout}");
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
            && effects_stdout.contains("apply G('unit', _Evidence, _ReturnK)")
            && !effects_stdout.contains("__saga_direct_hof_apply_eff"),
        "{effects_stdout}"
    );

    let run = std::process::Command::new(binary)
        .current_dir(&project_dir)
        .args(["run"])
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
        inspect_stdout.contains("call 'std_evidence_bridge':'insert_canonical'"),
        "{inspect_stdout}"
    );
    assert!(inspect_stdout.contains("let <Value>"), "{inspect_stdout}");
    assert!(inspect_stdout.contains("41"), "{inspect_stdout}");
    assert!(
        inspect_stdout.contains("call 'erlang':'+'"),
        "{inspect_stdout}"
    );

    let run = std::process::Command::new(binary)
        .current_dir(&project_dir)
        .args(["run"])
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
        lib_stdout.contains("'__dict_Lib_Encodable_Std_Int_Int'/0"),
        "{lib_stdout}"
    );
    assert!(
        lib_stdout.contains("call 'std_evidence_bridge':'find_evidence'")
            && lib_stdout.contains("apply _LambdaK"),
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
    assert!(main_stdout.contains("module 'Main' []"), "{main_stdout}");

    let run = std::process::Command::new(binary)
        .current_dir(&project_dir)
        .args(["run"])
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
        .args(["run"])
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
    assert!(effects_core.contains("'pure_value'/1"), "{effects_core}");
    assert!(effects_core.contains("'apply_eff'/3"), "{effects_core}");
    assert!(
        effects_core.contains("'__saga_direct_hof_apply_eff'/1"),
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

#[test]
fn selective_core_codegen_lowers_beam_actor_native_project() {
    let binary = env!("CARGO_BIN_EXE_saga");
    let project_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("examples/optimization/selective-uniform/beam-actor-native-project");

    let inspect = std::process::Command::new(binary)
        .current_dir(&project_dir)
        .args([
            "inspect",
            "src/Main.saga",
            "--stage",
            "selective-core",
            "--selective-no-fallback",
        ])
        .output()
        .expect("inspect beam actor native project selective Core");
    assert!(
        inspect.status.success(),
        "saga inspect failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&inspect.stdout),
        String::from_utf8_lossy(&inspect.stderr)
    );
    let core = String::from_utf8_lossy(&inspect.stdout);
    assert!(
        core.contains("'__saga_native_variant__run__native__beam_actor"),
        "{core}"
    );
    for native_call in [
        "call 'erlang':'self'",
        "call 'erlang':'spawn'",
        "call 'erlang':'monitor'",
        "call 'erlang':'link'",
        "call 'erlang':'unlink'",
        "call 'erlang':'exit'",
        "call 'timer':'sleep'",
        "call 'erlang':'send_after'",
        "call 'erlang':'cancel_timer'",
        "receive",
    ] {
        assert!(core.contains(native_call), "missing {native_call}\n{core}");
    }

    let run = std::process::Command::new(binary)
        .current_dir(&project_dir)
        .args(["run"])
        .output()
        .expect("run beam actor native project");
    assert!(
        run.status.success(),
        "saga run failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&run.stdout),
        String::from_utf8_lossy(&run.stderr)
    );
    let run_stdout = String::from_utf8_lossy(&run.stdout);
    assert!(
        run_stdout.contains("process:monitor:link:timer\n"),
        "{run_stdout}"
    );
}

#[test]
fn selective_core_codegen_lowers_stdlib_stream_strict_frontier() {
    let binary = env!("CARGO_BIN_EXE_saga");
    let repo_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));

    let inspect = std::process::Command::new(binary)
        .current_dir(&repo_dir)
        .args([
            "inspect",
            "src/stdlib/Stream.saga",
            "--stage",
            "selective-core",
            "--selective-no-fallback",
        ])
        .output()
        .expect("inspect stdlib Stream selective Core");
    assert!(
        inspect.status.success(),
        "saga inspect failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&inspect.stdout),
        String::from_utf8_lossy(&inspect.stderr)
    );
    let core = String::from_utf8_lossy(&inspect.stdout);
    assert!(core.contains("'for_each'/4"), "{core}");
    assert!(core.contains("'__saga_direct_hof_for_each'/2"), "{core}");
    assert!(
        core.contains("apply F(V, _Evidence, fun (_CpsBindArg"),
        "{core}"
    );
    assert!(
        core.contains("apply 'for_each'/4(F, Rest, {}, fun (_CpsResult"),
        "{core}"
    );
}

#[test]
fn selective_core_codegen_lowers_stdlib_atomic_ref_strict_frontier() {
    let binary = env!("CARGO_BIN_EXE_saga");
    let repo_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));

    let inspect = std::process::Command::new(binary)
        .current_dir(&repo_dir)
        .args([
            "inspect",
            "src/stdlib/AtomicRef.saga",
            "--stage",
            "selective-core",
            "--selective-no-fallback",
        ])
        .output()
        .expect("inspect stdlib AtomicRef selective Core");
    assert!(
        inspect.status.success(),
        "saga inspect failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&inspect.stdout),
        String::from_utf8_lossy(&inspect.stderr)
    );
    let core = String::from_utf8_lossy(&inspect.stdout);
    assert!(core.contains("'lock_server'/3"), "{core}");
    assert!(
        core.contains("call 'std_evidence_bridge':'find_evidence'")
            && core.contains("'Std.Actor.Monitor'")
            && core.contains("'Std.Actor.Process'"),
        "{core}"
    );
    assert!(
        core.contains("apply 'lock_server'/3('unit', _Evidence, _ReturnK)"),
        "{core}"
    );
}
