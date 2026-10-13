//! Tests for the function-value call helpers in `src/stdlib/runtime.erl`
//! (`saga_runtime:apply_n/2` and `saga_runtime:apply_cps/4`).
//!
//! The helpers are exercised directly from Erlang with hand-written funs as
//! stand-ins for compiled Saga function values, so these tests do not depend
//! on what the compiler emits. Requires `erlc` and `erl` on PATH.

mod common;

use common::run_bounded;
use std::path::PathBuf;
use std::sync::OnceLock;
use std::time::Duration;

const RUNTIME_SRC: &str = include_str!("../src/stdlib/runtime.erl");

/// Wall-clock limit for each `erlc`/`erl` child.
const LIMIT: Duration = Duration::from_secs(20);

/// Stand-in function values shared by the tests.
///
/// - `K` tags what it receives, so a test can tell a value passed to the
///   continuation from one returned some other way.
/// - `EAdd`/`EAdd3` are effectful (tagged) and report the evidence they ran
///   with; `Add`/`Add3` are their pure (bare) counterparts.
const PRELUDE: &str = r#"
    K = fun(R) -> {k, R} end,
    EAdd = {'$saga_cps', fun(A, B, Ev, K0) -> K0({A + B, Ev}) end},
    EAdd3 = {'$saga_cps', fun(A, B, C, Ev, K0) -> K0({A + B + C, Ev}) end},
    Add = fun(A, B) -> A + B end,
    Add3 = fun(A, B, C) -> A + B + C end,
    Wide = fun(A, _, _, _, _, _, _, _, _, _, _, _, _, Z) -> {A, Z} end,
    EWide = {'$saga_cps',
             fun(A, _, _, _, _, _, _, _, _, _, _, _, _, Z, Ev, K0) -> K0({A, Z, Ev}) end},
    Rest12 = [3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14],
    Caught = fun(Thunk) ->
        try Thunk() of V -> {no_error, V}
        catch error:Reason -> Reason
        end
    end,
"#;

/// Directory holding the compiled `saga_runtime.beam`, built once per test
/// process.
fn runtime_dir() -> &'static PathBuf {
    static DIR: OnceLock<PathBuf> = OnceLock::new();
    DIR.get_or_init(|| {
        let dir = std::env::temp_dir().join(format!("saga_runtime_helpers_{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        let src = dir.join("saga_runtime.erl");
        std::fs::write(&src, RUNTIME_SRC).unwrap();
        let output = run_bounded(
            std::process::Command::new("erlc")
                .arg("-Werror")
                .arg("-o")
                .arg(&dir)
                .arg(&src),
            LIMIT,
        )
        .expect("failed to run erlc on runtime.erl");
        assert!(
            output.status.success(),
            "erlc failed on runtime.erl:\n{}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        dir
    })
}

/// Evaluate an Erlang expression sequence after `PRELUDE` and return its
/// value printed with `~0p`.
fn eval(body: &str) -> String {
    let program = format!("io:format(\"~0p~n\", [begin {PRELUDE} {body} end]).");
    let output = run_bounded(
        std::process::Command::new("erl")
            .arg("-noshell")
            .arg("-pa")
            .arg(runtime_dir())
            .arg("-eval")
            .arg(&program)
            .arg("-s")
            .arg("init")
            .arg("stop"),
        LIMIT,
    )
    .expect("failed to run erl");
    let stdout = String::from_utf8_lossy(&output.stdout).trim().to_string();
    assert!(
        output.status.success() && !stdout.is_empty(),
        "erl failed evaluating:\n{body}\nstdout: {stdout}\nstderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    stdout
}

#[track_caller]
fn assert_eval(body: &str, expected: &str) {
    assert_eq!(eval(body), expected, "evaluating:\n{body}");
}

// ---------------------------------------------------------------------------
// apply_cps: tagged values
// ---------------------------------------------------------------------------

#[test]
fn apply_cps_tagged_exact_arity_passes_evidence_and_continuation() {
    assert_eval("saga_runtime:apply_cps(EAdd, [1, 2], ev, K)", "{k,{3,ev}}");
}

#[test]
fn apply_cps_tagged_too_few_args_continues_with_a_tagged_partial() {
    assert_eval(
        r#"
        {k, {'$saga_cps', P} = Partial} = saga_runtime:apply_cps(EAdd, [1], ev1, K),
        {is_function(P, 3), saga_runtime:apply_cps(Partial, [2], ev2, K)}
        "#,
        // The evidence is the one given at saturation, not `ev1`.
        "{true,{k,{3,ev2}}}",
    );
}

#[test]
fn apply_cps_tagged_partial_can_be_called_directly_as_a_cps_fun() {
    assert_eval(
        r#"
        {k, {'$saga_cps', P}} = saga_runtime:apply_cps(EAdd3, [1], ev1, K),
        P(2, 3, ev2, K)
        "#,
        "{k,{6,ev2}}",
    );
}

#[test]
fn apply_cps_tagged_too_many_args_with_tagged_intermediate() {
    assert_eval(
        r#"
        Mk = {'$saga_cps', fun(A, Ev, K0) ->
            K0({'$saga_cps', fun(B, Ev2, K2) -> K2({A + B, Ev, Ev2}) end})
        end},
        saga_runtime:apply_cps(Mk, [1, 2], ev, K)
        "#,
        "{k,{3,ev,ev}}",
    );
}

#[test]
fn apply_cps_tagged_too_many_args_with_bare_intermediate() {
    assert_eval(
        r#"
        Mk = {'$saga_cps', fun(A, Ev, K0) -> K0(fun(B) -> {A * B, Ev} end) end},
        saga_runtime:apply_cps(Mk, [3, 4], ev, K)
        "#,
        "{k,{12,ev}}",
    );
}

#[test]
fn apply_cps_tagged_too_many_args_then_too_few() {
    // One argument consumed, and the tagged result still wants two more.
    assert_eval(
        r#"
        Mk = {'$saga_cps', fun(A, _Ev, K0) ->
            K0({'$saga_cps', fun(B, C, Ev2, K2) -> K2({A + B + C, Ev2}) end})
        end},
        {k, Partial} = saga_runtime:apply_cps(Mk, [1, 2], ev1, K),
        saga_runtime:apply_cps(Partial, [3], ev2, K)
        "#,
        "{k,{6,ev2}}",
    );
}

#[test]
fn apply_cps_tagged_chain_of_two_partial_applications() {
    assert_eval(
        r#"
        {k, P1} = saga_runtime:apply_cps(EAdd3, [1], ev1, K),
        {k, P2} = saga_runtime:apply_cps(P1, [2], ev2, K),
        {'$saga_cps', F1} = P1,
        {'$saga_cps', F2} = P2,
        {is_function(F1, 4), is_function(F2, 3), saga_runtime:apply_cps(P2, [3], ev3, K)}
        "#,
        "{true,true,{k,{6,ev3}}}",
    );
}

// ---------------------------------------------------------------------------
// apply_cps: bare values
// ---------------------------------------------------------------------------

#[test]
fn apply_cps_bare_exact_arity_passes_result_to_continuation() {
    assert_eval("saga_runtime:apply_cps(Add, [1, 2], ev, K)", "{k,3}");
}

#[test]
fn apply_cps_bare_too_few_args_continues_with_a_bare_partial() {
    assert_eval(
        r#"
        {k, P} = saga_runtime:apply_cps(Add, [1], ev, K),
        {is_function(P, 1), P(2), saga_runtime:apply_cps(P, [2], ev2, K)}
        "#,
        "{true,3,{k,3}}",
    );
}

#[test]
fn apply_cps_bare_too_many_args_with_bare_intermediate() {
    assert_eval(
        r#"
        Mk = fun(A) -> fun(B) -> A * B end end,
        saga_runtime:apply_cps(Mk, [3, 4], ev, K)
        "#,
        "{k,12}",
    );
}

#[test]
fn apply_cps_bare_too_many_args_with_tagged_intermediate() {
    assert_eval(
        r#"
        Mk = fun(A) -> {'$saga_cps', fun(B, Ev, K0) -> K0({A * B, Ev}) end} end,
        saga_runtime:apply_cps(Mk, [3, 4], ev, K)
        "#,
        "{k,{12,ev}}",
    );
}

#[test]
fn apply_cps_bare_chain_of_two_partial_applications() {
    assert_eval(
        r#"
        {k, P1} = saga_runtime:apply_cps(Add3, [1], ev1, K),
        {k, P2} = saga_runtime:apply_cps(P1, [2], ev2, K),
        {is_function(P1, 2), is_function(P2, 1), saga_runtime:apply_cps(P2, [3], ev3, K)}
        "#,
        "{true,true,{k,6}}",
    );
}

// ---------------------------------------------------------------------------
// apply_cps: errors and the partial application limit
// ---------------------------------------------------------------------------

#[test]
fn apply_cps_rejects_values_that_are_not_functions() {
    assert_eval(
        r#"
        NotCps = {'$saga_cps', fun(A) -> A end},
        [
            Caught(fun() -> saga_runtime:apply_cps(42, [1], ev, K) end),
            Caught(fun() -> saga_runtime:apply_cps({'$saga_cps', 42}, [1], ev, K) end),
            %% A fun too small to take evidence and a continuation.
            Caught(fun() -> saga_runtime:apply_cps(NotCps, [1], ev, K) end) =:= {badfun, NotCps},
            %% Over-application whose intermediate result is not a function.
            Caught(fun() -> saga_runtime:apply_cps(Add, [1, 2, 3], ev, K) end),
            Caught(fun() -> saga_runtime:apply_cps(EAdd, [1, 2, 3], ev, K) end)
        ]
        "#,
        "[{badfun,42},{badfun,{'$saga_cps',42}},true,{badfun,3},{badfun,{3,ev}}]",
    );
}

#[test]
fn apply_cps_rejects_zero_user_arity_values_given_arguments() {
    assert_eval(
        r#"
        Bare0 = fun() -> ok end,
        Tagged0 = {'$saga_cps', fun(_Ev, K0) -> K0(ok) end},
        [
            Caught(fun() -> saga_runtime:apply_cps(Bare0, [1], ev, K) end)
                =:= {badarity, {Bare0, [1]}},
            Caught(fun() -> saga_runtime:apply_cps(Tagged0, [1], ev, K) end)
                =:= {badarity, {Tagged0, [1]}},
            saga_runtime:format_caught_panic(error, {badarity, {Tagged0, [1]}})
        ]
        "#,
        "[true,true,<<\"function called with 1 argument(s), but expects 0\">>]",
    );
}

#[test]
fn apply_cps_partial_application_supports_twelve_remaining_args() {
    assert_eval(
        r#"
        {k, BareP} = saga_runtime:apply_cps(Wide, [1, 2], ev1, K),
        {k, {'$saga_cps', F} = TaggedP} = saga_runtime:apply_cps(EWide, [1, 2], ev1, K),
        [
            is_function(BareP, 12),
            is_function(F, 14),
            saga_runtime:apply_cps(BareP, Rest12, ev2, K),
            saga_runtime:apply_cps(TaggedP, Rest12, ev2, K)
        ]
        "#,
        "[true,true,{k,{1,14}},{k,{1,14,ev2}}]",
    );
}

#[test]
fn apply_cps_partial_application_beyond_twelve_remaining_args_is_a_limit_error() {
    assert_eval(
        r#"
        [
            Caught(fun() -> saga_runtime:apply_cps(Wide, [1], ev, K) end),
            Caught(fun() -> saga_runtime:apply_cps(EWide, [1], ev, K) end),
            saga_runtime:format_caught_panic(
                error, Caught(fun() -> saga_runtime:apply_cps(EWide, [1], ev, K) end))
        ]
        "#,
        "[{saga_partial_application_limit,14,1,13},{saga_partial_application_limit,14,1,13},\
         <<\"cannot partially apply a function of 14 parameter(s) to 1 argument(s): \
         13 would remain, and partial applications built at runtime support at most 12\">>]",
    );
}

// ---------------------------------------------------------------------------
// apply_n: tagged values at a pure call site
// ---------------------------------------------------------------------------

#[test]
fn apply_n_tagged_too_few_args_returns_a_tagged_partial() {
    assert_eval(
        r#"
        {'$saga_cps', P} = Partial = saga_runtime:apply_n(EAdd, [1]),
        {is_function(P, 3), saga_runtime:apply_cps(Partial, [2], ev, K), P(5, ev2, K)}
        "#,
        "{true,{k,{3,ev}},{k,{6,ev2}}}",
    );
}

#[test]
fn apply_n_tagged_chain_of_two_partial_applications() {
    assert_eval(
        r#"
        P1 = saga_runtime:apply_n(EAdd3, [1]),
        P2 = saga_runtime:apply_n(P1, [2]),
        {'$saga_cps', F2} = P2,
        {is_function(F2, 3), saga_runtime:apply_cps(P2, [3], ev, K)}
        "#,
        "{true,{k,{6,ev}}}",
    );
}

#[test]
fn apply_n_bare_over_application_reaching_a_tagged_partial() {
    assert_eval(
        r#"
        Mk = fun(A) -> {'$saga_cps', fun(B, C, Ev, K0) -> K0({A + B + C, Ev}) end} end,
        Partial = saga_runtime:apply_n(Mk, [1, 2]),
        saga_runtime:apply_cps(Partial, [3], ev, K)
        "#,
        "{k,{6,ev}}",
    );
}

// A tagged closure at a pure call site is a row-polymorphic function used at
// the empty row: it runs with an empty evidence frame and an identity
// continuation.
#[test]
fn apply_n_tagged_saturated_runs_with_an_empty_frame() {
    assert_eval(
        "saga_runtime:apply_n(EAdd, [1, 2])",
        // Returned as is: the identity continuation, not `K`.
        "{3,{}}",
    );
}

#[test]
fn apply_n_tagged_over_applied_applies_the_result_to_the_rest() {
    assert_eval(
        r#"
        Bare = {'$saga_cps', fun(A, Ev, K0) -> K0(fun(B) -> {A + B, Ev} end) end},
        Tagged = {'$saga_cps', fun(A, _Ev, K0) -> K0({'$saga_cps', fun(B, Ev, K1) ->
            K1({A + B, Ev}) end}) end},
        Partial = {'$saga_cps', fun(A, _Ev, K0) -> K0(fun(B, C) -> A + B + C end) end},
        [
            saga_runtime:apply_n(Bare, [1, 2]),
            saga_runtime:apply_n(Tagged, [1, 2]),
            (saga_runtime:apply_n(Partial, [1, 2]))(3)
        ]
        "#,
        "[{3,{}},{3,{}},6]",
    );
}

#[test]
fn apply_n_tagged_partial_saturated_at_a_pure_site() {
    assert_eval(
        r#"
        P1 = saga_runtime:apply_n(EAdd3, [1]),
        saga_runtime:apply_n(P1, [2, 3])
        "#,
        "{6,{}}",
    );
}

#[test]
fn apply_n_tagged_values_that_cannot_be_called() {
    assert_eval(
        r#"
        Tagged0 = {'$saga_cps', fun(_Ev, K0) -> K0(ok) end},
        NotCps = {'$saga_cps', fun(A) -> A end},
        [
            Caught(fun() -> saga_runtime:apply_n(Tagged0, [1]) end) =:= {badarity, {Tagged0, [1]}},
            Caught(fun() -> saga_runtime:apply_n(NotCps, [1]) end) =:= {badfun, NotCps},
            Caught(fun() -> saga_runtime:apply_n({'$saga_cps', 42}, [1]) end)
        ]
        "#,
        "[true,true,{badfun,{'$saga_cps',42}}]",
    );
}

// Unreachable under sound typing: a closure run with the empty frame of a
// pure call site looks an effect up. The crash names the effect.
#[test]
fn missing_evidence_is_reported_by_effect_name() {
    assert_eval(
        "saga_runtime:format_caught_panic(error, {evidence_tag_not_found, 'Main.Skip'})",
        "<<\"effect Main.Skip was performed where no handler for it is installed\">>",
    );
}

// bare_fun: what an `@external` wrapper hands to Erlang code as a callback.
#[test]
fn bare_fun_returns_a_fun_of_the_right_arity_and_wraps_the_rest() {
    assert_eval(
        r#"
        Curried = fun(A) -> fun(B) -> A + B end end,
        W = saga_runtime:bare_fun(EAdd, 2),
        C = saga_runtime:bare_fun(Curried, 2),
        [
            saga_runtime:bare_fun(Add, 2) =:= Add,
            is_function(W, 2), W(1, 2),
            is_function(C, 2), C(1, 2),
            saga_runtime:bare_fun(EWide, 14) =:= EWide
        ]
        "#,
        "[true,true,{3,{}},true,3,true]",
    );
}

#[test]
fn apply_n_tagged_partial_application_limit() {
    assert_eval(
        r#"
        {'$saga_cps', F} = Partial = saga_runtime:apply_n(EWide, [1, 2]),
        [
            is_function(F, 14),
            saga_runtime:apply_cps(Partial, Rest12, ev, K),
            Caught(fun() -> saga_runtime:apply_n(EWide, [1]) end)
        ]
        "#,
        "[true,{k,{1,14,ev}},{saga_partial_application_limit,14,1,13}]",
    );
}

#[test]
fn apply_n_bare_behaviour_is_unchanged() {
    assert_eval(
        r#"
        Mk = fun(A) -> fun(B) -> A * B end end,
        Bare0 = fun() -> ok end,
        P = saga_runtime:apply_n(Add3, [1]),
        [
            saga_runtime:apply_n(Add, [1, 2]),
            is_function(P, 2),
            P(2, 3),
            saga_runtime:apply_n(Mk, [3, 4]),
            Caught(fun() -> saga_runtime:apply_n(42, [1]) end),
            Caught(fun() -> saga_runtime:apply_n(Bare0, [1]) end) =:= {badarity, {Bare0, [1]}},
            Caught(fun() -> saga_runtime:apply_n(Wide, [1]) end)
        ]
        "#,
        "[3,true,6,12,{badfun,42},true,{saga_partial_application_limit,14,1,13}]",
    );
}
