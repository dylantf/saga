//! BEAM-execution property test harness for effect-using programs.
//!
//! Each fixture is a small, self-contained Saga program that defines
//! `pub fun result : Unit -> String` (or similar). The harness compiles
//! it to Core Erlang, runs it on the BEAM via `erl -noshell`, and asserts
//! exact stdout output. The point is broad regression coverage of the
//! effectful calling convention: resume/abort, nested handlers, partial
//! application, cross-module calls, multishot, BEAM-native effects, and
//! mixed BEAM-native/CPS programs.
//!
//! See `docs/planning/plans/evidence-passing-plan.md` Phase 0 for the
//! coverage list.
//!
//! These tests require `erlc` and `erl` on PATH.
mod common;

use common::*;
use saga::{lexer, parser};

/// Typecheck a single-module source that must be rejected, returning the
/// rendered type errors.
fn typecheck_error(src: &str) -> String {
    let root = fixtures_root_for_main_only();
    let mut checker = make_checker(root.clone());
    let result = try_typecheck_source(src, &mut checker).map(|_| ());
    let _ = std::fs::remove_dir_all(&root);
    match result {
        Err(FrontendError::Typecheck(message)) => message,
        other => panic!("expected a type error, got {other:?}"),
    }
}

/// `typecheck_error` for a main module importing `modules` (relative path,
/// source) from a project on disk.
fn typecheck_error_cross_module(fixture: &str, modules: &[(&str, &str)], main_src: &str) -> String {
    let root = fresh_dir(&format!("{fixture}_root"));
    std::fs::write(root.join("project.toml"), "[project]\nname=\"prop\"\n").unwrap();
    for (rel, src) in modules {
        let path = root.join(rel);
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent).unwrap();
        }
        std::fs::write(&path, src).unwrap();
    }
    let mut checker = make_checker(root.clone());
    let result = try_typecheck_source(main_src, &mut checker).map(|_| ());
    let _ = std::fs::remove_dir_all(&root);
    match result {
        Err(FrontendError::Typecheck(message)) => message,
        other => panic!("[{fixture}] expected a type error, got {other:?}"),
    }
}

/// The error for two applications of one effect family meeting in a row.
fn assert_one_application_per_family(message: &str, family: &str, first: &str, second: &str) {
    assert!(
        message.contains(&format!("can hold only one `{family}`"))
            && message.contains(first)
            && message.contains(second)
            && message.contains("neweffect"),
        "expected a one-application-per-family error for {first} and {second}, got: {message}"
    );
}

// ---------------------------------------------------------------------------
// Fixtures: basic op call (resume / abort)
// ---------------------------------------------------------------------------

#[test]
fn basic_resume_unit() {
    let src = r#"module Main

effect Log {
  fun log : String -> Unit
}

handler accumulating for Log {
  log msg = msg <> "/" <> resume ()
  return _ = "end"
}

pub fun result : Unit -> String
result () = {
  log! "a"
  log! "b"
} with accumulating
"#;
    check_result_string("basic_resume_unit", src, "a/b/end");
}

#[test]
fn basic_resume_with_value() {
    let src = r#"module Main

effect Ask {
  fun ask : String -> Int
}

handler answer for Ask {
  ask _ = resume 42
}

pub fun result : Unit -> String
result () = {
  let n = ask! "what?"
  show n
} with answer
"#;
    check_result_string("basic_resume_with_value", src, "42");
}

#[test]
fn basic_abort_no_resume() {
    let src = r#"module Main

import Std.Fail (Fail)

handler to_result_str for Fail String {
  fail e = "err:" <> e
  return v = "ok:" <> v
}

fun maybe_fail : Bool -> String needs {Fail String}
maybe_fail True = fail! "oops"
maybe_fail False = "value"

pub fun result : Unit -> String
result () = maybe_fail True with to_result_str
"#;
    check_result_string("basic_abort_no_resume", src, "err:oops");
}

#[test]
fn basic_abort_returns_value_on_success() {
    let src = r#"module Main

import Std.Fail (Fail)

handler to_result_str for Fail String {
  fail e = "err:" <> e
  return v = "ok:" <> v
}

fun maybe_fail : Bool -> String needs {Fail String}
maybe_fail True = fail! "oops"
maybe_fail False = "value"

pub fun result : Unit -> String
result () = maybe_fail False with to_result_str
"#;
    check_result_string("basic_abort_returns_value_on_success", src, "ok:value");
}

#[test]
fn inline_handler_specializes_open_row_parameterized_effect_slot() {
    // A row-polymorphic function entry may describe its known slot by the
    // effect family's bare declaration name, while its caller has already
    // specialized the runtime entry to `Fail String`. Installing middleware
    // for that application must replace/specialize the one slot rather than
    // make lowering believe a second Fail slot exists.
    let lib = r#"module Middleware.Relay

import Std.Fail (Fail)

pub fun relay : (Unit -> String needs {Fail String, ..e}) -> String
  needs {Fail String, ..e}
relay decoder = decoder () with {
  fail e = fail! ("wrapped:" <> e)
}
"#;
    let main_src = r#"module Main

import Std.Fail (Fail)
import Middleware.Relay (relay)

handler capture for Fail String {
  fail e = "err:" <> e
  return v = "ok:" <> v
}

pub fun result : Unit -> String
result () = relay (fun () -> fail! "boom") with capture
"#;
    check_cross_module(
        "inline_handler_specializes_open_row_parameterized_effect_slot",
        &[("lib/Middleware/Relay.saga", lib)],
        main_src,
        "err:wrapped:boom",
    );
}

#[test]
fn dict_method_effectful_call_threads_evidence() {
    // Trait method calls elaborate to `App(DictMethodAccess, ...)`. When the
    // selected impl declares `needs`, the call must thread evidence/return_k
    // like any other effectful call. Regression test for the bug repro at
    // `examples/bugs/dict-method-effectful-call/`. Exercises both the abort
    // path (Box -1 → fail!) and the success path (Box 5 → 10).
    let src = r#"module Main

import Std.Fail (Fail)

trait Decoder a {
  fun decode : a -> Int needs {..e}
}

type Box = Box Int

impl Decoder for Box needs {Fail String} {
  decode (Box n) = if n < 0 then fail! "neg" else n
}

handler to_result for Fail a {
  fail e = Err e
  return v = Ok v
}

fun describe : Result Int String -> String
describe (Ok n) = "ok:" <> show n
describe (Err e) = "err:" <> e

pub fun result : Unit -> String
result () = {
  let neg = decode (Box (-1)) with to_result
  let pos = decode (Box 5) with to_result
  describe neg <> ";" <> describe pos
}
"#;
    check_result_string(
        "dict_method_effectful_call_threads_evidence",
        src,
        "err:neg;ok:5",
    );
}

#[test]
fn trait_impls_preserve_distinct_neweffect_instances() {
    // Was two applications of `Fail` in one block; they are now two
    // `neweffect` instances (a row holds one application per family).
    let src = r#"
effect Fail e {
  fun fail : e -> a
}

neweffect FailText = Fail String
neweffect FailInt = Fail Int

trait Decode a {
  fun decode : a -> Int needs {..e}
}

type TextInput = TextInput
type IntInput = IntInput

impl Decode for TextInput needs {FailText} {
  decode TextInput = FailText.fail! "text"
}

impl Decode for IntInput needs {FailInt} {
  decode IntInput = FailInt.fail! 7
}

handler text_fail for FailText {
  fail _message = resume 10
}

handler int_fail for FailInt {
  fail _code = resume 32
}

pub fun result : Unit -> String
result () = show ({ decode TextInput + decode IntInput } with {text_fail, int_fail})
"#;
    check_result_string("trait_impl_distinct_applied_effects", src, "42");
}

#[test]
fn cross_module_trait_impls_preserve_distinct_neweffect_instances() {
    // Was two applications of `Fail` in one block; now two `neweffect`
    // instances.
    let lib = r#"module Applied.Decode

pub effect Fail e {
  fun fail : e -> a
}

pub neweffect FailText = Fail String
pub neweffect FailInt = Fail Int

pub trait Decode a {
  fun decode : a -> Int needs {..e}
}

pub type TextInput = TextInput
pub type IntInput = IntInput

impl Decode for TextInput needs {FailText} {
  decode TextInput = FailText.fail! "text"
}

impl Decode for IntInput needs {FailInt} {
  decode IntInput = FailInt.fail! 7
}
"#;
    let main_src = r#"module Main

import Applied.Decode (FailText, FailInt, Decode, TextInput, IntInput)

handler text_fail for FailText {
  fail _message = resume 10
}

handler int_fail for FailInt {
  fail _code = resume 32
}

pub fun result : Unit -> String
result () = show ({ decode TextInput + decode IntInput } with {text_fail, int_fail})
"#;
    check_cross_module(
        "cross_module_trait_impl_distinct_applied_effects",
        &[("lib/Applied/Decode.saga", lib)],
        main_src,
        "42",
    );
}

#[test]
fn nullary_effect_op_performs_immediately() {
    // A zero-parameter effect op (`fun number : Int`) is a saturated perform,
    // not an eta-reduced op reference. `number!` must run the handler and yield
    // the value, not a thunk. Regression for zero-arity effect ops being
    // lowered as `fun () -> perform`.
    let src = r#"module Main

effect Config {
  fun number : Int
}

fun compute : Unit -> Int needs {Config}
compute () = number! + 1

pub fun result : Unit -> String
result () = {
  let n = compute () with { number = resume 41 }
  show n
}
"#;
    check_result_string("nullary_effect_op_performs_immediately", src, "42");
}

#[test]
fn nullary_trait_method_dispatches_by_return_type() {
    // A zero-parameter trait method (`fun default : a`) dispatches purely by
    // return type and is stored in the dict as a zero-arity thunk. Accessing it
    // must apply the thunk so the call yields the value, not the closure.
    let src = r#"module Main

trait LocalDefault a {
  fun default : a
}

impl LocalDefault for Int {
  default = 7
}

impl LocalDefault for String {
  default = "hi"
}

fun an_int : Unit -> Int
an_int () = default + 1

fun a_string : Unit -> String
a_string () = default

pub fun result : Unit -> String
result () = show (an_int ()) <> ";" <> a_string ()
"#;
    check_result_string(
        "nullary_trait_method_dispatches_by_return_type",
        src,
        "8;hi",
    );
}

#[test]
fn derived_record_default_uses_field_defaults() {
    let src = r#"module Main

record Settings {
  retries: Int,
  name: String,
  enabled: Bool,
  labels: List String,
  fallback: Maybe Int
} deriving (Default)

pub fun result : Unit -> String
result () = {
  let settings : Settings = default
  show settings.retries
    <> "|"
    <> settings.name
    <> "|"
    <> show settings.enabled
    <> "|"
    <> debug settings.labels
    <> "|"
    <> debug settings.fallback
}
"#;
    check_result_string(
        "derived_record_default_uses_field_defaults",
        src,
        "0||False|[]|Nothing",
    );
}

#[test]
fn where_bound_trait_method_effect_threads_evidence() {
    // A where-bound dict elaborates to `DictMethodAccess(Var __dict_..., ...)`.
    // The call-effects pre-pass must use the trait method's declared `needs`
    // contract because no concrete impl dict is available at that site.
    let src = r#"module Main

import Std.Fail (Fail)

type DecodeErr = DecodeErr String

trait Decode a {
  fun decode : Int -> a needs {Fail DecodeErr}
}

impl Decode for Int needs {Fail DecodeErr} {
  decode n = if n < 0 then fail! (DecodeErr "neg") else n
}

type Wrap a = Wrap a

impl Decode for Wrap a where {a: Decode} needs {Fail DecodeErr} {
  decode n = Wrap (decode n)
}

handler to_result for Fail a {
  fail e = Err e
  return v = Ok v
}

fun describe_int : Result Int DecodeErr -> String
describe_int (Ok n) = "int-ok:" <> show n
describe_int (Err (DecodeErr e)) = "int-err:" <> e

fun describe_wrap : Result (Wrap Int) DecodeErr -> String
describe_wrap (Ok (Wrap n)) = "wrap-ok:" <> show n
describe_wrap (Err (DecodeErr e)) = "wrap-err:" <> e

pub fun result : Unit -> String
result () = {
  let int_neg = decode (-1) with to_result
  let int_ok = decode 0 with to_result
  let wrap_neg = decode (-1) with to_result
  let wrap_ok = decode 0 with to_result
  describe_int int_neg <> ";" <> describe_int int_ok <> ";" <> describe_wrap wrap_neg <> ";" <> describe_wrap wrap_ok
}
"#;
    check_result_string(
        "where_bound_trait_method_effect_threads_evidence",
        src,
        "int-err:neg;int-ok:0;wrap-err:neg;wrap-ok:0",
    );
}

#[test]
fn op_called_in_a_loop_resumes_each_time() {
    let src = r#"module Main

effect Tick {
  fun tick : String -> String
}

handler counting for Tick {
  tick s = s <> "/" <> resume "x"
}

pub fun result : Unit -> String
result () = {
  let a = tick! "1"
  let b = tick! "2"
  let c = tick! "3"
  a <> b <> c
} with counting
"#;
    // Each tick wraps the body's continuation. The body's tail `a <> b <> c` is
    // evaluated under all three resumes (each resume makes the rest of the body
    // continue with its own value of n). innermost: a=b=c="x" → "xxx".
    check_result_string("op_called_in_a_loop_resumes_each_time", src, "1/2/3/xxx");
}

#[test]
fn lambda_head_effectful_call_threads_evidence() {
    // `(fun x -> ...) y` where the lambda body is effectful. The App head is
    // a Lambda literal — neither Var, QualifiedName, nor DictMethodAccess —
    // so prior to the fix the populator classified the call as Pure and the
    // lowerer emitted a plain `Apply` with no evidence/return_k. The lambda
    // body's `log!` calls then ran against missing evidence and crashed.
    let src = r#"module Main

effect Log {
  fun log : String -> Unit
}

handler accumulating for Log {
  log msg = msg <> "/" <> resume ()
  return _ = "end"
}

pub fun result : Unit -> String
result () = (fun x -> {
  log! x
  log! "y"
}) "a" with accumulating
"#;
    check_result_string(
        "lambda_head_effectful_call_threads_evidence",
        src,
        "a/y/end",
    );
}

#[test]
fn lambda_head_effectful_call_nested_in_outer_effectful_call() {
    // Lambda-headed call appearing as the inner arg of an outer effectful
    // call. Both calls thread evidence; the outer call sequences the inner
    // call as an effectful argument so the inner lambda body's ops have
    // somewhere to resume to.
    //
    // Under a deep handler the inner op's continuation extends up to the
    // `with echo` boundary — it includes the outer `log!`. So this is exactly
    // equivalent to the direct form `log! (log! "inner")` and to the statement
    // form `{ let a = log! "inner"; log! a }`, all of which yield
    // "[inner][x]x":
    //   inner log!"inner" -> "[inner]" <> resume "x"
    //     resume "x" runs the outer log!"x" -> "[x]" <> resume "x" -> "[x]x"
    //   => "[inner]" <> "[x]x" = "[inner][x]x"
    // (An earlier lowering evaluated the inner arg as a *delimited*
    // sub-computation — "[[inner]x]x" — which disagreed with the equivalent
    // direct/statement forms; that inconsistency was the bug.)
    let src = r#"module Main

effect Log {
  fun log : String -> String
}

handler echo for Log {
  log msg = "[" <> msg <> "]" <> resume "x"
}

pub fun result : Unit -> String
result () = log! ((fun n -> log! n) "inner") with echo
"#;
    check_result_string(
        "lambda_head_effectful_call_nested_in_outer_effectful_call",
        src,
        "[inner][x]x",
    );
}

#[test]
fn lambda_head_open_row_call_forwards_evidence() {
    // The lambda head is effect-polymorphic: `(fun f -> f ())` has an open
    // effect row because it calls the callback it receives. The call site must
    // be classified as row-forwarded even though the lambda head itself has no
    // named static effects.
    let src = r#"module Main

effect Log {
  fun log : String -> String
}

handler accumulating for Log {
  log msg = msg <> "/" <> resume "end"
}

pub fun result : Unit -> String
result () = ((fun f -> f ()) (fun () -> log! "x")) with accumulating
"#;
    check_result_string("lambda_head_open_row_call_forwards_evidence", src, "x/end");
}

#[test]
fn lambda_head_pure_call_under_effect_handler_stays_pure() {
    // A pure-bodied lambda head used inside an effectful function should not
    // be misclassified — no evidence/return_k threading. This guards against
    // the populator over-applying the lambda-head rule.
    let src = r#"module Main

effect Log {
  fun log : String -> Unit
}

handler echoing for Log {
  log msg = msg <> "/" <> resume ()
  return _ = "end"
}

pub fun result : Unit -> String
result () = {
  let n = (fun x -> x + 1) 41
  log! (show n)
} with echoing
"#;
    check_result_string(
        "lambda_head_pure_call_under_effect_handler_stays_pure",
        src,
        "42/end",
    );
}

// ---------------------------------------------------------------------------
// Fixtures: nested with blocks (handler stacking)
// ---------------------------------------------------------------------------

#[test]
fn nested_with_two_distinct_effects() {
    let src = r#"module Main

import Std.Fail (Fail)

effect Log {
  fun log : String -> Unit
}

handler collect for Log {
  log msg = msg <> "/" <> resume ()
}

handler to_result_str for Fail String {
  fail e = "err:" <> e
  return v = "ok:" <> v
}

fun work : Unit -> String needs {Log, Fail String}
work () = {
  log! "first"
  log! "second"
  "done"
}

pub fun result : Unit -> String
result () = (work () with to_result_str) with collect
"#;
    check_result_string(
        "nested_with_two_distinct_effects",
        src,
        "first/second/ok:done",
    );
}

#[test]
fn nested_same_effect_inner_shadows_outer() {
    // Two nested handlers for the same effect: the inner one must take ops.
    let src = r#"module Main

effect Log {
  fun log : String -> Unit
}

handler outer for Log {
  log msg = "OUTER:" <> msg <> resume ()
  return _ = ""
}

handler inner for Log {
  log msg = "INNER:" <> msg <> resume ()
  return _ = ""
}

pub fun result : Unit -> String
result () = {
  {
    log! "x"
  } with inner
} with outer
"#;
    // `inner` takes the op and its `with` has the value "INNER:x"; that is
    // the value of the computation `outer` handles, which `outer`'s return
    // clause then replaces.
    check_result_string("nested_same_effect_inner_shadows_outer", src, "");
    let passing_on = src.replace(
        "handler outer for Log {\n  log msg = \"OUTER:\" <> msg <> resume ()\n  return _ = \"\"",
        "handler outer for Log {\n  log msg = \"OUTER:\" <> msg <> resume ()\n  return v = v",
    );
    assert_ne!(passing_on, src);
    check_result_string(
        "nested_same_effect_inner_shadows_outer_passing_on",
        &passing_on,
        "INNER:x",
    );
}

#[test]
fn nested_same_effect_outer_visible_after_inner_block() {
    // Verifies that a nested `with` for the same effect doesn't permanently
    // shadow the outer handler — once we leave the inner block, ops route to
    // the outer handler again.
    let src = r#"module Main

effect Log {
  fun log : String -> Unit
}

handler outer for Log {
  log msg = "O(" <> msg <> ")" <> resume ()
}

handler inner for Log {
  log msg = "I(" <> msg <> ")" <> resume ()
}

pub fun result : Unit -> String
result () = {
  log! "before"
  let mid = { log! "mid"; "M" } with inner
  log! "after"
  mid
} with outer
"#;
    // outer.log "before" -> "O(before)" + resume; resume runs let mid block:
    //   inner.log "mid" -> "I(mid)" + resume -> "M" => "I(mid)M"
    // mid = "I(mid)M". then outer.log "after" -> "O(after)" + resume; resume
    // returns mid's value as the body's tail. Final value = "I(mid)M".
    // Outer chain wraps: "O(before)" + ("O(after)" + "I(mid)M")
    check_result_string(
        "nested_same_effect_outer_visible_after_inner_block",
        src,
        "O(before)O(after)I(mid)M",
    );
}

#[test]
fn nested_with_three_distinct_effects() {
    let src = r#"module Main

import Std.Fail (Fail)

effect Tag {
  fun tag : String -> String
}

effect Log {
  fun log : String -> Unit
}

handler collect for Log {
  log msg = msg <> "/" <> resume ()
}

handler tagger for Tag {
  tag s = resume ("[" <> s <> "]")
}

handler to_result_str for Fail String {
  fail e = "err:" <> e
  return v = "ok:" <> v
}

fun work : Unit -> String needs {Log, Tag, Fail String}
work () = {
  log! "go"
  let t = tag! "name"
  t
}

pub fun result : Unit -> String
result () =
  (((work () with to_result_str) with tagger) with collect)
"#;
    check_result_string("nested_with_three_distinct_effects", src, "go/ok:[name]");
}

// ---------------------------------------------------------------------------
// Fixtures: partial application of effectful functions
// ---------------------------------------------------------------------------

#[test]
fn partial_app_effectful_two_args() {
    let src = r#"module Main

effect Log {
  fun log : String -> Unit
}

handler collect for Log {
  log msg = msg <> "|" <> resume ()
}

fun pair_log : String -> String -> String needs {Log}
pair_log a b = {
  log! a
  log! b
  a <> "+" <> b
}

pub fun result : Unit -> String
result () = {
  let f = pair_log "x"
  f "y"
} with collect
"#;
    check_result_string("partial_app_effectful_two_args", src, "x|y|x+y");
}

#[test]
fn partial_app_effectful_then_apply_under_handler() {
    let src = r#"module Main

import Std.Fail (Fail)

handler to_result_str for Fail String {
  fail e = "err:" <> e
  return v = "ok:" <> v
}

fun checked_div : Int -> Int -> String needs {Fail String}
checked_div _ 0 = fail! "div0"
checked_div x y = show (x / y)

pub fun result : Unit -> String
result () = {
  let by_two = checked_div 10
  by_two 2
} with to_result_str
"#;
    check_result_string(
        "partial_app_effectful_then_apply_under_handler",
        src,
        "ok:5",
    );
}

#[test]
fn partial_app_then_passed_to_higher_order() {
    let src = r#"module Main

effect Log {
  fun log : String -> Unit
}

handler collect for Log {
  log msg = msg <> "/" <> resume ()
}

fun greet : String -> String -> String needs {Log}
greet hi name = {
  log! (hi <> " " <> name)
  hi <> " " <> name
}

fun apply_str : (String -> String needs {Log}) -> String -> String needs {Log}
apply_str f x = f x

pub fun result : Unit -> String
result () = {
  let hello = greet "hello"
  apply_str hello "world"
} with collect
"#;
    check_result_string(
        "partial_app_then_passed_to_higher_order",
        src,
        "hello world/hello world",
    );
}

// ---------------------------------------------------------------------------
// Fixtures: effectful var bindings (let g = factory(); g x)
// ---------------------------------------------------------------------------

#[test]
fn effectful_var_binding_simple() {
    let src = r#"module Main

effect Log {
  fun log : String -> Unit
}

handler collect for Log {
  log msg = msg <> "/" <> resume ()
  return _ = ""
}

fun make_logger : Unit -> (String -> Unit needs {Log})
make_logger () = fun s -> log! s

pub fun result : Unit -> String
result () = {
  let g = make_logger ()
  g "a"
  g "b"
  ()
} with collect
"#;
    check_result_string("effectful_var_binding_simple", src, "a/b/");
}

#[test]
fn effectful_var_binding_with_capture() {
    let src = r#"module Main

effect Log {
  fun log : String -> Unit
}

handler collect for Log {
  log msg = msg <> "/" <> resume ()
  return _ = ""
}

fun mk_prefixed : String -> (String -> Unit needs {Log})
mk_prefixed pre = fun s -> log! (pre <> ":" <> s)

pub fun result : Unit -> String
result () = {
  let info = mk_prefixed "INFO"
  info "hi"
  info "bye"
  ()
} with collect
"#;
    check_result_string(
        "effectful_var_binding_with_capture",
        src,
        "INFO:hi/INFO:bye/",
    );
}

// ---------------------------------------------------------------------------
// Fixtures: multishot resumption
// ---------------------------------------------------------------------------

#[test]
fn multishot_two_resumes_concat() {
    let src = r#"module Main

effect Log {
  fun log : String -> Unit
}

handler double_log for Log {
  log msg = {
    let a = resume ()
    let b = resume ()
    "(" <> msg <> "<" <> a <> "|" <> b <> ">)"
  }
  return _ = "."
}

pub fun result : Unit -> String
result () = {
  log! "X"
} with double_log
"#;
    check_result_string("multishot_two_resumes_concat", src, "(X<.|.>)");
}

#[test]
fn multishot_choose_collects_all() {
    let src = r#"module Main

effect Choose {
  fun choose : List Int -> Int
}

handler all_solutions for Choose {
  choose options = List.flat_map (fun x -> resume x) options
  return v = [v]
}

pub fun result : Unit -> String
result () = {
  let xs = {
    let a = choose! [1, 2]
    let b = choose! [10, 20]
    a + b
  } with all_solutions
  String.join "," (List.map show xs)
}
"#;
    check_result_string("multishot_choose_collects_all", src, "11,21,12,22");
}

#[test]
fn multishot_resume_with_different_values() {
    // Handler resumes with two different values, accumulating both.
    let src = r#"module Main

effect Pick {
  fun pick : Unit -> Int
}

handler both for Pick {
  pick () = {
    let x = resume 1
    let y = resume 2
    x <> "," <> y
  }
  return v = v
}

pub fun result : Unit -> String
result () = {
  let n = pick! ()
  show (n * 10)
} with both
"#;
    check_result_string("multishot_resume_with_different_values", src, "10,20");
}

// ---------------------------------------------------------------------------
// Fixtures: BEAM-native effects
// ---------------------------------------------------------------------------

#[test]
fn beam_ref_basic_get_set() {
    let src = r#"module Main

import Std.Ref (Ref, beam_ref)

pub fun result : Unit -> String
result () = {
  let r = new! 10
  set! r 99
  show (get! r)
} with beam_ref
"#;
    check_result_string("beam_ref_basic_get_set", src, "99");
}

#[test]
fn beam_ref_modify_returns_new() {
    let src = r#"module Main

import Std.Ref (Ref, beam_ref)

pub fun result : Unit -> String
result () = {
  let r = new! 7
  let _ = modify! r (fun n -> n * 2)
  let _ = modify! r (fun n -> n + 1)
  show (get! r)
} with beam_ref
"#;
    check_result_string("beam_ref_modify_returns_new", src, "15");
}

#[test]
fn beam_ref_two_refs_independent() {
    let src = r#"module Main

import Std.Ref (Ref, beam_ref)

pub fun result : Unit -> String
result () = {
  let a = new! 1
  let b = new! 100
  set! a 5
  set! b 200
  show (get! a) <> "," <> show (get! b)
} with beam_ref
"#;
    check_result_string("beam_ref_two_refs_independent", src, "5,200");
}

#[test]
fn beam_actor_self_returns_pid() {
    // Process effect: self! returns this process's pid. Just check it's
    // non-empty (pid printing is opaque).
    let src = r#"module Main

import Std.Actor (Process, Actor, beam_actor)

pub fun result : Unit -> String
result () = {
  let _pid = self! ()
  "self-ok"
} with beam_actor
"#;
    check_result_string("beam_actor_self_returns_pid", src, "self-ok");
}

#[test]
fn beam_actor_send_receive_roundtrip_self() {
    // Send a message to self and receive it back. This avoids the
    // multi-`Actor msg` instantiation issue that arises when spawning
    // a child whose mailbox type differs from the parent's.
    let src = r#"module Main

import Std.Actor (Process, Actor, beam_actor)

pub fun result : Unit -> String
result () = {
  let me = self! ()
  send! me 42
  let answer = receive {
    n -> n
  }
  show answer
} with beam_actor
"#;
    check_result_string("beam_actor_send_receive_roundtrip_self", src, "42");
}

#[test]
fn beam_timer_sleep_no_crash() {
    // sleep! 0 is a no-op-ish call into the runtime; verify it round-trips.
    let src = r#"module Main

import Std.Actor (Timer, beam_actor)

pub fun result : Unit -> String
result () = {
  sleep! 0
  "slept"
} with beam_actor
"#;
    check_result_string("beam_timer_sleep_no_crash", src, "slept");
}

// ---------------------------------------------------------------------------
// Fixtures: mixed BEAM-native + CPS handlers
// ---------------------------------------------------------------------------

#[test]
fn mixed_ref_and_log_effects() {
    let src = r#"module Main

import Std.Ref (Ref, beam_ref)

effect Log {
  fun log : String -> Unit
}

handler collect for Log {
  log msg = msg <> "/" <> resume ()
}

fun work : Unit -> String needs {Ref, Log}
work () = {
  let r = new! 0
  set! r 1
  log! "step1"
  set! r ((get! r) + 5)
  log! "step2"
  show (get! r)
}

pub fun result : Unit -> String
result () = (work () with beam_ref) with collect
"#;
    check_result_string("mixed_ref_and_log_effects", src, "step1/step2/6");
}

#[test]
fn mixed_actor_and_fail() {
    let src = r#"module Main

import Std.Actor (Process, Actor, beam_actor)
import Std.Fail (Fail)

handler to_result_str for Fail String {
  fail e = "err:" <> e
  return v = "ok:" <> v
}

fun maybe : Bool -> String needs {Process, Actor Int, Fail String}
maybe True = fail! "no"
maybe False = {
  let _pid = self! ()
  "yes"
}

pub fun result : Unit -> String
result () = (maybe False with to_result_str) with beam_actor
"#;
    check_result_string("mixed_actor_and_fail", src, "ok:yes");
}

#[test]
fn mixed_ref_and_fail_abort() {
    // Fail handler aborts; ref allocated before the fail call should
    // simply be unreachable after.
    let src = r#"module Main

import Std.Ref (Ref, beam_ref)
import Std.Fail (Fail)

handler to_result_str for Fail String {
  fail e = "err:" <> e
  return v = "ok:" <> v
}

fun work : Unit -> String needs {Ref, Fail String}
work () = {
  let r = new! 100
  set! r 7
  fail! "boom"
  show (get! r)
}

pub fun result : Unit -> String
result () = (work () with to_result_str) with beam_ref
"#;
    check_result_string("mixed_ref_and_fail_abort", src, "err:boom");
}

// ---------------------------------------------------------------------------
// Fixtures: cross-module effectful calls
// ---------------------------------------------------------------------------

#[test]
fn cross_module_basic_effectful_call() {
    let lib = r#"module LogLib

pub effect Log {
  fun log : String -> Unit
}

pub fun shout : String -> String needs {Log}
shout s = {
  log! s
  "S(" <> s <> ")"
}
"#;
    let main_src = r#"module Main

import LogLib (Log, shout)

handler collect for Log {
  log msg = msg <> "/" <> resume ()
}

pub fun result : Unit -> String
result () = (LogLib.shout "hi") with collect
"#;
    check_cross_module(
        "cross_module_basic_effectful_call",
        &[("lib/LogLib.saga", lib)],
        main_src,
        "hi/S(hi)",
    );
}

#[test]
fn cross_module_neweffects_have_distinct_evidence_slots() {
    let lib = r#"module Repos

type UserDb = UserDb
type DataDb = DataDb

effect Repo db {
  fun execute : String -> String
}

pub neweffect UserRepo = Repo UserDb
pub neweffect DataRepo = Repo DataDb

pub fun query_both : Unit -> String needs {UserRepo, DataRepo}
query_both () =
  UserRepo.execute! "users" <> "|" <> DataRepo.execute! "data"
"#;
    let facade = r#"module RepoApi

import Repos (pub ..)
"#;
    let main_src = r#"module Main

import RepoApi (UserRepo, DataRepo, query_both)

handler users for UserRepo {
  execute query = resume ("U:" <> query)
}

handler data for DataRepo {
  execute query = resume ("D:" <> query)
}

pub fun result : Unit -> String
result () = query_both () with {users, data}
"#;
    check_cross_module(
        "cross_module_neweffects_have_distinct_evidence_slots",
        &[("lib/Repos.saga", lib), ("lib/RepoApi.saga", facade)],
        main_src,
        "U:users|D:data",
    );
}

#[test]
fn neweffect_handler_factory_captures_dynamic_handler_and_forwards_open_row() {
    let src = r#"
type TxError e = TransactionFailed | RolledBack e

effect Repo {
  fun read : Unit -> String
  fun transaction :
    (Unit -> Result a e needs {..r})
    -> Result a (TxError e)
}

neweffect AuthRepo = Repo

fun empty_repo : Unit -> Handler Repo
empty_repo () = handler for Repo {
  read () = resume "base"
  transaction body = case body () {
    Ok value -> resume Ok value
    Err error -> resume Err (RolledBack error)
  }
}

fun transaction_with : Handler Repo
  -> Handler AuthRepo
  -> (Unit -> Result a e needs {AuthRepo, ..r})
  -> Result a (TxError e)
  needs {..r}
transaction_with backend nested body =
  Repo.transaction! (fun () -> body () with nested) with backend

fun auth_repo : Handler Repo -> Handler AuthRepo
auth_repo backend = handler for AuthRepo {
  read () = resume (Repo.read! () with backend)
  transaction body = {
    let nested = handler for AuthRepo {
      read () = resume (Repo.read! () with backend)
      transaction _ = resume Err TransactionFailed
    }
    let value = transaction_with backend nested body
    resume value
  }
}

fun program : Unit -> Result String (TxError String) needs {AuthRepo}
program () = AuthRepo.transaction! (fun () -> Ok (AuthRepo.read! ()))

pub fun result : Unit -> String
result () = {
  let base = empty_repo ()
  let auth = auth_repo base
  case (program () with auth) {
    Ok value -> value
    Err _ -> "error"
  }
}
"#;
    check_result_string("neweffect_handler_factory_dynamic_open_row", src, "base");
}

#[test]
fn distinct_applied_fail_effects_in_one_block_are_rejected() {
    // Two applications of one family used to coexist in a block and dispatch
    // by type argument. An effect is now identified by its family alone, so
    // the block's row cannot hold both. (Distinct `neweffect` instances
    // coexisting is covered by the `neweffect` fixtures.)
    let src = r#"
effect Fail e {
  fun fail : e -> a
}

handler string_fail for Fail String {
  fail _message = resume 10
}

handler int_fail for Fail Int {
  fail _code = resume 32
}

fun from_string : Unit -> Int needs {Fail String}
from_string () = fail! "nope"

fun from_int : Unit -> Int needs {Fail Int}
from_int () = fail! 7

pub fun result : Unit -> String
result () = show ({ from_string () + from_int () } with {string_fail, int_fail})
"#;
    assert_one_application_per_family(&typecheck_error(src), "Fail", "Fail String", "Fail Int");
}

#[test]
fn nested_handler_replaces_only_matching_neweffect_instance() {
    // Was `Fail String` and `Fail Int`; now two `neweffect` instances.
    let src = r#"
effect Fail e {
  fun fail : e -> a
}

neweffect FailString = Fail String
neweffect FailInt = Fail Int

handler outer_string for FailString {
  fail _message = resume 1
}

handler inner_string for FailString {
  fail _message = resume 2
}

handler outer_int for FailInt {
  fail _code = resume 10
}

fun from_string : Unit -> Int needs {FailString}
from_string () = FailString.fail! "nope"

fun from_int : Unit -> Int needs {FailInt}
from_int () = FailInt.fail! 7

pub fun result : Unit -> String
result () = show ({
  let inner = from_string () with inner_string
  inner + from_int ()
} with {outer_string, outer_int})
"#;
    check_result_string("nested_applied_effect_shadow", src, "12");
}

#[test]
fn neweffect_handler_factory_coexists_with_sibling_instance() {
    // Was a `Handler (Fail String)` factory next to a `Fail Int` handler; now
    // two `neweffect` instances.
    let src = r#"
effect Fail e {
  fun fail : e -> a
}

neweffect FailString = Fail String
neweffect FailInt = Fail Int

fun make_string_fail : Int -> Handler FailString
make_string_fail fallback = handler for FailString {
  fail _message = resume fallback
}

handler int_fail for FailInt {
  fail _code = resume 32
}

fun from_string : Unit -> Int needs {FailString}
from_string () = FailString.fail! "nope"

fun from_int : Unit -> Int needs {FailInt}
from_int () = FailInt.fail! 7

pub fun result : Unit -> String
result () = {
  let string_fail = make_string_fail 10
  show ({ from_string () + from_int () } with {string_fail, int_fail})
}
"#;
    check_result_string("applied_effect_handler_factory", src, "42");
}

#[test]
fn open_row_inner_handler_preserves_sibling_instance_in_tail() {
    // Was `Fail Int` travelling through the open tail next to a handled
    // `Fail String`; now two `neweffect` instances.
    let src = r#"
effect Fail e {
  fun fail : e -> a
}

neweffect FailString = Fail String
neweffect FailInt = Fail Int

handler outer_string for FailString {
  fail _message = resume 10
}

handler inner_string for FailString {
  fail _message = resume 2
}

handler outer_int for FailInt {
  fail _code = resume 32
}

fun from_string : Unit -> Int needs {FailString}
from_string () = FailString.fail! "nope"

fun from_int : Unit -> Int needs {FailInt}
from_int () = FailInt.fail! 7

fun wrapped : Unit -> Int needs {FailString, ..r}
wrapped () = (from_string () with inner_string) + from_int ()

pub fun result : Unit -> String
result () = show (wrapped () with {outer_string, outer_int})
"#;
    check_result_string("open_row_inner_applied_handler", src, "34");
}

#[test]
fn cross_module_generic_code_cannot_serve_two_applications_in_one_block() {
    // Generic code over `Repo db` used at two databases in one block. That
    // needed two applications of `Repo` in one row and is now rejected;
    // `neweffect` instances are nominal, so generic code written against
    // `Repo db` does not serve them and there is no direct rewrite.
    let lib = r#"module Applied.Repo

pub type UsersDb = UsersDb
pub type DataDb = DataDb

pub effect Repo db {
  fun get : db -> Int
}

pub effect Extra {
  fun extra : Unit -> Int
}

pub fun generic_get : db -> Int needs {Repo db, ..r}
generic_get db = get! db

pub fun forward : db -> Int needs {Repo db, ..r}
forward db = generic_get db

pub fun use_users : Unit -> Int needs {Repo UsersDb, Extra, ..r}
use_users () = generic_get UsersDb + extra! ()
"#;
    let main_src = r#"module Main

import Applied.Repo (UsersDb, DataDb, Repo, Extra, use_users, forward)

handler users_repo for Repo UsersDb {
  get _db = resume 10
}

handler data_repo for Repo DataDb {
  get _db = resume 32
}

handler extra_handler for Extra {
  extra () = resume 100
}

pub fun result : Unit -> String
result () =
  show ({ use_users () + forward DataDb } with {users_repo, data_repo, extra_handler})
"#;
    let message = typecheck_error_cross_module(
        "cross_module_applied_effects_generic_open_row",
        &[("lib/Applied/Repo.saga", lib)],
        main_src,
    );
    assert_one_application_per_family(&message, "Repo", "Repo UsersDb", "Repo DataDb");
}

#[test]
fn imported_nested_handler_specializes_callback_effect_and_preserves_open_tail() {
    let transactions = r#"module Transactions

pub effect Abort e {
  fun abort : e -> a
}

effect InnerTransaction {
  fun transact :
    (Unit -> Result a e needs {Abort e})
    -> Result a e
}

pub effect Repo {
  fun ping : Unit -> Unit
  fun transaction :
    (Unit -> Result a e needs {Repo, Abort e, ..r})
    -> Result a e
    needs {..r}
}

fun inner_transaction : Unit -> Handler InnerTransaction
inner_transaction () = handler for InnerTransaction {
  transact body = {
    let result = body () with {
      abort err = Err err
    }
    resume result
  }
}

fun transaction_repo : Unit -> Handler Repo
transaction_repo () = handler for Repo {
  ping _ = resume ()
  # `e` is chosen by whoever performs `transaction`, so this arm cannot
  # answer with a `String` error (`resume (Err "nested transaction")`).
  transaction _body = resume (panic "nested transaction")
}

pub fun repo : Unit -> Handler Repo
repo () = handler for Repo {
  ping _ = resume ()
  transaction body = {
    let inner = inner_transaction ()
    let scoped_repo = transaction_repo ()
    let result = transact! (fun () -> body () with scoped_repo) with inner
    resume result
  }
}
"#;
    let main_src = r#"module Main

import Transactions (Abort, Repo, repo)

effect Trace {
  fun trace : String -> Unit
}

handler tracing for Trace {
  trace _message = resume ()
}

handler outer_abort for Abort String {
  abort _message = panic "outer abort handler was selected"
}

fun stop : Unit -> Unit needs {Abort String}
stop () = abort! "stop"

fun operation : Unit -> Unit needs {Repo, Abort String, Trace}
operation () = {
  trace! "inside"
  ping! ()
  stop ()
}

fun run : Unit -> Result Int String needs {Repo, Trace, Abort String}
run () = transaction! (fun () -> {
  operation ()
  Ok 42
})

pub fun result : Unit -> String
result () = {
  let installed_repo = repo ()
  case (run () with installed_repo) {
    Err "stop" -> "stopped"
    _ -> "wrong"
  }
} with {tracing, outer_abort}
"#;
    check_cross_module(
        "imported_nested_handler_generic_effect_specialization",
        &[("lib/Transactions.saga", transactions)],
        main_src,
        "stopped",
    );
}

#[test]
fn callback_layout_keeps_unused_effect_before_nonresuming_effect_slot() {
    let src = r#"module Main

effect Rollback e {
  fun rollback : e -> a
}

type Outcome a e = Completed a | Returned e | Aborted e

effect Repo {
  fun transaction :
    (Unit -> Result a e needs {Rollback e, ..r})
    -> Result a e
    needs {..r}
}

fun run_logical :
     Handler Repo
  -> (Unit -> Result a e needs {Repo, Rollback e, ..r})
  -> Result a e
  needs {..r}
run_logical body_repo body = {
  let run_body = fun () -> body () with body_repo
  let outcome = (fun () -> case run_body () {
    Ok value -> Completed value
    Err err -> Returned err
  }) () with {
    rollback err = Aborted err
  }
  case outcome {
    Completed value -> Ok value
    Returned err -> Err err
    Aborted err -> Err err
  }
}

handler body_repo for Repo {
  transaction _body = panic "wrong rollback slot"
}

handler empty_repo for Repo {
  transaction body = resume (run_logical body_repo body)
}

fun transaction :
     (Unit -> Result a e needs {Repo, Rollback e, ..r})
  -> Result a e
  needs {Repo, ..r}
transaction body = transaction! body

pub fun result : Unit -> String
result () = case (transaction (fun () -> {
  let _ = rollback! "stop"
  panic "continued after rollback"
}) with empty_repo) {
  Err "stop" -> "stopped"
  _ -> "wrong"
}
"#;
    check_result_string(
        "callback_layout_keeps_unused_effect_before_nonresuming_slot",
        src,
        "stopped",
    );
}

#[test]
fn closed_lambda_in_open_hof_keeps_tail_shape_for_nested_handler_insertion() {
    let parser = r#"module Parser

pub effect Fail {
  fun fail : String -> String
}

pub effect File {
  fun read : String -> String
}

handler files for File {
  read path = resume ("file:" <> path)
}

pub fun parse : String -> List String needs {Fail}
parse path = [read! path] with files
"#;
    let main_src = r#"module Main

import Std.List
import Parser (Fail, parse)

effect Repo {
  fun run : String -> String
}

handler failures for Fail {
  fail message = resume ("fail:" <> message)
}

handler repository for Repo {
  run query = resume ("repo:" <> query)
}

pub fun result : Unit -> String
result () = case ((List.flat_map (fun _year -> parse "csv") [2012]) with repository) with failures {
  value :: _ -> value
  [] -> "empty"
}
"#;
    check_cross_module(
        "closed_lambda_open_hof_nested_handler_insertion",
        &[("lib/Parser.saga", parser)],
        main_src,
        "file:csv",
    );
}

#[test]
fn closed_imported_function_in_open_hof_drops_tail_before_nested_handler() {
    let parser = r#"module Parser

pub effect Fail {
  fun fail : String -> String
}

pub effect File {
  fun read : String -> String
}

handler files for File {
  read path = resume ("file:" <> path)
}

pub fun parse : String -> List String needs {Fail}
parse path = [read! path] with files
"#;
    let main_src = r#"module Main

import Std.List
import Parser (Fail, parse)

effect Repo {
  fun run : String -> String
}

handler failures for Fail {
  fail message = resume ("fail:" <> message)
}

handler repository for Repo {
  run query = resume ("repo:" <> query)
}

pub fun result : Unit -> String
result () = case ((List.flat_map parse ["csv"]) with repository) with failures {
  value :: _ -> value
  [] -> "empty"
}
"#;
    check_cross_module(
        "closed_imported_function_open_hof_nested_handler",
        &[("lib/Parser.saga", parser)],
        main_src,
        "file:csv",
    );
}

#[test]
fn cross_module_stdlib_fail_handler() {
    let lib = r#"module FailLib

import Std.Fail (Fail)

pub fun safe_div : Int -> Int -> String needs {Fail String}
safe_div _ 0 = fail! "div0"
safe_div x y = show (x / y)
"#;
    let main_src = r#"module Main

import Std.Fail (Fail)
import FailLib (safe_div)

handler to_result_str for Fail String {
  fail e = "err:" <> e
  return v = "ok:" <> v
}

pub fun result : Unit -> String
result () = (FailLib.safe_div 10 0) with to_result_str
"#;
    check_cross_module(
        "cross_module_stdlib_fail_handler",
        &[("lib/FailLib.saga", lib)],
        main_src,
        "err:div0",
    );
}

#[test]
fn cross_module_effectful_call_resume_path() {
    let lib = r#"module FailLib

import Std.Fail (Fail)

pub fun safe_div : Int -> Int -> String needs {Fail String}
safe_div _ 0 = fail! "div0"
safe_div x y = show (x / y)
"#;
    let main_src = r#"module Main

import Std.Fail (Fail)
import FailLib (safe_div)

handler to_result_str for Fail String {
  fail e = "err:" <> e
  return v = "ok:" <> v
}

pub fun result : Unit -> String
result () = (FailLib.safe_div 20 4) with to_result_str
"#;
    check_cross_module(
        "cross_module_effectful_call_resume_path",
        &[("lib/FailLib.saga", lib)],
        main_src,
        "ok:5",
    );
}

#[test]
fn cross_module_handler_factory() {
    // Library exports a handler-producing function; main installs it.
    let lib = r#"module LogLib

pub effect Log {
  fun log : String -> Unit
}

pub fun mk_collect : Unit -> Handler Log
mk_collect () = handler for Log {
  log msg = msg <> "/" <> resume ()
}

pub fun do_work : Unit -> String needs {Log}
do_work () = {
  log! "u"
  log! "v"
  "fin"
}
"#;
    let main_src = r#"module Main

import LogLib (Log, mk_collect, do_work)

pub fun result : Unit -> String
result () = {
  let h = LogLib.mk_collect ()
  LogLib.do_work () with h
}
"#;
    check_cross_module(
        "cross_module_handler_factory",
        &[("lib/LogLib.saga", lib)],
        main_src,
        "u/v/fin",
    );
}

#[test]
fn reexported_handler_factory_can_use_private_nested_factory() {
    let base = r#"module RepoBase

pub effect Repo {
  fun read : Unit -> Int
  fun scope : (Unit -> Int needs {Repo}) -> Int
}

fun private_repo : Int -> Handler Repo
private_repo n = handler for Repo {
  read () = resume n
  scope _body = resume 0
}

pub fun make_repo : Int -> Handler Repo
make_repo n = handler for Repo {
  read () = resume n
  scope body = {
    let nested = private_repo n
    let value = body () with nested
    resume value
  }
}
"#;
    let facade = r#"module RepoFacade

import RepoBase (pub ..)
"#;
    let main_src = r#"module Main

import RepoFacade (Repo, make_repo)

pub fun result : Unit -> String
result () = {
  let repo = make_repo 40
  show (Repo.scope! (fun () -> Repo.read! () + 2) with repo)
}
"#;
    check_cross_module(
        "reexported_handler_factory_private_nested_factory",
        &[("lib/RepoBase.saga", base), ("lib/RepoFacade.saga", facade)],
        main_src,
        "42",
    );
}

#[test]
fn cross_module_partial_app() {
    let lib = r#"module GreetLib

pub effect Log {
  fun log : String -> Unit
}

pub fun greet : String -> String -> String needs {Log}
greet hi name = {
  log! (hi <> " " <> name)
  hi <> " " <> name
}
"#;
    let main_src = r#"module Main

import GreetLib (Log, greet)

handler collect for Log {
  log msg = msg <> "/" <> resume ()
}

pub fun result : Unit -> String
result () = {
  let hi = GreetLib.greet "hello"
  hi "world"
} with collect
"#;
    check_cross_module(
        "cross_module_partial_app",
        &[("lib/GreetLib.saga", lib)],
        main_src,
        "hello world/hello world",
    );
}

#[test]
fn cross_module_two_effects_in_one_call() {
    let lib = r#"module MixLib

import Std.Fail (Fail)

pub effect Log {
  fun log : String -> Unit
}

pub fun work : Int -> String needs {Log, Fail String}
work 0 = fail! "zero"
work n = {
  log! (show n)
  show (n * 2)
}
"#;
    let main_src = r#"module Main

import Std.Fail (Fail)
import MixLib (Log, work)

handler collect for Log {
  log msg = msg <> "/" <> resume ()
}

handler to_result_str for Fail String {
  fail e = "err:" <> e
  return v = "ok:" <> v
}

pub fun result_ok : Unit -> String
result_ok () = ((MixLib.work 3) with to_result_str) with collect

pub fun result : Unit -> String
result () = ((MixLib.work 0) with to_result_str) with collect
"#;
    check_cross_module(
        "cross_module_two_effects_in_one_call",
        &[("lib/MixLib.saga", lib)],
        main_src,
        "err:zero",
    );
}

// ---------------------------------------------------------------------------
// Fixtures: pure return-value sanity (control)
// ---------------------------------------------------------------------------

#[test]
fn control_pure_arithmetic() {
    let src = r#"module Main

pub fun result : Unit -> Int
result () = 1 + 2 * 3
"#;
    check_result_int("control_pure_arithmetic", src, 7);
}

#[test]
fn control_pure_list_sum() {
    let src = r#"module Main

pub fun result : Unit -> Int
result () = List.foldl (fun a b -> a + b) 0 [1, 2, 3, 4, 5]
"#;
    check_result_int("control_pure_list_sum", src, 15);
}

// ---------------------------------------------------------------------------
// Fixtures: handler-bound vars + conditional handler binding
// ---------------------------------------------------------------------------

#[test]
fn handler_bound_to_let_binding() {
    let src = r#"module Main

effect Log {
  fun log : String -> Unit
}

handler collect for Log {
  log msg = msg <> "/" <> resume ()
  return _ = ""
}

pub fun result : Unit -> String
result () = {
  let h = collect
  {
    log! "u"
    log! "v"
    ()
  } with h
}
"#;
    check_result_string("handler_bound_to_let_binding", src, "u/v/");
}

#[test]
fn handler_chosen_conditionally() {
    let src = r#"module Main

effect Log {
  fun log : String -> Unit
}

handler loud for Log {
  log msg = "L:" <> msg <> "/" <> resume ()
  return _ = ""
}

handler quiet for Log {
  log _ = resume ()
  return _ = "Q"
}

pub fun result : Unit -> String
result () = {
  let h = if True then loud else quiet
  {
    log! "x"
    ()
  } with h
}
"#;
    check_result_string("handler_chosen_conditionally", src, "L:x/");
}

#[test]
fn handler_inline_block() {
    let src = r#"module Main

effect Log {
  fun log : String -> Unit
}

pub fun result : Unit -> String
result () = {
  log! "hello"
  "done"
} with {
  log msg = msg <> "/" <> resume ()
  return v = v
}
"#;
    check_result_string("handler_inline_block", src, "hello/done");
}

// ---------------------------------------------------------------------------
// Fixtures: additional coverage
// ---------------------------------------------------------------------------

#[test]
fn multishot_three_resumes() {
    let src = r#"module Main

effect Pick {
  fun pick : Unit -> Int
}

handler triple for Pick {
  pick () = {
    let a = resume 1
    let b = resume 2
    let c = resume 3
    a <> "," <> b <> "," <> c
  }
  return v = v
}

pub fun result : Unit -> String
result () = {
  let n = pick! ()
  show (n * 100)
} with triple
"#;
    check_result_string("multishot_three_resumes", src, "100,200,300");
}

#[test]
fn multishot_choose_with_fail_pruning() {
    let src = r#"module Main

effect Choose {
  fun choose : List Int -> Int
}

effect Prune {
  fun prune : Unit -> a
}

handler all_solutions for Choose, Prune {
  choose options = List.flat_map (fun x -> resume x) options
  prune () = []
  return v = [v]
}

pub fun result : Unit -> String
result () = {
  let xs = {
    let a = choose! [1, 2, 3]
    if a == 2 then prune! () else a
  } with all_solutions
  String.join "," (List.map show xs)
}
"#;
    check_result_string("multishot_choose_with_fail_pruning", src, "1,3");
}

#[test]
fn nested_with_returns_distinct_value() {
    // Two distinct effects in deeply nested fashion. Each handler's
    // value flows up cleanly; the outermost wraps the innermost result.
    let src = r#"module Main

import Std.Fail (Fail)

effect Tag {
  fun tag : String -> String
}

handler tagger for Tag {
  tag s = resume ("[" <> s <> "]")
}

handler to_result_str for Fail String {
  fail e = "err:" <> e
  return v = "ok:" <> v
}

fun work : Unit -> String needs {Tag, Fail String}
work () = {
  let t = tag! "name"
  if t == "[name]" then t else fail! "wrong"
}

pub fun result : Unit -> String
result () = (work () with to_result_str) with tagger
"#;
    check_result_string("nested_with_returns_distinct_value", src, "ok:[name]");
}

// FIXME: `let a = mk_call "alpha"; a (); a (); "tail"` miscompiles. Each
// `a ()` is a mid-block effectful call; the resume continuation produces the
// wrong shape (the runtime gets Unit where the handler's `<>` chain expects
// String). The simpler `let g = factory(); g x` shape (single call, last
// stmt) works — see `effectful_var_binding_simple`.
#[test]
fn effectful_var_binding_deferred_call() {
    // The factory returns a function that captures handler state at call time
    // (not at binding time). Reusing the same binding across multiple sites
    // should route ops to the *current* handler.
    let src = r#"module Main

effect Log {
  fun log : String -> Unit
}

handler collect for Log {
  log msg = msg <> "/" <> resume ()
}

fun mk_call : String -> (Unit -> Unit needs {Log})
mk_call s = fun () -> log! s

pub fun result : Unit -> String
result () = {
  let a = mk_call "alpha"
  let b = mk_call "beta"
  a ()
  b ()
  a ()
  "end"
} with collect
"#;
    check_result_string(
        "effectful_var_binding_deferred_call",
        src,
        "alpha/beta/alpha/end",
    );
}

#[test]
fn ref_inside_effect_handler_persists_across_resumes() {
    // Ref-backed counter incremented on every Log call. Verifies that
    // the BEAM-native Ref handler maintains state across the CPS-shaped
    // continuations of a user-defined effect.
    let src = r#"module Main

import Std.Ref (MutRef, Ref, beam_ref)

effect Log {
  fun log : String -> Unit
}

fun work : MutRef Int -> Unit needs {Log, Ref}
work counter = {
  log! "a"
  log! "b"
  log! "c"
}

pub fun result : Unit -> String
result () = {
  let counter = new! 0
  let _ = work counter with {
    log _ = {
      let _ = modify! counter (fun n -> n + 1)
      resume ()
    }
  }
  show (get! counter)
} with beam_ref
"#;
    check_result_string(
        "ref_inside_effect_handler_persists_across_resumes",
        src,
        "3",
    );
}

#[test]
fn fail_handler_inside_resume_aborts_correctly() {
    // The Fail handler aborts mid-resume in a Log handler; the abort must
    // unwind through the surrounding handler.
    let src = r#"module Main

import Std.Fail (Fail)

effect Log {
  fun log : String -> Unit
}

handler collect for Log {
  log msg = msg <> "/" <> resume ()
}

handler to_result_str for Fail String {
  fail e = "err:" <> e
  return v = "ok:" <> v
}

fun work : Unit -> String needs {Log, Fail String}
work () = {
  log! "before"
  fail! "bang"
  log! "after"
  "tail"
}

pub fun result : Unit -> String
result () = (work () with to_result_str) with collect
"#;
    // log "before" runs through collect; fail! aborts; collect.log's resume
    // returns immediately with the inner Fail's err string; "after" never runs.
    check_result_string(
        "fail_handler_inside_resume_aborts_correctly",
        src,
        "before/err:bang",
    );
}

#[test]
fn cross_module_effectful_var_binding() {
    // The lib exports an effectful function; main partially applies it,
    // binds the result, and calls it twice under a local handler.
    let lib = r#"module GreetLib

pub effect Log {
  fun log : String -> Unit
}

pub fun stamped : String -> String -> Unit needs {Log}
stamped tag name = log! (tag <> ":" <> name)
"#;
    let main_src = r#"module Main

import GreetLib (Log, stamped)

handler collect for Log {
  log msg = msg <> "/" <> resume ()
}

pub fun result : Unit -> String
result () = {
  let info = GreetLib.stamped "INFO"
  info "alice"
  info "bob"
  "done"
} with collect
"#;
    check_cross_module(
        "cross_module_effectful_var_binding",
        &[("lib/GreetLib.saga", lib)],
        main_src,
        "INFO:alice/INFO:bob/done",
    );
}

#[test]
fn cross_module_open_row_higher_order() {
    // The lib takes a callback whose effects forward through ..e. The
    // callback uses Log; main's handler captures it.
    let lib = r#"module HofLib

pub fun apply_twice : (String -> Unit needs {..e}) -> Unit needs {..e}
apply_twice f = {
  f "first"
  f "second"
}
"#;
    let main_src = r#"module Main

import HofLib (apply_twice)

effect Log {
  fun log : String -> Unit
}

handler collect for Log {
  log msg = msg <> "/" <> resume ()
}

pub fun result : Unit -> String
result () = {
  HofLib.apply_twice (fun s -> log! s)
  "end"
} with collect
"#;
    check_cross_module(
        "cross_module_open_row_higher_order",
        &[("lib/HofLib.saga", lib)],
        main_src,
        "first/second/end",
    );
}

#[test]
fn open_cps_function_value_reframes_a_different_static_prefix() {
    // `invoke` exposes a callback frame shaped as {B, ..e}, while `actual`
    // is compiled against {Z, ..r}. Both are open, so the adapter must still
    // move Z into the implementation's first static slot.
    let src = r#"module Main

effect A { fun get_a : Unit -> String }
effect B { fun get_b : Unit -> String }
effect Z { fun get_z : Unit -> String }

handler handle_a for A { get_a () = resume "a" }
handler handle_b for B { get_b () = resume "b" }
handler handle_z for Z { get_z () = resume "z" }

fun actual : Unit -> String needs {Z, ..r}
actual () = get_z! ()

fun invoke : (Unit -> String needs {B, ..e}) -> String needs {A, B, ..e}
invoke callback = {
  let _ = get_a! ()
  callback ()
}

pub fun result : Unit -> String
result () = (((invoke actual) with handle_z) with handle_b) with handle_a

main () = ()
"#;
    check_result_string(
        "open_cps_function_value_reframes_a_different_static_prefix",
        src,
        "z",
    );
}

#[test]
fn cross_module_open_cps_function_value_reframes_a_different_static_prefix() {
    let lib = r#"module OpenAdapter

pub effect A { fun get_a : Unit -> String }
pub effect B { fun get_b : Unit -> String }

pub fun invoke : (Unit -> String needs {B, ..e}) -> String needs {A, B, ..e}
invoke callback = {
  let _ = get_a! ()
  callback ()
}
"#;
    let main_src = r#"module Main

import OpenAdapter (A, B, invoke)

effect Z { fun get_z : Unit -> String }

handler handle_a for A { get_a () = resume "a" }
handler handle_b for B { get_b () = resume "b" }
handler handle_z for Z { get_z () = resume "z" }

fun actual : Unit -> String needs {Z, ..r}
actual () = get_z! ()

pub fun result : Unit -> String
result () = (((invoke actual) with handle_z) with handle_b) with handle_a
"#;
    check_cross_module(
        "cross_module_open_cps_function_value_reframes_a_different_static_prefix",
        &[("lib/OpenAdapter.saga", lib)],
        main_src,
        "z",
    );
}

#[test]
fn nested_cross_module_open_hofs_drop_handled_static_prefix() {
    // `choose` installs Skip around `group`; `group` installs a second Skip
    // around `route`.  The route callback must receive only its ambient Check
    // tail.  Retaining either handled Skip prefix makes `check!` dispatch to a
    // Skip operation closure with the wrong arity.
    let lib = r#"module NestedRoutes

pub effect Skip {
  fun skip : Unit -> a
  fun rejected : String -> a
}

pub fun route :
  (Unit -> String needs {..e}) -> Unit -> String needs {Skip, ..e}
route callback () = callback ()

pub fun choose :
  List (Unit -> String needs {Skip, ..e}) -> Unit -> String needs {..e}
choose routes () = choose_loop routes ()

fun choose_loop :
  List (Unit -> String needs {Skip, ..e}) -> Unit -> String needs {..e}
choose_loop routes () = case routes {
  [] -> "missing"
  current :: rest -> current () with {
    skip () = choose_loop rest ()
    rejected _ = choose_loop rest ()
  }
}

pub fun group :
  List (Unit -> String needs {Skip, ..e}) -> Unit -> String needs {Skip, ..e}
group routes () = choose_or_skip routes ()

fun choose_or_skip :
  List (Unit -> String needs {Skip, ..e}) -> Unit -> String needs {Skip, ..e}
choose_or_skip routes () = case routes {
  [] -> skip! ()
  current :: rest -> current () with {
    skip () = choose_or_skip rest ()
    rejected _ = choose_or_skip rest ()
  }
}
"#;
    let main_src = r#"module Main

import NestedRoutes (choose, group, route)

effect Check {
  fun check : Unit -> Unit
}

handler checks for Check {
  check () = resume ()
}

pub fun result : Unit -> String
result () = {
  let app = choose [group [route (fun () -> {
    check! ()
    "ok"
  })]]
  app ()
} with checks
"#;
    check_cross_module(
        "nested_cross_module_open_hofs_drop_handled_static_prefix",
        &[("lib/NestedRoutes.saga", lib)],
        main_src,
        "ok",
    );
}

#[test]
fn beam_ref_with_fail_recover() {
    let src = r#"module Main

import Std.Ref (MutRef, Ref, beam_ref)
import Std.Fail (Fail)

handler default_zero for Fail String {
  fail _ = resume "0"
}

fun read_or_default : MutRef String -> String needs {Fail String, Ref}
read_or_default r = {
  let s = get! r
  if s == "" then fail! "empty" else s
}

pub fun result : Unit -> String
result () = {
  let a = new! "hello"
  let b = new! ""
  let r1 = read_or_default a with default_zero
  let r2 = read_or_default b with default_zero
  r1 <> "," <> r2
} with beam_ref
"#;
    check_result_string("beam_ref_with_fail_recover", src, "hello,0");
}

#[test]
fn handler_with_state_param_threads_state() {
    // Classic state-passing pattern: handler arms return functions of the
    // current state; each op threads state through.
    let src = r#"module Main

effect Counter {
  fun bump : Unit -> Int
}

fun run_counter : (init: Int) -> (f: Unit -> a needs {Counter}) -> (a, Int)
run_counter init f = {
  let stateful = f () with {
    bump () = fun s -> (resume (s + 1)) (s + 1)
    return v = fun s -> (v, s)
  }
  stateful init
}

pub fun result : Unit -> String
result () = {
  let (final_val, final_state) = run_counter 10 (fun () -> {
    let a = bump! ()
    let b = bump! ()
    let c = bump! ()
    a + b + c
  })
  show final_val <> "/" <> show final_state
}
"#;
    // bump increments state; resume passes new state. With init=10:
    //   a = 11 (state: 11), b = 12 (state: 12), c = 13 (state: 13)
    //   final_val = 11 + 12 + 13 = 36, final_state = 13
    check_result_string("handler_with_state_param_threads_state", src, "36/13");
}

#[test]
fn op_call_with_multiple_args() {
    let src = r#"module Main

effect Combine {
  fun mix : String -> Int -> String
}

handler m for Combine {
  mix s n = resume (s <> ":" <> show n)
}

pub fun result : Unit -> String
result () = {
  let a = mix! "x" 1
  let b = mix! "y" 2
  a <> "," <> b
} with m
"#;
    check_result_string("op_call_with_multiple_args", src, "x:1,y:2");
}

#[test]
fn handler_resume_with_complex_value() {
    let src = r#"module Main

effect Get {
  fun get : Unit -> Maybe Int
}

handler some_42 for Get {
  get () = resume (Just 42)
}

pub fun result : Unit -> String
result () = {
  case get! () {
    Just n -> "got:" <> show n
    Nothing -> "none"
  }
} with some_42
"#;
    check_result_string("handler_resume_with_complex_value", src, "got:42");
}

#[test]
fn inline_handler_multi_arm_adt_patterns_dispatch_by_pattern() {
    let src = r#"module Main

type Reason =
  | First String
  | Second String
  | Third String

effect Fail {
  fun fail : Reason -> a
}

fun call_first : Unit -> String needs {Fail}
call_first () = fail! (First "1st")

fun call_second : Unit -> String needs {Fail}
call_second () = fail! (Second "2nd")

fun call_third : Unit -> String needs {Fail}
call_third () = fail! (Third "3rd")

fun recover : (Unit -> String needs {Fail}) -> String
recover thunk = thunk () with {
  fail (First msg) = "got First: " <> msg
  fail (Second msg) = "got Second: " <> msg
  fail (Third msg) = "got Third: " <> msg
}

pub fun result : Unit -> String
result () =
  recover call_first <> "/" <> recover call_second <> "/" <> recover call_third
"#;
    check_result_string(
        "inline_handler_multi_arm_adt_patterns_dispatch_by_pattern",
        src,
        "got First: 1st/got Second: 2nd/got Third: 3rd",
    );
}

#[test]
fn open_row_callback_param_normalizes_function_value_shape() {
    let src = r#"module Main

effect BeforeFoo {
  fun before : String -> Unit
}

effect Foo {
  fun foo : Unit -> Unit
}

fun bar : Unit -> Unit needs {Foo}
bar () = foo! ()

fun wrap : (Unit -> Unit needs {..e}) -> Unit -> String needs {BeforeFoo, ..e}
wrap f () = {
  before! "before"
  f ()
  before! "after"
  "ok"
}

pub fun result : Unit -> String
result () = {
  wrap bar () with {
    foo () = resume ()
  }
} with {
  before _ = resume ()
}
"#;
    check_result_string(
        "open_row_callback_param_normalizes_function_value_shape",
        src,
        "ok",
    );
}

#[test]
fn open_row_pattern_bound_callback_forwards_static_prefix_and_tail() {
    let src = r#"module Main

effect Foo {
  fun foo : Unit -> Unit
}

effect Skip {
  fun skip : Unit -> a
}

fun do_foo : Unit -> Unit needs {Foo}
do_foo () = foo! ()

fun route : Bool -> (Unit -> Unit needs {..e}) -> Unit -> Unit needs {Skip, ..e}
route match h () =
  if match then h ()
  else skip! ()

fun choose : List (Unit -> Unit needs {Skip, ..e}) -> Unit -> Unit needs {..e}
choose rs () = case rs {
  [] -> ()
  r :: rest -> r () with {
    skip () = choose rest ()
  }
}

pub fun result : Unit -> String
result () = {
  choose [route True do_foo] () with {
    foo () = resume ()
  }
  "ok"
}
"#;
    check_result_string(
        "open_row_pattern_bound_callback_forwards_static_prefix_and_tail",
        src,
        "ok",
    );
}

#[test]
fn imported_handler_factory_captures_nested_open_row_callback_evidence() {
    let factory = r#"module HandlerFactory

pub effect Repo {
  fun run : String -> String
}

type Logger e = Logger (String -> Unit needs {..e})
pub opaque type Config e = Config (Logger e)

pub fun config : (String -> Unit needs {..e}) -> Config e needs {..e}
config sink = Config (Logger sink)

pub fun build : Config e -> Handler Repo needs {..e}
build (Config (Logger sink)) = handler for Repo {
  run value = {
    sink value
    resume value
  }
}

pub fun program : Unit -> String needs {Repo}
program () = run! "hello"
"#;
    let main_src = r#"module Main

import HandlerFactory (config, build, program)

effect Log {
  fun write : String -> Unit
}

handler log_sink for Log {
  write _message = resume ()
}

pub fun result : Unit -> String
result () = {
  let repo = build (config (fun message -> write! message))
  program () with repo
} with log_sink
"#;
    check_cross_module(
        "imported_handler_factory_nested_open_callback_evidence",
        &[("lib/HandlerFactory.saga", factory)],
        main_src,
        "hello",
    );
}

#[test]
fn effectful_handler_factory_results_escape_together_as_first_class_values() {
    let src = r#"module Main

effect Repo {
  fun run : String -> String
}

effect Log {
  fun write : String -> Unit
}

type Logger e = Logger (String -> Unit needs {..e})
opaque type Config e = Config (Logger e)

fun config : (String -> Unit needs {..e}) -> Config e needs {..e}
config sink = Config (Logger sink)

fun build : Config e -> Handler Repo needs {..e}
build (Config (Logger sink)) = handler for Repo {
  run value = {
    sink value
    resume value
  }
}

fun make_handlers : Config e -> (Handler Repo, Handler Repo) needs {..e}
make_handlers cfg = {
  let plain = build cfg
  let logged = build cfg
  (plain, logged)
}

handler log_sink for Log {
  write _message = resume ()
}

fun program : Unit -> String needs {Repo}
program () = run! "hello"

pub fun result : Unit -> String
result () = {
  let cfg = config (fun message -> write! message)
  let (plain, logged) = make_handlers cfg
  let one = program () with plain
  let two = program () with logged
  one <> "/" <> two
} with log_sink
"#;
    check_result_string(
        "effectful_handler_factory_results_escape_together",
        src,
        "hello/hello",
    );
}

#[test]
fn pure_dynamic_handler_results_escape_let_bindings() {
    let src = r#"module Main

effect Repo {
  fun run : String -> String
}

fun identity_handler : Handler Repo -> Handler Repo
identity_handler backend = backend

fun make_handlers : Handler Repo -> (Handler Repo, Handler Repo)
make_handlers backend = {
  let plain = identity_handler backend
  let logged = identity_handler backend
  (plain, logged)
}

handler repo for Repo {
  run value = resume value
}

fun program : Unit -> String needs {Repo}
program () = run! "hello"

pub fun result : Unit -> String
result () = {
  let (plain, logged) = make_handlers repo
  let one = program () with plain
  let two = program () with logged
  one <> "/" <> two
}
"#;
    check_result_string(
        "pure_dynamic_handler_results_escape_let_bindings",
        src,
        "hello/hello",
    );
}

// --- Row widening across multi-element forms (end-to-end) ---
//
// The driving use case: a list of heterogeneous-effect functions passed
// to a dispatch combinator. Today this requires every element to declare
// the union of effects the whole app might use; with the row-widening
// fix, each element declares only what it uses and the row joins at the
// list literal site. Verifies that the per-element CPS-shape adapters
// (`wrap_pure_function_value_as_cps_adapter` and
// `adapt_cps_function_value_to_expected_shape`) project evidence
// correctly when a closed-row element is called via the wider open-row
// element type the joined list produces.

#[test]
fn heterogeneous_effect_list_dispatch_runs_correctly() {
    let src = r#"module Main

effect Foo {
  fun foo : Unit -> String
}

effect Bar {
  fun bar : Unit -> String
}

fun pure_thing : Unit -> String
pure_thing () = "pure"

fun do_foo : Unit -> String needs {Foo}
do_foo () = foo! ()

fun do_bar : Unit -> String needs {Bar}
do_bar () = bar! ()

fun run_all : List (Unit -> String needs {..e}) -> List String needs {..e}
run_all fs = case fs {
  [] -> []
  f :: rest -> f () :: run_all rest
}

pub fun result : Unit -> String
result () = {
  let results = run_all [pure_thing, do_foo, do_bar] with {
    foo () = resume "foo-handled",
    bar () = resume "bar-handled",
  }
  case results {
    a :: b :: c :: _ -> a <> "/" <> b <> "/" <> c
    _ -> "fewer than three results"
  }
}
"#;
    check_result_string(
        "heterogeneous_effect_list_dispatch_runs_correctly",
        src,
        "pure/foo-handled/bar-handled",
    );
}

#[test]
fn narrowed_partial_app_of_cps_function_in_widened_list() {
    // Regression: `wrap pure_fn` partially applies a row-polymorphic
    // function. The type system narrows `..e` to closed empty, but the
    // runtime closure has the CPS calling convention. Without the
    // CPS->pure adapter at the binding site, calling the value via its
    // narrowed pure type would crash with arity mismatch. Joined into
    // a list alongside an effectful element, the codegen must emit
    // adapters on both sides so the list element calling convention
    // is uniform.
    let src = r#"module Main

effect Foo {
  fun foo : Unit -> String
}

fun wrap : (Unit -> String needs {..e}) -> Unit -> String needs {..e}
wrap inner () = inner ()

fun pure_fn : Unit -> String
pure_fn () = "pure"

fun do_foo : Unit -> String needs {Foo}
do_foo () = foo! ()

fun first : List (Unit -> String needs {..e}) -> String needs {..e}
first fs = case fs {
  [] -> "empty"
  f :: _ -> f ()
}

pub fun result : Unit -> String
result () = {
  let wrapped: Unit -> String = wrap pure_fn
  first [wrapped, do_foo] with {
    foo () = resume "foo-handled"
  }
}
"#;
    check_result_string(
        "narrowed_partial_app_of_cps_function_in_widened_list",
        src,
        "pure",
    );
}

#[test]
fn narrowed_cps_partial_app_passed_to_open_row_param() {
    // Like the previous test but the narrowed partial app is then passed
    // as a callback argument to ANOTHER partial application of an
    // open-row function. The outer adapter dispatch must recognize that
    // the actual is a CPS partial-app (not a genuinely-pure function)
    // and forward it unchanged rather than emitting a pure->CPS wrapper
    // around an already-CPS closure.
    let src = r#"module Main

effect Foo {
  fun foo : Unit -> String
}

effect Skip {
  fun skip : Unit -> a
}

fun wrap : String -> (Unit -> String needs {..e}) -> Unit -> String needs {..e}
wrap _ inner () = inner ()

fun route : Bool -> (Unit -> String needs {..e}) -> Unit -> String needs {Skip, ..e}
route m h () =
  if m then h ()
  else skip! ()

fun choose : List (Unit -> String needs {Skip, ..e}) -> Unit -> String needs {..e}
choose rs () = case rs {
  [] -> "no match"
  r :: rest -> r () with {
    skip () = choose rest ()
  }
}

fun pure_fn : Unit -> String
pure_fn () = "pure"

fun do_foo : Unit -> String needs {Foo}
do_foo () = foo! ()

pub fun result : Unit -> String
result () = {
  choose [
    route True (wrap "key" pure_fn),
    route True do_foo,
  ] () with {
    foo () = resume "foo-handled"
  }
}
"#;
    check_result_string(
        "narrowed_cps_partial_app_passed_to_open_row_param",
        src,
        "pure",
    );
}

#[test]
fn imported_open_partial_app_keeps_declared_static_effect_prefix() {
    let routing = r#"module Routing

pub effect Skip {
  fun skip : Unit -> a
}

pub fun route : Bool -> (Unit -> String needs {..e}) -> Unit -> String
  needs {Skip, ..e}
route matches app () =
  if matches then app ()
  else skip! ()

pub fun choose : List (Unit -> String needs {Skip, ..e}) -> Unit -> String
  needs {..e}
choose routes () = case routes {
  [] -> "no match"
  route :: rest -> route () with {
    skip () = choose rest ()
  }
}
"#;
    let main_src = r#"module Main

import Routing (route, choose)

effect Foo {
  fun foo : Unit -> String
}

fun pure : Unit -> String
pure () = "wrong route"

fun use_foo : Unit -> String needs {Foo}
use_foo () = foo! ()

pub fun result : Unit -> String
result () =
  choose [route False pure, route True use_foo] () with {
    foo () = resume "matched"
  }
"#;
    check_cross_module(
        "imported_open_partial_app_static_prefix",
        &[("lib/Routing.saga", routing)],
        main_src,
        "matched",
    );
}

#[test]
fn branch_returning_mixed_callable_values_installs_adapter() {
    let src = r#"module Main

effect Log {
  fun log : String -> Unit
}

handler collect for Log {
  log msg = msg <> "/" <> resume ()
}

fun pure_cb : Unit -> String
pure_cb () = "pure"

fun effect_cb : Unit -> String needs {Log}
effect_cb () = {
  log! "hit"
  "effect"
}

fun choose : Bool -> (Unit -> String needs {Log})
choose flag = if flag then effect_cb else pure_cb

pub fun result : Unit -> String
result () = {
  let f = choose False
  let g = choose True
  let a = f ()
  let b = g ()
  a <> "/" <> b
} with collect
"#;
    check_result_string(
        "branch_returning_mixed_callable_values_installs_adapter",
        src,
        "hit/pure/effect",
    );
}

#[test]
fn intrinsic_dbg_with_effectful_argument_lowers_after_nested_effect() {
    let src = r#"module Main

effect Ask {
  fun ask : Unit -> String
}

handler fixed for Ask {
  ask () = resume "value"
}

pub fun result : Unit -> String
result () = {
  dbg (ask! ())
  "ok"
} with fixed
"#;
    check_result_string(
        "intrinsic_dbg_with_effectful_argument_lowers_after_nested_effect",
        src,
        "ok",
    );
}

#[test]
fn multiple_intrinsics_under_with_boundary_compile_and_resume() {
    let src = r#"module Main

effect Ask {
  fun ask : String -> String
}

handler bracket for Ask {
  ask label = resume ("[" <> label <> "]")
}

pub fun result : Unit -> String
result () = {
  dbg (ask! "a")
  dbg (ask! "b")
  "done"
} with bracket
"#;
    check_result_string(
        "multiple_intrinsics_under_with_boundary_compile_and_resume",
        src,
        "done",
    );
}

#[test]
fn multiple_intrinsics_with_effectful_function_arguments_under_handler_factory() {
    let src = r#"module Main

effect Ask {
  fun ask : String -> String
}

fun answer : String -> String needs {Ask}
answer label = ask! label

fun ask_handler : String -> Handler Ask
ask_handler prefix = handler for Ask {
  ask label = resume (prefix <> label)
}

pub fun result : Unit -> String
result () = {
  let h = ask_handler "["
  {
    dbg (answer "a")
    dbg (answer "b")
    "done"
  } with h
}
"#;
    check_result_string(
        "multiple_intrinsics_with_effectful_function_arguments_under_handler_factory",
        src,
        "done",
    );
}

#[test]
fn pure_only_list_runs_without_adapter_wrapping() {
    // Lists of only-pure elements should not gain spurious effect
    // wrapping. Verifies that the join's all-closed branch returns a
    // closed empty row and the elements are called as plain pure
    // functions.
    let src = r#"module Main

fun a : Unit -> String
a () = "a"

fun b : Unit -> String
b () = "b"

fun c : Unit -> String
c () = "c"

fun first : List (Unit -> String) -> String
first fs = case fs {
  [] -> "empty"
  f :: _ -> f ()
}

pub fun result : Unit -> String
result () = first [a, b, c]
"#;
    check_result_string("pure_only_list_runs_without_adapter_wrapping", src, "a");
}

// ---------------------------------------------------------------------------
// Function representation repros
//
// The reproductions from docs/planning/sound-function-representation.md,
// Appendix A. They failed under the old bare-fun representation and are
// regression tests now that function values are tagged closures.
// ---------------------------------------------------------------------------

/// Typecheck a single-module source and assert it is rejected.
fn check_type_error(fixture: &str, src: &str) {
    let root = fixtures_root_for_main_only();
    let mut checker = make_checker(root.clone());
    let tokens = lexer::Lexer::new(src)
        .lex()
        .unwrap_or_else(|e| panic!("[{fixture}] lex error: {e:?}"));
    let mut program = parser::Parser::new(tokens)
        .parse_program()
        .unwrap_or_else(|e| panic!("[{fixture}] parse error: {e:?}"));
    let imported = saga::derive::collect_imported_decls(&program, checker.module_map());
    let derive_errors = saga::derive::expand_derives(&mut program, &imported);
    assert!(
        derive_errors.is_empty(),
        "[{fixture}] derive error: {:?}",
        derive_errors
    );
    saga::desugar::desugar_program(&mut program);
    checker.set_current_module("Main".to_string());
    let result = checker.check_program(&mut program);
    let _ = std::fs::remove_dir_all(&root);
    assert!(
        result.has_errors(),
        "[{fixture}] expected a type error, but the program typechecked"
    );
}

const REPRO_PRELUDE: &str = r#"module Main

effect Skip { fun skip : Unit -> Int }

fun add : Int -> Int -> Int
add a b = a + b

fun ident : a -> a
ident x = x

fun apply_gen : (a -> b) -> a -> b
apply_gen f x = f x

fun eff : Unit -> Int needs {Skip}
eff () = skip! ()

fun pures : Unit -> List (Unit -> Int)
pures () = [fun () -> 1, fun () -> 2]
"#;

fn repro_src(body: &str) -> String {
    format!("{REPRO_PRELUDE}\n{body}")
}

#[test]
fn repro_a1_case_arms_with_different_conventions() {
    let src = repro_src(
        r#"fun choose : Int -> (Unit -> Int needs {Skip})
choose n = case n {
  0 -> fun () -> 1
  _ -> fun () -> skip! ()
}

pub fun result : Unit -> Int
result () = {
  let f = choose 1
  f () with { skip () = resume 10 }
}
"#,
    );
    check_result_int("repro_a1", &src, 10);
}

#[test]
fn repro_a2_function_through_polymorphic_function() {
    let src = repro_src(
        r#"pub fun result : Unit -> Int
result () = (apply_gen add 1) 2
"#,
    );
    check_result_int("repro_a2", &src, 3);
}

#[test]
fn repro_a3_partial_application_of_call_result() {
    let src = repro_src(
        r#"pub fun result : Unit -> Int
result () = {
  let h = (ident add) 3
  h 4
}
"#,
    );
    check_result_int("repro_a3", &src, 7);
}

#[test]
fn repro_a4_effectful_function_through_polymorphic_function() {
    let src = repro_src(
        r#"fun eadd : Int -> Int -> Int needs {Skip}
eadd a b = a + b + skip! ()

pub fun result : Unit -> Int
result () = {
  let e = apply_gen eadd 1
  e 2 with { skip () = resume 100 }
}
"#,
    );
    check_result_int("repro_a4", &src, 103);
}

#[test]
fn repro_a5_effectful_lambda_in_polymorphic_position() {
    let src = repro_src(
        r#"pub fun result : Unit -> Int
result () = {
  let e = ident (fun x -> x + skip! ())
  e 5 with { skip () = resume 100 }
}
"#,
    );
    check_result_int("repro_a5", &src, 105);
}

#[test]
fn repro_a6_effectful_list_rejected_as_pure_list() {
    let src = repro_src(
        r#"fun sum_pure : List (Unit -> Int) -> Int
sum_pure fs = case fs {
  [] -> 0
  f :: rest -> f () + sum_pure rest
}

fun effs : Unit -> List (Unit -> Int needs {Skip})
effs () = [fun () -> skip! (), fun () -> 2]

pub fun result : Unit -> Int
result () = sum_pure (effs ())
"#,
    );
    check_type_error("repro_a6", &src);
}

// A7 runs correctly once closures are tagged, then becomes a type error when
// the row rule is enforced. This pins the final state.
#[test]
fn repro_a7_pure_list_rejected_as_effectful_list() {
    let src = repro_src(
        r#"fun run_all : List (Unit -> Int needs {Skip}) -> Int needs {Skip}
run_all fs = case fs {
  [] -> 0
  f :: rest -> f () + run_all rest
}

pub fun result : Unit -> Int
result () = run_all (pures ()) with { skip () = resume 100 }
"#,
    );
    check_type_error("repro_a7", &src);
}

#[test]
fn repro_a8_row_variable_instantiated_to_empty_in_list() {
    let src = repro_src(
        r#"fun run_each : List (Unit -> Int needs {..e}) -> Int needs {..e}
run_each fs = case fs {
  [] -> 0
  f :: rest -> f () + run_each rest
}

pub fun result : Unit -> Int
result () = run_each (pures ())
"#,
    );
    check_result_int("repro_a8", &src, 3);
}

#[test]
fn repro_a9_partially_applied_open_row_trait_method() {
    let src = repro_src(
        r#"trait Runner a {
  fun go : a -> Int -> Int needs {..e}
}

type Q = Q

impl Runner for Q needs {Skip} {
  go _ n = n + skip! ()
}

fun use_it : a -> Int needs {..a} where {a: Runner}
use_it x = {
  let f = go x
  f 10
}

pub fun result : Unit -> Int
result () = use_it Q with { skip () = resume 100 }
"#,
    );
    check_result_int("repro_a9", &src, 110);
}

#[test]
fn repro_a10_returned_effectful_lambda_compiles() {
    let src = repro_src(
        r#"fun mk : Unit -> (Unit -> Int needs {Skip})
mk () = fun () -> skip! ()

pub fun result : Unit -> Int
result () = {
  let f = mk ()
  f () with { skip () = resume 1 }
}
"#,
    );
    check_result_int("repro_a10", &src, 1);
}

#[test]
fn repro_a11_effectful_branch_rejected_as_pure() {
    let src = repro_src(
        r#"fun get : Bool -> (Unit -> Int)
get b = if b then eff else (fun () -> 1)

pub fun result : Unit -> Int
result () = (get True) ()
"#,
    );
    check_type_error("repro_a11", &src);
}

#[test]
fn repro_a12_effectful_record_field_rejected_as_pure() {
    let src = repro_src(
        r#"record Box { run : Unit -> Int }

pub fun result : Unit -> Int
result () = {
  let b = Box { run: eff }
  b.run ()
}
"#,
    );
    check_type_error("repro_a12", &src);
}

// ---------------------------------------------------------------------------
// Runtime arity check (plan step A3, decision D1)
//
// Functions are curried in the type system and compiled uncurried, so a
// function value reaching a call site through a type variable, a `let`, a
// field or a list can have any arity. Calls whose callee arity is not known
// statically test it at runtime: an exact match calls directly, too few
// arguments build a partial application, too many call in stages.
// ---------------------------------------------------------------------------

const ARITY_PRELUDE: &str = r#"
fun add3 : Int -> Int -> Int -> Int
add3 a b c = a + b * 10 + c * 100

fun inc : Int -> Int
inc x = x + 1

fun compose : (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)

fun flip : (a -> b -> c) -> b -> a -> c
flip f b a = f a b

fun map_gen : (a -> b) -> List a -> List b
map_gen f xs = case xs {
  [] -> []
  x :: rest -> f x :: map_gen f rest
}

fun sum : List Int -> Int
sum xs = case xs {
  [] -> 0
  x :: rest -> x + sum rest
}

fun eadd : Int -> Int -> Int needs {Skip}
eadd a b = a + b + skip! ()

fun eadd3 : Int -> Int -> Int -> Int needs {Skip}
eadd3 a b c = a + b * 10 + c * 100 + skip! ()
"#;

fn arity_src(body: &str) -> String {
    format!("{REPRO_PRELUDE}{ARITY_PRELUDE}\n{body}")
}

#[test]
fn arity_over_application_through_polymorphic_function() {
    // `apply_gen add 1 2`: the saturated call returns a function value, and
    // the leftover argument is applied to it.
    let src = arity_src(
        r#"pub fun result : Unit -> Int
result () = {
  let a = apply_gen add 1 2
  let b = apply_gen (apply_gen add) 3 4
  let c = ident add3 1 2 3
  let d = apply_gen (ident add3) 1 2 3
  let e = ident ident ident add 5 6
  a + b * 10 + c * 100 + d * 100000 + e * 100000000
}
"#,
    );
    // a = 3, b = 7, c = 321, d = 321, e = 11
    check_result_int("arity_over_application", &src, 1_132_132_173);
}

#[test]
fn arity_under_application_builds_closure_called_later() {
    // `apply_gen add3 1` calls a three-argument fun with one argument inside
    // generic code. The closure it returns is then applied one argument at a
    // time, two at once, and through generic code again.
    let src = arity_src(
        r#"pub fun result : Unit -> Int
result () = {
  let p = apply_gen add3 1
  let q = p 2
  let r = apply_gen p 3
  q 4 + r 5 * 1000 + p 6 7 * 1000000
}
"#,
    );
    // q 4 = 421, r 5 = 531, p 6 7 = 761
    check_result_int("arity_under_application", &src, 761_531_421);
}

#[test]
fn arity_compose_and_flip_over_multi_argument_functions() {
    let src = arity_src(
        r#"pub fun result : Unit -> Int
result () = {
  let a = compose (apply_gen add 10) inc 1
  let b = flip (ident add3) 1 2 3
  let c = compose add inc 1 2
  let d = flip add3 1 2 3
  let e = compose (flip add3 1) inc 1 2
  a + b * 100 + c * 100000 + d * 1000000 + e * 1000000000
}
"#,
    );
    // a = 12, b = 312, c = 4, d = 312, e = add3 2 1 2 = 212
    check_result_int("arity_compose_flip", &src, 212_312_431_212);
}

#[test]
fn arity_multi_argument_functions_in_list_partially_applied_by_generic_code() {
    let src = arity_src(
        r#"fun fns : Unit -> List (Int -> Int -> Int)
fns () = [add, fun a b -> a * b, add3 1]

pub fun result : Unit -> Int
result () = {
  let partials = map_gen (fun f -> f 10) (fns ())
  let direct = sum (map_gen (fun g -> g 2) partials)
  let partials2 = map_gen (flip apply_gen 10) (fns ())
  let generic = sum (map_gen (flip apply_gen 2) partials2)
  direct + generic * 1000
}
"#,
    );
    // 12 + 20 + 301 = 333 both ways
    check_result_int("arity_list_of_functions", &src, 333_333);
}

#[test]
fn arity_field_access_headed_call() {
    let src = arity_src(
        r#"record Ops { run : Int -> Int -> Int }
record Holder a { item : a }

fun unhold : Holder a -> a
unhold h = h.item

pub fun result : Unit -> Int
result () = {
  let ops = Ops { run: add }
  let a = ops.run 1 2
  let p = ops.run 1
  let b = p 5
  let g = Holder { item: add3 }
  let c = g.item 1 2 3
  let d = unhold g 1 2 3
  let h = Holder { item: apply_gen add3 1 }
  let e = h.item 2 3
  a + b * 10 + c * 100 + d * 100000 + e * 100000000
}
"#,
    );
    // a = 3, b = 6, c = 321, d = 321, e = 321
    check_result_int("arity_field_access", &src, 32_132_132_163);
}

#[test]
fn arity_top_level_function_whose_body_returns_a_function() {
    // `stage` is declared with three parameters in its type but written with
    // one; the remaining arguments reach a body that returns a one-argument
    // closure returning another closure.
    let src = arity_src(
        r#"fun stage : Int -> Int -> Int -> Int
stage a = {
  let k = a * 2
  fun b -> {
    let j = k + b
    fun c -> j + c
  }
}

fun via_ident : Int -> Int -> Int -> Int
via_ident = ident stage

pub fun result : Unit -> Int
result () = {
  let a = stage 1 2 3
  let b = apply_gen stage 1 2 3
  let c = via_ident 1 2 3
  let d = (fun x -> {
    let k = x
    fun y -> k + y
  }) 1 2
  a + b * 10 + c * 100 + d * 1000
}
"#,
    );
    // a = b = c = 7, d = 3
    check_result_int("arity_staged_body", &src, 3_777);
}

#[test]
fn arity_pure_trait_method_partially_and_over_applied() {
    // A dictionary slot's arity follows the impl body, not the trait
    // signature: `mk w = fun n -> ...` is stored as a two-argument fun.
    let src = arity_src(
        r#"trait Comb a {
  fun comb : a -> Int -> Int -> Int
}

impl Comb for Int {
  comb a b c = a + b * 10 + c * 100
}

trait Mk a {
  fun mk : a -> (Int -> Int)
}

type Wrap a = Wrap a

impl Mk for Int {
  mk a = {
    let k = a
    fun n -> n + k
  }
}

impl Mk for Wrap a where {a: Mk} {
  mk w = fun n -> case w { Wrap x -> mk x n }
}

fun partial_comb : a -> Int where {a: Comb}
partial_comb x = {
  let p = comb x
  let q = p 2
  q 3
}

fun over_mk : a -> Int where {a: Mk}
over_mk x = mk x 5

fun just_mk : a -> (Int -> Int) where {a: Mk}
just_mk x = mk x

pub fun result : Unit -> Int
result () = {
  let p = comb 1
  let a = p 2 3
  let b = apply_gen (comb 1) 2 3
  let c = partial_comb 1
  let d = over_mk 1 + over_mk (Wrap 2) + mk (Wrap 3) 5 + just_mk (Wrap 4) 5
  a + b * 1000 + c * 1000000 + d * 1000000000
}
"#,
    );
    // a = b = c = 321, d = 6 + 7 + 8 + 9
    check_result_int("arity_trait_methods", &src, 30_321_321_321);
}

#[test]
fn arity_pure_call_with_effectful_arguments() {
    // The callee is a pure function value of unknown arity; its arguments
    // perform effects, so the call is assembled in continuation style.
    let src = arity_src(
        r#"fun use_exact : (Int -> Int -> Int) -> Int needs {Skip}
use_exact f = f (skip! ()) 2

fun use_partial : (Int -> Int -> Int -> Int) -> Int needs {Skip}
use_partial f = {
  let p = f (skip! ())
  p 2 (skip! ())
}

pub fun result : Unit -> Int
result () = {
  let a = use_exact add with { skip () = resume 5 }
  let b = use_exact (apply_gen add3 1) with { skip () = resume 5 }
  let c = use_partial add3 with { skip () = resume 5 }
  a + b * 10 + c * 10000
}
"#,
    );
    // a = 7, b = 251, c = 525
    check_result_int("arity_effectful_arguments", &src, 5_252_517);
}

#[test]
fn arity_function_value_resumed_from_handler() {
    let src = arity_src(
        r#"effect Ask { fun ask : Unit -> (Int -> Int -> Int) }

fun use_ask : Unit -> Int needs {Ask}
use_ask () = {
  let f = ask! ()
  let p = f 1
  let g = ask! ()
  p 2 + g 3 4
}

pub fun result : Unit -> Int
result () = {
  let a = use_ask () with { ask () = resume add }
  let b = use_ask () with { ask () = resume (apply_gen add3 1) }
  a + b * 100
}
"#,
    );
    // a = 3 + 7, b = 211 + 431
    check_result_int("arity_resumed_function_value", &src, 64_210);
}

#[test]
fn arity_partial_application_with_many_remaining_arguments() {
    let src = arity_src(
        r#"fun nine : Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int
nine a b c d e f g h i = a + b + c + d + e + f + g + h + i

pub fun result : Unit -> Int
result () = {
  let p = apply_gen nine 1
  let q = p 2 3 4
  q 5 6 7 8 9
}
"#,
    );
    check_result_int("arity_many_remaining", &src, 45);
}

#[test]
fn arity_effectful_function_partially_applied_by_generic_code() {
    // An effectful function value is a fun with trailing evidence and
    // continuation parameters. A partial application built by the arity check
    // leaves them in place, so the eventual effectful call still works.
    let src = arity_src(
        r#"pub fun result : Unit -> Int
result () = {
  let e = apply_gen eadd3 1
  let a = e 2 3 with { skip () = resume 1000 }
  let e2 = (ident eadd) 1
  let b = e2 2 with { skip () = resume 100 }
  a + b * 10000
}
"#,
    );
    // a = 1321, b = 103
    check_result_int("arity_effectful_partial", &src, 1_031_321);
}

#[test]
fn arity_effectful_function_as_callback_and_in_list() {
    let src = arity_src(
        r#"fun run_cb : (Int -> Int needs {Skip}) -> Int needs {Skip}
run_cb f = f 5

pub fun result : Unit -> Int
result () = {
  let a = run_cb (apply_gen eadd 1) with { skip () = resume 100 }
  let es = map_gen (flip apply_gen 1) [eadd, eadd]
  let b = case es {
    f :: _ -> f 2 with { skip () = resume 100 }
    [] -> 0
  }
  a + b * 1000
}
"#,
    );
    // a = 106, b = 103
    check_result_int("arity_effectful_callback_list", &src, 103_106);
}

#[test]
fn arity_effectful_field_access_headed_call() {
    let src = arity_src(
        r#"record EffOps { run : Int -> Int -> Int needs {Skip} }
record Holder a { item : a }

pub fun result : Unit -> Int
result () = {
  let ops = EffOps { run: eadd }
  let a = ops.run 1 2 with { skip () = resume 100 }
  let g = Holder { item: eadd }
  let b = g.item 1 2 with { skip () = resume 100 }
  let h = Holder { item: apply_gen eadd3 1 }
  let c = h.item 2 3 with { skip () = resume 1000 }
  a + b * 1000 + c * 1000000
}
"#,
    );
    // a = 103, b = 103, c = 1321
    check_result_int("arity_effectful_field_access", &src, 1_321_103_103);
}

// --- Multi-parameter effectful lambdas ---
//
// A lambda's effect row sits on the arrow of its last parameter, like a
// declared function's, so `fun acc x -> .. skip! ()` fits a callback
// parameter typed `b -> a -> b needs {..e}`.

#[test]
fn multi_param_effectful_lambda_as_foldl_callback() {
    let src = r#"module Main

effect Skip { fun skip : Unit -> Int }

fun sum_skip : List Int -> Int needs {Skip}
sum_skip xs = List.foldl (fun acc x -> acc + x + skip! ()) 0 xs

pub fun result : Unit -> Int
result () = sum_skip [1, 2, 3] with { skip () = resume 10 }
"#;
    // 1 + 2 + 3 + three skips
    check_result_int("multi_param_lambda_foldl", src, 36);
}

#[test]
fn multi_param_effectful_lambda_let_bound_and_returned() {
    let src = r#"module Main

effect Skip { fun skip : Unit -> Int }

fun mk : Unit -> (Int -> Int -> Int needs {Skip})
mk () = fun a b -> a + b + skip! ()

fun nested : Unit -> (Int -> Int -> Int needs {Skip})
nested () = fun a -> fun b -> a + b + skip! ()

fun local : Unit -> Int needs {Skip}
local () = {
  let f = fun a b -> a + b + skip! ()
  let u = fun () b -> b + skip! ()
  f 1 2 + u () 4
}

pub fun result : Unit -> Int
result () = {
  let a = (mk ()) 1 2 with { skip () = resume 10 }
  let b = (nested ()) 1 2 with { skip () = resume 10 }
  let c = local () with { skip () = resume 100 }
  a + b * 100 + c * 10000
}
"#;
    // a = 13, b = 13, c = 103 + 104
    check_result_int("multi_param_lambda_shapes", src, 2_071_313);
}

#[test]
fn local_multi_clause_function_with_an_effect_in_a_later_clause() {
    let src = r#"module Main

effect Skip { fun skip : Unit -> Int }

fun later : Int -> Int needs {Skip}
later n = {
  let go 0 = 0
  let go m = m + skip! ()
  go n
}

fun looped : Int -> Int needs {Skip}
looped n = {
  let go 0 acc = acc
  let go m acc = go (m - 1) (acc + skip! ())
  go n 0
}

pub fun result : Unit -> Int
result () = {
  let a = later 3 with { skip () = resume 10 }
  let b = later 0 with { skip () = resume 10 }
  let c = looped 3 with { skip () = resume 10 }
  a + b * 100 + c * 10000
}
"#;
    // a = 13, b = 0, c = 30
    check_result_int("local_multi_clause_effect", src, 300_013);
}

// A lambda performs its operations against the handler in scope where it is
// *called*. Fast-path facts recorded by a `with` that merely encloses the
// lambda lexically (inlined tail-resume value, `no_resume` continuation) must
// not be baked into the lambda body.

#[test]
fn lambda_under_with_uses_call_site_handler_inline_tail_resume() {
    let src = r#"module Main

effect Ask { fun ask : Unit -> Int }

fun run2 : (Unit -> Int needs {Ask}) -> Int
run2 f = f () with { ask () = resume 2 }

pub fun result : Unit -> Int
result () = {
  let outer = ask! ()
  outer * 10 + run2 (fun () -> ask! ())
} with { ask () = resume 1 }
"#;
    check_result_int("lambda_call_site_handler_inline", src, 12);
}

#[test]
fn lambda_under_with_uses_call_site_handler_named_tail_resume() {
    let src = r#"module Main

effect Ask { fun ask : Unit -> Int }

handler one for Ask {
  ask () = resume 1
}

handler two for Ask {
  ask () = resume 2
}

fun run2 : (Unit -> Int needs {Ask}) -> Int
run2 f = f () with two

pub fun result : Unit -> Int
result () = {
  let outer = ask! ()
  let f = fun () -> ask! ()
  outer * 10 + run2 f
} with one
"#;
    check_result_int("lambda_call_site_handler_named", src, 12);
}

#[test]
fn lambda_under_aborting_with_uses_call_site_handler() {
    let src = r#"module Main

effect Ask { fun ask : Unit -> Int }

fun run2 : (Unit -> Int needs {Ask}) -> Int
run2 f = f () with { ask () = resume 2 }

fun guarded : Bool -> Int
guarded abort = {
  if abort then ask! () else run2 (fun () -> ask! () + 5)
} with { ask () = 100 }

pub fun result : Unit -> Int
result () = guarded False + guarded True
"#;
    // a = 2 + 5 (resumed by run2's handler), b = 100 (aborted by the outer one)
    check_result_int("lambda_call_site_handler_abort", src, 107);
}

/// An open-row trait method passed as a value carries its impl's effects on
/// its arrow: the enclosing function declares them and the caller's handler
/// receives the operation at the impl's type.
#[test]
fn trait_method_reference_performs_its_impls_effect_under_the_callers_handler() {
    let src = r#"module Main

effect Fail e { fun fail : e -> Int }

trait Decode a { fun decode : a -> Int needs {..e} }

type TextInput = TextInput

impl Decode for TextInput needs {Fail String} {
  decode _ = fail! "text"
}

fun apply_open : (a -> Int needs {..r}) -> a -> Int needs {..r}
apply_open f x = f x

fun decode_text : Unit -> Int needs {Fail String}
decode_text () = apply_open decode TextInput

pub fun result : Unit -> Int
result () = decode_text () with { fail s = resume (String.length s) }
"#;
    check_result_int("trait_method_reference_impl_effect", src, 4);
}

// ---------------------------------------------------------------------------
// Callback overlay: a callback passed to an effect operation, typed
// `needs {Counter, ..r}`, takes its named effects (`Counter`) from the frame
// the handler arm calls it with and everything in `..r` from the frame the
// operation was performed in. Each handler resumes with a distinct number so
// the result shows which one was reached.
// ---------------------------------------------------------------------------

const OVERLAY_PRELUDE: &str = r#"module Main

effect Log { fun log : Unit -> Int }
effect Counter { fun tick : Unit -> Int }
effect Scope {
  fun scoped : (Unit -> Int needs {Counter, ..r}) -> Int needs {..r}
}
"#;

fn overlay_src(body: &str) -> String {
    format!("{OVERLAY_PRELUDE}\n{body}")
}

/// The arm runs under the outer `Log` handler (2) and the operation is
/// performed under the inner one (1). `Log` is in `..r`, so the callback
/// reaches the inner handler.
#[test]
fn callback_overlay_tail_effect_comes_from_the_perform_site() {
    let src = overlay_src(
        r#"handler scope_h for Scope needs {Log} {
  scoped body = {
    let seen = log! ()
    let r = body () with { tick () = resume 100 }
    resume (r + seen * 1000)
  }
}

fun perform : Unit -> Int needs {Scope, Log}
perform () = scoped! (fun () -> log! () + tick! ())

pub fun result : Unit -> Int
result () = {
  perform () with { log () = resume 1 }
} with { scope_h, log () = resume 2 }
"#,
    );
    // arm's own log = 2, callback's log = 1, callback's tick = 100
    check_result_int("callback_overlay_tail_from_perform_site", &src, 2101);
}

/// The same with a named function as the callback, which is wrapped rather
/// than overlaying in its own body.
#[test]
fn callback_overlay_tail_effect_comes_from_the_perform_site_for_named_callback() {
    let src = overlay_src(
        r#"handler scope_h for Scope needs {Log} {
  scoped body = {
    let seen = log! ()
    let r = body () with { tick () = resume 100 }
    resume (r + seen * 1000)
  }
}

fun work : Unit -> Int needs {Counter, Log}
work () = log! () + tick! ()

fun perform : Unit -> Int needs {Scope, Log}
perform () = scoped! work

pub fun result : Unit -> Int
result () = {
  perform () with { log () = resume 1 }
} with { scope_h, log () = resume 2 }
"#,
    );
    check_result_int("callback_overlay_tail_named_callback", &src, 2101);
}

/// The perform site has a `Counter` handler too (5), but `Counter` is named
/// by the callback's type, so the one the arm installs (100) wins.
#[test]
fn callback_overlay_named_effect_comes_from_the_handler_arm() {
    let src = overlay_src(
        r#"handler scope_h for Scope needs {Log} {
  scoped body = {
    let r = body () with { tick () = resume 100 }
    resume (r + log! () * 1000)
  }
}

fun perform : Unit -> Int needs {Scope, Log, Counter}
perform () = tick! () * 10000 + scoped! (fun () -> log! () + tick! ())

pub fun result : Unit -> Int
result () = {
  perform () with { log () = resume 1, tick () = resume 5 }
} with { scope_h, log () = resume 2 }
"#,
    );
    // perform's own tick = 5, arm's log = 2, callback's tick = 100, log = 1
    check_result_int("callback_overlay_named_from_arm", &src, 52101);
}

/// The arm does not handle `Counter` itself: it passes on the one its
/// handler was installed under (100), not the perform site's (5).
#[test]
fn callback_overlay_named_effect_comes_from_the_handlers_own_frame() {
    let src = overlay_src(
        r#"handler scope_h for Scope needs {Counter, Log} {
  scoped body = resume (body () + log! () * 1000)
}

fun perform : Unit -> Int needs {Scope, Log, Counter}
perform () = scoped! (fun () -> log! () + tick! ())

pub fun result : Unit -> Int
result () = {
  perform () with { log () = resume 1, tick () = resume 5 }
} with { scope_h, log () = resume 2, tick () = resume 100 }
"#,
    );
    check_result_int("callback_overlay_named_from_handler_frame", &src, 2101);
}

/// `Log` is handled only around the perform site; the handler knows nothing
/// about it.
#[test]
fn callback_overlay_reaches_an_effect_only_the_perform_site_has() {
    let src = overlay_src(
        r#"handler scope_h for Scope {
  scoped body = resume (body () with { tick () = resume 100 })
}

fun perform : Unit -> Int needs {Scope, Log}
perform () = scoped! (fun () -> log! () + tick! ())

pub fun result : Unit -> Int
result () = {
  perform () with { log () = resume 1 }
} with scope_h
"#,
    );
    check_result_int("callback_overlay_perform_site_only_effect", &src, 101);
}

/// An operation with a callback performed inside another's callback, each
/// under its own `Log` handler, with a third around the handler.
#[test]
fn callback_overlay_nested_operations_each_keep_their_perform_site() {
    let src = overlay_src(
        r#"handler scope_h for Scope needs {Log} {
  scoped body = {
    let r = body () with { tick () = resume 100 }
    resume (r + log! () * 10000)
  }
}

fun inner : Unit -> Int needs {Scope, Log}
inner () = scoped! (fun () -> log! () + tick! ())

fun outer : Unit -> Int needs {Scope, Log}
outer () = scoped! (fun () -> {
  let nested = inner () with { log () = resume 10 }
  log! () + tick! () + nested
})

pub fun result : Unit -> Int
result () = {
  outer () with { log () = resume 1 }
} with { scope_h, log () = resume 3 }
"#,
    );
    // outer callback: 1 + 100; inner callback: 10 + 100; the arm's own log
    // (3), once per `scoped!`: 2 * 30000
    check_result_int("callback_overlay_nested_operations", &src, 60211);
}

/// Compile a single module and call its entry point `main:main(unit)`.
fn check_main_int(fixture: &str, src: &str, expected: i64) {
    let root = fixtures_root_for_main_only();
    let mut checker = make_checker(root.clone());
    let program = typecheck_source(src, &mut checker, fixture);
    let core = emit_program(&program, "main", &checker, Some("main"));
    let dir = fresh_dir(fixture);
    compile_with_erlc(&dir, &core, "main", fixture);
    let stdout = run_erl(
        &dir,
        "io:format(\"~p\", [main:main(unit)]), init:stop().",
        fixture,
    );
    let _ = std::fs::remove_dir_all(&dir);
    let _ = std::fs::remove_dir_all(&root);
    assert_eq!(
        stdout.trim(),
        expected.to_string(),
        "[{fixture}] result mismatch\nexpected: {expected}\nactual:   {stdout:?}"
    );
}

/// `f` is a function taken out of an empty list, so nothing fixes the effect
/// row of its type and the row `main` infers for itself stays open. `main`
/// has no caller to choose that row or supply handlers for it, so it is the
/// empty row and `main` keeps its one-argument entry point.
#[test]
fn unannotated_main_with_unresolved_row_variable_is_pure() {
    let src = r#"module Main

main () = case [] {
  f :: _ -> f ()
  [] -> 7
}
"#;
    check_main_int("unannotated_main_open_row", src, 7);
}

/// The same through an open-row higher-order function.
#[test]
fn unannotated_main_forwarding_an_unresolved_row_variable_is_pure() {
    let src = r#"module Main

fun apply : (Unit -> a needs {..e}) -> a needs {..e}
apply f = f ()

main () = {
  let fs = []
  case fs {
    f :: _ -> apply f
    [] -> 7
  }
}
"#;
    check_main_int("unannotated_main_open_row_forwarded", src, 7);
}

/// Closing the leftover row variable does not hide a real effect: `Log` is
/// still unhandled in `main` and still an error.
#[test]
fn unannotated_main_with_unresolved_row_variable_still_rejects_named_effects() {
    let message = typecheck_error(
        r#"module Main

effect Log { fun log : Unit -> Int }

main () = case [] {
  f :: _ -> f () + log! ()
  [] -> 7
}
"#,
    );
    assert!(
        message.contains("`main` cannot use `needs`") && message.contains("Log"),
        "{message}"
    );
}

// ---------------------------------------------------------------------------
// Effectful sub-expressions nested inside the arguments of an effectful call.
//
// `fin (1 + g n)` with `fin` and `g` both effectful: the rest of the argument,
// the remaining arguments and the call to `fin` are all part of `g n`'s
// continuation, so a handler that aborts must skip them. Each cell of the grid
// below is run under an aborting handler (the result must be exactly the abort
// value, 1000) and under a resuming handler (the result must be the ordinary
// value, so the fix cannot work by dropping the argument).
// ---------------------------------------------------------------------------

const NESTED_ARG_PRELUDE: &str = r#"module Main

effect Stop { fun stop : Int -> Int }
effect Tick { fun tick : Unit -> Unit }
effect Sink { fun sink : a -> (a -> Int) -> Int }

record Box { value : Int }
type Wrap = Wrap(Int)

fun g : Int -> Int needs {Stop}
g i = stop! i

fun g_st : Int -> Int needs {Stop, Tick}
g_st i = {
  tick! ()
  stop! i
}

fun fin : a -> (a -> Int) -> Int needs {Tick}
fin x proj = {
  tick! ()
  proj x + 100
}

fun fin_st : a -> (a -> Int) -> Int needs {Stop, Tick}
fin_st x proj = {
  tick! ()
  proj x + 100
}

fun finb : Int -> a -> (a -> Int) -> Int needs {Tick}
finb z x proj = {
  tick! ()
  proj x + 100 + z
}

fun id2 : Int -> Int
id2 x = x

fun mkbox : Int -> Box
mkbox v = Box { value: v }

fun boxv : Box -> Int
boxv b = b.value

fun unwrap : Wrap -> Int
unwrap w = case w {
  Wrap(v) -> v
}

fun addp : (Int, Int) -> Int
addp p = case p {
  (a, b) -> a + b
}

fun sum2 : List Int -> Int
sum2 xs = case xs {
  [a, b] -> a + b
  _ -> 0
}

fun sval : String -> Int
sval s = if s == "v3" then 3 else 0
"#;

/// What surrounds the inner effectful call inside the argument. `expr` holds
/// `@` where the inner call goes; `proj` is a pure function turning the
/// argument back into an `Int`; `value` is that `Int` when the inner call
/// yields 3.
struct NestedArgWrapper {
    name: &'static str,
    ty: &'static str,
    expr: &'static str,
    proj: &'static str,
    value: i64,
}

const NESTED_ARG_WRAPPERS: &[NestedArgWrapper] = &[
    NestedArgWrapper {
        name: "bare",
        ty: "Int",
        expr: "@",
        proj: "id2",
        value: 3,
    },
    NestedArgWrapper {
        name: "binop_right",
        ty: "Int",
        expr: "1 + @",
        proj: "id2",
        value: 4,
    },
    NestedArgWrapper {
        name: "binop_left",
        ty: "Int",
        expr: "@ + 1",
        proj: "id2",
        value: 4,
    },
    NestedArgWrapper {
        name: "tuple",
        ty: "(Int, Int)",
        expr: "(@, 1)",
        proj: "addp",
        value: 4,
    },
    NestedArgWrapper {
        name: "constructor",
        ty: "Wrap",
        expr: "Wrap(@)",
        proj: "unwrap",
        value: 3,
    },
    NestedArgWrapper {
        name: "record_field",
        ty: "Box",
        expr: "Box { value: @ }",
        proj: "boxv",
        value: 3,
    },
    NestedArgWrapper {
        name: "record_update",
        ty: "Box",
        expr: "{ mkbox 0 | value: @ }",
        proj: "boxv",
        value: 3,
    },
    NestedArgWrapper {
        name: "list_literal",
        ty: "List Int",
        expr: "[@, 1]",
        proj: "sum2",
        value: 4,
    },
    NestedArgWrapper {
        name: "string_interp",
        ty: "String",
        expr: "$\"v{@}\"",
        proj: "sval",
        value: 3,
    },
    NestedArgWrapper {
        name: "if_condition",
        ty: "Int",
        expr: "if @ == 3 then 5 else 6",
        proj: "id2",
        value: 5,
    },
    NestedArgWrapper {
        name: "if_branch",
        ty: "Int",
        expr: "if 1 == 1 then @ else 6",
        proj: "id2",
        value: 3,
    },
    NestedArgWrapper {
        name: "case_scrutinee",
        ty: "Int",
        expr: "case @ {\n    3 -> 5\n    _ -> 6\n  }",
        proj: "id2",
        value: 5,
    },
    NestedArgWrapper {
        name: "case_arm",
        ty: "Int",
        expr: "case 1 {\n    1 -> @\n    _ -> 6\n  }",
        proj: "id2",
        value: 3,
    },
    NestedArgWrapper {
        name: "field_access",
        ty: "Int",
        expr: "(Box { value: @ }).value",
        proj: "id2",
        value: 3,
    },
    NestedArgWrapper {
        name: "field_of_pure_call",
        ty: "Int",
        expr: "(mkbox (@)).value",
        proj: "id2",
        value: 3,
    },
    NestedArgWrapper {
        name: "pipe",
        ty: "Int",
        expr: "@ |> id2",
        proj: "id2",
        value: 3,
    },
    NestedArgWrapper {
        name: "pure_call",
        ty: "Int",
        expr: "id2 (@)",
        proj: "id2",
        value: 3,
    },
    NestedArgWrapper {
        name: "negation",
        ty: "Int",
        expr: "-(@)",
        proj: "id2",
        value: -3,
    },
    NestedArgWrapper {
        name: "block",
        ty: "Int",
        expr: "{\n    let t = @\n    t + 1\n  }",
        proj: "id2",
        value: 4,
    },
    NestedArgWrapper {
        name: "two_deep",
        ty: "Int",
        expr: "1 + id2 (@ * 2)",
        proj: "id2",
        value: 7,
    },
];

/// The effectful call at the bottom of the argument.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum NestedArgInner {
    Named,
    ClosedParam,
    OpenParam,
    Op,
}

const NESTED_ARG_INNERS: &[NestedArgInner] = &[
    NestedArgInner::Named,
    NestedArgInner::ClosedParam,
    NestedArgInner::OpenParam,
    NestedArgInner::Op,
];

/// The effectful callee whose argument holds the nested call.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum NestedArgOuter {
    Named,
    NamedSecondArg,
    ClosedParam,
    OpenParam,
    Lambda,
    Op,
    InsideConstructor,
    InsideTuple,
}

/// One generated cell: its label and the three function names it defines.
struct NestedArgCell {
    label: String,
    abort_fn: String,
    resume_fn: String,
    resume_value: i64,
}

fn nested_arg_cells(outer: NestedArgOuter) -> (String, Vec<NestedArgCell>) {
    let mut src = String::from(NESTED_ARG_PRELUDE);
    let mut cells = Vec::new();
    for wrapper in NESTED_ARG_WRAPPERS {
        for &inner in NESTED_ARG_INNERS {
            let idx = cells.len();
            let inner_open = inner == NestedArgInner::OpenParam;
            let outer_open = outer == NestedArgOuter::OpenParam;

            // Parameters of the cell function and the values passed for them.
            let mut params: Vec<(&str, String, &str)> = Vec::new();
            // Effects the cell names directly, and those reaching it only
            // through the row variable of an open-row parameter.
            let mut named: Vec<&str> = Vec::new();
            let mut via_row: Vec<&str> = Vec::new();

            let ty = wrapper.ty;
            let callee_ty = |row: &str| format!("({ty} -> ({ty} -> Int) -> Int needs {{{row}}})");
            match outer {
                NestedArgOuter::ClosedParam => {
                    params.push(("h", callee_ty("Tick"), "fin"));
                    named.push("Tick");
                }
                NestedArgOuter::OpenParam => {
                    let passed = if inner_open { "fin_st" } else { "fin" };
                    params.push(("h", callee_ty("..e"), passed));
                    via_row.push("Tick");
                }
                NestedArgOuter::Op => named.push("Sink"),
                _ => named.push("Tick"),
            }
            match inner {
                NestedArgInner::ClosedParam => {
                    params.push(("f", "(Int -> Int needs {Stop})".to_string(), "g"));
                    named.push("Stop");
                }
                NestedArgInner::OpenParam => {
                    let passed = if outer_open { "g_st" } else { "g" };
                    params.push(("f", "(Int -> Int needs {..e})".to_string(), passed));
                    via_row.push("Stop");
                }
                NestedArgInner::Named | NestedArgInner::Op => named.push("Stop"),
            }

            let inner_expr = match inner {
                NestedArgInner::Named => "g 3",
                NestedArgInner::ClosedParam | NestedArgInner::OpenParam => "f 3",
                NestedArgInner::Op => "stop! 3",
            };
            let arg = wrapper.expr.replace('@', inner_expr);
            let proj = wrapper.proj;
            let body = match outer {
                NestedArgOuter::Named => format!("fin ({arg}) {proj}"),
                NestedArgOuter::NamedSecondArg => format!("finb 0 ({arg}) {proj}"),
                NestedArgOuter::ClosedParam | NestedArgOuter::OpenParam => {
                    format!("h ({arg}) {proj}")
                }
                NestedArgOuter::Lambda => format!(
                    "{{\n  let lam = fun x p -> {{\n    tick! ()\n    p x + 100\n  }}\n  lam ({arg}) {proj}\n}}"
                ),
                NestedArgOuter::Op => format!("sink! ({arg}) {proj}"),
                NestedArgOuter::InsideConstructor => {
                    format!("unwrap (Wrap(fin ({arg}) {proj}))")
                }
                NestedArgOuter::InsideTuple => format!("addp (fin ({arg}) {proj}, 0)"),
            };

            let mut row: Vec<String> = named.iter().map(|e| e.to_string()).collect();
            if !via_row.is_empty() {
                row.push("..e".to_string());
            }
            let sig: String = params
                .iter()
                .map(|(_, ty, _)| format!("{ty} -> "))
                .collect();
            let names: String = params.iter().map(|(n, _, _)| format!("{n} ")).collect();
            let passed: String = params.iter().map(|(_, _, p)| format!("{p} ")).collect();
            src.push_str(&format!(
                "\nfun c{idx} : {sig}Unit -> Int needs {{{}}}\nc{idx} {names}() = {body}\n",
                row.join(", ")
            ));

            let handles = |eff: &str| named.contains(&eff) || via_row.contains(&eff);
            let mut common_arms = String::new();
            if handles("Tick") {
                common_arms.push_str(", tick () = resume ()");
            }
            if handles("Sink") {
                common_arms.push_str(", sink x p = resume (p x + 100)");
            }
            for (suffix, stop_arm) in [("abort", "stop i = 1000"), ("resume", "stop i = resume i")]
            {
                src.push_str(&format!(
                    "\npub fun c{idx}_{suffix} : Unit -> Int\nc{idx}_{suffix} () = c{idx} {passed}() with {{ {stop_arm}{common_arms} }}\n"
                ));
            }
            cells.push(NestedArgCell {
                label: format!("{outer:?} / {} / {inner:?}", wrapper.name),
                abort_fn: format!("c{idx}_abort"),
                resume_fn: format!("c{idx}_resume"),
                resume_value: wrapper.value + 100,
            });
        }
    }
    (src, cells)
}

/// Call each exported `Unit -> _` function of the compiled `main` module in
/// one VM, returning `name -> printed result`, with a runtime exception
/// reported as `crash` instead of taking the VM down.
fn call_each_export(
    fixture: &str,
    src: &str,
    functions: &[String],
) -> std::collections::HashMap<String, String> {
    let root = fixtures_root_for_main_only();
    let mut checker = make_checker(root.clone());
    let program = typecheck_source(src, &mut checker, fixture);
    let core = emit_program(&program, "main", &checker, Some("main"));
    let dir = fresh_dir(fixture);
    compile_with_erlc(&dir, &core, "main", fixture);
    let eval = format!(
        "lists:foreach(fun(N) -> R = try erlang:apply(main, N, [unit]) of V -> \
         io_lib:format(\"~0p\", [V]) catch _:_ -> \"crash\" end, \
         io:format(\"~s=~s~n\", [N, R]) end, [{}]), init:stop().",
        functions.join(", ")
    );
    let stdout = run_erl(&dir, &eval, fixture);
    let _ = std::fs::remove_dir_all(&dir);
    let _ = std::fs::remove_dir_all(&root);
    stdout
        .lines()
        .filter_map(|line| line.split_once('='))
        .map(|(name, value)| (name.to_string(), value.to_string()))
        .collect()
}

fn check_nested_arg_grid(fixture: &str, outer: NestedArgOuter) {
    let (src, cells) = nested_arg_cells(outer);
    let functions: Vec<String> = cells
        .iter()
        .flat_map(|c| [c.abort_fn.clone(), c.resume_fn.clone()])
        .collect();
    let results = call_each_export(fixture, &src, &functions);
    let mut failures = Vec::new();
    for cell in &cells {
        let abort = results.get(&cell.abort_fn).map(String::as_str);
        if abort != Some("1000") {
            failures.push(format!(
                "{}: aborting handler gave {abort:?}, expected 1000",
                cell.label
            ));
        }
        let resume = results.get(&cell.resume_fn).map(String::as_str);
        if resume != Some(cell.resume_value.to_string().as_str()) {
            failures.push(format!(
                "{}: resuming handler gave {resume:?}, expected {}",
                cell.label, cell.resume_value
            ));
        }
    }
    assert!(
        failures.is_empty(),
        "[{fixture}] {} of {} cells failed:\n{}",
        failures.len(),
        cells.len(),
        failures.join("\n")
    );
}

#[test]
fn nested_effectful_arg_of_named_effectful_call() {
    check_nested_arg_grid("nested_arg_named", NestedArgOuter::Named);
}

#[test]
fn nested_effectful_arg_in_second_position_of_named_effectful_call() {
    check_nested_arg_grid("nested_arg_named_second", NestedArgOuter::NamedSecondArg);
}

#[test]
fn nested_effectful_arg_of_closed_row_parameter_call() {
    check_nested_arg_grid("nested_arg_closed_param", NestedArgOuter::ClosedParam);
}

#[test]
fn nested_effectful_arg_of_open_row_parameter_call() {
    check_nested_arg_grid("nested_arg_open_param", NestedArgOuter::OpenParam);
}

#[test]
fn nested_effectful_arg_of_local_effectful_lambda_call() {
    check_nested_arg_grid("nested_arg_lambda", NestedArgOuter::Lambda);
}

#[test]
fn nested_effectful_arg_of_effect_operation() {
    check_nested_arg_grid("nested_arg_op", NestedArgOuter::Op);
}

#[test]
fn nested_effectful_arg_of_effectful_call_inside_constructor() {
    check_nested_arg_grid("nested_arg_in_ctor", NestedArgOuter::InsideConstructor);
}

#[test]
fn nested_effectful_arg_of_effectful_call_inside_tuple() {
    check_nested_arg_grid("nested_arg_in_tuple", NestedArgOuter::InsideTuple);
}

/// Other call shapes with an effectful sub-expression in an argument (or in
/// the function position). Each entry is `(label, cell body, value under a
/// resuming handler)`; the cell is `Unit -> Int needs {Stop, Tick}` and may
/// use the parameter-free helpers below. Under the aborting handler every
/// cell must give exactly 1000.
#[test]
fn nested_effectful_arg_in_other_call_shapes() {
    let prelude = r#"module Main

effect Stop { fun stop : Int -> Int }
effect Tick { fun tick : Unit -> Unit }
effect Ask { fun ask : Unit -> Int }

fun g : Int -> Int needs {Stop}
g i = stop! i

fun fin : Int -> Int needs {Tick}
fin x = {
  tick! ()
  x + 100
}

fun fin2 : Int -> Int -> Int needs {Tick}
fin2 x y = {
  tick! ()
  x + y + 100
}

fun mk : Int -> (Int -> Int needs {Tick})
mk a = fun x -> {
  tick! ()
  a + x + 100
}

fun each : (Int -> Int needs {Tick}) -> Int -> Int needs {Tick}
each f x = f x + 100

trait Run a {
  fun run : a -> Int -> Int needs {Tick}
}

impl Run for Int needs {Tick} {
  run a x = {
    tick! ()
    a + x + 100
  }
}

fun id2 : Int -> Int
id2 x = x

fun inc : Int -> Int
inc x = x + 1

fun ident : a -> a
ident x = x

fun eident : a -> a needs {Tick}
eident x = {
  tick! ()
  x
}

fun user : Unit -> Int needs {Ask}
user () = ask! () + 1
"#;
    let cells: &[(&str, &str, i64)] = &[
        // A function that returns an effectful function, called in one go.
        ("returned_function_first_arg", "mk (1 + g 3) 5", 109),
        ("returned_function_rest_arg", "mk 1 (1 + g 3)", 105),
        // A named function applied to more arguments than it takes.
        ("over_applied_effectful_rest", "ident fin (1 + g 3)", 104),
        ("over_applied_pure_rest", "eident inc (1 + g 3)", 5),
        (
            "over_applied_nested_first_arg",
            "ident (if g 3 == 3 then fin else fin) 1",
            101,
        ),
        (
            "over_applied_effectful_first_call",
            "eident (if g 3 == 3 then inc else inc) 1",
            2,
        ),
        // A higher-order function with a pure callback takes the direct
        // (non-CPS) specialization; its other arguments may still perform.
        (
            "hof_direct_nested_arg",
            "each (fun x -> x + 1) (1 + g 3)",
            105,
        ),
        (
            "hof_direct_effectful_arg",
            "each (fun x -> x + 1) (g 3)",
            104,
        ),
        (
            "hof_partial_application_arg",
            "each (fin2 (1 + g 3)) 1",
            205,
        ),
        ("trait_method", "run 1 (1 + g 3)", 105),
        (
            "effectful_head_of_effectful_call",
            "(if g 3 == 3 then fin else fin) 1",
            101,
        ),
        (
            "effectful_head_and_nested_arg",
            "(if g 3 == 3 then fin else fin) (1 + g 3)",
            104,
        ),
        (
            "effectful_head_of_pure_call",
            "{\n  tick! ()\n  let v = (if g 3 == 3 then inc else id2) 1\n  v + 100\n}",
            102,
        ),
        (
            "effectful_head_of_pure_call_in_arg",
            "fin ((if g 3 == 3 then inc else id2) 1)",
            102,
        ),
        (
            "partial_application_bound",
            "{\n  let p = fin2 (1 + g 3)\n  p 1\n}",
            105,
        ),
        ("operator_over_call", "1 + fin (1 + g 3)", 105),
        ("call_in_arg_of_call", "fin (fin (1 + g 3) + 1)", 205),
        // The value passed to `resume` in a handler arm.
        (
            "resume_effectful_call",
            "{\n  tick! ()\n  user () with { ask () = resume (g 3) }\n}",
            4,
        ),
        (
            "resume_nested_call",
            "{\n  tick! ()\n  user () with { ask () = resume (1 + g 3) }\n}",
            5,
        ),
        (
            "resume_nested_call_not_last",
            "{\n  tick! ()\n  user () with { ask () = {\n    let r = resume (1 + g 3)\n    r + 10\n  } }\n}",
            15,
        ),
    ];

    let mut src = String::from(prelude);
    let mut functions = Vec::new();
    for (idx, (_, body, _)) in cells.iter().enumerate() {
        src.push_str(&format!(
            "\nfun c{idx} : Unit -> Int needs {{Stop, Tick}}\nc{idx} () = {body}\n"
        ));
        for (suffix, stop_arm) in [("abort", "stop i = 1000"), ("resume", "stop i = resume i")] {
            src.push_str(&format!(
                "\npub fun c{idx}_{suffix} : Unit -> Int\nc{idx}_{suffix} () = c{idx} () with {{ {stop_arm}, tick () = resume () }}\n"
            ));
            functions.push(format!("c{idx}_{suffix}"));
        }
    }
    let results = call_each_export("nested_arg_other_shapes", &src, &functions);
    let mut failures = Vec::new();
    for (idx, (label, _, resume_value)) in cells.iter().enumerate() {
        let abort = results.get(&format!("c{idx}_abort")).map(String::as_str);
        if abort != Some("1000") {
            failures.push(format!(
                "{label}: aborting handler gave {abort:?}, expected 1000"
            ));
        }
        let resume = results.get(&format!("c{idx}_resume")).map(String::as_str);
        if resume != Some(resume_value.to_string().as_str()) {
            failures.push(format!(
                "{label}: resuming handler gave {resume:?}, expected {resume_value}"
            ));
        }
    }
    assert!(
        failures.is_empty(),
        "{} of {} cells failed:\n{}",
        failures.len(),
        cells.len(),
        failures.join("\n")
    );
}

/// Arguments that perform effects are evaluated left to right, each exactly
/// once, whichever of them are direct effectful calls and whichever merely
/// contain one. The handler resumes and prepends the operation's argument to
/// the result, so the result spells out the order the operations ran in.
#[test]
fn nested_effectful_args_evaluate_left_to_right_once() {
    let prelude = r#"module Main

effect Mark { fun mark : Int -> Int }
effect Note { fun note : Int -> Int }
effect Sink { fun sink : Int -> Int -> Int }

fun m : Int -> Int needs {Mark}
m i = mark! i

fun n : Int -> Int needs {Note}
n i = note! i

fun noted2 : Int -> Int -> Int needs {Note}
noted2 a b = {
  let z = note! 9
  a * 10 + b
}

fun fin2 : Int -> Int -> Int needs {Mark}
fin2 a b = {
  let z = mark! 9
  a * 10 + b
}

fun fin3 : Int -> Int -> Int -> Int needs {Mark}
fin3 a b c = {
  let z = mark! 9
  a * 100 + b * 10 + c
}

fun id2 : Int -> Int
id2 x = x
"#;
    // (label, expression of type Int, expected result)
    let cells: &[(&str, &str, &str)] = &[
        ("named_both_nested", "fin2 (1 + m 1) (2 + m 2)", "129=24"),
        ("named_direct_then_nested", "fin2 (m 1) (2 + m 2)", "129=14"),
        ("named_nested_then_direct", "fin2 (1 + m 1) (m 2)", "129=22"),
        (
            "named_pure_between",
            "fin3 (1 + m 1) (id2 5) (2 + m 2)",
            "129=254",
        ),
        (
            "named_two_in_one_arg",
            "fin2 (m 1 + m 2) (m 3 * m 4)",
            "12349=42",
        ),
        (
            "named_nested_calls",
            "fin2 (fin2 (m 1) (1 + m 2)) (m 3 + 1)",
            "12939=134",
        ),
        ("closed_param", "h (1 + f 1) (2 + f 2)", "129=24"),
        ("open_param", "ho (1 + fo 1) (2 + fo 2)", "129=24"),
        (
            "lambda",
            "{\n    let lam = fun a b -> {\n      let z = mark! 9\n      a * 10 + b\n    }\n    lam (1 + m 1) (2 + m 2)\n  }",
            "129=24",
        ),
        ("operation", "sink! (1 + m 1) (2 + m 2)", "12=24"),
        (
            "tuple_of_calls",
            "case (fin2 (1 + m 1) 0, 2 + m 2) {\n    (a, b) -> a + b\n  }",
            "192=24",
        ),
    ];

    let mut src = String::from(prelude);
    let mut functions = Vec::new();
    for (idx, (_, expr, _)) in cells.iter().enumerate() {
        src.push_str(&format!(
            r#"
fun c{idx} : (Int -> Int needs {{Mark}}) -> (Int -> Int -> Int needs {{Mark}}) -> (Int -> Int needs {{..e}}) -> (Int -> Int -> Int needs {{..e}}) -> Unit -> String needs {{Mark, Sink, ..e}}
c{idx} f h fo ho () = {{
  let r = {expr}
  "=" <> show r
}}

pub fun c{idx}_run : Unit -> String
c{idx}_run () = c{idx} m fin2 n noted2 () with {{
  mark i = {{
    let rest = resume i
    show i <> rest
  }},
  note i = {{
    let rest = resume i
    show i <> rest
  }},
  sink a b = resume (a * 10 + b),
}}
"#
        ));
        functions.push(format!("c{idx}_run"));
    }
    let results = call_each_export("nested_arg_order", &src, &functions);
    let mut failures = Vec::new();
    for (idx, (label, _, expected)) in cells.iter().enumerate() {
        let got = results.get(&format!("c{idx}_run")).map(String::as_str);
        // Strings print as Erlang binaries: <<"129=24">>.
        let want = format!("<<\"{expected}\">>");
        if got != Some(want.as_str()) {
            failures.push(format!("{label}: got {got:?}, expected {want}"));
        }
    }
    assert!(
        failures.is_empty(),
        "{} of {} cells failed:\n{}",
        failures.len(),
        cells.len(),
        failures.join("\n")
    );
}

// ---------------------------------------------------------------------------
// Let-generalised function values
//
// `let run = fun g -> g ()` has the scheme
// `(Unit -> a needs {..e}) -> a needs {..e}`, so the closure is built as a
// tagged CPS closure. A use that instantiates `e` to the empty row has a pure
// type, so a tagged closure legitimately reaches a pure call site. At that
// instance it performs nothing of its own: `saga_runtime:apply_n/2` runs it
// with an empty evidence frame and an identity continuation. The same holds
// for any value whose type quantifies a row variable, `let` or not.
// ---------------------------------------------------------------------------

fn let_poly_int(fixture: &str, body: &str, expected: i64) {
    let src = repro_src(&format!(
        "pub fun result : Unit -> Int\nresult () = {{\n{body}\n}}\n"
    ));
    check_result_int(fixture, &src, expected);
}

#[test]
fn let_poly_called_at_pure_instance() {
    let_poly_int(
        "let_poly_called_pure",
        r#"  let run = fun g -> g ()
  run (fun () -> 3)"#,
        3,
    );
}

#[test]
fn let_poly_called_at_effectful_instance() {
    let_poly_int(
        "let_poly_called_effectful",
        r#"  let run = fun g -> g ()
  run (fun () -> skip! () + 1) with { skip () = resume 10 }"#,
        11,
    );
}

#[test]
fn let_poly_passed_where_pure_function_expected() {
    let src = repro_src(
        r#"fun use_pure : ((Unit -> Int) -> Int) -> Int
use_pure h = h (fun () -> 4)

pub fun result : Unit -> Int
result () = {
  let run = fun g -> g ()
  use_pure run
}
"#,
    );
    check_result_int("let_poly_passed_pure", &src, 4);
}

#[test]
fn let_poly_passed_where_effectful_function_expected() {
    let src = repro_src(
        r#"fun use_eff : ((Unit -> Int needs {Skip}) -> Int needs {Skip}) -> Int needs {Skip}
use_eff h = h eff

pub fun result : Unit -> Int
result () = {
  let run = fun g -> g ()
  use_eff run with { skip () = resume 20 }
}
"#,
    );
    check_result_int("let_poly_passed_effectful", &src, 20);
}

#[test]
fn let_poly_passed_where_open_row_function_expected() {
    let src = repro_src(
        r#"fun use_open : ((Unit -> Int needs {..e}) -> Int needs {..e}) -> (Unit -> Int needs {..e}) -> Int needs {..e}
use_open h g = h g

pub fun result : Unit -> Int
result () = {
  let run = fun g -> g ()
  let a = use_open run (fun () -> 1)
  let b = use_open run eff with { skip () = resume 20 }
  a + b
}
"#,
    );
    check_result_int("let_poly_passed_open", &src, 21);
}

#[test]
fn let_poly_passed_to_pure_stdlib_callback() {
    let src = r#"module Main

import Std.List

pub fun result : Unit -> Int
result () = {
  let app = fun f x -> f x
  let ys = List.map (app (fun n -> n + 1)) [1, 2, 3]
  List.foldl (fun acc n -> acc + n) 0 ys
}
"#;
    check_result_int("let_poly_stdlib_callback", src, 9);
}

#[test]
fn let_poly_stored_in_list_at_pure_instance() {
    let src = repro_src(
        r#"fun first : List ((Unit -> Int) -> Int) -> Int
first fs = case fs {
  f :: _ -> f (fun () -> 5)
  [] -> 0
}

pub fun result : Unit -> Int
result () = {
  let run = fun g -> g ()
  first [run]
}
"#,
    );
    check_result_int("let_poly_stored_list", &src, 5);
}

#[test]
fn let_poly_stored_in_record_at_pure_instance() {
    let src = repro_src(
        r#"record Holder { run : (Unit -> Int) -> Int }

pub fun result : Unit -> Int
result () = {
  let run = fun g -> g ()
  let h = Holder { run: run }
  h.run (fun () -> 6)
}
"#,
    );
    check_result_int("let_poly_stored_record", &src, 6);
}

#[test]
fn let_poly_returned_at_pure_instance() {
    let src = repro_src(
        r#"fun mk : Unit -> ((Unit -> Int) -> Int)
mk () = {
  let run = fun g -> g ()
  run
}

pub fun result : Unit -> Int
result () = (mk ()) (fun () -> 7)
"#,
    );
    check_result_int("let_poly_returned_pure", &src, 7);
}

#[test]
fn let_poly_returned_at_effectful_instance() {
    let src = repro_src(
        r#"fun mk : Unit -> ((Unit -> Int needs {Skip}) -> Int needs {Skip})
mk () = {
  let run = fun g -> g ()
  run
}

pub fun result : Unit -> Int
result () = (mk ()) eff with { skip () = resume 8 }
"#,
    );
    check_result_int("let_poly_returned_effectful", &src, 8);
}

#[test]
fn let_poly_used_at_two_instances_in_one_scope() {
    let_poly_int(
        "let_poly_two_instances",
        r#"  let run = fun g -> g ()
  let a = run (fun () -> 1)
  let b = run (fun () -> skip! ()) with { skip () = resume 10 }
  let c = run (fun () -> 100)
  a + b + c"#,
        111,
    );
}

// A local function definition (`let run g = ...`) is not generalised at all:
// it is checked against one monomorphic type, so each use below gets its own
// definition. It is compiled like a named function, with a direct entry
// point.
#[test]
fn let_poly_local_function_definition_at_pure_instance() {
    let src = repro_src(
        r#"fun use_pure : ((Unit -> Int) -> Int) -> Int
use_pure h = h (fun () -> 4)

pub fun result : Unit -> Int
result () = {
  let run g = g ()
  let again g = g ()
  run (fun () -> 1) + use_pure again
}
"#,
    );
    check_result_int("let_poly_letfun_pure", &src, 5);
}

#[test]
fn let_poly_local_function_definition_at_effectful_instance() {
    let src = repro_src(
        r#"fun use_eff : ((Unit -> Int needs {Skip}) -> Int needs {Skip}) -> Int needs {Skip}
use_eff h = h eff

pub fun result : Unit -> Int
result () = {
  let run g = g ()
  let again g = g ()
  { run (fun () -> skip! ()) + use_eff again } with { skip () = resume 10 }
}
"#,
    );
    check_result_int("let_poly_letfun_effectful", &src, 20);
}

#[test]
fn let_poly_nested_capture() {
    let_poly_int(
        "let_poly_nested",
        r#"  let run = fun g -> g ()
  let twice = fun g -> run g + run g
  let a = twice (fun () -> 2)
  let b = twice (fun () -> skip! ()) with { skip () = resume 10 }
  a + b"#,
        24,
    );
}

#[test]
fn let_poly_alias_of_generalised_binding() {
    let_poly_int(
        "let_poly_alias",
        r#"  let run = fun g -> g ()
  let again = run
  let a = again (fun () -> 2)
  let b = again eff with { skip () = resume 10 }
  a + b"#,
        12,
    );
}

#[test]
fn let_poly_two_parameters() {
    let_poly_int(
        "let_poly_two_params",
        r#"  let app = fun f x -> f x
  let a = app (fun n -> n + 1) 1
  let inc = app (fun n -> n + 1)
  let b = inc 10
  let c = app (fun n -> n + skip! ()) 100 with { skip () = resume 1000 }
  a + b + c"#,
        1113,
    );
}

#[test]
fn let_poly_binding_of_open_row_named_function() {
    let src = repro_src(
        r#"fun call : (Unit -> Int needs {..e}) -> Int needs {..e}
call g = g ()

pub fun result : Unit -> Int
result () = {
  let run = call
  let a = run (fun () -> 3)
  let b = run eff with { skip () = resume 40 }
  a + b
}
"#,
    );
    check_result_int("let_poly_named_alias", &src, 43);
}

#[test]
fn let_poly_effect_reaches_innermost_handler() {
    let_poly_int(
        "let_poly_innermost_handler",
        r#"  let run = fun g -> g ()
  let outer = {
    let inner = run (fun () -> skip! ()) with { skip () = resume 1 }
    inner + run (fun () -> skip! ())
  } with { skip () = resume 10 }
  outer + run (fun () -> 100)"#,
        111,
    );
}

#[test]
fn let_poly_aborting_handler_still_aborts() {
    let_poly_int(
        "let_poly_abort",
        r#"  let run = fun g -> g () + 1000
  let a = run (fun () -> 1)
  let b = { run (fun () -> skip! ()) + 5000 } with { skip () = 7 }
  a + b"#,
        1008,
    );
}

// The first arrow of `f` is pure at this instance and the second is not.
#[test]
fn let_poly_pure_prefix_before_an_effectful_arrow() {
    let_poly_int(
        "let_poly_pure_prefix",
        r#"  let f = fun g -> {
    let r = g ()
    fun h -> r + h ()
  }
  let a = f (fun () -> 1) (fun () -> skip! ()) with { skip () = resume 10 }
  let p = f (fun () -> 2)
  let b = p (fun () -> skip! ()) with { skip () = resume 20 }
  let c = f (fun () -> 3) (fun () -> 4)
  let d = { f (fun () -> skip! ()) (fun () -> 1000) } with { skip () = 500 }
  a + b + c + d"#,
        540,
    );
}

#[test]
fn let_poly_shadowed_by_a_monomorphic_binding() {
    let_poly_int(
        "let_poly_shadowed",
        r#"  let run = fun g -> g ()
  let a = run (fun () -> 1)
  let b = (fun run -> run 10) (fun n -> n + 1)
  let c = run (fun () -> 100)
  let run = fun n -> n + 1000
  a + b + c + run 0"#,
        1112,
    );
}

// The closure sits inside a data structure, so no reference to a binding
// could have converted it.
#[test]
fn let_poly_closure_held_in_tuple() {
    let_poly_int(
        "let_poly_tuple",
        r#"  let run = fun g -> g ()
  let p = (run, 1)
  let (f, n) = p
  let a = f (fun () -> 2) + n
  let (h, _) = p
  let b = h eff with { skip () = resume 10 }
  a + b"#,
        13,
    );
}

#[test]
fn let_poly_closure_held_in_generalised_list() {
    let_poly_int(
        "let_poly_generalised_list",
        r#"  let run = fun g -> g ()
  let fs = [run]
  let a = case fs {
    f :: _ -> f (fun () -> 5)
    [] -> 0
  }
  let b = case fs {
    f :: _ -> f eff
    [] -> 0
  } with { skip () = resume 30 }
  a + b"#,
        35,
    );
}

const OPEN_ROW_LIST: &str = r#"fun mk : Unit -> List ((Unit -> Int needs {..e}) -> Int needs {..e})
mk () = [fun g -> g () + 1000]
"#;

// No `let` generalisation at all: the caller of `mk` picks the row.
#[test]
fn open_row_closure_from_function_used_at_pure_instance() {
    let src = repro_src(&format!(
        r#"{OPEN_ROW_LIST}
pub fun result : Unit -> Int
result () = case mk () {{
  f :: _ -> f (fun () -> 1)
  [] -> 0
}}
"#
    ));
    check_result_int("open_row_list_pure", &src, 1001);
}

#[test]
fn open_row_closure_from_function_used_at_effectful_instance() {
    let src = repro_src(&format!(
        r#"{OPEN_ROW_LIST}
pub fun result : Unit -> Int
result () = {{
  let resumed = case mk () {{
    f :: _ -> f eff
    [] -> 0
  }} with {{ skip () = resume 10 }}
  let aborted = {{
    case mk () {{
      f :: _ -> f eff + 50000
      [] -> 0
    }}
  }} with {{ skip () = 7 }}
  resumed + aborted
}}
"#
    ));
    check_result_int("open_row_list_effectful", &src, 1017);
}

// Erlang code calls a callback as a plain fun. The wrapper of an `@external`
// function passes pure callback arguments through `saga_runtime:bare_fun/2`,
// so a tagged closure used at a pure instance still works there.
#[test]
fn tagged_closure_at_pure_instance_passed_to_external_callback() {
    let src = r#"module Main

import Std.List

fun mk : Unit -> List ((Int -> Int needs {..e}) -> Int -> Int needs {..e})
mk () = [fun g n -> g (0 - n)]

fun first : List Int -> Int
first xs = case xs {
  x :: _ -> x
  [] -> 0
}

pub fun result : Unit -> Int
result () = {
  let app = fun f x -> f x
  let a = first (List.sort_by (app (fun n -> 0 - n)) [1, 3, 2])
  let b = case mk () {
    f :: _ -> first (List.sort_by (f (fun x -> x)) [10, 30, 20])
    [] -> 0
  }
  a + b
}
"#;
    check_result_int("tagged_closure_external_callback", src, 33);
}

// A `let` that is both dictionary-abstracted and row-polymorphic. The
// elaborated wrapper `fun (dict, arg) -> value arg` must stay un-reduced:
// `arg` is made after typechecking and has no type, so substituting it for
// the value's parameter `g` would turn `g ()` into a pure call.
#[test]
fn let_poly_dictionary_abstracted_with_open_row() {
    let src = repro_src(
        r#"pub fun result : Unit -> String
result () = {
  let show_run = fun g -> show (g ())
  let a = show_run (fun () -> 1)
  let b = show_run (fun () -> True)
  let c = show_run (fun () -> skip! ()) with { skip () = resume 5 }
  let d = { show_run (fun () -> skip! ()) <> "unreached" } with { skip () = "aborted" }
  a <> " " <> b <> " " <> c <> " " <> d
}
"#,
    );
    check_result_string("let_poly_dict_open_row", &src, "1 True 5 aborted");
}

// A block is a lexical scope: a `let` inside a block expression ends with the
// block. Below, the last `x` is the outer Int again.
#[test]
fn let_inside_nested_block_does_not_leak() {
    let_poly_int(
        "nested_block_let_scope",
        r#"  let x = 1
  let b = {
    let x = "inner"
    x
  }
  if b == "inner" then x + 1 else 0"#,
        2,
    );
}

// The same when the inner blocks perform operations, so that the rest of the
// enclosing block is a continuation, and when the block is an operand or an
// argument that normalization lifts out.
#[test]
fn let_inside_effectful_nested_block_does_not_leak() {
    let_poly_int(
        "nested_block_let_scope_effectful",
        r#"  let run = fun u -> {
    let x = 1
    let b = {
      let x = skip! ()
      let y = skip! () + x
      y * 10
    }
    let c = ident ({ let x = skip! (); x + 100 })
    let d = if b > 0 then { let x = skip! () + 1000; x } else 0
    let s = x + { let x = skip! (); x * 2 } + x
    {
      let x = "stmt"
      let _ = skip! ()
      ()
    }
    x + b + c + d + s
  }
  run () with { skip () = resume 7 }"#,
        1 + 140 + 107 + 1007 + 16,
    );
}

// The handler clause of a `with` is checked (and lowered) in the scope of the
// block it wraps. A handler bound inside the block and attached by the outer
// `with` is documented (docs/handler-bindings.md). Inline arm bodies seeing
// the block's values is existing behaviour kept deliberately, pending a
// language decision.
#[test]
fn with_clause_sees_the_wrapped_block_bindings() {
    let src = repro_src(
        r#"fun mk : Int -> Handler Skip
mk n = handler for Skip { skip () = resume n }

fun bound_handler : Unit -> Int
bound_handler () = {
  let h = mk 5
  {
    skip! () + 1
  }
} with {h}

fun arm_body : Unit -> Int
arm_body () = {
  let y = 2
  skip! () + y
} with { skip () = resume (y * 10) }

pub fun result : Unit -> Int
result () = bound_handler () * 100 + arm_body ()
"#,
    );
    check_result_int("with_clause_wrapped_block_scope", &src, 622);
}

// Known codegen bug, not fixed here: a local function that shadows a value
// bound earlier in the same block. The call `x 2` lowers to the variable `X`
// (the value 1) instead of the letrec-bound 'x'/1, and fails at runtime with
// "tried to call a value that is not a function: 1". No nested block needed.
#[test]
#[ignore = "codegen: a local function shadowing an earlier value of the same name is called as that value"]
fn local_function_shadowing_a_value_is_called() {
    let_poly_int(
        "local_fun_shadows_value",
        r#"  let x = 1
  let x n = n + 1
  x 2"#,
        3,
    );
}

// Known codegen bug, not fixed here: the lowerer's handler-name maps
// (`handler_canonical`, `handle_cond_vars`) are keyed by name and not scoped
// to blocks, so the inner `h` is still the one attached after its block ends.
// The typechecker resolves the second `with h` to the outer handler; the
// lowered program answers 100 for it, giving 200. The same leak is what
// lowers `{ let h = ...; ... } with h`, so it needs a deliberate fix.
#[test]
#[ignore = "codegen: a let-bound handler in a nested block replaces the outer handler of the same name after the block (200, not 101)"]
fn let_bound_handler_in_nested_block_does_not_replace_outer_one() {
    let_poly_int(
        "nested_block_handler_scope",
        r#"  let h = handler for Skip { skip () = resume 1 }
  let inner = {
    let h = handler for Skip { skip () = resume 100 }
    skip! () with h
  }
  let outer = skip! () with h
  inner + outer"#,
        101,
    );
}

// ---------------------------------------------------------------------------
// Effectful sub-expressions inside handler arms, return clauses and impl
// methods, under an outer handler that aborts the effect they perform.
// ---------------------------------------------------------------------------

const HANDLER_BODY_PRELUDE: &str = r#"module Main

effect Stop { fun stop : Int -> Int }
effect Ask { fun ask : Unit -> Int }

fun g : Int -> Int needs {Stop}
g i = stop! i

fun user : Unit -> Int needs {Ask}
user () = ask! () + 1

fun addp : (Int, Int) -> Int
addp p = case p {
  (a, b) -> a + b
}

type Wrap = Wrap(Int)

fun unwrap : Wrap -> Int
unwrap w = case w {
  Wrap(v) -> v
}

handler h_resume_call for Ask needs {Stop} {
  ask () = resume (g 3)
}

handler h_resume_nested for Ask needs {Stop} {
  ask () = resume (1 + g 3)
}

handler h_resume_then_op for Ask needs {Stop} {
  ask () = resume (g 3) + 1
}

handler h_resume_op for Ask needs {Stop} {
  ask () = resume (1 + stop! 3)
}

handler h_abort_call for Ask needs {Stop} {
  ask () = g 3
}

handler h_abort_nested for Ask needs {Stop} {
  ask () = g 3 + 1
}

handler h_abort_op for Ask needs {Stop} {
  ask () = 1 + stop! 3
}

handler h_return_nested for Ask needs {Stop} {
  ask () = resume 1
  return v = g v + 1
}

handler h_return_call for Ask needs {Stop} {
  ask () = resume 1
  return v = g v
}

trait Run a {
  fun run : a -> Int needs {Stop}
  fun run_op : a -> Int needs {Stop}
  fun run_tuple : a -> Int needs {Stop}
}

impl Run for Int needs {Stop} {
  run a = a + g 3
  run_op a = a + stop! 3
  run_tuple a = addp (stop! 3, a)
}
"#;

/// `(label, expression of type Int performing Stop, value when Stop resumes)`.
const HANDLER_BODY_CELLS: &[(&str, &str, i64)] = &[
    // Inline handler arms.
    (
        "inline_resume_call",
        "user () with { ask () = resume (g 3) }",
        4,
    ),
    (
        "inline_resume_nested",
        "user () with { ask () = resume (1 + g 3) }",
        5,
    ),
    (
        "inline_resume_op",
        "user () with { ask () = resume (1 + stop! 3) }",
        5,
    ),
    (
        "inline_resume_then_operator",
        "user () with { ask () = resume (g 3) + 1 }",
        5,
    ),
    (
        "inline_resume_in_tuple",
        "user () with { ask () = addp (resume (g 3), 1) }",
        5,
    ),
    (
        "inline_resume_in_if_condition",
        "user () with { ask () = if g 3 == 3 then resume 1 else resume 5 }",
        2,
    ),
    (
        "inline_resume_in_case_scrutinee",
        "user () with { ask () = case g 3 {\n    3 -> resume 1\n    _ -> resume 5\n  } }",
        2,
    ),
    ("inline_abort_call", "user () with { ask () = g 3 }", 3),
    (
        "inline_abort_nested",
        "user () with { ask () = g 3 + 1 }",
        4,
    ),
    (
        "inline_abort_op",
        "user () with { ask () = 1 + stop! 3 }",
        4,
    ),
    (
        "inline_abort_constructor",
        "user () with { ask () = unwrap (Wrap(g 3)) }",
        3,
    ),
    (
        "inline_abort_tuple_op",
        "user () with { ask () = addp (stop! 3, 1) }",
        4,
    ),
    (
        "inline_abort_if_condition",
        "user () with { ask () = if g 3 == 3 then 7 else 8 }",
        7,
    ),
    (
        "inline_return_nested",
        "user () with { ask () = resume 1, return v = g v + 1 }",
        3,
    ),
    (
        "inline_return_call",
        "user () with { ask () = resume 1, return v = g v }",
        2,
    ),
    (
        "inline_return_op",
        "user () with { ask () = resume 1, return v = 1 + stop! v }",
        3,
    ),
    // Named handlers that declare `needs {Stop}`.
    ("named_resume_call", "user () with h_resume_call", 4),
    ("named_resume_nested", "user () with h_resume_nested", 5),
    ("named_resume_op", "user () with h_resume_op", 5),
    (
        "named_resume_then_operator",
        "user () with h_resume_then_op",
        5,
    ),
    ("named_abort_call", "user () with h_abort_call", 3),
    ("named_abort_nested", "user () with h_abort_nested", 4),
    ("named_abort_op", "user () with h_abort_op", 4),
    ("named_return_nested", "user () with h_return_nested", 3),
    ("named_return_call", "user () with h_return_call", 2),
    // Impl methods.
    ("impl_method_call", "run 1", 4),
    ("impl_method_op", "run_op 1", 4),
    ("impl_method_tuple_op", "run_tuple 1", 4),
];

/// Where the expression sits relative to the outer `Stop` handler.
#[derive(Clone, Copy, Debug)]
enum HandlerBodyHost {
    /// In a function that declares `needs {Stop}`, so it has a `_ReturnK`.
    EffectfulFunction,
    /// Directly under the outer handler, in a pure function.
    UnderOuterHandler,
    /// Under the outer handler with more of the block after it.
    LetUnderOuterHandler,
}

fn check_handler_body_cells(fixture: &str, host: HandlerBodyHost) {
    check_handler_body_cells_where(fixture, host, |_| true);
}

fn check_handler_body_cells_where(fixture: &str, host: HandlerBodyHost, keep: fn(&str) -> bool) {
    let mut src = String::from(HANDLER_BODY_PRELUDE);
    let mut functions = Vec::new();
    for (idx, (label, expr, _)) in HANDLER_BODY_CELLS.iter().enumerate() {
        if !keep(label) {
            continue;
        }
        if let HandlerBodyHost::EffectfulFunction = host {
            src.push_str(&format!(
                "\nfun c{idx} : Unit -> Int needs {{Stop}}\nc{idx} () = {expr}\n"
            ));
        }
        for (suffix, stop_arm) in [("abort", "stop i = 1000"), ("resume", "stop i = resume i")] {
            let body = match host {
                HandlerBodyHost::EffectfulFunction => format!("c{idx} () with {{ {stop_arm} }}"),
                HandlerBodyHost::UnderOuterHandler => {
                    format!("{{\n  {expr}\n}} with {{ {stop_arm} }}")
                }
                HandlerBodyHost::LetUnderOuterHandler => {
                    format!("{{\n  let v = {expr}\n  v + 100\n}} with {{ {stop_arm} }}")
                }
            };
            src.push_str(&format!(
                "\npub fun c{idx}_{suffix} : Unit -> Int\nc{idx}_{suffix} () = {body}\n"
            ));
            functions.push(format!("c{idx}_{suffix}"));
        }
    }
    let results = call_each_export(fixture, &src, &functions);
    let offset = match host {
        HandlerBodyHost::LetUnderOuterHandler => 100,
        _ => 0,
    };
    let mut failures = Vec::new();
    for (idx, (label, _, resume_value)) in HANDLER_BODY_CELLS.iter().enumerate() {
        if !keep(label) {
            continue;
        }
        let abort = results.get(&format!("c{idx}_abort")).map(String::as_str);
        if abort != Some("1000") {
            failures.push(format!(
                "{host:?} / {label}: aborting handler gave {abort:?}, expected 1000"
            ));
        }
        let resume = results.get(&format!("c{idx}_resume")).map(String::as_str);
        let want = (resume_value + offset).to_string();
        if resume != Some(want.as_str()) {
            failures.push(format!(
                "{host:?} / {label}: resuming handler gave {resume:?}, expected {want}"
            ));
        }
    }
    assert!(
        failures.is_empty(),
        "[{fixture}] {} of {} cells failed:\n{}",
        failures.len(),
        HANDLER_BODY_CELLS.len(),
        failures.join("\n")
    );
}

#[test]
fn effectful_handler_bodies_in_effectful_function() {
    check_handler_body_cells("handler_body_fn", HandlerBodyHost::EffectfulFunction);
}

#[test]
fn effectful_handler_bodies_under_outer_handler() {
    check_handler_body_cells("handler_body_under", HandlerBodyHost::UnderOuterHandler);
}

/// The same cells bound by a `let` with more of the block after them: the
/// rest of the block is the continuation of the whole `with`, so the outer
/// handler's abort skips it.
#[test]
fn effectful_handler_bodies_let_bound_under_outer_handler() {
    check_handler_body_cells_where(
        "handler_body_let",
        HandlerBodyHost::LetUnderOuterHandler,
        |label| label != "inline_resume_in_tuple",
    );
}

/// `ask () = addp (resume (g 3), 1)` uses the value `resume` returns, so its
/// `with` is delimited: the rest of the block reaches the outer handler
/// through the lifted `Stop` operation (see
/// `non_tail_with_delimited_handler_under_aborting_outer_handler`).
#[test]
fn effectful_handler_body_using_resume_value_let_bound_under_outer_handler() {
    check_handler_body_cells_where(
        "handler_body_let_resume_value",
        HandlerBodyHost::LetUnderOuterHandler,
        |label| label == "inline_resume_in_tuple",
    );
}

/// Every remaining expression form that can hold an effectful
/// sub-expression. Each cell's expression is bound by a `let` with more of
/// the block after it, so a sub-expression lowered without a continuation
/// shows up as the abort value flowing into `v + 100`.
///
/// `(label, expression, value under the aborting handler, value under the
/// resuming handler)`.
const EXPRESSION_FORM_CELLS: &[(&str, &str, i64, i64)] = &[
    (
        "do_binding_call",
        "do {\n    Ok(x) <- gr 3\n    x + 1\n  } else {\n    Err(_) -> 0\n  }",
        1000,
        104,
    ),
    (
        "do_binding_nested",
        "do {\n    Ok(x) <- Ok(g 3)\n    x + 1\n  } else {\n    Err(_) -> 0\n  }",
        1000,
        104,
    ),
    (
        "do_binding_op",
        "do {\n    Ok(x) <- Ok(stop! 3)\n    x + 1\n  } else {\n    Err(_) -> 0\n  }",
        1000,
        104,
    ),
    (
        "do_second_binding",
        "do {\n    Ok(x) <- mkok 1\n    Ok(y) <- gr (x + 2)\n    x + y\n  } else {\n    Err(_) -> 0\n  }",
        1000,
        104,
    ),
    (
        "do_success",
        "do {\n    Ok(x) <- mkok 1\n    g x + 1\n  } else {\n    Err(_) -> 0\n  }",
        1000,
        102,
    ),
    (
        "do_else_arm",
        "do {\n    Ok(x) <- mkerr ()\n    x\n  } else {\n    Err(_) -> g 3 + 1\n  }",
        1000,
        104,
    ),
    (
        "do_binding_fails_to_else",
        "do {\n    Ok(x) <- gerr 3\n    x\n  } else {\n    Err(_) -> 7\n  }",
        1000,
        107,
    ),
    (
        "bitstring_segment",
        "case <<(g 3)>> {\n    <<x>> -> x\n    _ -> 0\n  }",
        1000,
        103,
    ),
    (
        "bitstring_second_segment",
        "case <<1, (1 + g 3)>> {\n    <<x, y>> -> x + y\n    _ -> 0\n  }",
        1000,
        105,
    ),
    (
        "and_short_circuits",
        "if False && g 3 == 3 then 1 else 2",
        102,
        102,
    ),
    (
        "and_evaluates_right",
        "if True && g 3 == 3 then 1 else 2",
        1000,
        101,
    ),
    (
        "or_short_circuits",
        "if True || g 3 == 3 then 1 else 2",
        101,
        101,
    ),
    (
        "or_evaluates_right",
        "if False || g 3 == 4 then 1 else 2",
        1000,
        102,
    ),
    ("and_left", "if g 3 == 3 && True then 1 else 2", 1000, 101),
    ("ascription", "(g 3 : Int) + 1", 1000, 104),
    ("ascription_nested", "((1 + g 3) : Int)", 1000, 104),
    ("lambda_called_in_place", "(fun x -> x + g 3) 1", 1000, 104),
    (
        "block_in_operand",
        "1 + {\n    let t = g 3\n    t\n  }",
        1000,
        104,
    ),
    (
        "inline_abort_with",
        "{\n    let a = g 3\n    a + ask! ()\n  } with { ask () = 5 }",
        1000,
        105,
    ),
];

/// Receive needs the actor effects and a running process.
const RECEIVE_FORM_CELLS: &[(&str, &str, i64, i64)] = &[
    (
        "receive_arm",
        "{\n    send! (self! ()) 5\n    receive {\n      n -> g n\n    }\n  }",
        1000,
        105,
    ),
    (
        "receive_arm_nested",
        "{\n    send! (self! ()) 5\n    receive {\n      n -> 1 + g n\n    }\n  }",
        1000,
        106,
    ),
    (
        "receive_after_body",
        "receive {\n    n -> n\n    after 0 -> g 3\n  }",
        1000,
        103,
    ),
    (
        "receive_timeout",
        "receive {\n    n -> n\n    after g 0 -> 7\n  }",
        1000,
        107,
    ),
];

fn check_expression_form_cells(
    fixture: &str,
    cells: &[(&str, &str, i64, i64)],
    needs: &str,
    extra_handler: &str,
) {
    let mut src = String::from(
        r#"module Main

import Std.Actor (Process, Actor, beam_actor)

effect Stop { fun stop : Int -> Int }
effect Ask { fun ask : Unit -> Int }

fun g : Int -> Int needs {Stop}
g i = stop! i

fun gr : Int -> Result Int String needs {Stop}
gr i = Ok(stop! i)

fun gerr : Int -> Result Int String needs {Stop}
gerr i = {
  let v = stop! i
  Err("e")
}

fun mkok : Int -> Result Int String
mkok i = Ok(i)

fun mkerr : Unit -> Result Int String
mkerr () = Err("e")
"#,
    );
    let mut functions = Vec::new();
    for (idx, (_, expr, _, _)) in cells.iter().enumerate() {
        src.push_str(&format!(
            "\nfun c{idx} : Unit -> Int needs {{{needs}}}\nc{idx} () = {{\n  let v = {expr}\n  v + 100\n}}\n"
        ));
        for (suffix, stop_arm) in [("abort", "stop i = 1000"), ("resume", "stop i = resume i")] {
            src.push_str(&format!(
                "\npub fun c{idx}_{suffix} : Unit -> Int\nc{idx}_{suffix} () = c{idx} () with {{ {extra_handler}{stop_arm} }}\n"
            ));
            functions.push(format!("c{idx}_{suffix}"));
        }
    }
    let results = call_each_export(fixture, &src, &functions);
    let mut failures = Vec::new();
    for (idx, (label, _, abort_value, resume_value)) in cells.iter().enumerate() {
        for (suffix, want) in [("abort", abort_value), ("resume", resume_value)] {
            let got = results.get(&format!("c{idx}_{suffix}")).map(String::as_str);
            if got != Some(want.to_string().as_str()) {
                failures.push(format!(
                    "{label}: {suffix} handler gave {got:?}, expected {want}"
                ));
            }
        }
    }
    assert!(
        failures.is_empty(),
        "[{fixture}] {} of {} cells failed:\n{}",
        failures.len(),
        cells.len(),
        failures.join("\n")
    );
}

#[test]
fn effectful_subexpressions_in_every_expression_form() {
    check_expression_form_cells("expr_forms", EXPRESSION_FORM_CELLS, "Stop", "");
}

#[test]
fn effectful_subexpressions_in_receive() {
    check_expression_form_cells(
        "expr_forms_receive",
        RECEIVE_FORM_CELLS,
        "Stop, Process, Actor Int",
        "beam_actor, ",
    );
}

/// The handled computation of a `let`-bound `with` performs an effect handled
/// further out; that handler's abort skips the rest of the block.
#[test]
fn let_bound_with_under_outer_aborting_handler() {
    let src = r#"module Main

effect Stop { fun stop : Int -> Int }
effect Ask { fun ask : Unit -> Int }

fun both : Unit -> Int needs {Stop, Ask}
both () = {
  let a = stop! 3
  a + ask! ()
}

pub fun result : Unit -> Int
result () = {
  let v = both () with { ask () = resume 1 }
  v + 100
} with { stop i = 1000 }
"#;
    check_result_int("let_bound_with_outer_abort", src, 1000);
}

/// Guards are pure. A guard that calls an effectful function is a type error
/// in a `case` arm and on a function clause, whether or not the enclosing
/// function declares the effect: the typechecker used to drop the guard's
/// effects, so the first form ran with no handler in scope and the second
/// did not compile. (`typechecker::guard_purity_tests` covers every guard
/// position.)
#[test]
fn effectful_guard_is_a_type_error() {
    let decls = "module Main\n\neffect Stop { fun stop : Int -> Int }\n\nfun g : Int -> Int needs {Stop}\ng i = stop! i\n";
    for (fixture, needs) in [("declared", " needs {Stop}"), ("pure", "")] {
        check_type_error(
            &format!("effectful_case_guard_{fixture}"),
            &format!(
                "{decls}\npub fun f : Int -> Int{needs}\nf x = case x {{\n  n when g n == 3 -> 5\n  _ -> 6\n}}\n"
            ),
        );
        check_type_error(
            &format!("effectful_clause_guard_{fixture}"),
            &format!("{decls}\npub fun f : Int -> Int{needs}\nf n when g n == 3 = 5\nf _ = 6\n"),
        );
    }
}

/// An operation call nested in an expression is lifted into a `let` ahead of
/// the statement by the normalize pass. Everything evaluated before it in
/// source order is lifted too, so an effectful function call written to its
/// left still runs first.
#[test]
fn operation_after_effectful_call_in_one_expression_keeps_order() {
    let src = r#"module Main

effect Mark { fun mark : Int -> Int }

fun m : Int -> Int needs {Mark}
m i = mark! i

fun run : Unit -> String needs {Mark}
run () = {
  let r = m 1 + mark! 2
  "=" <> show r
}

pub fun result : Unit -> String
result () = run () with {
  mark i = {
    let rest = resume i
    show i <> rest
  },
}
"#;
    check_result_string("op_after_call_order", src, "12=3");
}

/// Source for the order table: one function per (wrapper, left sibling)
/// cell, each evaluating `L` and then `mark! 2` inside the wrapper, run under
/// handlers that prepend the operation's argument to the result (so the
/// result spells out the order) and abort when the argument is `abort_at`.
const OP_ORDER_PRELUDE: &str = r#"module Main

effect Mark { fun mark : Int -> Int }
effect Note { fun note : Int -> Int }
effect Sink { fun sink : Int -> Int -> Int }

type P = P(Int, Int)

record Pt {
  x : Int,
  y : Int,
}

fun m : Int -> Int needs {Mark}
m i = mark! i

fun n : Int -> Int needs {Note}
n i = note! i

fun fin2 : Int -> Int -> Int needs {Mark}
fin2 a b = {
  let z = mark! 9
  a * 10 + b
}

fun add2 : Int -> Int -> Int
add2 a b = a * 10 + b

fun id2 : Int -> Int
id2 x = x
"#;

/// (label, template with `L` and `R` holes giving an Int, value, operations
/// the wrapper itself performs after its parts)
const OP_ORDER_WRAPPERS: &[(&str, &str, &str, &str)] = &[
    ("binop", "L - R", "-1", ""),
    ("tuple", "case (L, R) {\n    (a, b) -> a * 10 + b\n  }", "12", ""),
    (
        "ctor_args",
        "case P(L, R) {\n    P(a, b) -> a * 10 + b\n  }",
        "12",
        "",
    ),
    (
        "record_fields",
        "{\n    let p = Pt { x: L, y: R }\n    p.x * 10 + p.y\n  }",
        "12",
        "",
    ),
    (
        "record_fields_reversed",
        "{\n    let p = Pt { y: L, x: R }\n    p.y * 10 + p.x\n  }",
        "12",
        "",
    ),
    (
        "list_literal",
        "case [L, R] {\n    [a, b] -> a * 10 + b\n    _ -> 0\n  }",
        "12",
        "",
    ),
    (
        "string_interp",
        "{\n    let s = $\"{show (L)}-{show (R)}\"\n    if s == \"1-2\" then 12 else 0\n  }",
        "12",
        "",
    ),
    ("pure_call_args", "add2 (L) (R)", "12", ""),
    ("effectful_call_args", "fin2 (L) (R)", "12", "9"),
    ("param_call_args", "h (L) (R)", "12", "9"),
    ("operation_args", "sink! (L) (R)", "12", ""),
    (
        "nested_two_deep",
        "(1 * (L + 0)) - (0 + id2 (R))",
        "-1",
        "",
    ),
    (
        "nested_in_call_arg",
        "add2 (id2 (L + 0)) (0 + id2 (R))",
        "12",
        "",
    ),
];

/// (label, expression of value 1, whether it records a "1")
const OP_ORDER_LEFTS: &[(&str, &str, bool)] = &[
    ("named_call", "m 1", true),
    ("closed_param", "f 1", true),
    ("open_param", "fo 1", true),
    ("operation", "mark! 1", true),
    ("pure_call", "id2 1", false),
];

/// Build the table's source for one handler variant and return
/// `(source, [(label, exported function, expected result)])`.
fn op_order_cells(abort_at: i64) -> (String, Vec<(String, String, String)>) {
    let mut src = String::from(OP_ORDER_PRELUDE);
    let mut cells = Vec::new();
    let mut idx = 0;
    for (wrapper, template, value, after) in OP_ORDER_WRAPPERS {
        for (left, left_expr, records) in OP_ORDER_LEFTS {
            let expr = template.replace('L', left_expr).replace('R', "mark! 2");
            src.push_str(&format!(
                r#"
fun c{idx} : (Int -> Int needs {{Mark}}) -> (Int -> Int -> Int needs {{Mark}}) -> (Int -> Int needs {{..e}}) -> Unit -> String needs {{Mark, Sink, ..e}}
c{idx} f h fo () = {{
  let r = {expr}
  "=" <> show r
}}

pub fun c{idx}_run : Unit -> String
c{idx}_run () = c{idx} m fin2 n () with {{
  mark i = if i == {abort_at} then "A" else {{
    let rest = resume i
    show i <> rest
  }},
  note i = if i == {abort_at} then "A" else {{
    let rest = resume i
    show i <> rest
  }},
  sink a b = resume (a * 10 + b),
}}
"#
            ));
            let order = format!("{}2{after}", if *records { "1" } else { "" });
            let expected = match order.find(&abort_at.to_string()) {
                Some(pos) => format!("{}A", &order[..pos]),
                None => format!("{order}={value}"),
            };
            cells.push((
                format!("{wrapper}/{left}"),
                format!("c{idx}_run"),
                expected,
            ));
            idx += 1;
        }
    }
    (src, cells)
}

fn check_op_order_table(fixture: &str, abort_at: i64) {
    let (src, cells) = op_order_cells(abort_at);
    let functions: Vec<String> = cells.iter().map(|(_, f, _)| f.clone()).collect();
    let results = call_each_export(fixture, &src, &functions);
    let mut failures = Vec::new();
    for (label, function, expected) in &cells {
        let got = results.get(function).map(String::as_str);
        // Strings print as Erlang binaries: <<"12=3">>.
        let want = format!("<<\"{expected}\">>");
        if got != Some(want.as_str()) {
            failures.push(format!("{label}: got {got:?}, expected {want}"));
        }
    }
    assert!(
        failures.is_empty(),
        "[{fixture}] {} of {} cells failed:\n{}",
        failures.len(),
        cells.len(),
        failures.join("\n")
    );
}

/// Whatever is written to the left of a nested operation call runs before
/// it, exactly once: an effectful function call, a call through an effectful
/// or open-row parameter, another operation, or a pure call.
#[test]
fn left_sibling_of_nested_operation_runs_first() {
    check_op_order_table("op_order_resume", 0);
}

/// The same table when the handler aborts at the left sibling: nothing
/// after it runs, in particular not the operation to its right.
#[test]
fn left_sibling_of_nested_operation_can_abort() {
    check_op_order_table("op_order_abort_left", 1);
}

/// The same table when the handler aborts at the nested operation: the left
/// sibling has run, the rest of the expression and the block have not.
#[test]
fn nested_operation_after_left_sibling_can_abort() {
    check_op_order_table("op_order_abort_right", 2);
}

/// Left-to-right order also holds for a sibling whose effect is not tracked
/// by the type system: a foreign call that writes the process dictionary, and
/// a `panic`.
#[test]
fn impure_left_sibling_of_nested_operation_runs_first() {
    let src = r#"module Main

effect Mark { fun mark : Int -> Int }

@external("erlang", "erlang", "put")
fun pd_put : Int -> Int -> Int

@external("erlang", "erlang", "get")
fun pd_get : Int -> Int

fun bump : Int -> Int
bump i = {
  let previous = pd_put 7 i
  i
}

fun boom : Int -> Int
boom i = panic "left sibling ran first"

fun seen : Unit -> Int needs {Mark}
seen () = bump 1 + mark! 2

fun panics : Unit -> Int needs {Mark}
panics () = boom 1 + mark! 2

pub fun order : Unit -> Int
order () = seen () with { mark i = resume (pd_get 7 * 10 + i) }

pub fun panic_first : Unit -> Int
panic_first () = panics () with { mark i = 1000 }
"#;
    let functions = vec!["order".to_string(), "panic_first".to_string()];
    let results = call_each_export("op_order_impure", src, &functions);
    assert_eq!(results.get("order").map(String::as_str), Some("13"));
    assert_eq!(results.get("panic_first").map(String::as_str), Some("crash"));
}

/// Shapes around the sibling lifting: a function head that is itself
/// computed, an ascribed operation, and the right operand of `&&`/`||`,
/// which runs only when the left operand does not decide the result. Each
/// function runs under a recording handler and under handlers aborting at
/// the first, second and third operation.
#[test]
fn lifted_heads_ascriptions_and_short_circuit_operands_keep_order() {
    let src = r#"module Main

effect Mark { fun mark : Int -> Int }
effect Flag { fun flag : Int -> Bool }

fun m : Int -> Int needs {Mark}
m i = mark! i

fun fl : Int -> Bool needs {Flag}
fl i = flag! i

fun inc : Int -> Int -> Int needs {Mark}
inc a b = {
  let z = mark! 8
  a * 10 + b
}

fun dec : Int -> Int -> Int needs {Mark}
dec a b = {
  let z = mark! 9
  a * 100 + b
}

fun head_if : Unit -> String needs {Mark}
head_if () = {
  let r = (if m 1 == 1 then inc else dec) (m 2) (mark! 3)
  "=" <> show r
}

fun ascribed : Unit -> String needs {Mark}
ascribed () = {
  let r = m 1 + (mark! 2 : Int)
  "=" <> show r
}

fun sc_skipped : Unit -> String needs {Flag}
sc_skipped () = {
  let a = False && flag! 1
  let b = True || flag! 2
  "=" <> show a <> show b
}

fun sc_if : Unit -> String needs {Mark, Flag}
sc_if () = {
  let r = if fl 1 && flag! 2 then m 3 else mark! 4
  let s = if flag! 5 || fl 6 then 1 else 2
  "=" <> show r <> show s
}

fun sc_arg : Unit -> String needs {Mark, Flag}
sc_arg () = {
  let r = inc (if (False && flag! 1) || flag! 2 then 1 else 0) (mark! 3)
  "=" <> show r
}

fun run : (Unit -> String needs {Mark, Flag}) -> Int -> String
run f stop = f () with {
  mark i = if i == stop then "A" else {
    let rest = resume i
    show i <> rest
  },
  flag i = if i == stop then "A" else {
    let rest = resume (i % 2 == 0)
    show i <> rest
  },
}

fun one : (Unit -> String needs {Mark, Flag}) -> String
one f = run f 0 <> " " <> run f 1 <> " " <> run f 2 <> " " <> run f 3

pub fun result : Unit -> String
result () = one head_if <> "|" <> one ascribed <> "|" <> one sc_skipped <> "|" <> one sc_if <> "|" <> one sc_arg
"#;
    check_result_string(
        "op_order_heads_short_circuit",
        src,
        "1238=23 A 1A 12A|12=3 A 1A 12=3|=FalseTrue =FalseTrue =FalseTrue =FalseTrue|1456=41 A 1456=41 1456=41|238=13 238=13 A 2A",
    );
}

/// A callback argument of an operation that is lifted because an operation
/// follows it keeps its type, so it is still wrapped to run against the
/// perform-site handlers.
#[test]
fn lifted_callback_argument_of_operation_keeps_perform_site_handlers() {
    let src = r#"module Main

effect Inner { fun inner : Unit -> Int }
effect Mark { fun mark : Int -> Int }
effect Scope {
  fun scope : (Unit -> Int needs {Inner, ..r}) -> Int -> Int needs {..r}
}

fun cb_a : Unit -> Int needs {Inner, Mark}
cb_a () = inner! () + mark! 5

fun choose : Int -> (Unit -> Int needs {Inner, Mark})
choose i = cb_a

fun lifted : Unit -> Int needs {Scope, Mark}
lifted () = scope! (choose 1) (mark! 2)

pub fun result : Unit -> Int
result () = {
  lifted () with {
    scope body n = resume ((body () with { inner () = resume 100 }) + n),
  }
} with { mark i = resume i }
"#;
    check_result_int("op_order_lifted_callback", src, 107);
}

/// The nested-argument chaining holds across a module boundary: the outer
/// callee, the inner effectful call and the effect are all imported.
#[test]
fn nested_effectful_arg_of_cross_module_call() {
    let lib = r#"module Nested.Lib

pub effect Stop { fun stop : Int -> Int }
pub effect Tick { fun tick : Unit -> Unit }

pub fun g : Int -> Int needs {Stop}
g i = stop! i

pub fun fin : Int -> Int -> Int needs {Tick}
fin a b = {
  tick! ()
  a + b + 100
}

pub fun each : (Int -> Int needs {Tick}) -> Int -> Int needs {Tick}
each f x = f x + 100
"#;
    let main_src = r#"module Main

import Nested.Lib (Stop, Tick, g, fin, each)
import Nested.Lib as L

fun direct : Unit -> Int needs {Stop, Tick}
direct () = fin (1 + g 3) (g 4 * 2)

fun qualified : Unit -> Int needs {Stop, Tick}
qualified () = L.fin (1 + L.g 3) 2

fun hof : Unit -> Int needs {Stop, Tick}
hof () = each (fun x -> x + 1) (1 + g 3)

fun run : (Unit -> Int needs {Stop, Tick}) -> String
run f = {
  let aborted = f () with { stop i = 1000, tick () = resume () }
  let resumed = f () with { stop i = resume i, tick () = resume () }
  show aborted <> "/" <> show resumed
}

pub fun result : Unit -> String
result () = run direct <> " " <> run qualified <> " " <> run hof
"#;
    check_cross_module(
        "nested_arg_cross_module",
        &[("Nested/Lib.saga", lib)],
        main_src,
        "1000/112 1000/106 1000/105",
    );
}

// ---------------------------------------------------------------------------
// A `with` that is not in tail position, under an outer handler. Everything
// after the `with` in the enclosing body is its continuation, so an outer
// handler that aborts an operation performed inside it (by the handled
// computation, a handler arm or the return clause) skips that rest.
// ---------------------------------------------------------------------------

const NON_TAIL_WITH_PRELUDE: &str = r#"module Main

effect Stop { fun stop : Int -> Int }
effect Ask { fun ask : Unit -> Int }
effect Tell { fun tell : Int -> Unit }
effect Go { fun go : Unit -> Int }

fun g : Int -> Int needs {Stop}
g i = stop! i

fun both : Unit -> Int needs {Stop, Ask}
both () = {
  let a = stop! 3
  a + ask! ()
}

fun both3 : Unit -> Int needs {Stop, Ask, Tell}
both3 () = {
  let a = stop! 3
  tell! a
  a + ask! ()
}

fun user : Unit -> Int needs {Ask}
user () = ask! () + 1

fun inc : Int -> Int
inc x = x + 1

fun eadd : Int -> Int needs {Stop}
eadd x = if x > 5000 then stop! x else x + 100

handler n_tail for Ask {
  ask () = resume 1
}

handler n_nontail for Ask {
  ask () = (resume 1) + 10
}

handler n_abort for Ask {
  ask () = 50
}

handler n_return for Ask {
  ask () = resume 1
  return v = v * 2
}

handler n_finally for Ask {
  ask () = {
    resume 1
  } finally {
    ()
  }
}

handler n_tell for Tell {
  tell _ = resume ()
}

handler n_needs for Ask needs {Stop} {
  ask () = resume (g 1)
}

handler n_needs_abort for Ask needs {Stop} {
  ask () = g 3 + 1
}

handler n_needs_return for Ask needs {Stop} {
  ask () = resume 1
  return v = g v + 1
}
"#;

/// `(label, expression of type Int that performs Stop, value when Stop resumes)`.
///
/// Labels starting with `delimited/` are handlers that use the value `resume`
/// returns, or have a `finally` block. Their `with` cannot take the rest of
/// the enclosing body as the handled computation's return continuation (the
/// value of `resume` would then be the answer of that rest). The rest is
/// supplied as a meta continuation instead, and the operations of the
/// inherited frame are lifted to capture it; a `finally` handler still runs
/// its handled computation to a plain value.
const NON_TAIL_WITH_HANDLERS: &[(&str, &str, i64)] = &[
    // The handled computation performs the outer effect.
    (
        "comp/inline_tail_resume",
        "both () with { ask () = resume 1 }",
        4,
    ),
    ("comp/inline_abort", "both () with { ask () = 50 }", 50),
    (
        "comp/inline_return",
        "both () with { ask () = resume 1, return v = v * 2 }",
        8,
    ),
    ("comp/named_tail_resume", "both () with n_tail", 4),
    ("comp/named_abort", "both () with n_abort", 50),
    ("comp/named_return", "both () with n_return", 8),
    ("comp/named_needs", "both () with n_needs", 4),
    ("comp/two_named", "both3 () with {n_tail, n_tell}", 4),
    (
        "comp/named_and_inline",
        "both3 () with {n_tail, tell _ = resume ()}",
        4,
    ),
    ("comp/two_withs", "(both3 () with n_tell) with n_tail", 4),
    // A handler arm performs the outer effect.
    (
        "arm/inline_tail_resume",
        "user () with { ask () = resume (g 3) }",
        4,
    ),
    ("arm/inline_abort", "user () with { ask () = g 3 + 1 }", 4),
    ("arm/named_tail_resume", "user () with n_needs", 2),
    ("arm/named_abort", "user () with n_needs_abort", 4),
    // The return clause performs the outer effect.
    (
        "ret/inline",
        "user () with { ask () = resume 1, return v = g v + 1 }",
        3,
    ),
    ("ret/named", "user () with n_needs_return", 3),
    // Handlers that use the value of `resume`.
    (
        "delimited/comp_inline_resume_value",
        "both () with { ask () = (resume 1) + 10 }",
        14,
    ),
    (
        "delimited/comp_inline_multishot",
        "both () with { ask () = (resume 1) + (resume 2) }",
        9,
    ),
    (
        "delimited/comp_named_resume_value",
        "both () with n_nontail",
        14,
    ),
    ("delimited/comp_named_finally", "both () with n_finally", 4),
    (
        "delimited/comp_two_withs",
        "(both3 () with n_tell) with n_nontail",
        14,
    ),
    (
        "delimited/arm_inline_resume_value",
        "user () with { ask () = (resume (g 3)) + 1 }",
        5,
    ),
    (
        "delimited/arm_inline_after_resume",
        "user () with { ask () = {\n    let r = resume 1\n    r + g 3\n  } }",
        5,
    ),
];

type NonTailWithPosition = (&'static str, fn(&str) -> String, fn(i64) -> i64);

/// `(label, body built around the expression, value of the body)`.
const NON_TAIL_WITH_POSITIONS: &[NonTailWithPosition] = &[
    ("tail", |e| e.to_string(), |r| r),
    ("let", |e| format!("let v = {e}\n  v + 100"), |r| r + 100),
    ("binop_left", |e| format!("({e}) + 100"), |r| r + 100),
    ("binop_right", |e| format!("100 + ({e})"), |r| r + 100),
    ("pure_call_arg", |e| format!("inc ({e})"), |r| r + 1),
    ("effectful_call_arg", |e| format!("eadd ({e})"), |r| r + 100),
    (
        "if_condition",
        |e| format!("if ({e}) > 0 then 100 else 200"),
        |_| 100,
    ),
    (
        "case_scrutinee",
        |e| format!("case ({e}) {{\n    1000 -> 7\n    _ -> 100\n  }}"),
        |_| 100,
    ),
    ("statement", |e| format!("let _ = {e}\n  100"), |_| 100),
];

#[derive(Clone, Copy, Debug, PartialEq)]
enum NonTailWithHost {
    /// A pure function; the body is the outer handler's handled block.
    UnderOuterHandler,
    /// A function declaring `needs {Stop}`, called with more work after it.
    EffectfulFunction,
    /// A lambda called with more work after it.
    Lambda,
    /// The body of an aborting handler arm.
    AbortingArm,
    /// A handler arm that resumes with the body's value.
    ResumingArm,
}

const NON_TAIL_WITH_HOSTS: &[NonTailWithHost] = &[
    NonTailWithHost::UnderOuterHandler,
    NonTailWithHost::EffectfulFunction,
    NonTailWithHost::Lambda,
    NonTailWithHost::AbortingArm,
    NonTailWithHost::ResumingArm,
];

#[derive(Clone, Copy, Debug, PartialEq)]
enum OuterStop {
    Aborts,
    Resumes,
}

/// Runs every selected handler x position cell in every host, under the
/// outer handlers in `outer`, and asserts that none fails.
/// `keep(handler label, position label, host)` selects the cells.
fn check_non_tail_with(
    fixture: &str,
    outer: &[OuterStop],
    keep: fn(&str, &str, NonTailWithHost) -> bool,
) {
    let mut failures = Vec::new();
    for host in NON_TAIL_WITH_HOSTS {
        let mut src = String::from(NON_TAIL_WITH_PRELUDE);
        let mut cells = Vec::new();
        let mut functions = Vec::new();
        let mut idx = 0;
        for (h_label, expr, resume_value) in NON_TAIL_WITH_HANDLERS {
            for (p_label, build, value) in NON_TAIL_WITH_POSITIONS {
                if !keep(h_label, p_label, *host) {
                    continue;
                }
                let body = build(expr);
                let inner = value(*resume_value);
                if *host == NonTailWithHost::EffectfulFunction {
                    src.push_str(&format!(
                        "\nfun c{idx} : Unit -> Int needs {{Stop}}\nc{idx} () = {{\n  {body}\n}}\n"
                    ));
                }
                let (block, want) = match host {
                    NonTailWithHost::UnderOuterHandler => (format!("{{\n  {body}\n}}"), inner),
                    NonTailWithHost::EffectfulFunction => {
                        (format!("{{\n  let x = c{idx} ()\n  x * 2\n}}"), inner * 2)
                    }
                    NonTailWithHost::Lambda => (
                        format!(
                            "{{\n  let f = fun () -> {{\n  {body}\n}}\n  let x = f ()\n  x * 2\n}}"
                        ),
                        inner * 2,
                    ),
                    NonTailWithHost::AbortingArm => (
                        format!(
                            "{{\n  {{\n    let x = go! ()\n    x * 2\n  }} with {{ go () = {{\n  {body}\n}} }}\n}}"
                        ),
                        inner,
                    ),
                    NonTailWithHost::ResumingArm => (
                        format!(
                            "{{\n  {{\n    let x = go! ()\n    x * 2\n  }} with {{ go () = {{\n  let y = {{\n  {body}\n}}\n  resume y\n}} }}\n}}"
                        ),
                        inner * 2,
                    ),
                };
                for stop in outer {
                    let (suffix, stop_arm, want) = match stop {
                        OuterStop::Aborts => ("abort", "stop i = 1000", 1000),
                        OuterStop::Resumes => ("resume", "stop i = resume i", want),
                    };
                    src.push_str(&format!(
                        "\npub fun c{idx}_{suffix} : Unit -> Int\nc{idx}_{suffix} () = {block} with {{ {stop_arm} }}\n"
                    ));
                    functions.push(format!("c{idx}_{suffix}"));
                    cells.push((
                        format!("c{idx}_{suffix}"),
                        format!("{host:?} / {h_label} @ {p_label} / outer {stop:?}"),
                        want,
                    ));
                }
                idx += 1;
            }
        }
        if cells.is_empty() {
            continue;
        }
        let results = call_each_export(&format!("{fixture}_{host:?}"), &src, &functions);
        for (function, label, want) in cells {
            let got = results.get(&function).map(String::as_str);
            if got != Some(want.to_string().as_str()) {
                failures.push(format!(
                    "{label}: gave {}, expected {want}",
                    got.unwrap_or("nothing")
                ));
            }
        }
    }
    assert!(
        failures.is_empty(),
        "[{fixture}] {} cells failed:\n{}",
        failures.len(),
        failures.join("\n")
    );
}

fn is_delimited_handler(label: &str) -> bool {
    label.starts_with("delimited/")
}

/// Whether the `with` is the last thing its host's body does. In
/// `ResumingArm` the body is itself bound by a `let`.
fn with_is_last(position: &str, host: NonTailWithHost) -> bool {
    position == "tail" && host != NonTailWithHost::ResumingArm
}

/// Whether the host's body has a return continuation of its own, which a
/// `with` in its tail position inherits.
fn host_has_continuation(host: NonTailWithHost) -> bool {
    matches!(
        host,
        NonTailWithHost::EffectfulFunction | NonTailWithHost::Lambda
    )
}

/// Handlers that never use the value of `resume`: in every position and
/// host, the outer handler's abort skips everything after the `with`, and
/// its resume gives the ordinary value.
#[test]
fn non_tail_with_takes_rest_of_body_as_continuation() {
    check_non_tail_with(
        "non_tail_with",
        &[OuterStop::Aborts, OuterStop::Resumes],
        |handler, _, _| !is_delimited_handler(handler),
    );
}

/// Handlers that use the value of `resume` get the value of the handled
/// computation (after the return clause) from it, not the value of the rest
/// of the enclosing body, when the `with` is not in tail position.
#[test]
fn non_tail_with_delimited_handler_resume_returns_value_of_with() {
    check_non_tail_with(
        "non_tail_with_delimited_resume",
        &[OuterStop::Resumes],
        |handler, position, host| {
            is_delimited_handler(handler)
                && !(with_is_last(position, host) && host_has_continuation(host))
        },
    );
}

/// The same handlers as the last thing their host does: nothing of the
/// host's body is left to skip, so the outer handler's abort is the result.
#[test]
fn tail_with_delimited_handler_under_aborting_outer_handler() {
    check_non_tail_with(
        "tail_with_delimited_abort",
        &[OuterStop::Aborts],
        |handler, position, host| is_delimited_handler(handler) && with_is_last(position, host),
    );
}

/// A `with` whose handler uses the value of `resume` and is not the last
/// thing its host does. An operation performed inside it and handled further
/// out must capture the rest of the host's body too, so that an outer
/// handler that aborts skips it: the operations of the inherited frame are
/// lifted to take that rest as a meta continuation.
#[test]
fn non_tail_with_delimited_handler_under_aborting_outer_handler() {
    check_non_tail_with(
        "non_tail_with_delimited_abort",
        &[OuterStop::Aborts],
        |handler, position, host| {
            is_delimited_handler(handler)
                && handler != "delimited/comp_named_finally"
                && !with_is_last(position, host)
        },
    );
}

/// Known gap: a handler with a `finally` block runs its handled computation
/// to a plain value on the Erlang stack, so that cleanup follows it. The
/// cleanup has to run when an outer handler aborts as well, and before that
/// handler's continuation; with CPS the only point at which an abort can be
/// observed is the return of the resumed computation, so the outer abort
/// returns its value there, it becomes the value of the `with`, and the rest
/// of the body runs. Expected 1000 everywhere; gives e.g. 1100 for the `let`
/// position.
#[test]
#[ignore = "`finally`: an outer abort returns through the `with` so that cleanup runs, and becomes its value"]
fn non_tail_with_finally_handler_under_aborting_outer_handler() {
    check_non_tail_with(
        "non_tail_with_finally_abort",
        &[OuterStop::Aborts],
        |handler, position, host| {
            handler == "delimited/comp_named_finally" && !with_is_last(position, host)
        },
    );
}

/// The other side: in tail position of a body that has a continuation (an
/// effectful function, a lambda), `resume` still returns the value of the
/// `with`, not the answer of the caller's rest. `c () = user () with { ask ()
/// = { let r = resume 1; r + g 3 } }` called as `let x = c (); x * 2` gives
/// 10.
#[test]
fn tail_with_delimited_handler_resume_returns_value_of_with() {
    check_non_tail_with(
        "tail_with_delimited_resume",
        &[OuterStop::Resumes],
        |handler, position, host| {
            is_delimited_handler(handler)
                && handler != "delimited/comp_named_finally"
                && with_is_last(position, host)
                && host_has_continuation(host)
        },
    );
}

// ---------------------------------------------------------------------------
// Effect normalization at the lowering roots (`codegen::lower::anf`): an
// effectful expression in operand position is moved into a `let` before
// lowering. These shapes had no lowering routine of their own and were
// lowered as plain values, so an outer handler's abort value was used as the
// operand's value and the rest of the body ran.
// ---------------------------------------------------------------------------

const ANF_PRELUDE: &str = r#"module Main

effect Stop { fun stop : Int -> Int }
effect Ask { fun ask : Unit -> Int }

fun g : Int -> Int needs {Stop}
g i = stop! i

handler one for Ask { ask () = resume 1 }
handler two for Ask { ask () = resume 2 }
"#;

fn anf_int(fixture: &str, body: &str, expected: i64) {
    check_result_int(fixture, &format!("{ANF_PRELUDE}\n{body}"), expected);
}

/// The condition that picks a `let`-bound handler performs an effect. It
/// answered 102: the abort value 1000 was compared with 0 and `two` chosen.
#[test]
fn effectful_condition_selecting_a_let_bound_handler() {
    anf_int(
        "anf_handler_condition",
        r#"
fun f : Unit -> Int needs {Stop}
f () = {
  let h = if g 0 == 0 then one else two
  let v = ask! () with h
  v + 100
}

pub fun result : Unit -> Int
result () = f () with { stop i = 1000 }
"#,
        1000,
    );
}

/// The return clause of a handler value has an effectful call as an operand.
/// It answered 1100: the abort value went through `+ 100`.
#[test]
fn effectful_operand_in_return_clause_of_a_handler_value() {
    anf_int(
        "anf_handler_value_return",
        r#"
fun mk : Unit -> Handler Ask needs {Stop}
mk () = handler for Ask needs {Stop} {
  ask () = resume 1
  return v = g v + 100
}

fun body : Unit -> Int needs {Stop}
body () = {
  let h = mk ()
  ask! () with h
}

pub fun result : Unit -> Int
result () = body () with { stop i = 1000 }
"#,
        1000,
    );
}

/// The size of a bit string segment performs an effect. It answered 100:
/// the abort value was used as the size and the rest of the block ran.
#[test]
fn effectful_bit_string_segment_size() {
    anf_int(
        "anf_bit_string_size",
        r#"
fun f : Unit -> Int needs {Stop}
f () = {
  let b = <<1:(g 8)>>
  let _ = b
  100
}

pub fun result : Unit -> Int
result () = f () with { stop i = 1000 }
"#,
        1000,
    );
}

// Effectful expressions already in `let` or tail position, which the two
// block lowerings (with and without a continuation) each handled partly.
// There is one block lowerer now (`lower_block`), with one rule for a
// statement that performs effects.

/// A block that is the value of a `let`, has effects in it and defines a
/// local function. The continuation-threaded block lowering had no case for
/// a local function and reached `unreachable!`.
#[test]
fn local_function_in_a_block_lowered_with_a_continuation() {
    anf_int(
        "anf_local_fun_in_k_block",
        r#"
fun f : Unit -> Int needs {Stop}
f () = {
  let x = {
    let h y = y + 1
    h (g 5)
  }
  x + 100
}

pub fun result : Unit -> Int
result () = f () with { stop i = resume i }
"#,
        106,
    );
}

/// `let assert` on the value of an effectful call: the rest of the block
/// becomes the call's continuation. It bound the pattern with an ordinary
/// match, so a mismatch was a `case_clause` error, not an assertion failure.
#[test]
fn let_assert_on_an_effectful_call_keeps_the_assertion() {
    let src = format!(
        "{ANF_PRELUDE}{}",
        r#"
fun mk : Int -> Maybe Int needs {Stop}
mk i = if stop! i == 0 then Nothing else Just 1

fun f : Unit -> Int needs {Stop}
f () = {
  let assert Just(x) = mk 0
  x + 100
}

pub fun result : Unit -> Int
result () = f () with { stop i = resume i }
"#
    );
    let root = fixtures_root_for_main_only();
    let mut checker = make_checker(root.clone());
    let program = typecheck_source(&src, &mut checker, "anf_let_assert");
    let core = emit_program(&program, "main", &checker, Some("main"));
    let _ = std::fs::remove_dir_all(&root);
    assert!(
        core.contains("'assert_fail'"),
        "the assertion is not in the lowered program"
    );
}

/// A block that ends in `let x = <effectful call>`: the call was lowered as
/// a plain value with an identity continuation, so the abort value became
/// the value of the block and the caller's rest ran. It answered 100.
#[test]
fn block_ending_in_let_of_an_effectful_call() {
    anf_int(
        "anf_trailing_let",
        r#"
fun f : Unit -> Unit needs {Stop}
f () = {
  let x = g 5
}

fun h : Unit -> Int needs {Stop}
h () = {
  f ()
  100
}

pub fun result : Unit -> Int
result () = h () with { stop i = 1000 }
"#,
        1000,
    );
}

/// A nullary operation (`number!`) performs when it is evaluated. It was
/// lowered as a plain value with an identity continuation wherever it
/// stood, a `let` included, so the handler's abort value became the value
/// of the operation and the rest of the block ran (1001). It is a
/// performing leaf now, for normalization and for the block rule.
#[test]
fn nullary_operation_aborted_by_its_handler() {
    check_result_int(
        "anf_nullary_op",
        r#"module Main

effect Config { fun number : Int }

fun compute : Unit -> Int needs {Config}
compute () = {
  let n = number!
  n + 1
}

pub fun result : Unit -> Int
result () = compute () with { number = 1000 }
"#,
        1000,
    );
}

/// The same operation as an operand: normalization binds it first.
#[test]
fn nullary_operation_as_an_operand_aborted_by_its_handler() {
    check_result_int(
        "anf_nullary_op_operand",
        r#"module Main

effect Config { fun number : Int }

fun compute : Unit -> Int needs {Config}
compute () = (number! + 1) * 2

pub fun result : Unit -> Int
result () = compute () with { number = 1000 }
"#,
        1000,
    );
}

/// Whether an untyped lambda is a tagged closure is recorded in the plan
/// from "its body is an effectful call". Inside a direct-callback variant of
/// a higher-order function, a call of the callback parameter is direct, so
/// a lambda there whose body is such a call would have to be bare. That
/// cannot arise: a function with a lambda left in its body after the
/// generic fold gets no direct-callback variant
/// (`optimize::hof_body_supported`), so `apply_l` below is only ever
/// lowered with `f y` as an effectful call. `apply_d`
/// has a variant and no lambda. Both are called with a pure and with an
/// effectful callback.
#[test]
fn lambda_calling_a_callback_parameter_has_no_direct_variant() {
    let src = format!(
        "{ANF_PRELUDE}{}",
        r#"
fun apply_d : (Int -> Int needs {Stop}) -> Int -> Int needs {Stop}
apply_d f x = f x + 1

fun apply_l : (Int -> Int needs {Stop}) -> Int -> Int needs {Stop}
apply_l f x = {
  let h = fun y -> f y
  h x + 1
}

fun inc : Int -> Int
inc i = i + 10

fun direct : Unit -> Int needs {Stop}
direct () = apply_d inc 1 + apply_l inc 2

fun effectful : Unit -> Int needs {Stop}
effectful () = apply_d g 1 + apply_l g 2

pub fun result : Unit -> Int
result () = {
  let pure = direct () with { stop i = resume i }
  let eff = effectful () with { stop i = resume (i * 100) }
  pure * 1000 + eff
}
"#
    );
    let root = fixtures_root_for_main_only();
    let mut checker = make_checker(root.clone());
    let program = typecheck_source(&src, &mut checker, "anf_hof_lambda");
    let core = emit_program(&program, "main", &checker, Some("main"));
    let _ = std::fs::remove_dir_all(&root);
    assert!(core.contains("__saga_direct_hof_apply_d"));
    assert!(!core.contains("__saga_direct_hof_apply_l"));
    // pure: (11 + 1) + (12 + 1) = 25; effectful: (100 + 1) + (200 + 1) = 302
    check_result_int("anf_hof_lambda", &src, 25_302);
}

// ---------------------------------------------------------------------------
// Delimited `with`: a handler whose arms use the value `resume` returns. The
// continuation of the `with` is a meta continuation; operations of the
// inherited frame are lifted to capture it.
// ---------------------------------------------------------------------------

const DELIMITED_PRELUDE: &str = r#"module Main

effect Stop { fun stop : Int -> Int }
effect Ask { fun ask : Unit -> Int }
effect Ask2 { fun ask2 : Unit -> Int }
effect Scope { fun scope : (Unit -> Int needs {..r}) -> Int needs {..r} }

fun ask_stop : Unit -> Int needs {Stop, Ask}
ask_stop () = {
  let a = ask! ()
  let b = stop! a
  a * 10 + b
}

fun comp_n : Unit -> Int needs {Stop, Ask, Ask2}
comp_n () = {
  let a = ask! ()
  let b = ask2! ()
  stop! (a + b)
}
"#;

/// The outer `Stop` handlers every cell is run under, by name: one that
/// aborts, one that resumes in tail position, one that uses the value of its
/// `resume` and one that resumes twice. The last two are themselves
/// delimited.
const DELIMITED_OUTER_STOPS: &[(&str, &str)] = &[
    ("abort", "stop i = 1000"),
    ("resume", "stop i = resume i"),
    ("nontail", "stop i = (resume i) * 2"),
    ("twice", "stop i = (resume i) + (resume (i + 1))"),
];

/// Each cell is the body of a `Int -> Int needs {Stop}` function (or
/// `needs {Stop, Scope}` when it uses `scope!`); `wants` are its values
/// under [`DELIMITED_OUTER_STOPS`], in order.
fn check_delimited_cells(fixture: &str, extra: &str, cells: &[(&str, &str, [i64; 4])]) {
    let mut src = String::from(DELIMITED_PRELUDE);
    src.push_str(extra);
    let mut functions = Vec::new();
    let mut wants = Vec::new();
    for (label, body, values) in cells {
        let uses_scope = body.contains("scope!");
        let row = if uses_scope {
            "{Stop, Scope}"
        } else {
            "{Stop}"
        };
        src.push_str(&format!(
            "\nfun {label} : Int -> Int needs {row}\n{label} _ = {{\n{body}\n}}\n"
        ));
        for ((stop_label, stop_arm), want) in DELIMITED_OUTER_STOPS.iter().zip(values) {
            let scope_arm = if uses_scope {
                ", scope g = { let r = g (); resume (r + 1) }"
            } else {
                ""
            };
            let name = format!("{label}_{stop_label}");
            src.push_str(&format!(
                "\npub fun {name} : Unit -> Int\n{name} () = {label} 0 with {{ {stop_arm}{scope_arm} }}\n"
            ));
            functions.push(name.clone());
            wants.push((name, *want));
        }
    }
    let results = call_each_export(fixture, &src, &functions);
    let failures: Vec<String> = wants
        .iter()
        .filter_map(|(name, want)| {
            let got = results.get(name).map(String::as_str);
            (got != Some(want.to_string().as_str()))
                .then(|| format!("{name}: gave {}, expected {want}", got.unwrap_or("nothing")))
        })
        .collect();
    assert!(
        failures.is_empty(),
        "[{fixture}] {} cells failed:\n{}",
        failures.len(),
        failures.join("\n")
    );
}

/// The operation handled outside is performed after the delimited handler
/// has resumed, so the arm's `+ 10` is pending when the outer handler runs:
/// an outer handler that uses the value of its own `resume` must get the
/// answer of everything, the pending `+ 10` and the `+ 100` included.
#[test]
fn delimited_with_under_outer_handler_using_its_resume_value() {
    check_delimited_cells(
        "delimited_outer_kinds",
        "",
        &[
            (
                "one",
                "  let v = ask_stop () with { ask () = (resume 1) + 10 }\n  v + 100",
                [1000, 121, 242, 243],
            ),
            (
                "multishot",
                "  let v = ask_stop () with { ask () = (resume 1) + (resume 2) }\n  v + 100",
                [1000, 133, 532, 536],
            ),
        ],
    );
}

/// Two delimited `with`s (the inherited frame is lifted twice), and one
/// inside or around a chained one.
#[test]
fn nested_delimited_withs() {
    let nest = |inner: &str, outer: &str| {
        format!(
            "  let v = {{\n    let w = comp_n () with {{ ask2 () = {inner} }}\n    w + 7\n  }} with {{ ask () = {outer} }}\n  v + 100"
        )
    };
    let dd = nest("(resume 5) * 3", "(resume 1) + 10");
    let cd = nest("(resume 5) * 3", "resume 1");
    let dc = nest("resume 5", "(resume 1) + 10");
    check_delimited_cells(
        "delimited_nested",
        "",
        &[
            ("delimited_in_delimited", &dd, [1000, 135, 270, 273]),
            ("delimited_in_chained", &cd, [1000, 125, 250, 253]),
            ("chained_in_delimited", &dc, [1000, 123, 246, 247]),
        ],
    );
}

/// Function values and effect-polymorphic callees inside a delimited `with`
/// run with the lifted frame; a closure built inside and called outside runs
/// with the frame of its caller.
#[test]
fn delimited_with_and_function_values() {
    check_delimited_cells(
        "delimited_function_values",
        r#"
fun twice_apply : (Int -> Int needs {..e}) -> Int -> Int needs {..e}
twice_apply f x = f (f x)

fun poly : Unit -> Int needs {Stop, Ask}
poly () = twice_apply (fun x -> x + stop! x + ask! ()) 1
"#,
        &[
            // f 1 = 3, f 3 = 7, each `ask` adds 10; `Stop` is performed twice.
            // Resumed twice: f 1 is 3 or 4, then f 3 is 7 or 8, f 4 is 9 or 10.
            (
                "polymorphic_callee",
                "  let v = poly () with { ask () = (resume 1) + 10 }\n  v + 100",
                [1000, 127, 508, 127 + 128 + 129 + 130],
            ),
            (
                "closure_called_outside",
                "  let f = { let a = ask! (); stop! a; fun x -> x + stop! (x + a) } with { ask () = { let r = resume 1; r } }\n  f 10 + 100",
                [1000, 121, 484, 121 + 122 + 121 + 122],
            ),
            (
                "closure_called_inside",
                "  let f = fun x -> x + stop! x\n  let v = { let a = ask! (); f a + f (a + 1) } with { ask () = (resume 1) + 10 }\n  v + 100",
                [1000, 116, 464, 116 + 117 + 117 + 118],
            ),
        ],
    );
}

/// A callback passed to an operation. Handled by the delimited `with`
/// itself, the arm runs the callback against the lifted frame. Handled
/// further out, the outer arm runs a callback that was built inside the
/// `with`: the operations it performs (of the lifted frame, and of the
/// delimited handler) still reach their handlers with the rest of the
/// callback, of the outer arm and of the enclosing body behind them.
#[test]
fn callbacks_across_a_delimited_with() {
    check_delimited_cells(
        "delimited_callbacks",
        "",
        &[
            (
                "own_arm_runs_callback",
                "  let v = {\n    let s = scope! (fun () -> stop! 2 * 3)\n    s + ask! ()\n  } with {\n    ask () = (resume 1) + 10\n    scope f = { let r = f (); resume (r + 1) }\n  }\n  v + 100",
                [1000, 118, 236, 118 + 121],
            ),
            (
                "outer_arm_runs_callback",
                "  let v = {\n    let s = scope! (fun () -> stop! 2 * 3)\n    s + ask! ()\n  } with { ask () = (resume 1) + 10 }\n  v + 100",
                [1000, 118, 236, 118 + 121],
            ),
            (
                "outer_arm_callback_uses_delimited_handler",
                "  let v = {\n    let s = scope! (fun () -> ask! () * 3)\n    s * 2 + stop! 1\n  } with { ask () = (resume 1) * 5 }\n  v + 100",
                [1000, 145, 290, 145 + 150],
            ),
        ],
    );
}

/// Handlers the lowering knows statically but that are not a single arm
/// using the value of `resume`: a conditional handler with one such branch,
/// and an arm that resumes on one path and aborts on the other.
#[test]
fn conditional_and_mixed_handlers_are_delimited() {
    check_delimited_cells(
        "delimited_conditional",
        r#"
handler h_value for Ask { ask () = (resume 1) + 10 }
handler h_tail for Ask { ask () = resume 2 }

fun both : Unit -> Int needs {Stop, Ask}
both () = {
  let a = stop! 3
  a + ask! ()
}

fun pick : Bool -> Int needs {Stop}
pick c = {
  let h = if c then h_value else h_tail
  let v = both () with h
  v + 100
}

fun mixed : Int -> Int needs {Stop}
mixed n = {
  let v = both () with { ask () = if n > 0 then resume 1 else 50 }
  v + 100
}
"#,
        &[
            (
                "conditional_value_branch",
                "  pick True",
                [1000, 114, 228, 114 + 115],
            ),
            (
                "conditional_tail_branch",
                "  pick False",
                [1000, 105, 210, 105 + 106],
            ),
            (
                "mixed_arm_resumes",
                "  mixed 1",
                [1000, 104, 208, 104 + 105],
            ),
            ("mixed_arm_aborts", "  mixed 0", [1000, 150, 300, 300]),
        ],
    );
}

/// A `finally` handler inside a delimited `with`: an operation of the lifted
/// frame performed after `acquire!` suspends, which must not look like the
/// end of the resumed computation, and the cleanup's own operation belongs to
/// the lifted frame too.
#[test]
fn finally_inside_delimited_with_cleans_up_after_the_computation() {
    let src = r#"module Main

import Std.Ref (MutRef, Ref, beam_ref)

effect Stop { fun stop : Int -> Int }
effect Ask { fun ask : Unit -> Int }
effect Res { fun acquire : String -> Int }
effect Log { fun log : String -> Unit }

handler managed for Res needs {Log} {
  acquire name = {
    log! ("open " <> name)
    resume 7
  } finally {
    log! ("close " <> name)
  }
}

fun work : Unit -> Int needs {Stop, Log}
work () = {
  let v = {
    let w = {
      let r = acquire! "db"
      log! "work"
      let s = stop! r
      log! "more"
      s + ask! ()
    } with managed
    w + 1
  } with { ask () = (resume 1) + 10 }
  v + 100
}

fun run : MutRef String -> Int needs {Ref}
run out = work () with {
  stop i = resume i
  log m = {
    let _ = modify! out (fun s -> s <> m <> ", ")
    resume ()
  }
}

pub fun result : Unit -> String
result () = {
  let out = new! ""
  let v = run out
  get! out <> show v
} with beam_ref
"#;
    check_result_string(
        "finally_inside_delimited",
        src,
        "open db, work, more, close db, 119",
    );
}

/// A process spawned inside a delimited `with`: its callback is the whole
/// computation of the new process, so an operation of the lifted frame it
/// performs has nothing behind it but the rest of the callback.
#[test]
fn spawn_inside_delimited_with_runs_lifted_operations() {
    let src = r#"module Main

import Std.Actor (Actor, Process, beam_actor)

effect Stop { fun stop : Int -> Int }
effect Ask { fun ask : Unit -> Int }

fun recv : Unit -> Int needs {Actor Int}
recv () = receive { n -> n }

fun work : Unit -> Int needs {Stop, Process, Actor Int}
work () = {
  let me = self! ()
  let v = {
    let _ = spawn! (fun () -> send! me (stop! 5 + 1))
    let got = recv ()
    got + ask! ()
  } with { ask () = (resume 1) + 10 }
  v + 100
}

pub fun result : Unit -> String
result () = show ((work () with { stop i = resume i }) with beam_actor)
"#;
    check_result_string("spawn_inside_delimited", src, "117");
}

/// Known gap: a handler value only known at runtime (here a parameter)
/// keeps its handled computation on the Erlang stack, like a `finally`
/// handler: whether its arms use the value of `resume` or have a `finally`
/// block is not known where the `with` is lowered. Under the aborting outer
/// handler: expected 1000, gives 1100.
#[test]
#[ignore = "a `with` whose handler is only known at runtime is not given a continuation"]
fn runtime_handler_value_under_aborting_outer_handler() {
    check_delimited_cells(
        "delimited_runtime_handler",
        r#"
fun with_h : Handler Ask -> Int needs {Stop}
with_h h = {
  let v = { let a = stop! 3; a + ask! () } with h
  v + 100
}

fun make : Int -> Handler Ask
make n = if n > 0 then handler for Ask { ask () = (resume n) + 10 } else handler for Ask { ask () = resume n }
"#,
        &[("runtime", "  with_h (make 1)", [1000, 114, 228, 114 + 115])],
    );
}

/// A `resume` inside a function value (state passing: `get () = fun s ->
/// (resume s) s`) runs the rest of the handled computation when that
/// function is called (`f 20`, after the `with`). That computation performs
/// `Stop`, which the `with` does not handle, so calling `f` performs `Stop`:
/// `f` must be typed (and called) as effectful, or an outer abort has
/// nowhere to go. Expected 1000 under the aborting handler; gives 1100
/// (180 and 181 under the non-tail ones), because `resume` is typed as pure.
///
/// Typing `resume` with the residual row of the `with` is not enough on its
/// own: the closure is then CPS code, but it hands the suspension of the
/// resumed computation (`mbind`) back to its caller as its value instead of
/// binding it to its own continuation, so every cell gives
/// `{'$saga_meta', _}`.
const RESUME_UNDER_LAMBDA_STATE: &str = r#"
effect State {
  fun get : Unit -> Int
  fun put : Int -> Unit
}

fun counter : Unit -> Int needs {Stop, State}
counter () = {
  let s = get! ()
  let t = stop! s
  put! (s + t)
  get! ()
}

handler passing for State {
  get () = fun s -> (resume s) s
  put n = fun _ -> (resume ()) n
  return v = fun _ -> v
}
"#;

#[test]
#[ignore = "`resume` is typed as pure, so the function that resumes is called as pure code"]
fn resume_under_lambda_under_aborting_outer_handler() {
    check_delimited_cells(
        "delimited_state_passing",
        RESUME_UNDER_LAMBDA_STATE,
        &[(
            "state",
            "  let f = counter () with {\n    get () = fun s -> (resume s) s\n    put n = fun _ -> (resume ()) n\n    return v = fun _ -> v\n  }\n  f 20 + 100",
            [1000, 140, 280, 140 + 141],
        )],
    );
}

/// The same state-passing handler declared as a named handler: what its
/// `resume` performs is only known where it is installed.
#[test]
#[ignore = "`resume` is typed as pure; a named handler has no residual row to give it"]
fn resume_under_lambda_in_named_handler_under_aborting_outer_handler() {
    check_delimited_cells(
        "delimited_state_passing_named",
        RESUME_UNDER_LAMBDA_STATE,
        &[(
            "named",
            "  let f = counter () with passing\n  f 20 + 100",
            [1000, 140, 280, 140 + 141],
        )],
    );
}

/// A multishot handler that resumes inside the callback of a higher-order
/// function (`List.flat_map`), and one that keeps a resuming closure in a
/// list before calling it. The resumed computation performs `Stop`. The
/// closures are pure code, so the resumed computation is run to a plain
/// value: the aborting cells crash or give 1110.
#[test]
#[ignore = "`resume` is typed as pure, so the closures that resume are pure code"]
fn resume_under_callback_or_in_data_under_outer_handlers() {
    check_delimited_cells(
        "delimited_resume_in_callback",
        r#"
effect Choose { fun choose : Unit -> Bool }

fun pick_stop : Unit -> Int needs {Stop, Choose}
pick_stop () = {
  let b = choose! ()
  stop! (if b then 1 else 2)
}

fun total : List Int -> Int
total xs = List.foldl (fun acc x -> acc + x) 0 xs
"#,
        &[
            (
                "collect",
                "  let xs = pick_stop () with {\n    choose () = List.flat_map (fun b -> resume b) [True, False]\n    return v = [v]\n  }\n  total xs + 100",
                [1000, 103, 412, 416],
            ),
            (
                "stored",
                "  let r = ask_stop () with {\n    ask () = {\n      let ks = [fun x -> resume x]\n      List.foldl (fun acc k -> acc + k 1) 10 ks\n    }\n  }\n  r + 100",
                [1000, 121, 242, 243],
            ),
        ],
    );
}

/// Code that is not CPS calling code that is, inside a `with` that lifted
/// the frame: what the call leaves suspended is run to a plain value. Here a
/// local function in an arm that resumes, the thunk of `catch_panic`, and a
/// process spawned by a handler installed inside the `with`.
#[test]
fn pure_callers_inside_a_lifting_with_get_plain_values() {
    let src = r#"module Main

import Std.Actor (Actor, Process, beam_actor)
import Std.Process (catch_panic)

effect Stop { fun stop : Int -> Int }
effect Ask { fun ask : Unit -> Int }

fun local_fun_resumes : Unit -> Int needs {Stop}
local_fun_resumes () = {
  let v = { let a = ask! (); a + stop! 3 } with {
    ask () = {
      let go n = (resume n) + 10
      go 1 + go 2
    }
  }
  v + 100
}

fun panics_caught : Unit -> Int needs {Stop}
panics_caught () = {
  let v = {
    let r = catch_panic (fun () -> stop! 5 + 1)
    let n = case r {
      Ok n -> n
      Err _ -> 0
    }
    n + ask! ()
  } with { ask () = (resume 1) + 10 }
  v + 100
}

fun recv : Unit -> Int needs {Actor Int}
recv () = receive { n -> n }

fun spawned : Unit -> Int needs {Stop}
spawned () = {
  let v = {
    let me = self! ()
    let _ = spawn! (fun () -> send! me (stop! 5 + 1))
    let got = recv ()
    got + ask! ()
  } with {beam_actor, ask () = (resume 1) + 10}
  v + 100
}

pub fun result : Unit -> String
result () = {
  let a = local_fun_resumes () with { stop i = resume i }
  let b = panics_caught () with { stop i = resume i }
  let c = spawned () with { stop i = resume i }
  show a <> " " <> show b <> " " <> show c
}
"#;
    // a: go 1 = (1 + 3) + 10, go 2 = (2 + 3) + 10.
    check_result_string("pure_callers_in_lifting_with", src, "129 117 117");
}

/// An inline handler with several arms for one operation: an arm that
/// resumes reaches the rest of the host's body through its own continuation
/// only. It used to apply the rest a second time.
#[test]
fn multi_arm_inline_handler_resumes_once() {
    let src = r#"module Main

effect Op { fun op : Int -> Int }
effect Count { fun tick : Unit -> Unit }

fun both : Unit -> Int needs {Op}
both () = op! 1 + op! 0

fun host : Unit -> Int needs {Count}
host () = {
  let v = both () with {
    op 0 = resume 10
    op n = resume n
  }
  tick! ()
  v + 100
}

pub fun result : Unit -> String
result () = {
  let f = host () with {
    tick () = fun n -> (resume ()) (n + 1)
    return v = fun n -> v * 10 + n
  }
  show (f 0)
}
"#;
    // 111, and one tick.
    check_result_string("multi_arm_inline_resumes_once", src, "1111");
}

/// Known gap: an operation that is passed a callback is not lifted (the
/// meta continuation current when its arm resumes, after running the
/// callback, cannot reach the continuation built when it was performed
/// without process state). It is performed inside the extent of the `with`,
/// so an arm for it further out that aborts returns its value to the `with`.
/// Expected 1000, gives 1100.
#[test]
#[ignore = "an operation carrying a callback is not lifted: an outer arm for it that aborts returns to the inner `with`"]
fn callback_operation_aborted_by_outer_handler() {
    let src = r#"module Main

effect Ask { fun ask : Unit -> Int }
effect Scope { fun scope : (Unit -> Int needs {..r}) -> Int needs {..r} }

fun inner : Unit -> Int needs {Scope}
inner () = {
  let v = {
    let s = scope! (fun () -> ask! ())
    s + ask! ()
  } with { ask () = (resume 1) + 10 }
  v + 100
}

fun aborted : Unit -> Int
aborted () = inner () with { scope g = 1000 }

pub fun result : Unit -> String
result () = show (aborted ())
"#;
    check_result_string("callback_operation_outer_abort", src, "1000");
}
