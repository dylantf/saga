//! Guards are pure: the effect row a guard infers must be the empty row, in
//! every guard position (`case` arm, `receive` arm, top-level function
//! clause, local function clause). See `Checker::check_guard`.

use super::*;
use crate::lexer::Lexer;
use crate::parser::Parser;

/// Declarations shared by the programs below.
const DECLS: &str = r#"
import Std.Actor (Actor)

effect Stop { fun stop : Int -> Int }

fun eff : Int -> Int needs {Stop}
eff n = stop! n

fun pure_fn : Int -> Int
pure_fn n = n + 1

fun twice : (Int -> Int needs {..r}) -> Int -> Int needs {..r}
twice f n = f (f n)
"#;

/// In scope for every guard: `n : Int`, `ke : Int -> Bool needs {Stop}`,
/// `ko : Int -> Bool needs {..e}`, `kp : Int -> Bool`.
const SIG: &str =
    "(Int -> Bool needs {Stop}) -> (Int -> Bool needs {..e}) -> (Int -> Bool) -> Int -> Int";

/// One program per guard position, with `guard` as the guard expression.
fn positions(guard: &str) -> Vec<(&'static str, String)> {
    vec![
        (
            "case arm",
            format!(
                "{DECLS}
fun f : {SIG} needs {{Stop, ..e}}
f ke ko kp x = case x {{
  n when {guard} -> ke n |> fun _ -> ko n |> fun _ -> kp n |> fun _ -> 5
  _ -> 6
}}
"
            ),
        ),
        (
            "function clause",
            format!(
                "{DECLS}
fun f : {SIG} needs {{Stop, ..e}}
f ke ko kp n when {guard} = ke n |> fun _ -> ko n |> fun _ -> kp n |> fun _ -> 5
f _ _ _ _ = 6
"
            ),
        ),
        (
            "local function clause",
            format!(
                "{DECLS}
fun f : {SIG} needs {{Stop, ..e}}
f ke ko kp x = {{
  let h n when {guard} = ke n |> fun _ -> ko n |> fun _ -> kp n |> fun _ -> 5
  let h _ = 6
  h x
}}
"
            ),
        ),
        (
            "receive arm",
            format!(
                "{DECLS}
fun f : {SIG} needs {{Actor Int, Stop, ..e}}
f ke ko kp x = receive {{
  n when {guard} -> ke n |> fun _ -> ko n |> fun _ -> kp n |> fun _ -> x
  _ -> 6
}}
"
            ),
        ),
    ]
}

fn check(src: &str) -> Result<(), Diagnostic> {
    let tokens = Lexer::new(src).lex().expect("lex error");
    let mut program = Parser::new(tokens).parse_program().expect("parse error");
    crate::desugar::desugar_program(&mut program);
    let mut checker = Checker::with_prelude(None).expect("prelude");
    let result = checker.check_program(&mut program);
    match result.errors().into_iter().next() {
        Some(e) => Err(e.clone()),
        None => Ok(()),
    }
}

fn accepted_everywhere(guard: &str) {
    for (position, src) in positions(guard) {
        if let Err(e) = check(&src) {
            panic!(
                "guard `{guard}` in a {position} should be accepted: {}",
                e.message
            );
        }
    }
}

/// The guard is rejected in every position, with the purity diagnostic
/// naming `effects`, spanning exactly the guard expression (or, for a direct
/// operation call, the call).
fn rejected_everywhere(guard: &str, effects: &str, span_text: &str) {
    for (position, src) in positions(guard) {
        let err = match check(&src) {
            Ok(()) => panic!("guard `{guard}` in a {position} should be rejected"),
            Err(e) => e,
        };
        assert!(
            err.message
                .starts_with("Effect calls are not allowed in guard expressions"),
            "guard `{guard}` in a {position}: unexpected error: {}",
            err.message
        );
        assert!(
            err.message.ends_with(effects),
            "guard `{guard}` in a {position}: expected the message to end with `{effects}`: {}",
            err.message
        );
        let span = err.span.expect("guard error without a span");
        assert_eq!(
            &src[span.start..span.end],
            span_text,
            "guard `{guard}` in a {position}: wrong span"
        );
    }
}

#[test]
fn direct_operation_call_in_guard_is_rejected() {
    rejected_everywhere("stop! n == 3", "guard expressions", "stop!");
}

#[test]
fn operation_call_nested_in_guard_is_rejected() {
    // Not reached by the syntactic check for a direct call; the row catches it.
    rejected_everywhere(
        "{ let v = stop! n; v == 3 }",
        "this guard needs {Stop}",
        "{ let v = stop! n; v == 3 }",
    );
}

#[test]
fn effectful_named_function_in_guard_is_rejected() {
    rejected_everywhere("eff n == 3", "this guard needs {Stop}", "eff n == 3");
}

#[test]
fn effectful_parameter_in_guard_is_rejected() {
    rejected_everywhere("ke n", "this guard needs {Stop}", "ke n");
}

#[test]
fn open_row_parameter_in_guard_is_rejected() {
    rejected_everywhere("ko n", "this guard needs {..e}", "ko n");
}

#[test]
fn effectful_and_open_row_in_guard_names_both() {
    rejected_everywhere(
        "ke n && ko n",
        "this guard needs {Stop, ..e}",
        "ke n && ko n",
    );
}

#[test]
fn effectful_function_through_open_row_function_in_guard_is_rejected() {
    rejected_everywhere(
        "twice eff n == 3",
        "this guard needs {Stop}",
        "twice eff n == 3",
    );
    rejected_everywhere(
        "twice (fun y -> eff y) n == 3",
        "this guard needs {Stop}",
        "twice (fun y -> eff y) n == 3",
    );
}

#[test]
fn pure_function_in_guard_is_accepted() {
    accepted_everywhere("pure_fn n == 3");
}

#[test]
fn pure_parameter_in_guard_is_accepted() {
    accepted_everywhere("kp n");
}

#[test]
fn open_row_function_at_pure_argument_in_guard_is_accepted() {
    // `twice`'s row variable is instantiated fresh for the guard and bound to
    // the empty row by its pure argument.
    accepted_everywhere("twice pure_fn n == 3");
    accepted_everywhere("twice (fun y -> y + 1) n == 3");
}

#[test]
fn effectful_lambda_not_called_in_guard_is_accepted() {
    accepted_everywhere("{ let k = fun y -> eff y; let _ = k; n == 3 }");
}

#[test]
fn pure_trait_method_in_guard_is_accepted() {
    accepted_everywhere("show n == \"3\"");
    accepted_everywhere("compare n 3 == Eq");
}

#[test]
fn effect_handled_inside_guard_is_accepted() {
    // The guard's own row is empty: the effect does not leave it.
    accepted_everywhere("(eff n with { stop i = resume i }) == 3");
}

#[test]
fn function_declared_pure_cannot_perform_effects_from_a_guard() {
    // The reported hole: `f` is declared pure and `eff` needs `Stop`.
    for body in [
        "f x = case x {\n  n when eff n == 3 -> 5\n  _ -> 6\n}",
        "f n when eff n == 3 = 5\nf _ = 6",
    ] {
        let src = format!("{DECLS}\nfun f : Int -> Int\n{body}\n");
        let err = check(&src).expect_err("effectful guard in a pure function");
        assert!(
            err.message.ends_with("this guard needs {Stop}"),
            "{}",
            err.message
        );
    }
}

#[test]
fn unannotated_parameter_called_in_guard_becomes_pure() {
    // `k`'s row is an inference variable: the guard closes it, so `f` takes a
    // pure function and an effectful argument is a type error at the call.
    let f = "f k x = case x {\n  n when k n -> 5\n  _ -> 6\n}\n";
    let clause = "f k n when k n = 5\nf _ _ = 6\n";
    let local = "f k x = {\n  let h n when k n = 5\n  let h _ = 6\n  h x\n}\n";
    for def in [f, clause, local] {
        check(&format!(
            "{DECLS}\n{def}\nfun ok : Int -> Bool\nok n = n == 1\n\nfun go : Unit -> Int\ngo () = f ok 3\n"
        ))
        .unwrap_or_else(|e| panic!("pure argument should be accepted: {}", e.message));
        let err = check(&format!(
            "{DECLS}\n{def}\nfun bad : Int -> Bool needs {{Stop}}\nbad n = stop! n == 1\n\nfun go : Unit -> Int needs {{Stop}}\ngo () = f bad 3\n"
        ))
        .expect_err("effectful argument to a function that calls it in a guard");
        assert!(
            err.message.contains("effect row mismatch"),
            "{}",
            err.message
        );
    }
}

#[test]
fn open_row_trait_method_on_abstract_type_in_guard_is_rejected() {
    let src = "
trait Risky a {
  fun risk : a -> Int needs {..e}
}

fun guarded : a -> Int needs {..a} where {a: Risky}
guarded x = case x {
  y when risk y == 3 -> 5
  _ -> 6
}
";
    let err = check(src).expect_err("open-row trait method in a guard");
    assert!(
        err.message.ends_with("this guard needs {..a}"),
        "{}",
        err.message
    );
}
