//! Tests for the effect-row rule warning (decisions D2a and D7 of
//! `docs/planning/sound-function-representation.md`): closed effect rows
//! unify only when equal, except that at a coercion position the actual row
//! may be a subset of the expected row. Violations are warnings for now.

use super::unify::ROW_RULE_NOTE;
use super::*;
use crate::lexer::Lexer;
use crate::parser::Parser;

/// Declarations shared by the programs below (Appendix A of the plan).
const PRELUDE: &str = r#"
effect Skip { fun skip : Unit -> Int }

fun eff : Unit -> Int needs {Skip}
eff () = skip! ()

fun pure_fn : Unit -> Int
pure_fn () = 1
"#;

/// Type-check `PRELUDE + src`, require that it has no errors, and return the
/// effect-row rule warnings (message text only).
fn row_warnings(src: &str) -> Vec<String> {
    let src = format!("{PRELUDE}\n{src}");
    let tokens = Lexer::new(&src).lex().expect("lex error");
    let mut program = Parser::new(tokens).parse_program().expect("parse error");
    crate::desugar::desugar_program(&mut program);
    let mut checker = Checker::with_prelude(None).expect("prelude");
    let result = checker.check_program(&mut program);
    assert!(
        !result.has_errors(),
        "unexpected type errors: {:?}",
        result
            .errors()
            .iter()
            .map(|d| &d.message)
            .collect::<Vec<_>>()
    );
    for warning in result.warnings() {
        if warning.message.ends_with(ROW_RULE_NOTE) {
            assert!(warning.span.is_some(), "row warning without a span");
        }
    }
    result
        .warnings()
        .iter()
        .filter(|d| d.message.ends_with(ROW_RULE_NOTE))
        .map(|d| d.message.clone())
        .collect()
}

const AT_DEPTH: &str = "are treated as the same type inside a larger type";
const NOT_A_COERCION: &str = "are treated as the same type here";
const WRONG_DIRECTION: &str = "is used where a function with no effects is expected";

#[track_caller]
fn assert_one(warnings: &[String], needle: &str) {
    assert_eq!(warnings.len(), 1, "expected one warning, got {warnings:#?}");
    assert!(
        warnings[0].contains(needle),
        "expected a warning containing `{needle}`, got: {}",
        warnings[0]
    );
}

#[track_caller]
fn assert_none(warnings: &[String]) {
    assert!(warnings.is_empty(), "expected no warnings: {warnings:#?}");
}

// --- Appendix A programs that the rule is meant to reject ---

#[test]
fn a6_effectful_functions_as_pure_in_a_list_warns_at_depth() {
    let warnings = row_warnings(
        r#"
fun sum_pure : List (Unit -> Int) -> Int
sum_pure fs = case fs {
  [] -> 0
  f :: rest -> f () + sum_pure rest
}

fun effs : Unit -> List (Unit -> Int needs {Skip})
effs () = [fun () -> skip! (), fun () -> 2]

main () = dbg (sum_pure (effs ()))
"#,
    );
    assert_one(&warnings, AT_DEPTH);
    assert!(warnings[0].contains("({Skip} and no effects)"));
}

#[test]
fn a7_pure_functions_as_effectful_in_a_list_warns_at_depth() {
    let warnings = row_warnings(
        r#"
fun run_all : List (Unit -> Int needs {Skip}) -> Int needs {Skip}
run_all fs = case fs {
  [] -> 0
  f :: rest -> f () + run_all rest
}

fun pures : Unit -> List (Unit -> Int)
pures () = [fun () -> 1, fun () -> 2]

main () = dbg (run_all (pures ()) with { skip () = resume 100 })
"#,
    );
    assert_one(&warnings, AT_DEPTH);
}

#[test]
fn a11_effectful_function_as_pure_in_an_if_branch_warns() {
    let warnings = row_warnings(
        r#"
fun get : Bool -> (Unit -> Int)
get b = if b then eff else (fun () -> 1)

main () = dbg ((get True) ())
"#,
    );
    assert_one(&warnings, WRONG_DIRECTION);
    assert!(warnings[0].contains("a function that uses {Skip}"));
    assert!(warnings[0].contains("add `needs {Skip}`"));
}

#[test]
fn a12_effectful_function_as_pure_in_a_record_field_warns() {
    let warnings = row_warnings(
        r#"
record Box { run : Unit -> Int }

main () = {
  let b = Box { run: eff }
  dbg (b.run ())
}
"#,
    );
    assert_one(&warnings, WRONG_DIRECTION);
}

// --- Wrong direction at the other coercion positions ---

#[test]
fn effectful_function_as_pure_warns_at_every_coercion_position() {
    // Annotated `let`.
    assert_one(
        &row_warnings("fun f : Unit -> Int\nf () = {\n  let _g : Unit -> Int = eff\n  1\n}"),
        WRONG_DIRECTION,
    );
    // Type ascription.
    assert_one(
        &row_warnings("fun f : Unit -> Int\nf () = (eff : Unit -> Int) ()"),
        WRONG_DIRECTION,
    );
    // Function return position.
    assert_one(
        &row_warnings("fun f : Unit -> (Unit -> Int)\nf () = eff"),
        WRONG_DIRECTION,
    );
    // `case` branch against the declared return type.
    assert_one(
        &row_warnings(
            "fun f : Int -> (Unit -> Int)\nf n = case n {\n  0 -> pure_fn\n  _ -> eff\n}",
        ),
        WRONG_DIRECTION,
    );
    // Tuple literal element.
    assert_one(
        &row_warnings("fun f : Unit -> (Unit -> Int, Unit -> Int)\nf () = (eff, pure_fn)"),
        WRONG_DIRECTION,
    );
    // List literal element.
    assert_one(
        &row_warnings("fun f : Unit -> List (Unit -> Int)\nf () = [pure_fn, eff]"),
        WRONG_DIRECTION,
    );
    // Record update field.
    assert_one(
        &row_warnings(
            "record Box { run : Unit -> Int }\n\
             fun f : Box -> Box\nf b = { b | run: eff }",
        ),
        WRONG_DIRECTION,
    );
    // Return position of a lambda checked against an expected type: the
    // existing call-argument check only looks at the lambda's own arrow.
    assert_one(
        &row_warnings(
            "fun call : (Int -> (Unit -> Int)) -> Int\ncall mk = (mk 1) ()\n\
             fun f : Unit -> Int\nf () = call (fun _ -> eff)",
        ),
        WRONG_DIRECTION,
    );
}

#[test]
fn partially_allowed_effects_name_the_expected_row() {
    let warnings = row_warnings(
        r#"
effect Log { fun log : String -> Unit }

fun both : Unit -> Int needs {Skip, Log}
both () = {
  log! "x"
  skip! ()
}

fun f : Unit -> (Unit -> Int needs {Log})
f () = both
"#,
    );
    assert_eq!(warnings.len(), 1, "{warnings:#?}");
    assert!(warnings[0].contains("a function that uses {Log, Skip}"));
    assert!(warnings[0].contains("a function that only allows {Log} is expected"));
    assert!(warnings[0].contains("Handle {Skip} first"));
}

// --- At depth, away from a literal ---

#[test]
fn rows_at_depth_warn_in_either_direction() {
    let take_pair = "fun take_pair : (Unit -> Int needs {Skip}, Unit -> Int needs {Skip}) -> Int needs {Skip}\n\
                     take_pair p = {\n  let (a, b) = p\n  a () + b ()\n}\n";
    // A tuple held in a variable is not a literal: its element rows are
    // nested in the tuple type.
    assert_one(
        &row_warnings(&format!(
            "{take_pair}\
             fun f : Unit -> Int needs {{Skip}}\n\
             f () = {{\n  let pair = (pure_fn, pure_fn)\n  take_pair pair\n}}"
        )),
        AT_DEPTH,
    );
    // Inside another function's parameter type.
    assert_one(
        &row_warnings(
            "fun apply_pure : ((Unit -> Int) -> Int) -> Int\napply_pure k = k pure_fn\n\
             fun wants_eff : (Unit -> Int needs {Skip}) -> Int\nwants_eff g = g () with { skip () = resume 1 }\n\
             fun f : Unit -> Int\nf () = apply_pure wants_eff",
        ),
        AT_DEPTH,
    );
    // Inside a named record's type argument.
    assert_one(
        &row_warnings(
            "record Holder a { item : a }\n\
             fun unwrap : Holder (Unit -> Int) -> Int\nunwrap h = h.item ()\n\
             fun mk : Unit -> Holder (Unit -> Int needs {Skip})\nmk () = Holder { item: eff }\n\
             fun f : Unit -> Int\nf () = unwrap (mk ())",
        ),
        AT_DEPTH,
    );
}

#[test]
fn branches_holding_literals_with_different_nested_rows_warn() {
    // `if`/`case` branches are joined before any expected type is consulted,
    // and the join only widens rows of function-typed branches. Tuples are
    // joined by plain unification, so their element rows must agree.
    assert_one(
        &row_warnings(
            "fun f : Bool -> (Unit -> Int needs {Skip}, Int)
\
             f b = if b then (eff, 1) else (pure_fn, 2)",
        ),
        AT_DEPTH,
    );
    // A constructor applied to a function is not a literal position either:
    // `Just pure_fn` is a `Maybe (Unit -> Int)`.
    assert_one(
        &row_warnings(
            "fun take : Maybe (Unit -> Int needs {Skip}) -> Int needs {Skip}
\
             take m = case m {\n  Just g -> g ()\n  Nothing -> 0\n}\n\
             fun f : Unit -> Int needs {Skip}\nf () = take (Just pure_fn)",
        ),
        AT_DEPTH,
    );
}

#[test]
fn local_function_clauses_with_different_rows_warn() {
    // Not a coercion position: the clauses of one function must agree. Today
    // the function's row is pinned to the first clause, so `go` is typed as
    // pure although its second clause performs `Skip`.
    let warnings = row_warnings(
        r#"
fun f : Int -> Int
f n = {
  let go 0 = 0
  let go m = m + skip! ()
  go n
}
"#,
    );
    assert_one(&warnings, NOT_A_COERCION);
}

// --- Legal subsumption: no warning ---

#[test]
fn pure_function_passed_where_effectful_callback_is_expected_is_silent() {
    assert_none(&row_warnings(
        r#"
fun run : (Unit -> Int needs {Skip}) -> Int needs {Skip}
run f = f ()

fun run_open : (Unit -> Int needs {..e}) -> Int needs {..e}
run_open f = f ()

fun a : Unit -> Int needs {Skip}
a () = run pure_fn + run (fun () -> 2) + run eff

fun b : Unit -> Int
b () = run_open pure_fn + run_open (fun () -> 2)
"#,
    ));
}

#[test]
fn tuple_and_list_literal_widening_is_silent() {
    // `tuple_widens_shared_row_var_at_expected_type` from tests.rs.
    assert_none(&row_warnings(
        "effect Foo {\n  fun foo : Unit -> Unit\n}\n\
         effect Bar {\n  fun bar : Unit -> Unit\n}\n\
         fun do_foo : Unit -> Unit needs {Foo}\n\
         do_foo () = foo! ()\n\
         fun do_bar : Unit -> Unit needs {Bar}\n\
         do_bar () = bar! ()\n\
         fun run_pair : (Unit -> Unit needs {..e}, Unit -> Unit needs {..e}) -> Unit needs {..e}\n\
         run_pair p = {\n  let (a, b) = p\n  a ()\n  b ()\n}\n\
         fun caller : Unit -> Unit needs {Foo, Bar}\n\
         caller () = run_pair (do_foo, do_bar)\n\
         fun run_list : List (Unit -> Unit needs {..e}) -> Unit needs {..e}\n\
         run_list fs = case fs {\n  [] -> ()\n  f :: rest -> {\n    f ()\n    run_list rest\n  }\n}\n\
         fun list_caller : Unit -> Unit needs {Foo, Bar}\n\
         list_caller () = run_list [do_foo, do_bar, fun () -> ()]",
    ));
}

#[test]
fn pure_function_at_each_coercion_position_is_silent() {
    assert_none(&row_warnings(
        r#"
record Box { run : Unit -> Int needs {Skip} }

fun take_pair : (Unit -> Int needs {Skip}, Unit -> Int needs {Skip}) -> Int needs {Skip}
take_pair p = {
  let (a, b) = p
  a () + b ()
}

fun take_rec : { a : Unit -> Int needs {Skip}, b : Int } -> Int needs {Skip}
take_rec r = r.a () + r.b

fun take_list : List (Unit -> Int needs {Skip}) -> Int needs {Skip}
take_list fs = case fs {
  [] -> 0
  f :: _ -> f ()
}

# return position, if / case branches (A1's shape)
fun choose : Int -> (Unit -> Int needs {Skip})
choose n = case n {
  0 -> fun () -> 1
  1 -> if n > 0 then pure_fn else eff
  _ -> fun () -> skip! ()
}

fun just_pure : Unit -> (Unit -> Int needs {Skip})
just_pure () = pure_fn

fun via_block : Unit -> (Unit -> Int needs {Skip})
via_block () = {
  let x = 1
  if x > 0 then pure_fn else eff
}

fun rest : Result Int String -> Int needs {Skip}
rest r = {
  # annotated let and ascription
  let f : Unit -> Int needs {Skip} = pure_fn
  let g = (pure_fn : Unit -> Int needs {Skip})
  # record field initialiser and update
  let b = Box { run: pure_fn }
  let b2 = { b | run: fun () -> 2 }
  # tuple, list and anonymous-record literals as direct arguments
  let n = take_pair (pure_fn, eff) + take_list [pure_fn, eff] + take_rec { a: pure_fn, b: 2 }
  # a literal as the result of a block
  let m = take_pair {
    let one = pure_fn
    (one, eff)
  }
  # do / else: the else arm may have fewer effects than the success value
  let h = do {
    Ok _ <- r
    eff
  } else {
    Err _ -> pure_fn
  }
  f () + g () + b.run () + b2.run () + n + m + h ()
}
"#,
    ));
}

#[test]
fn multi_parameter_effectful_lambda_matches_a_declared_curried_type() {
    // `infer_lambda` puts a lambda's row on its first arrow; a declared
    // `A -> B -> C needs {E}` has it on the last. They describe the same
    // two-argument effectful function, so no warning (see
    // `Checker::coercion_warning`).
    assert_none(&row_warnings(
        r#"
record Ops { combine : Int -> Int -> Int needs {Skip} }

fun mk : Unit -> (Int -> Int -> Int needs {Skip})
mk () = fun a b -> a + b + skip! ()

fun use_ops : Unit -> Int needs {Skip}
use_ops () = {
  let ops = Ops { combine: fun a b -> a + b + skip! () }
  ops.combine 1 2
}
"#,
    ));
    // The effects still have to be declared somewhere on the expected type.
    assert_one(
        &row_warnings(
            "record Ops { combine : Int -> Int -> Int }\n\
             fun f : Unit -> Ops\nf () = Ops { combine: fun a b -> a + b + skip! () }",
        ),
        WRONG_DIRECTION,
    );
}

#[test]
fn equal_rows_and_row_variables_are_silent() {
    assert_none(&row_warnings(
        r#"
fun run_each : List (Unit -> Int needs {..e}) -> Int needs {..e}
run_each fs = case fs {
  [] -> 0
  f :: rest -> f () + run_each rest
}

fun effs : Unit -> List (Unit -> Int needs {Skip})
effs () = [eff, fun () -> 2]

fun pures : Unit -> List (Unit -> Int)
pures () = [pure_fn]

fun same : List (Unit -> Int needs {Skip}) -> List (Unit -> Int needs {Skip})
same fs = fs

# row variables instantiate at any depth (A8's shape)
fun f : Unit -> Int needs {Skip}
f () = run_each (effs ()) + run_each (pures ()) + run_each (same (effs ()))
"#,
    ));
}

#[test]
fn warning_is_reported_for_imported_modules() {
    // Module checkers do not run the deferred-warning pass, so the row
    // warnings are pushed straight onto the module's diagnostics.
    let lib = r#"
module Lib

effect Skip { fun skip : Unit -> Int }

fun eff : Unit -> Int needs {Skip}
eff () = skip! ()

pub fun get : Bool -> (Unit -> Int)
get b = if b then eff else (fun () -> 1)
"#;
    let main = "module Main\nimport Lib\n\nmain () = dbg ((Lib.get False) ())\n";
    let checker = super::tests::check_with_project_files(&[("src/Lib.saga", lib)], main)
        .expect("project should typecheck");
    let lib_result = checker
        .modules
        .check_results
        .get("Lib")
        .expect("Lib check result");
    let warnings: Vec<_> = lib_result
        .warnings()
        .into_iter()
        .filter(|d| d.message.ends_with(ROW_RULE_NOTE))
        .collect();
    assert_eq!(warnings.len(), 1, "{:?}", lib_result.diagnostics);
    assert!(warnings[0].message.contains(WRONG_DIRECTION));
    assert!(warnings[0].span.is_some());
}

#[test]
fn call_argument_error_supersedes_the_warning() {
    // Direct call arguments already have a hard error for this; the warning
    // for the same expression is dropped rather than reported twice.
    let src = format!(
        "{PRELUDE}\nfun run_pure : (Unit -> Int) -> Int\nrun_pure f = f ()\n\
         fun f : Unit -> Int needs {{Skip}}\nf () = run_pure eff\n"
    );
    let tokens = Lexer::new(&src).lex().expect("lex error");
    let mut program = Parser::new(tokens).parse_program().expect("parse error");
    crate::desugar::desugar_program(&mut program);
    let mut checker = Checker::with_prelude(None).expect("prelude");
    let result = checker.check_program(&mut program);
    assert!(result.errors().iter().any(|d| {
        d.message
            .contains("passed where a pure callback is expected")
    }));
    assert!(
        result
            .warnings()
            .iter()
            .all(|d| !d.message.ends_with(ROW_RULE_NOTE))
    );
}
