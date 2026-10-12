//! Tests for the effect-row rule (decisions D2a and D7 of
//! `docs/planning/sound-function-representation.md`): closed effect rows
//! unify only when equal, except that at a coercion position the actual row
//! may be a subset of the expected row. Violations are type errors.

use super::unify::ROW_RULE_MARKER;
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

/// Type-check `PRELUDE + src` and return the effect-row rule errors (message
/// text only). Any other type error fails the test, so an empty result means
/// the program type-checks.
fn row_errors(src: &str) -> Vec<String> {
    let src = format!("{PRELUDE}\n{src}");
    let tokens = Lexer::new(&src).lex().expect("lex error");
    let mut program = Parser::new(tokens).parse_program().expect("parse error");
    crate::desugar::desugar_program(&mut program);
    let mut checker = Checker::with_prelude(None).expect("prelude");
    let result = checker.check_program(&mut program);
    let errors = result.errors();
    for error in &errors {
        assert!(
            error.message.starts_with(ROW_RULE_MARKER),
            "unexpected type error: {}",
            error.message
        );
        assert!(error.span.is_some(), "row error without a span");
    }
    errors.iter().map(|d| d.message.clone()).collect()
}

/// Type-check `PRELUDE + src` and return the messages of its type errors.
fn type_errors(src: &str) -> Vec<String> {
    let src = format!("{PRELUDE}\n{src}");
    let tokens = Lexer::new(&src).lex().expect("lex error");
    let mut program = Parser::new(tokens).parse_program().expect("parse error");
    crate::desugar::desugar_program(&mut program);
    let mut checker = Checker::with_prelude(None).expect("prelude");
    let result = checker.check_program(&mut program);
    result.errors().iter().map(|d| d.message.clone()).collect()
}

/// "declares needs {..} but never uses it" warnings for `PRELUDE + src`.
fn unused_needs_warnings(src: &str) -> Vec<String> {
    let src = format!("{PRELUDE}\n{src}");
    let tokens = Lexer::new(&src).lex().expect("lex error");
    let mut program = Parser::new(tokens).parse_program().expect("parse error");
    crate::desugar::desugar_program(&mut program);
    let mut checker = Checker::with_prelude(None).expect("prelude");
    let result = checker.check_program(&mut program);
    result
        .warnings()
        .iter()
        .filter(|d| d.message.contains("but never uses it"))
        .map(|d| d.message.clone())
        .collect()
}

const AT_DEPTH: &str = "cannot be used as the same type inside a larger type";
const WRONG_DIRECTION: &str = "is used where a function with no effects is expected";

#[track_caller]
fn assert_one(errors: &[String], needle: &str) {
    assert_eq!(errors.len(), 1, "expected one error, got {errors:#?}");
    assert!(
        errors[0].contains(needle),
        "expected an error containing `{needle}`, got: {}",
        errors[0]
    );
}

#[track_caller]
fn assert_none(errors: &[String]) {
    assert!(errors.is_empty(), "expected no errors: {errors:#?}");
}

// --- Appendix A programs that the rule is meant to reject ---

#[test]
fn a6_effectful_functions_as_pure_in_a_list_is_an_error_at_depth() {
    let errors = row_errors(
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
    assert_one(&errors, AT_DEPTH);
    assert!(errors[0].contains("({Skip} and no effects)"));
}

#[test]
fn a7_pure_functions_as_effectful_in_a_list_is_an_error_at_depth() {
    let errors = row_errors(
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
    assert_one(&errors, AT_DEPTH);
}

#[test]
fn a11_effectful_function_as_pure_in_an_if_branch_is_an_error() {
    let errors = row_errors(
        r#"
fun get : Bool -> (Unit -> Int)
get b = if b then eff else (fun () -> 1)

main () = dbg ((get True) ())
"#,
    );
    assert_one(&errors, WRONG_DIRECTION);
    assert!(errors[0].contains("a function that uses {Skip}"));
    assert!(errors[0].contains("add `needs {Skip}`"));
}

#[test]
fn a12_effectful_function_as_pure_in_a_record_field_is_an_error() {
    let errors = row_errors(
        r#"
record Box { run : Unit -> Int }

main () = {
  let b = Box { run: eff }
  dbg (b.run ())
}
"#,
    );
    assert_one(&errors, WRONG_DIRECTION);
}

// --- Wrong direction at the other coercion positions ---

#[test]
fn effectful_function_as_pure_is_an_error_at_every_coercion_position() {
    // Annotated `let`.
    assert_one(
        &row_errors("fun f : Unit -> Int\nf () = {\n  let _g : Unit -> Int = eff\n  1\n}"),
        WRONG_DIRECTION,
    );
    // Type ascription.
    assert_one(
        &row_errors("fun f : Unit -> Int\nf () = (eff : Unit -> Int) ()"),
        WRONG_DIRECTION,
    );
    // Function return position.
    assert_one(
        &row_errors("fun f : Unit -> (Unit -> Int)\nf () = eff"),
        WRONG_DIRECTION,
    );
    // `case` branch against the declared return type.
    assert_one(
        &row_errors("fun f : Int -> (Unit -> Int)\nf n = case n {\n  0 -> pure_fn\n  _ -> eff\n}"),
        WRONG_DIRECTION,
    );
    // Tuple literal element.
    assert_one(
        &row_errors("fun f : Unit -> (Unit -> Int, Unit -> Int)\nf () = (eff, pure_fn)"),
        WRONG_DIRECTION,
    );
    // List literal element.
    assert_one(
        &row_errors("fun f : Unit -> List (Unit -> Int)\nf () = [pure_fn, eff]"),
        WRONG_DIRECTION,
    );
    // Record update field.
    assert_one(
        &row_errors(
            "record Box { run : Unit -> Int }\n\
             fun f : Box -> Box\nf b = { b | run: eff }",
        ),
        WRONG_DIRECTION,
    );
    // Return position of a lambda that is not a call argument.
    assert_one(
        &row_errors(
            "fun f : Unit -> Int\nf () = {\n  \
             let _mk : Int -> (Unit -> Int) = fun _ -> eff\n  1\n}",
        ),
        WRONG_DIRECTION,
    );
}

#[test]
fn call_argument_check_covers_every_arrow_of_the_callback() {
    // `Int -> (Unit -> Int)` is `Int -> Unit -> Int`: the call-argument check
    // compares the callback with its parameter type arrow by arrow, so an
    // effect on a later arrow is an error like one on the first.
    let call = "fun call : (Int -> Unit -> Int) -> Int\ncall mk = mk 1 ()\n";
    for arg in [
        "(fun _ -> eff)",
        "(fun _ () -> skip! ())",
        "(fun _ -> fun () -> skip! ())",
        "eff2",
    ] {
        let errors = type_errors(&format!(
            "{call}\
             fun eff2 : Int -> Unit -> Int needs {{Skip}}\neff2 _ () = skip! ()\n\
             fun f : Unit -> Int needs {{Skip}}\nf () = call {arg}"
        ));
        assert!(
            errors.iter().any(|e| e.contains(WRONG_DIRECTION)),
            "{arg}: {errors:#?}"
        );
    }
}

#[test]
fn partially_allowed_effects_name_the_expected_row() {
    let errors = row_errors(
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
    assert_eq!(errors.len(), 1, "{errors:#?}");
    assert!(errors[0].contains("a function that uses {Log, Skip}"));
    assert!(errors[0].contains("a function that only allows {Log} is expected"));
    assert!(errors[0].contains("Handle {Skip} first"));
}

// --- At depth, away from a literal ---

#[test]
fn rows_at_depth_are_errors_in_either_direction() {
    let take_pair = "fun take_pair : (Unit -> Int needs {Skip}, Unit -> Int needs {Skip}) -> Int needs {Skip}\n\
                     take_pair p = {\n  let (a, b) = p\n  a () + b ()\n}\n";
    // A tuple held in a variable is not a literal: its element rows are
    // nested in the tuple type.
    assert_one(
        &row_errors(&format!(
            "{take_pair}\
             fun f : Unit -> Int needs {{Skip}}\n\
             f () = {{\n  let pair = (pure_fn, pure_fn)\n  take_pair pair\n}}"
        )),
        AT_DEPTH,
    );
    // Inside another function's parameter type.
    assert_one(
        &row_errors(
            "fun apply_pure : ((Unit -> Int) -> Int) -> Int\napply_pure k = k pure_fn\n\
             fun wants_eff : (Unit -> Int needs {Skip}) -> Int\nwants_eff g = g () with { skip () = resume 1 }\n\
             fun f : Unit -> Int\nf () = apply_pure wants_eff",
        ),
        AT_DEPTH,
    );
    // Inside a named record's type argument.
    assert_one(
        &row_errors(
            "record Holder a { item : a }\n\
             fun unwrap : Holder (Unit -> Int) -> Int\nunwrap h = h.item ()\n\
             fun mk : Unit -> Holder (Unit -> Int needs {Skip})\nmk () = Holder { item: eff }\n\
             fun f : Unit -> Int\nf () = unwrap (mk ())",
        ),
        AT_DEPTH,
    );
}

#[test]
fn branches_holding_literals_with_different_nested_rows_are_errors() {
    // `if`/`case` branches are joined before any expected type is consulted,
    // and the join only widens rows of function-typed branches. Tuples are
    // joined by plain unification, so their element rows must agree.
    assert_one(
        &row_errors(
            "fun f : Bool -> (Unit -> Int needs {Skip}, Int)
\
             f b = if b then (eff, 1) else (pure_fn, 2)",
        ),
        AT_DEPTH,
    );
    // A constructor applied to a function is not a literal position either:
    // `Just pure_fn` is a `Maybe (Unit -> Int)`.
    assert_one(
        &row_errors(
            "fun take : Maybe (Unit -> Int needs {Skip}) -> Int needs {Skip}
\
             take m = case m {\n  Just g -> g ()\n  Nothing -> 0\n}\n\
             fun f : Unit -> Int needs {Skip}\nf () = take (Just pure_fn)",
        ),
        AT_DEPTH,
    );
}

#[test]
fn local_function_clauses_share_one_effect_row() {
    // The row of a local multi-clause function is the union of what its
    // clauses perform, not the row of its first clause.
    let go = "  let go 0 = 0\n  let go m = m + skip! ()\n  go n\n}";
    let src = format!("fun f : Int -> Int needs {{Skip}}\nf n = {{\n{go}");
    assert_none(&row_errors(&src));
    assert!(unused_needs_warnings(&src).is_empty());
    // A recursive one, and the effectful clause first.
    assert_none(&row_errors(
        "fun f : Int -> Int needs {Skip}\nf n = {\n  \
         let go 0 acc = acc\n  let go m acc = go (m - 1) (acc + skip! ())\n  go n 0\n}",
    ));
    assert_none(&row_errors(
        "fun f : Int -> Int needs {Skip}\nf n = {\n  \
         let go 1 = skip! ()\n  let go _ = 0\n  go n\n}",
    ));
    // The enclosing function has to declare it.
    let errors = type_errors(&format!("fun f : Int -> Int\nf n = {{\n{go}"));
    assert!(
        errors
            .iter()
            .any(|e| e.contains("uses effects {Skip} but has no 'needs' declaration")),
        "{errors:#?}"
    );
    // A pure local function stays pure.
    assert_none(&row_errors(
        "fun f : Int -> Int\nf n = {\n  let go 0 = 0\n  let go m = m + 1\n  go n\n}",
    ));
}

// --- Legal subsumption: accepted ---

#[test]
fn pure_function_passed_where_effectful_callback_is_expected_is_accepted() {
    assert_none(&row_errors(
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
fn tuple_and_list_literal_widening_is_accepted() {
    // `tuple_widens_shared_row_var_at_expected_type` from tests.rs.
    assert_none(&row_errors(
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
fn pure_function_at_each_coercion_position_is_accepted() {
    assert_none(&row_errors(
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
    // `fun a b -> ..` and a declared `A -> B -> C needs {E}` both carry the
    // row on the last arrow.
    assert_none(&row_errors(
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
    // The effects still have to be declared on the expected type.
    assert_one(
        &row_errors(
            "record Ops { combine : Int -> Int -> Int }\n\
             fun f : Unit -> Ops\nf () = Ops { combine: fun a b -> a + b + skip! () }",
        ),
        WRONG_DIRECTION,
    );
}

#[test]
fn effect_on_a_different_arrow_than_expected_is_an_error() {
    // The lambda performs `Skip` when given its first argument; the expected
    // type performs it when given the second. Rows are compared per arrow.
    let early = "fun a -> {\n  let n = skip! ()\n  fun b -> a + b + n\n}";
    let errors = row_errors(&format!(
        "fun mk : Unit -> (Int -> Int -> Int needs {{Skip}})\nmk () = {early}"
    ));
    assert_one(&errors, WRONG_DIRECTION);
    assert!(errors[0].contains("a function that uses {Skip}"));
    assert_one(
        &row_errors(&format!(
            "record Ops {{ combine : Int -> Int -> Int needs {{Skip}} }}\n\
             fun f : Unit -> Ops\nf () = Ops {{ combine: {early} }}"
        )),
        WRONG_DIRECTION,
    );
    // Against a type that puts the effect on the first arrow it is accepted.
    assert_none(&row_errors(&format!(
        "fun mk : Unit -> (Int -> (Int -> Int) needs {{Skip}})\nmk () = {early}"
    )));
    // The explicitly nested lambda performs it on the last arrow.
    assert_none(&row_errors(
        "fun mk : Unit -> (Int -> Int -> Int needs {Skip})\n\
         mk () = fun a -> fun b -> a + b + skip! ()",
    ));
}

#[test]
fn equal_rows_and_row_variables_are_accepted() {
    assert_none(&row_errors(
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
fn error_is_reported_for_imported_modules() {
    let lib = r#"
module Lib

effect Skip { fun skip : Unit -> Int }

fun eff : Unit -> Int needs {Skip}
eff () = skip! ()

pub fun get : Bool -> (Unit -> Int)
get b = if b then eff else (fun () -> 1)
"#;
    let main = "module Main\nimport Lib\n\nmain () = dbg ((Lib.get False) ())\n";
    let error = match super::tests::check_with_project_files(&[("src/Lib.saga", lib)], main) {
        Ok(_) => panic!("project should not typecheck"),
        Err(e) => e,
    };
    assert!(error.message.contains(WRONG_DIRECTION), "{}", error.message);
}

#[test]
fn call_argument_reports_the_rule_error_once() {
    // Direct call arguments used to have their own "pure callback" error;
    // the rule's error replaced it.
    let errors = row_errors(
        "fun run_pure : (Unit -> Int) -> Int\nrun_pure f = f ()\n\
         fun f : Unit -> Int needs {Skip}\nf () = run_pure eff\n",
    );
    assert_one(&errors, WRONG_DIRECTION);
    assert!(errors[0].contains("a function that uses {Skip}"));
}
