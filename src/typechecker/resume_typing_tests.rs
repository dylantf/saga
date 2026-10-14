//! Sound typing of `resume` (docs/planning/resume-typing.md): what resuming
//! performs, the unifier holes found on the way (U1-U3, H1-H3), and the
//! programs that must keep typechecking.

use super::*;
use crate::lexer::Lexer;
use crate::parser::Parser;

/// Declarations shared by the programs below.
const DECLS: &str = r#"
effect Stop { fun stop : Int -> Int }
effect Ask { fun ask : Unit -> Int }
effect Log { fun log : String -> Unit }
effect Choose { fun choose : Unit -> Bool }
effect State {
  fun get : Unit -> Int
  fun put : Int -> Unit
}

fun apply_pure : (Int -> Int) -> Int
apply_pure g = g 20

fun thunk_pure : (Unit -> Int) -> Int
thunk_pure g = g ()

fun eq : a -> a -> a
eq x _ = x

fun wrap : (Unit -> Int needs {..e}) -> (Unit -> Int needs {Stop, ..e})
wrap g = fun () -> g () + stop! 1

fun ask_stop : Unit -> Int needs {Ask, Stop}
ask_stop () = ask! () + stop! 1

fun ask_only : Unit -> Int needs {Ask}
ask_only () = ask! () + 1

fun counter : Unit -> Int needs {Stop, State}
counter () = {
  let s = get! ()
  let t = stop! s
  put! (s + t)
  get! ()
}

fun pick_stop : Unit -> Int needs {Stop, Choose}
pick_stop () = {
  let b = choose! ()
  stop! (if b then 1 else 2)
}
"#;

/// Type-check `DECLS + src` on top of the prelude. The first error's
/// message on failure.
fn check(src: &str) -> Result<Checker, String> {
    let src = format!("{DECLS}\n{src}");
    let tokens = Lexer::new(&src).lex().expect("lex error");
    let mut program = Parser::new(tokens).parse_program().expect("parse error");
    crate::desugar::desugar_program(&mut program);
    let mut checker = Checker::with_prelude(None).expect("prelude");
    let result = checker.check_program(&mut program);
    if let Some(error) = result.errors().into_iter().next() {
        return Err(error.message.clone());
    }
    Ok(checker)
}

#[track_caller]
fn accepted(src: &str) -> Checker {
    match check(src) {
        Ok(checker) => checker,
        Err(message) => panic!("expected the program to typecheck: {message}"),
    }
}

/// The program is rejected with an error mentioning every one of `needles`.
#[track_caller]
fn rejected(src: &str, needles: &[&str]) -> String {
    match check(src) {
        Ok(_) => panic!("expected the program to be rejected"),
        Err(message) => {
            for needle in needles {
                assert!(
                    message.contains(needle),
                    "expected the error to mention `{needle}`: {message}"
                );
            }
            message
        }
    }
}

/// The (resolved) type of a top-level name.
fn type_of(checker: &Checker, name: &str) -> Type {
    let scheme = checker
        .env
        .get(name)
        .unwrap_or_else(|| panic!("`{name}` not in the environment"));
    checker.sub.apply(&scheme.ty)
}

/// The rows on the arrows of `ty`, following the result spine.
fn spine_rows(ty: &Type) -> Vec<EffectRow> {
    let mut rows = Vec::new();
    let mut current = ty;
    while let Type::Fun(_, ret, row) = current {
        rows.push(row.clone());
        current = ret;
    }
    rows
}

fn names(row: &EffectRow) -> Vec<String> {
    let mut names: Vec<String> = row
        .effects
        .iter()
        .map(|e| e.name.rsplit('.').next().unwrap_or(&e.name).to_string())
        .collect();
    names.sort();
    names
}

// --- Unifier holes (step 1) ---

/// U1: an open row with a named effect unified with the empty row lost the
/// effect (`{Stop | e} ~ {}` bound `e := {}`). It hit `wrap`'s own
/// declaration: the row of the returned function was also put on `wrap`'s
/// first arrow and unified with the declared (empty) one there, which
/// closed `..e`.
#[test]
fn u1_declared_row_of_a_returned_function_keeps_its_tail() {
    let checker = accepted("");
    let ty = type_of(&checker, "wrap");
    let Type::Fun(param, ret, own) = &ty else {
        panic!("wrap is not a function: {ty:?}");
    };
    assert!(own.is_empty(), "applying `wrap` performs nothing: {ty:?}");
    let param_rows = spine_rows(param);
    let ret_rows = spine_rows(ret);
    assert_eq!(names(&ret_rows[0]), vec!["Stop".to_string()], "{ty:?}");
    assert_eq!(ret_rows[0].tails.len(), 1, "`..e` kept: {ty:?}");
    assert_eq!(param_rows[0].tails, ret_rows[0].tails, "{ty:?}");
}

/// The same placement let a function perform an effect before returning a
/// function while its first arrow stayed pure.
#[test]
fn u1_effect_before_returning_a_function_is_on_the_first_arrow() {
    rejected(
        "fun early : Int -> Int -> Int needs {Log}
early x = {
  log! \"early\"
  fun y -> x + y
}
",
        &["Log"],
    );
}

/// Passing the result of `wrap` where a pure function is expected.
#[test]
fn u1_open_row_with_an_effect_is_not_a_pure_function() {
    rejected("bad g = thunk_pure (wrap g)\n", &["Stop"]);
}

/// U2: two rows with the same single tail but different effects were
/// accepted as equal (`{Stop | r} ~ {| r}`), dropping Stop. Unannotated, the
/// row variable must take Stop on.
#[test]
fn u2_shared_tail_keeps_the_differing_effect() {
    let checker = accepted("bad f = (eq f (wrap f)) ()\n");
    let ty = type_of(&checker, "bad");
    let rows = spine_rows(&ty);
    assert!(
        names(&rows[0]).contains(&"Stop".to_string()),
        "calling `bad` performs Stop: {ty:?}"
    );
}

/// U2 at a declared row variable: the caller chooses `..e`, so the body may
/// not assume it contains Stop.
#[test]
#[ignore = "a declared row variable still takes on effects in equality unification (step 2)"]
fn u2_shared_rigid_tail_rejects_the_differing_effect() {
    rejected(
        "fun bad : (Unit -> Int needs {..e}) -> Int needs {..e}\nbad f = (eq f (wrap f)) ()\n",
        &["Stop"],
    );
}

/// U3: tails common to both rows must cancel before the rest is unified,
/// or `{..a, ..b} ~ {..b}` binds `b` to a row containing itself.
#[test]
fn u3_common_tails_cancel() {
    accepted(
        "fun two : (Unit -> Int needs {..a}) -> (Unit -> Int needs {..b}) -> Int needs {..a, ..b}
two f g = f () + g ()

both f g = eq (fun () -> two f g) g
",
    );
}

// --- H1: a declared open row names every effect the body performs (step 7) ---

#[test]
#[ignore = "H1: a declared open row accepts effects it does not name"]
fn h1_declared_open_row_rejects_an_unnamed_effect() {
    rejected(
        "fun h : (Unit -> Int needs {..e}) -> Int needs {..e}
h f = {
  log! \"x\"
  f ()
}
",
        &["Log"],
    );
}

// --- H2: the resume context is monomorphic (step 3) ---

/// `k` must not be generalised over the handler's answer type: here it
/// would be used at String while the handled computation is an Int.
#[test]
#[ignore = "H2: a let inside an arm generalises over the answer type"]
fn h2_resume_in_a_let_is_not_generalised_over_the_answer_type() {
    rejected(
        "handler bad_k for Ask {
  ask () = {
    let k = fun x -> resume x
    let s = k 1
    String.length s
  }
}

main () = dbg ((ask! () + 1) with bad_k)
",
        &[],
    );
}

// --- H3: handler values whose provenance is lost (step 6) ---

/// A handler whose arms decide the answer type, passed as a `Handler Ask`
/// value: the `with` inside `use_h` cannot know its answer type.
#[test]
#[ignore = "H3: a non-uniform handler passed as a Handler value"]
fn h3_non_uniform_handler_value_is_rejected() {
    rejected(
        "fun use_h : Handler Ask -> Int
use_h h = (ask! () + 1) with h

make_bad () = handler for Ask { ask () = \"oops\" }

main () = dbg (use_h (make_bad ()))
",
        &[],
    );
}

/// `if` over two handlers with different return clauses: which one is
/// installed is decided at run time, so neither's answer type can be used.
#[test]
#[ignore = "H3: extract_handler_info takes the first branch of an if"]
fn h3_handlers_chosen_by_if_must_be_uniform() {
    rejected(
        "effect Oops { fun oops : String -> a }

handler to_result for Oops {
  oops e = Err e
  return v = Ok v
}

handler to_list for Oops {
  oops _ = []
  return v = [v]
}

pick c = {
  let h = if c then to_result else to_list
  (oops! \"x\") with h
}
",
        &[],
    );
}
