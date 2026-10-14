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

// --- Directional row subsumption at coercion positions (step 2) ---

/// A pure function returned where a function over the caller's `..e` is
/// declared: `{} ⊆ {..e}` holds without choosing `e`.
#[test]
fn pure_lambda_returned_at_a_declared_row_variable_is_accepted() {
    accepted(
        "fun mk : Unit -> (Unit -> Int needs {..e})
mk () = fun () -> 1
",
    );
}

#[test]
fn effectful_lambda_returned_at_a_declared_row_variable_is_rejected() {
    rejected(
        "fun mk : Unit -> (Unit -> Int needs {..e})
mk () = fun () -> {
  log! \"x\"
  1
}
",
        &["effect row mismatch", "Log"],
    );
}

/// Two row variables the caller chooses independently: a function over one
/// is not a function over the other.
#[test]
fn function_over_one_declared_row_is_not_one_over_another() {
    rejected(
        "fun mix : (Unit -> Int needs {..a}) -> (Unit -> Int needs {..b})
mix f = f
",
        &["..a"],
    );
}

/// A declared row variable is never chosen to make room: here `..e` would
/// have to contain Log.
#[test]
fn declared_row_variable_does_not_absorb_an_effect() {
    rejected(
        "fun run : (Unit -> Int needs {..e}) -> Int needs {..e}
run f = f ()

fun with_log : (Unit -> Int needs {..e}) -> (Unit -> Int needs {..e})
with_log f = fun () -> {
  log! \"x\"
  f ()
}
",
        &["Log"],
    );
}

// --- H1: a declared open row names every effect the body performs (step 7) ---

#[test]
fn h1_declared_open_row_rejects_an_unnamed_effect() {
    rejected(
        "fun h : (Unit -> Int needs {..e}) -> Int needs {..e}
h f = {
  log! \"x\"
  f ()
}
",
        &["uses the effect `Log`", "does not name"],
    );
}

// --- H2: the resume context is monomorphic (step 3) ---

/// `k` must not be generalised over the handler's answer type: here it
/// would be used at String while the handled computation is an Int.
#[test]
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
        &["expected String, got Int"],
    );
}

// --- H3: handler values whose provenance is lost (step 6) ---

/// A handler whose arms decide the answer type, passed as a `Handler Ask`
/// value: the `with` inside `use_h` cannot know its answer type.
#[test]
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
/// installed is decided at run time, so both must give the `with` the same
/// type (only the first was looked at).
#[test]
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
        &["the handlers this `with` may install (chosen by an `if`) give it different types"],
    );
}

// --- What resume performs: inline `with` (step 4) ---

/// The unannotated generic state runner: the state function performs what
/// the computation does beyond State and Fail, and nothing is pinned by the
/// pure `fail` arm or `return` clause.
#[test]
fn unannotated_state_runner_keeps_the_computation_open() {
    let checker = accepted(
        "effect Fail { fun fail : String -> a }

rsf init f = {
  let g = f () with {
    get () = fun s -> (resume s) s
    put n = fun _ -> (resume ()) n
    fail msg = fun _ -> Err msg
    return v = fun _ -> Ok v
  }
  g init
}
",
    );
    let ty = type_of(&checker, "rsf");
    let rows = spine_rows(&ty);
    let Type::Fun(_, rest, _) = &ty else {
        panic!("{ty:?}")
    };
    let Type::Fun(f_ty, _, _) = &**rest else {
        panic!("{ty:?}")
    };
    let f_row = &spine_rows(f_ty)[0];
    assert_eq!(names(f_row), vec!["Fail", "State"], "{ty:?}");
    assert_eq!(f_row.tails.len(), 1, "f stays open: {ty:?}");
    assert_eq!(rows[1].tails, f_row.tails, "rsf performs f's rest: {ty:?}");
}

/// A resuming function given to a function that takes a pure one: fine
/// when the rest of the computation is pure, not when it performs Stop.
#[test]
fn resuming_function_passed_where_a_pure_one_is_expected() {
    accepted("ok () = ask_only () with { ask () = apply_pure (fun x -> resume x) }\n");
    let message = rejected(
        "bad () = ask_stop () with { ask () = apply_pure (fun x -> resume x) }\n",
        &["effect row mismatch", "Stop"],
    );
    assert!(
        message.contains("resum"),
        "the error says the function resumes: {message}"
    );
}

/// A multishot handler resuming inside a callback: the callback performs
/// what the rest of the computation does.
#[test]
fn resuming_callback_carries_the_rest_of_the_computation() {
    let checker = accepted(
        "pick_all () = pick_stop () with {
  choose () = List.flat_map (fun b -> resume b) [True, False]
  return v = [v]
}
",
    );
    let ty = type_of(&checker, "pick_all");
    assert_eq!(names(&spine_rows(&ty)[0]), vec!["Stop"], "{ty:?}");
    let result = checker.to_result();
    let bool_ty = Type::bool();
    let list_int = Type::Con("Std.List.List".into(), vec![Type::int()]);
    let callback = result.expr_types.values().find(|t| {
        matches!(t, Type::Fun(param, ret, _) if **param == bool_ty && **ret == list_int)
    });
    let Some(Type::Fun(_, _, row)) = callback else {
        panic!("no `Bool -> List Int` lambda in the expression types");
    };
    assert_eq!(names(row), vec!["Stop"], "the callback resumes: {row:?}");
}

/// Resumptions kept in a list and called later.
#[test]
fn resumptions_stored_in_a_list() {
    let checker = accepted(
        "r () = ask_stop () with {
  ask () = {
    let ks = [fun x -> resume x]
    List.foldl (fun acc k -> acc + k 1) 10 ks
  }
}
",
    );
    let ty = type_of(&checker, "r");
    assert_eq!(names(&spine_rows(&ty)[0]), vec!["Stop"], "{ty:?}");
}

/// A resuming function in a field declared pure.
#[test]
fn resuming_function_in_a_pure_field() {
    let decls = "record Box { run : Int -> Int }
type Step = Done(Int) | More(Unit -> Step)
";
    accepted(&format!(
        "{decls}
ok () = ask_only () with {{
  ask () = {{
    let b = Box {{ run: fun x -> resume x }}
    b.run 1
  }}
}}
"
    ));
    rejected(
        &format!(
            "{decls}
bad () = ask_stop () with {{
  ask () = {{
    let b = Box {{ run: fun x -> resume x }}
    b.run 1
  }}
}}
"
        ),
        &["Stop"],
    );
    rejected(
        &format!(
            "{decls}
bad () = ask_stop () with {{
  ask () = More(fun () -> resume 1)
  return v = Done(v)
}}
"
        ),
        &["Stop"],
    );
}

/// `resume` bound by a `let` in an arm is the same function.
#[test]
fn resume_bound_by_a_let() {
    accepted(
        "ok () = ask_only () with {
  ask () = {
    let k = fun x -> resume x
    apply_pure k
  }
}
",
    );
    rejected(
        "bad () = ask_stop () with {
  ask () = {
    let k = fun x -> resume x
    apply_pure k
  }
}
",
        &["Stop"],
    );
}

/// What the arms and the `return` clause perform is part of what resuming
/// performs: the state function logs.
#[test]
fn arm_and_return_effects_are_performed_by_resuming() {
    let make = "fun counter_state : Unit -> Int needs {State}
counter_state () = {
  put! (get! () + 1)
  get! ()
}

make8 () = counter_state () with {
  get () = {
    log! \"g\"
    fun s -> (resume s) s
  }
  put n = fun _ -> (resume ()) n
  return v = {
    log! \"r\"
    fun _ -> v
  }
}
";
    let checker = accepted(&format!(
        "{make}
fun ok8 : Unit -> Int
ok8 () = {{
  let f = make8 ()
  f 1
}} with {{ log _ = resume () }}
"
    ));
    let ty = type_of(&checker, "make8");
    let rows = spine_rows(&ty);
    assert_eq!(names(&rows[1]), vec!["Log"], "the state function logs: {ty:?}");
    rejected(
        &format!(
            "{make}
fun bad8 : Unit -> Int
bad8 () = {{
  let f = make8 () with {{ log _ = resume () }}
  f 1
}}
"
        ),
        &["Log"],
    );
}

/// An inner state-passing handler whose arm function performs the outer
/// State: the function carries State and the inner computation's Stop.
#[test]
fn nested_handlers_of_the_same_effect() {
    let inner = "inner () = counter () with {
  get () = fun s -> {
    let o = get! ()
    (resume (s + o)) s
  }
  put n = fun _ -> (resume ()) n
  return v = fun _ -> v
}
";
    let checker = accepted(inner);
    let ty = type_of(&checker, "inner");
    let rows = spine_rows(&ty);
    assert_eq!(names(&rows[1]), vec!["State", "Stop"], "{ty:?}");
    rejected(
        &format!(
            "{inner}
fun bad9 : Unit -> (Int -> Int)
bad9 () = inner () with {{
  get () = resume 1
  put _ = resume ()
  stop n = resume n
}}
"
        ),
        &["effect row mismatch"],
    );
}

/// Resuming over an open-row trait method at a where-bound type: the state
/// function performs the impl's effects, `..a`.
#[test]
fn resuming_over_an_open_row_trait_method() {
    accepted(
        "trait Src a { fun next : a -> Int needs {..e} }

fun drive : a -> Int -> Int needs {..a} where {a: Src}
drive x s0 = {
  let g = (next x + ask! ()) with {
    ask () = fun s -> (resume s) s
    return v = fun _ -> v
  }
  g s0
}
",
    );
}

/// A pure arm value and `return` clause next to a resuming arm, over a
/// computation with a declared open row: nothing is pinned.
#[test]
fn pure_arm_values_do_not_pin_the_resumed_row() {
    accepted(
        "effect Fail { fun fail : String -> a }

fun run : (Unit -> Int needs {State, Fail, ..e}) -> Int needs {..e}
run f = {
  let g = f () with {
    fail _ = fun _ -> 0
    get () = fun s -> (resume s) s
    put n = fun _ -> (resume ()) n
    return v = fun _ -> v
  }
  g 0
}
",
    );
}

/// The state function itself, passed on where a pure function is expected.
#[test]
fn value_of_a_resuming_with_is_not_a_pure_function() {
    rejected(
        "fun leak : Unit -> Int needs {Stop}
leak () = apply_pure (counter () with {
  get () = fun s -> (resume s) s
  put n = fun _ -> (resume ()) n
  return v = fun _ -> v
})
",
        &[
            "effect row mismatch",
            "{Stop}",
            "the value of a `with` whose handler resumes inside it",
        ],
    );
}

// --- Named handlers (step 5) ---

const PASSING: &str = "handler passing for State {
  get () = fun s -> (resume s) s
  put n = fun _ -> (resume ()) n
  return v = fun _ -> v
}
";

/// The state function a named state-passing handler returns performs what
/// the computation it is installed around leaves unhandled.
#[test]
fn named_state_passing_handler_carries_the_computation_row() {
    let checker = accepted(&format!(
        "{PASSING}
run_it () = counter () with passing

fun quiet : Unit -> Int needs {{State}}
quiet () = get! () + 1

fun pure_state : Int -> Int
pure_state n = apply_pure (quiet () with passing)
"
    ));
    let ty = type_of(&checker, "run_it");
    assert_eq!(names(&spine_rows(&ty)[1]), vec!["Stop"], "{ty:?}");
    rejected(
        &format!(
            "{PASSING}
fun leak : Unit -> Int needs {{Stop}}
leak () = apply_pure (counter () with passing)
"
        ),
        &[
            "effect row mismatch",
            "{Stop}",
            "the value of a `with` whose handler resumes inside it",
        ],
    );
}

/// A named handler does not know the computation it is installed around,
/// so its arms may not pass a resuming function where a pure one is
/// expected.
#[test]
fn named_handler_resuming_in_a_pure_function_is_rejected() {
    rejected(
        "handler bad for Ask {
  ask () = apply_pure (fun x -> resume x)
}
",
        &["handler 'bad' resumes inside a function", "no effects"],
    );
    accepted(
        "fun apply_open : (Int -> Int needs {..e}) -> Int needs {..e}
apply_open g = g 20

handler fine for Ask {
  ask () = apply_open (fun x -> resume x)
}

fun use_fine : Unit -> Int needs {Stop}
use_fine () = ask_stop () with fine
",
    );
}

/// A pure arm value, a pure `return` clause and a resuming function over
/// the handled computation: nothing pins what resuming performs.
#[test]
fn named_handler_pure_arm_values_do_not_pin_the_resumed_row() {
    accepted(
        "effect Fail { fun fail : String -> a }

handler runner for State, Fail {
  fail _ = fun _ -> 0
  get () = fun s -> (resume s) s
  put n = fun _ -> (resume ()) n
  return v = fun _ -> v
}

fun go : Unit -> Int needs {Stop}
go () = (counter () with runner) 0
",
    );
}

// --- Handler values (step 6) ---

/// A uniform handler (its answer type is the computation's) can be passed
/// as a `Handler` value; one that needs effects only a naming `with`
/// provides cannot; a non-uniform one can still be bound by a `let`.
#[test]
fn handler_values_must_be_uniform() {
    let use_h = "fun use_h : Handler Ask -> Int needs {Stop}
use_h h = ask_stop () with h
";
    accepted(&format!(
        "{use_h}
handler plain for Ask {{ ask () = resume 1 }}

fun go : Unit -> Int needs {{Stop}}
go () = use_h plain

fun go_expr : Unit -> Int needs {{Stop}}
go_expr () = use_h (handler for Ask {{ ask () = resume 2 }})
"
    ));
    rejected(
        &format!(
            "{use_h}
handler noisy for Ask needs {{Log}} {{
  ask () = {{
    log! \"asked\"
    resume 1
  }}
}}

fun go : Unit -> Int needs {{Stop, Log}}
go () = use_h noisy
"
        ),
        &["handler `noisy` cannot be used as a `Handler` value", "{Log}"],
    );
    rejected(
        &format!(
            "{use_h}
handler counting for Ask {{
  ask () = (resume 1) + 1
}}

fun go : Unit -> Int needs {{Stop}}
go () = use_h counting
"
        ),
        &["handler `counting` cannot be used as a `Handler` value"],
    );
    // Two handlers chosen by an `if` that agree on the `with`'s type.
    accepted(
        "handler loud for Log {
  log msg = \"L:\" <> msg <> \"/\" <> resume ()
  return _ = \"\"
}

handler quiet for Log {
  log _ = resume ()
  return _ = \"Q\"
}

fun choose : Bool -> String
choose c = {
  let h = if c then loud else quiet
  log! \"x\" with h
}
",
    );
    accepted(
        "effect Oops { fun oops : String -> a }

handler to_result for Oops {
  oops e = Err e
  return v = Ok v
}

fun bound : Unit -> Result Int String
bound () = {
  let h = to_result
  (oops! \"x\") with h
}
",
    );
}
