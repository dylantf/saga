//! Tests for family-only effect identity ("Family-only effect identity" in
//! `docs/planning/sound-function-representation.md`).
//!
//! An effect is identified by its family name, whatever its type arguments,
//! so an operation reaches the nearest handler for its family. Two rules keep
//! that sound:
//!
//! 1. A row holds at most one application of a family. Where two would meet,
//!    their arguments are unified; a mismatch is a type error.
//! 2. An operation of `Oops String` can never run under a handler typed for
//!    `Oops Int`. In particular a handler may not be installed around an open
//!    row chosen by the caller unless the signature names the family next to
//!    that row.

use super::unify::FAMILY_CONFLICT_MARKER;
use super::*;
use crate::lexer::Lexer;
use crate::parser::Parser;

/// Declarations shared by the programs below.
const PRELUDE: &str = r#"
effect Oops e {
  fun oops : e -> Int
}

effect Plain {
  fun plain : Unit -> Int
}

fun oops_string : Unit -> Int needs {Oops String}
oops_string () = oops! "s"

fun oops_int : Unit -> Int needs {Oops Int}
oops_int () = oops! 1

fun pure_int : Unit -> Int
pure_int () = 1
"#;

pub(super) fn diagnostics(src: &str) -> Vec<Diagnostic> {
    let src = format!("{PRELUDE}\n{src}");
    let tokens = Lexer::new(&src).lex().expect("lex error");
    let mut program = Parser::new(tokens).parse_program().expect("parse error");
    crate::desugar::desugar_program(&mut program);
    let mut checker = Checker::with_prelude(None).expect("prelude");
    let result = checker.check_program(&mut program);
    result.errors().into_iter().cloned().collect()
}

/// The program type-checks.
pub(super) fn accepted(src: &str) {
    let errors = diagnostics(src);
    assert!(
        errors.is_empty(),
        "expected no type errors, got: {:#?}",
        errors.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
}

/// The program is rejected with an error whose message contains every
/// needle, and that error has a source span. Returns the message.
pub(super) fn rejected(src: &str, needles: &[&str]) -> String {
    let errors = diagnostics(src);
    let found = errors
        .iter()
        .find(|d| needles.iter().all(|needle| d.message.contains(needle)));
    match found {
        Some(d) => {
            assert!(d.span.is_some(), "error has no span: {}", d.message);
            d.message.clone()
        }
        None => panic!(
            "expected an error containing {:?}, got: {:#?}",
            needles,
            errors.iter().map(|d| &d.message).collect::<Vec<_>>()
        ),
    }
}

/// Rejected as two applications of `Oops` in one row.
pub(super) fn rejected_as_conflict(src: &str) -> String {
    let message = rejected(src, &[FAMILY_CONFLICT_MARKER, "`Oops`", "neweffect"]);
    assert!(
        message.contains("Oops String") && message.contains("Oops Int"),
        "both applications should be shown: {message}"
    );
    message
}

// --- Rule 1: one application per family per row ---

#[test]
fn merging_two_applications_while_inferring_is_rejected() {
    rejected_as_conflict(
        "
fun both : Unit -> Int needs {Oops String}
both () = oops_string () + oops_int ()
",
    );
}

#[test]
fn merging_two_applications_in_an_unannotated_function_is_rejected() {
    rejected_as_conflict(
        "
both () = oops_string () + oops_int ()
",
    );
}

#[test]
fn merging_two_applications_in_a_lambda_is_rejected() {
    rejected_as_conflict(
        "
fun make : Unit -> (Unit -> Int needs {Oops String})
make () = fun () -> oops_string () + oops_int ()
",
    );
}

#[test]
fn merging_the_same_application_twice_is_one_entry() {
    accepted(
        "
fun twice : Unit -> Int needs {Oops String}
twice () = oops_string () + oops_string ()
",
    );
}

#[test]
fn an_omitted_argument_is_unified_with_the_other_use() {
    // `needs {Oops}` leaves the argument to inference: both uses are the one
    // `Oops` of the row, here at String.
    accepted(
        "
fun first : Unit -> Int needs {Oops}
first () = oops! \"s\"

fun both : Unit -> Int needs {Oops String}
both () = first () + oops_string ()
",
    );
}

#[test]
fn joining_branch_rows_with_two_applications_is_rejected() {
    rejected_as_conflict(
        "
fun pick : Bool -> (Unit -> Int needs {Oops String})
pick c = if c then oops_string else oops_int
",
    );
}

#[test]
fn joining_list_element_rows_with_two_applications_is_rejected() {
    rejected_as_conflict(
        "
all () = [oops_string, oops_int]
",
    );
}

#[test]
fn joining_branch_rows_with_one_application_is_accepted() {
    accepted(
        "
fun pick : Bool -> (Unit -> Int needs {Oops String})
pick c = if c then oops_string else pure_int
",
    );
}

#[test]
fn declared_function_row_with_two_applications_is_rejected() {
    rejected_as_conflict(
        "
fun both : Unit -> Int needs {Oops String, Oops Int}
both () = 1
",
    );
}

#[test]
fn declared_row_with_possibly_equal_applications_is_rejected() {
    rejected(
        "
fun both : a -> b -> Int needs {Oops a, Oops b}
both _ _ = 1
",
        &[FAMILY_CONFLICT_MARKER, "`Oops`", "neweffect"],
    );
}

#[test]
fn declared_row_repeating_one_application_is_accepted() {
    accepted(
        "
fun same : Unit -> Int needs {Oops String, Oops String}
same () = oops! \"s\"
",
    );
}

#[test]
fn declared_callback_row_with_two_applications_is_rejected() {
    rejected_as_conflict(
        "
fun run : (Unit -> Int needs {Oops String, Oops Int}) -> Int
run f = 1
",
    );
}

#[test]
fn declared_handler_needs_with_two_applications_is_rejected() {
    rejected_as_conflict(
        "
handler relay for Plain needs {Oops String, Oops Int} {
  plain () = resume 1
}
",
    );
}

#[test]
fn declared_impl_needs_with_two_applications_is_rejected() {
    rejected_as_conflict(
        "
trait Risky a {
  fun risk : a -> Int needs {..e}
}

impl Risky for Int needs {Oops String, Oops Int} {
  risk x = x
}
",
    );
}

#[test]
fn declared_trait_method_row_with_two_applications_is_rejected() {
    rejected_as_conflict(
        "
trait Risky a {
  fun risk : a -> Int needs {Oops String, Oops Int}
}
",
    );
}

#[test]
fn declared_operation_row_with_two_applications_is_rejected() {
    rejected_as_conflict(
        "
effect Relay {
  fun relay : Unit -> Int needs {Oops String, Oops Int}
}
",
    );
}

#[test]
fn body_application_must_be_the_declared_one() {
    rejected_as_conflict(
        "
fun wrong : Unit -> Int needs {Oops Int}
wrong () = oops_string ()
",
    );
}

#[test]
fn body_application_must_be_the_declared_one_under_an_open_row() {
    // The declared row is open, but its one `Oops` is still `Oops Int`: a
    // second application does not slip through the tail.
    rejected_as_conflict(
        "
fun wrong : (Unit -> Int needs {..r}) -> Int needs {Oops Int, ..r}
wrong f = oops_string () + f ()
",
    );
}

#[test]
fn subtracting_a_handler_for_another_application_is_rejected() {
    // The handler is found by family, so it would receive the String
    // operation; it is not "skipped" as a handler for a different effect.
    rejected(
        "
handler ints for Oops Int {
  oops n = resume (n + 1)
}

run () = oops_string () with ints
",
        &[
            "this handler handles `Oops Int`",
            "performs `Oops String`",
            "neweffect",
        ],
    );
}

#[test]
fn subtracting_a_handler_removes_the_one_application() {
    accepted(
        "
handler ints for Oops Int {
  oops n = resume (n + 1)
}

fun run : Unit -> Int
run () = (oops_int () + oops_int ()) with ints
",
    );
}

#[test]
fn a_generic_handler_declaration_serves_each_use_at_its_own_type() {
    accepted(
        "
handler zero for Oops a {
  oops _ = 0
}

fun run_string : Unit -> Int
run_string () = oops_string () with zero

fun run_int : Unit -> Int
run_int () = oops_int () with zero
",
    );
}

#[test]
fn inline_handler_arm_is_typed_at_the_one_application() {
    rejected(
        "
run () = oops_string () with { oops n = resume (n + 1) }
",
        &["String"],
    );
}

/// `r` appears with `Oops Int` in the second callback's row and alone in the
/// first, so the first argument can bind it before the second is seen.
const TWO_CALLBACKS: &str = "
fun two : (Unit -> Int needs {..r}) -> (Unit -> Int needs {Oops Int, ..r}) -> Int needs {Oops Int, ..r}
two f g = f () + g ()
";

#[test]
fn binding_a_tail_to_a_second_application_is_rejected() {
    // `{Oops Int, ..r}` with `r := {Oops String}`.
    rejected_as_conflict(&format!(
        "{TWO_CALLBACKS}
bad () = two oops_string oops_int
"
    ));
}

#[test]
fn binding_a_tail_to_the_same_application_collapses() {
    // `{Oops Int, ..r}` with `r := {Oops Int}` is `{Oops Int}`.
    accepted(&format!(
        "{TWO_CALLBACKS}
fun fine : Unit -> Int needs {{Oops Int}}
fine () = two oops_int oops_int
"
    ));
}

#[test]
fn binding_a_tail_after_its_row_was_seen_is_checked() {
    // `g`'s row is `{Oops Int, ..t}` with `t` the row of `k`, still unknown.
    // Passing `g` unifies `r` with `t`; only then is `t` bound, by the other
    // argument.
    rejected_as_conflict(
        "
fun two : (Unit -> Int needs {Oops Int, ..r}) -> (Unit -> Int needs {..r}) -> Int needs {Oops Int, ..r}
two f g = f () + g ()

bad k = {
  let g = fun () -> oops! 1 + k ()
  two g oops_string
}
",
    );
    accepted(
        "
fun two : (Unit -> Int needs {Oops Int, ..r}) -> (Unit -> Int needs {..r}) -> Int needs {Oops Int, ..r}
two f g = f () + g ()

fine k = {
  let g = fun () -> oops! 1 + k ()
  two g oops_int
}
",
    );
}

#[test]
fn a_tail_bound_before_its_row_is_seen_is_still_checked() {
    // Here `r` is bound by the first argument and the row that names `Oops`
    // next to it only arrives with the second.
    rejected_as_conflict(&format!(
        "{TWO_CALLBACKS}
bad () = two oops_string oops_int
"
    ));
}

#[test]
fn a_tail_bound_through_another_variable_is_still_checked() {
    // `r` is first unified with the lambda's own open row, and only that
    // row's variable is later bound to `Oops String`.
    rejected_as_conflict(&format!(
        "{TWO_CALLBACKS}
bad k = two (fun () -> k ()) oops_int + (k : Unit -> Int needs {{Oops String}}) ()
"
    ));
}

// --- Rule 2: an operation never meets a handler for another application ---

/// The well-formed catching function: the callback's row names the family
/// next to its open tail.
const CATCH_IT: &str = "
fun catch_it : (Unit -> Int needs {Oops e, ..r}) -> Int needs {..r}
catch_it f = f () with { oops _ = 0 }
";

#[test]
fn handler_around_a_callers_open_row_is_rejected() {
    // The adversarial shape. A caller may pass an `f` that performs
    // `Oops String`; its operation would reach this handler for `Oops Int`.
    let message = rejected(
        "
fun h : (Unit -> Int needs {..r}) -> Int needs {..r}
h f = f () with { oops n = resume (n + 1) }
",
        &["cannot handle `Oops` here", "`..r`"],
    );
    assert!(
        message.contains("needs {Oops e, ..r}"),
        "the fix should be spelled out: {message}"
    );
}

#[test]
fn handler_declaration_around_a_callers_open_row_is_rejected() {
    rejected(
        "
handler ints for Oops Int {
  oops n = resume (n + 1)
}

fun h : (Unit -> Int needs {..r}) -> Int needs {..r}
h f = f () with ints
",
        &["cannot handle `Oops` here", "`..r`"],
    );
}

#[test]
fn handler_around_a_callers_open_row_is_rejected_when_the_family_is_named_by_the_body() {
    // The row of the handled block names `Oops Int` (the block performs it
    // itself), but nothing obliges the caller to keep `r` consistent with it.
    rejected(
        "
fun h : (Unit -> Int needs {..r}) -> Int needs {..r}
h f = { oops! 1 + f () } with { oops n = resume (n + 1) }
",
        &["cannot handle `Oops` here", "`..r`"],
    );
}

#[test]
fn handler_around_a_callers_open_row_is_rejected_through_a_lambda() {
    rejected(
        "
fun h : (Unit -> Int needs {..r}) -> Int needs {..r}
h f = {
  let g = fun () -> f ()
  g () with { oops n = resume (n + 1) }
}
",
        &["cannot handle `Oops` here", "`..r`"],
    );
}

#[test]
fn callers_open_row_cannot_be_passed_to_a_handling_function_unnamed() {
    // `catch_it` handles `Oops e` around its callback. Wrapping `k` in a
    // lambda that performs `Oops String` makes that the handled application,
    // with `k`'s caller-chosen row inside it.
    rejected(
        &format!(
            "{CATCH_IT}
fun sneaky : (Unit -> Int needs {{..t}}) -> Int needs {{..t}}
sneaky k = catch_it (fun () -> oops! \"s\" + k ())
"
        ),
        &["`..t`", "Oops String", "needs {Oops String, ..t}"],
    );
}

#[test]
fn inferred_signature_cannot_hide_a_handled_family() {
    // Unannotated `sneaky`: its inferred type `(Unit -> Int needs {..t}) ->
    // Int needs {..t}` would let a caller choose `t := {Oops Int}`.
    rejected(
        &format!(
            "{CATCH_IT}
sneaky k = catch_it (fun () -> oops! \"s\" + k ())
"
        ),
        &["`sneaky`", "Oops String", "signature"],
    );
    // A local function is simply kept monomorphic in that row.
    rejected_as_conflict(&format!(
        "{CATCH_IT}
outer () = {{
  let sneaky k = catch_it (fun () -> oops! \"s\" + k ())
  sneaky oops_int
}}
"
    ));
    accepted(&format!(
        "{CATCH_IT}
fun outer : Unit -> Int
outer () = {{
  let sneaky k = catch_it (fun () -> oops! \"s\" + k ())
  sneaky pure_int
}}
"
    ));
}

#[test]
fn callers_open_row_cannot_be_closed_by_the_body() {
    // `only_ints` handles `Oops Int` around a callback it believes performs
    // nothing else. Passing `f` there claims `r` is `{Oops Int}`.
    rejected(
        "
fun only_ints : (Unit -> Int needs {Oops Int}) -> Int
only_ints f = f () with { oops n = resume (n + 1) }

fun h : (Unit -> Int needs {..r}) -> Int needs {..r}
h f = only_ints f
",
        &["`h` declares the open effect row `..r`", "Oops Int"],
    );
    rejected(
        "
fun only_pure : (Unit -> Int) -> Int
only_pure f = f ()

fun h : (Unit -> Int needs {..r}) -> Int needs {..r}
h f = only_pure (fun () -> f ()) with { oops n = resume (n + 1) }
",
        &["`h` declares the open effect row `..r`", "to be empty"],
    );
}

#[test]
fn handler_around_a_named_family_with_an_open_tail_is_accepted() {
    accepted(CATCH_IT);
}

#[test]
fn catching_function_is_usable_at_one_application() {
    accepted(&format!(
        "{CATCH_IT}
fun use_string : Unit -> Int
use_string () = catch_it oops_string
"
    ));
}

#[test]
fn catching_function_is_usable_at_another_application_in_another_scope() {
    // Each call instantiates the signature afresh: each has its own row.
    accepted(&format!(
        "{CATCH_IT}
fun use_string : Unit -> Int
use_string () = catch_it oops_string

fun use_int : Unit -> Int
use_int () = catch_it oops_int

fun use_both : Unit -> Int
use_both () = catch_it (fun () -> oops! \"s\") + catch_it (fun () -> oops! 1)
"
    ));
}

#[test]
fn catching_function_forwards_the_rest_of_the_row() {
    accepted(&format!(
        "{CATCH_IT}
fun use_it : Unit -> Int needs {{Plain}}
use_it () = catch_it (fun () -> oops! \"s\" + plain! ())
"
    ));
}

#[test]
fn caller_cannot_smuggle_a_second_application_through_the_tail() {
    // The callback's row is `{Oops String, ..q}` and `q` is then bound to
    // `{Oops Int}`: that is `r := {Oops Int}` under `{Oops String, ..r}`.
    rejected_as_conflict(&format!(
        "{CATCH_IT}
smuggle k = catch_it (fun () -> oops! \"s\" + k ()) + (k : Unit -> Int needs {{Oops Int}}) ()
"
    ));
}

#[test]
fn caller_cannot_smuggle_a_second_application_through_a_shared_tail() {
    // `r` is bound to `{Oops Int}` by the plain callback, so the handled
    // callback's row `{Oops e, ..r}` is `{Oops Int}`: it cannot be String.
    rejected(
        "
fun catch_second : (Unit -> Int needs {..r}) -> (Unit -> Int needs {Oops e, ..r}) -> Int needs {..r}
catch_second g f = g () + (f () with { oops _ = 0 })

bad () = catch_second oops_int oops_string
",
        &["type mismatch", "Oops Int", "Oops String"],
    );
    accepted(
        "
fun catch_second : (Unit -> Int needs {..r}) -> (Unit -> Int needs {Oops e, ..r}) -> Int needs {..r}
catch_second g f = g () + (f () with { oops _ = 0 })

fun fine : Unit -> Int needs {Oops Int}
fine () = catch_second oops_int oops_int
",
    );
}

#[test]
fn a_flexible_tail_is_refined_to_contain_the_handled_family() {
    // Unannotated: `f`'s row is an inference variable, so handling `Oops`
    // around it makes `f : Unit -> Int needs {Oops Int, ..}`.
    accepted(
        "
h f = f () with { oops n = resume (n + 1) }

fun fine : Unit -> Int
fine () = h oops_int + h pure_int
",
    );
    rejected(
        "
h f = f () with { oops n = resume (n + 1) }

bad () = h oops_string
",
        &["String"],
    );
}

#[test]
fn rethrowing_at_another_type_is_accepted() {
    // The handled application and the one the arm performs are in different
    // rows; `r` is held to each by the signature.
    accepted(
        "
fun convert : (Unit -> Int needs {Oops String, ..r}) -> Int needs {Oops Int, ..r}
convert f = f () with { oops s = oops! (String.length s) }
",
    );
}

#[test]
fn handler_value_for_another_application_is_rejected() {
    rejected(
        "
fun use_it : Handler (Oops Int) -> Int
use_it hh = oops_string () with hh
",
        &["this handler handles `Oops Int`", "performs `Oops String`"],
    );
    rejected(
        "
fun make : Unit -> Handler (Oops Int)
make () = handler for Oops Int {
  oops n = resume (n + 1)
}

run () = {
  let hh = make ()
  oops_string () with hh
}
",
        &["this handler handles `Oops Int`", "performs `Oops String`"],
    );
}

#[test]
fn handler_value_for_the_same_application_is_accepted() {
    accepted(
        "
fun use_it : Handler (Oops Int) -> Int
use_it hh = oops_int () with hh

fun generic : Handler (Oops e) -> (Unit -> Int needs {Oops e}) -> Int
generic hh f = f () with hh
",
    );
}

#[test]
fn handler_value_around_a_callers_open_row_is_rejected() {
    rejected(
        "
fun h : Handler (Oops Int) -> (Unit -> Int needs {..r}) -> Int needs {..r}
h hh f = f () with hh
",
        &["cannot handle `Oops` here", "`..r`"],
    );
}

#[test]
fn parameterised_effect_cannot_hide_in_a_declared_open_row() {
    // `..r` is the caller's row. If the body's own `Oops String` could pass
    // through it unnamed, a caller would see no `Oops` and could install an
    // `Oops Int` handler around the call.
    rejected(
        "
fun sneaky : Unit -> Int needs {..r}
sneaky () = oops! \"s\"
",
        &["uses the effect `Oops String`", "does not name"],
    );
    rejected(
        "
fun sneaky : (Unit -> Int needs {..r}) -> Int needs {..r}
sneaky f = oops! \"s\" + f ()
",
        &["uses the effect `Oops String`", "does not name"],
    );
    accepted(
        "
fun honest : Unit -> Int needs {Oops String, ..r}
honest () = oops! \"s\"

fun fine : Unit -> Int
fine () = honest () with { oops s = resume (String.length s) }
",
    );
    // An effect without type arguments still flows through an open row.
    accepted(
        "
fun loose : Unit -> Int needs {..r}
loose () = plain! ()
",
    );
}

#[test]
fn open_row_with_no_argument_to_bind_it_adds_nothing_to_the_caller() {
    // `r` is instantiated afresh by each call and nothing can bind it, so
    // the unannotated caller is not left with an open row of its own.
    let src = format!(
        "{PRELUDE}
fun honest : Unit -> Int needs {{Oops String, ..r}}
honest () = oops! \"s\"

caller () = honest () with {{ oops s = resume (String.length s) }}
"
    );
    let tokens = Lexer::new(&src).lex().expect("lex error");
    let mut program = Parser::new(tokens).parse_program().expect("parse error");
    crate::desugar::desugar_program(&mut program);
    let mut checker = Checker::with_prelude(None).expect("prelude");
    let result = checker.check_program(&mut program);
    assert!(!result.has_errors(), "{:?}", result.errors());
    let scheme = checker.env.get("caller").expect("caller");
    let ty = checker.sub.apply(&scheme.ty);
    assert_eq!(ty, Type::arrow(Type::unit(), Type::int()));
}

#[test]
fn handler_value_of_unknown_type_is_rejected() {
    // Nothing says what `hh` handles, so nothing could be checked against
    // the expression it is installed around.
    rejected(
        "
run hh f = f () with hh
",
        &["cannot tell which effects `hh` handles"],
    );
}

#[test]
fn declared_effect_argument_cannot_be_pinned_by_the_body() {
    // The signature promises a handler for `Oops e` at any `e`; the arm only
    // works for Int. Code checked before this body (an impl method) would
    // have used it at String.
    rejected(
        "
trait Go a {
  fun go : a -> Int
}

impl Go for Int {
  go _ = catch_num oops_string
}

fun catch_num : (Unit -> Int needs {Oops e, ..r}) -> Int needs {..r}
catch_num f = f () with { oops n = resume (n + 1) }
",
        &[
            "`catch_num` declares `Oops e` for any type `e`",
            "`e` is `Int`",
        ],
    );
}

#[test]
fn declared_effect_arguments_cannot_be_merged_by_the_body() {
    rejected(
        "
fun relay : (Unit -> Int needs {Oops a, ..r}) -> b -> Int needs {Oops b, ..r}
relay f _ = f () with { oops v = oops! v }
",
        &["independent type variables"],
    );
}

#[test]
fn omitted_effect_argument_is_one_type_for_code_checked_before_the_body() {
    // `needs {Oops}` leaves the argument to the body, which makes it Int.
    // The impl method is checked first and must not get to pick String.
    let errors = diagnostics(
        "
trait Go a {
  fun go : a -> Int
}

impl Go for Int {
  go _ = catch_num oops_string
}

fun catch_num : (Unit -> Int needs {Oops, ..r}) -> Int needs {..r}
catch_num f = f () with { oops n = resume (n + 1) }
",
    );
    assert!(
        errors
            .iter()
            .any(|d| d.message.contains("String") && d.message.contains("Int")),
        "expected a String/Int mismatch, got: {:#?}",
        errors.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
    accepted(
        "
trait Go a {
  fun go : a -> Int
}

impl Go for Int {
  go _ = catch_num oops_int
}

fun catch_num : (Unit -> Int needs {Oops, ..r}) -> Int needs {..r}
catch_num f = f () with { oops n = resume (n + 1) }
",
    );
}

#[test]
fn open_row_trait_method_with_a_named_family_is_checked_at_the_call() {
    // `guarded` names `Oops Int` next to `..a`, so it may handle it around
    // the method. A caller whose impl performs `Oops String` is rejected.
    let program = |impl_effect: &str, op: &str| {
        format!(
            "
trait Risky a {{
  fun risk : a -> Int needs {{..e}}
}}

impl Risky for Int needs {{{impl_effect}}} {{
  risk _ = {op}
}}

fun guarded : a -> Int needs {{Oops Int, ..a}} where {{a: Risky}}
guarded x = (risk x with {{ oops n = resume (n + 1) }}) + oops! 1

use_it () = guarded 3 with {{ oops n = resume n }}
"
        )
    };
    accepted(&program("Oops Int", "oops! 2"));
    rejected_as_conflict(&program("Oops String", "oops! \"s\""));
}

#[test]
fn handler_around_an_open_row_trait_method_is_rejected() {
    // The impl chosen by the caller supplies the row; it may perform `Oops`
    // at any type.
    rejected(
        "
trait Risky a {
  fun risk : a -> Int needs {..e}
}

fun guarded : a -> Int needs {..a} where {a: Risky}
guarded x = risk x with { oops n = resume (n + 1) }
",
        &["cannot handle `Oops` here"],
    );
}

#[test]
fn impl_effect_must_be_the_trait_methods_application() {
    rejected_as_conflict(
        "
trait Risky a {
  fun risk : a -> Int needs {Oops Int}
}

impl Risky for Int needs {Oops String} {
  risk x = oops! \"s\"
}
",
    );
    rejected_as_conflict(
        "
trait Risky a {
  fun risk : a -> Int needs {Oops Int}
}

impl Risky for Int needs {Oops} {
  risk x = oops! \"s\"
}
",
    );
}

#[test]
fn handler_arm_cannot_handle_around_an_operations_open_callback_row() {
    rejected(
        "
effect Scope {
  fun scoped : (Unit -> Int needs {..e}) -> Int needs {..e}
}

run () = scoped! pure_int with {
  scoped body = resume (body () with { oops n = resume (n + 1) })
}
",
        &["cannot handle `Oops` here"],
    );
}

#[test]
fn neweffect_instances_stay_distinct_from_each_other_and_their_source() {
    accepted(
        "
neweffect OopsA = Oops String
neweffect OopsB = Oops Int

fun all : Unit -> Int needs {OopsA, OopsB, Oops Bool}
all () = OopsA.oops! \"s\" + OopsB.oops! 1 + Oops.oops! True
",
    );
}

#[test]
fn neweffect_must_fix_its_type_arguments() {
    // With a variable, each operation call would choose its own type.
    rejected(
        "
neweffect Loose = Oops a
",
        &["neweffect `Loose` must fix every type argument"],
    );
}

#[test]
fn unparameterised_effects_keep_their_behaviour_around_open_rows() {
    // No type argument, so no handler can receive an operation at the wrong
    // type: handling `Plain` around a caller's open row is still allowed.
    accepted(
        "
fun with_plain : (Unit -> Int needs {..r}) -> Int needs {..r}
with_plain f = f () with { plain () = resume 1 }
",
    );
}

#[test]
fn single_instantiation_parameterised_effects_still_work() {
    accepted(
        "
effect State s {
  fun get : Unit -> s
  fun put : s -> Unit
}

fun run_state : s -> (Unit -> a needs {State s, ..r}) -> a needs {..r}
run_state init f = {
  let run = f () with {
    get () = fun s -> (resume s) s
    put new_s = fun _ -> (resume ()) new_s
    return value = fun _ -> value
  }
  run init
}

fun bump : Unit -> Int needs {State Int}
bump () = {
  put! (get! () + 1)
  get! ()
}

fun label : Unit -> String needs {State String}
label () = {
  put! (get! () <> \"!\")
  get! ()
}

fun counted : (Unit -> a needs {..e}) -> a needs {State Int, ..e}
counted f = {
  put! (get! () + 1)
  f ()
}

fun main_like : Unit -> Int needs {Plain}
main_like () = {
  let n = run_state 0 bump
  let s = run_state \"a\" label
  let m = run_state 0 (fun () -> counted (fun () -> plain! ()))
  n + String.length s + m
}
",
    );
}

#[test]
fn impl_method_cannot_handle_around_its_callbacks_open_row() {
    // The trait method's signature is the declared type of the impl's body.
    rejected(
        "
trait Each a {
  fun each : a -> (Int -> Int needs {..e}) -> Int needs {..e}
}

impl Each for Int {
  each x f = f x with { oops n = resume (n + 1) }
}
",
        &["cannot handle `Oops` here"],
    );
}

#[test]
fn handler_needs_share_the_row_of_what_escapes_the_handled_block() {
    // The arm performs `Oops Int` outward, and the handled block lets
    // `Oops String` escape: both would be in the row of the `with`.
    rejected_as_conflict(
        "
handler relay for Plain needs {Oops Int} {
  plain () = resume (oops! 1)
}

run () = (plain! () + oops_string ()) with relay
",
    );
}

#[test]
fn local_function_closes_its_row_over_a_recursive_call() {
    // A recursive call performs the function's own row; that adds nothing,
    // and must not leave the function with an open row of its own.
    accepted(
        "
fun count : Int -> Int needs {Oops Int}
count n = {
  let go m = if m == 0 then oops! 1 else go (m - 1)
  go n
}

fun pure_loop : Int -> Int
pure_loop n = {
  let go m = if m == 0 then 0 else go (m - 1)
  go n
}
",
    );
}

#[test]
fn one_handlers_arm_does_not_fix_an_operations_row_for_other_handlers() {
    // Regression (kraken's `Repo`). `closing` hands the operation's callback
    // to something that accepts only `{Plain}`, which closes the callback's
    // `..r` for that arm. `forwarding`, a second handler of the same effect,
    // forwards `..r`; it must not find it already bound to `{Plain}` and be
    // told it "uses effects {Plain}". Each arm gets its own copy of the
    // operation's row variables.
    accepted(
        "
effect Scope {
  fun scoped : (Unit -> Int needs {..r}) -> Int needs {..r}
}

fun run_closed : (Unit -> Int needs {Plain}) -> Int needs {Plain}
run_closed f = f ()

fun forward : (Unit -> Int needs {..r}) -> Int needs {..r}
forward f = f ()

handler closing for Scope {
  scoped body = resume (run_closed (fun () -> body ()) with { plain () = resume 1 })
}

handler forwarding for Scope {
  scoped body = resume (forward body)
}

fun also_forwarding : Unit -> Handler Scope
also_forwarding () = handler for Scope {
  scoped body = resume (forward body)
}
",
    );
}
