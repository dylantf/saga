//! Family-only effect identity, continued (see `effect_family_tests.rs`):
//! the two places where an implementation is checked against a signature it
//! does not own, or selected after the code using it was checked.
//!
//! A. A handler arm implements an operation's signature and an impl method
//!    implements a trait method's. A type variable either signature uses as
//!    an effect's argument (`needs {Oops e}` on a callback) is chosen by
//!    whoever performs the operation or calls the method, so the
//!    implementation may not pin it.
//! B. An open-row trait method (`needs {..e}`) performs what the selected
//!    impl performs. Used as a value, those effects belong on its arrow,
//!    also when the impl is only known after the reference was checked.

use super::effect_family_tests::{accepted, diagnostics, rejected, rejected_as_conflict};

// --- A: effect-argument variables of an operation or trait method ---

/// `Scope.scoped` takes a callback that may perform `Oops` at any type.
const SCOPE: &str = "
effect Scope {
  fun scoped : (Unit -> Int needs {Oops e, ..r}) -> Int needs {..r}
}

fun perform_scoped : Unit -> Int needs {Scope}
perform_scoped () = scoped! (fun () -> oops! \"text\")
";

fn pinned_by_operation(src: &str) {
    rejected(
        src,
        &[
            "operation `scoped` is declared with `Oops` at any type",
            "only works when that type is `Int`",
        ],
    );
}

#[test]
fn handler_arm_cannot_pin_an_operations_effect_argument() {
    pinned_by_operation(&format!(
        "{SCOPE}
handler closing for Scope {{
  scoped body = resume (body () with {{ oops n = resume (n + 1) }})
}}

run () = perform_scoped () with closing
"
    ));
}

#[test]
fn handler_arm_cannot_pin_an_operations_omitted_effect_argument() {
    // `needs {Oops, ..r}` in an operation is not a hole for one handler to
    // fill in: every performer gets its own.
    pinned_by_operation(
        "
effect Scope {
  fun scoped : (Unit -> Int needs {Oops, ..r}) -> Int needs {..r}
}

handler closing for Scope {
  scoped body = resume (body () with { oops n = resume (n + 1) })
}
",
    );
}

#[test]
fn handler_value_cannot_pin_an_operations_effect_argument() {
    pinned_by_operation(&format!(
        "{SCOPE}
fun mk : Unit -> Handler Scope
mk () = handler for Scope {{
  scoped body = resume (body () with {{ oops n = resume (n + 1) }})
}}

run () = {{
  let h = mk ()
  perform_scoped () with h
}}
"
    ));
}

#[test]
fn inline_handler_arm_cannot_pin_an_operations_effect_argument() {
    pinned_by_operation(&format!(
        "{SCOPE}
fun run : Unit -> Int
run () = perform_scoped () with {{
  scoped body = resume (body () with {{ oops n = resume (n + 1) }})
}}
"
    ));
}

#[test]
fn handler_arm_cannot_merge_two_effect_arguments_of_an_operation() {
    rejected(
        "
effect Other e {
  fun other : e -> Int
}

effect Two {
  fun two : (Unit -> Int needs {Oops a, ..r}) -> (Unit -> Int needs {Other b, ..r}) -> Int needs {..r}
}

fun same : (Unit -> Int needs {Oops t, ..r}) -> (Unit -> Int needs {Other t, ..r}) -> Int needs {..r}
same f g = (f () with { oops _ = resume 0 }) + (g () with { other _ = resume 0 })

handler merging for Two {
  two f g = resume (same f g)
}
",
        &[
            "operation `two` is declared with independent type variables as effect arguments",
            "`Oops`",
            "`Other`",
        ],
    );
}

#[test]
fn handler_arm_generic_in_the_effect_argument_is_accepted() {
    // Ignoring the payload works at every type.
    accepted(&format!(
        "{SCOPE}
handler closing for Scope {{
  scoped body = resume (body () with {{ oops _ = resume 0 }})
}}

run () = perform_scoped () with closing
"
    ));
    // So does handing the callback to something generic in the argument.
    accepted(&format!(
        "{SCOPE}
fun catch_any : (Unit -> Int needs {{Oops e, ..r}}) -> Int needs {{..r}}
catch_any f = f () with {{ oops _ = resume 0 }}

handler closing for Scope {{
  scoped body = resume (catch_any body)
}}

fun run : Unit -> Int
run () = perform_scoped () with {{
  scoped body = resume (catch_any body)
}}
"
    ));
}

#[test]
fn handler_for_a_parameterised_effect_may_fix_its_argument() {
    // Here the variable is the effect's own parameter: `Scoped String` says
    // what it is, and performers of `Scoped String` agree.
    accepted(
        "
effect Scoped e {
  fun scoped : (Unit -> Int needs {Oops e, ..r}) -> Int needs {..r}
}

handler closing for Scoped Int {
  scoped body = resume (body () with { oops n = resume (n + 1) })
}

fun perform_int : Unit -> Int needs {Scoped Int}
perform_int () = scoped! (fun () -> oops! 41)

run () = perform_int () with closing

fun run_inline : Unit -> Int
run_inline () = perform_int () with {
  scoped body = resume (body () with { oops n = resume (n + 1) })
}
",
    );
    // And a performer at another type is told so.
    rejected(
        "
effect Scoped e {
  fun scoped : (Unit -> Int needs {Oops e, ..r}) -> Int needs {..r}
}

handler closing for Scoped Int {
  scoped body = resume (body () with { oops n = resume (n + 1) })
}

fun perform_string : Unit -> Int needs {Scoped String}
perform_string () = scoped! (fun () -> oops! \"text\")

run () = perform_string () with closing
",
        &["this handler handles `Scoped Int`", "`Scoped String`"],
    );
}

#[test]
fn handler_arm_cannot_send_an_operations_effect_argument_outward() {
    // Re-performing the callback's `Oops e` outside the arm would deliver
    // each performer's `e` to one outer handler, typed for one of them.
    rejected(
        &format!(
            "{SCOPE}
fun run : Unit -> Int needs {{Oops String}}
run () = perform_scoped () with {{
  scoped body = resume (body () with {{ oops v = resume (oops! v) }})
}}
"
        ),
        &["operation `scoped`"],
    );
    rejected(
        &format!(
            "{SCOPE}
handler outward for Scope needs {{Oops x}} {{
  scoped body = resume (body () with {{ oops v = resume (oops! v) }})
}}
"
        ),
        &["operation `scoped`"],
    );
}

#[test]
fn impl_method_cannot_pin_a_trait_methods_effect_argument() {
    rejected(
        "
trait Run a {
  fun run : a -> (Unit -> Int needs {Oops e, ..r}) -> Int needs {..r}
}

impl Run for Int {
  run _ f = f () with { oops n = resume (n + 1) }
}

go () = run 1 (fun () -> oops! \"text\")
",
        &[
            "trait method `run` is declared with `Oops` at any type",
            "only works when that type is `Int`",
        ],
    );
}

#[test]
fn impl_method_cannot_pin_the_trait_methods_own_effect_argument() {
    // A caller of `risk` handles `Oops e` at a type of its choosing.
    rejected(
        "
trait Risky a {
  fun risk : a -> Int needs {Oops e}
}

impl Risky for Int {
  risk _ = oops! \"s\"
}
",
        &[
            "trait method `risk` is declared with `Oops` at any type",
            "only works when that type is `String`",
        ],
    );
}

#[test]
fn impl_method_generic_in_the_effect_argument_is_accepted() {
    accepted(
        "
trait Run a {
  fun run : a -> (Unit -> Int needs {Oops e, ..r}) -> Int needs {..r}
}

impl Run for Int {
  run _ f = f () with { oops _ = resume 0 }
}

go () = run 1 (fun () -> oops! \"text\")
",
    );
}

#[test]
fn impl_of_a_parameterised_trait_may_fix_the_effect_argument() {
    // The variable is the trait's own parameter, fixed by the impl header.
    accepted(
        "
trait RunAt a e {
  fun run_at : a -> (Unit -> Int needs {Oops e, ..r}) -> Int needs {..r}
}

impl RunAt Int for Bool {
  run_at _ f = f () with { oops n = resume (n + 1) }
}
",
    );
}

// --- B: open-row trait methods used as values ---

/// `decode` at `Text` performs `Oops String`; at `Quiet` it performs
/// nothing.
const DECODE: &str = "
trait Decode a {
  fun decode : a -> Int needs {..e}
}

type Text = Text
type Quiet = Quiet

impl Decode for Text needs {Oops String} {
  decode _ = oops! \"text\"
}

impl Decode for Quiet {
  decode _ = 0
}

fun apply_open : (a -> Int needs {..r}) -> a -> Int needs {..r}
apply_open f x = f x

fun apply_pure : (a -> Int) -> a -> Int
apply_pure f x = f x

fun catch_int : (Unit -> Int needs {Oops Int}) -> Int
catch_int f = f () with { oops n = resume (n + 1) }
";

/// Rejected with an error that names the impl's effect.
fn rejected_naming_impl_effect(src: &str) -> String {
    let errors = diagnostics(&format!("{DECODE}\n{src}"));
    let found = errors
        .iter()
        .find(|d| d.message.contains("Oops String") || d.message.contains("{Oops}"));
    match found {
        Some(d) => {
            assert!(d.span.is_some(), "error has no span: {}", d.message);
            d.message.clone()
        }
        None => panic!(
            "expected an error naming the impl's effect, got: {:#?}",
            errors.iter().map(|d| &d.message).collect::<Vec<_>>()
        ),
    }
}

fn accepted_with_decode(src: &str) {
    accepted(&format!("{DECODE}\n{src}"));
}

#[test]
fn method_reference_passed_to_an_open_row_runs_under_no_other_handler() {
    // `decode` at `Text` performs `Oops String`; it may not run under a
    // handler for `Oops Int`.
    let message = rejected_naming_impl_effect(
        "
run () = catch_int (fun () -> apply_open decode Text)
",
    );
    assert!(message.contains("Oops Int"), "{message}");
}

#[test]
fn method_reference_returned_at_another_application_is_rejected() {
    rejected_as_conflict(&format!(
        "{DECODE}
fun pick : Unit -> (Text -> Int needs {{Oops Int}})
pick () = decode
"
    ));
}

#[test]
fn method_reference_stored_in_a_field_at_another_application_is_rejected() {
    rejected_as_conflict(&format!(
        "{DECODE}
record Box {{ run: Text -> Int needs {{Oops Int}} }}

fun make : Unit -> Box
make () = Box {{ run: decode }}
"
    ));
}

#[test]
fn method_reference_cannot_escape_through_an_open_row() {
    rejected(
        &format!(
            "{DECODE}
fun run : Unit -> Int
run () = apply_open decode Text
"
        ),
        &["Oops"],
    );
}

#[test]
fn method_reference_cannot_be_used_as_a_pure_function() {
    let message = rejected_naming_impl_effect(
        "
fun run : Unit -> Int
run () = apply_pure decode Text
",
    );
    assert!(
        message.contains("`decode` is used here as a function value")
            && message.contains("impl of `Decode`")
            && message.contains("allows only no effects"),
        "{message}"
    );
    rejected_naming_impl_effect(
        "
fun pick : Unit -> (Text -> Int)
pick () = decode
",
    );
}

#[test]
fn method_reference_cannot_be_used_at_a_neweffect_instance() {
    let message = rejected_naming_impl_effect(
        "
neweffect OopsN = Oops Int

fun pick : Unit -> (Text -> Int needs {OopsN})
pick () = decode
",
    );
    assert!(message.contains("OopsN"), "{message}");
}

#[test]
fn method_reference_bound_by_let_keeps_the_impls_effects() {
    rejected_naming_impl_effect(
        "
run () = {
  let f = decode
  catch_int (fun () -> f Text)
}
",
    );
    // Also when the binding is itself used as a value.
    rejected_naming_impl_effect(
        "
run () = {
  let f = decode
  catch_int (fun () -> apply_open f Text)
}
",
    );
    rejected_naming_impl_effect(
        "
fun run : Unit -> Int
run () = {
  let f = decode
  apply_pure f Text
}
",
    );
}

#[test]
fn where_bound_function_reference_keeps_the_impls_effects() {
    // `use_it` forwards the impl's row as `..a`; referenced at `Text` that
    // row is `Oops String`.
    let generic = "
fun use_it : a -> Int needs {..a} where {a: Decode}
use_it x = decode x
";
    rejected_naming_impl_effect(&format!(
        "{generic}
run () = catch_int (fun () -> apply_open use_it Text)
"
    ));
    rejected_naming_impl_effect(&format!(
        "{generic}
fun pick : Unit -> (Text -> Int)
pick () = use_it
"
    ));
    accepted_with_decode(&format!(
        "{generic}
fun run : Unit -> Int needs {{Oops String}}
run () = apply_open use_it Text
"
    ));
}

#[test]
fn partially_applied_method_keeps_the_impls_effects() {
    let two = "
trait Decode2 a {
  fun decode2 : a -> Int -> Int needs {..e}
}

impl Decode2 for Text needs {Oops String} {
  decode2 _ n = n + oops! \"text\"
}
";
    rejected_naming_impl_effect(&format!(
        "{two}
fun run : Unit -> Int
run () = apply_pure (decode2 Text) 1
"
    ));
    accepted_with_decode(&format!(
        "{two}
fun run : Unit -> Int needs {{Oops String}}
run () = apply_open (decode2 Text) 1
"
    ));
}

#[test]
fn method_reference_is_usable_where_the_impls_effects_are_allowed() {
    // Declared by the enclosing function.
    accepted_with_decode(
        "
fun run : Unit -> Int needs {Oops String}
run () = apply_open decode Text
",
    );
    // Handled around the use.
    accepted_with_decode(
        "
fun run : Unit -> Int
run () = apply_open decode Text with { oops _ = resume 0 }
",
    );
    // Returned or stored at the impl's own effects.
    accepted_with_decode(
        "
record Box { run: Text -> Int needs {Oops String} }

fun pick : Unit -> (Text -> Int needs {Oops String})
pick () = decode

fun make : Unit -> Box
make () = Box { run: decode }
",
    );
    // An impl that performs nothing is a pure function.
    accepted_with_decode(
        "
fun run : Unit -> Int
run () = apply_pure decode Quiet + apply_open decode Quiet
",
    );
}

#[test]
fn method_uses_that_were_already_checked_stay_as_they_were() {
    accepted_with_decode(
        "
fun direct : Unit -> Int needs {Oops String}
direct () = decode Text

fun through_let : Unit -> Int needs {Oops String}
through_let () = {
  let f = decode
  f Text
}

fun through_lambda : Unit -> Int needs {Oops String}
through_lambda () = apply_open (fun x -> decode x) Text

fun generic : a -> Int needs {..a} where {a: Decode}
generic x = decode x

fun at_text : Unit -> Int needs {Oops String}
at_text () = generic Text
",
    );
    rejected_naming_impl_effect(
        "
run () = catch_int (fun () -> decode Text)
",
    );
    rejected_naming_impl_effect(
        "
run () = catch_int (fun () -> apply_open (fun x -> decode x) Text)
",
    );
}

#[test]
fn method_reference_at_a_where_bound_type_forwards_its_row() {
    // The impl is the caller's: the reference's row is `..a`, as for a call.
    accepted_with_decode(
        "
fun generic : a -> Int needs {..a} where {a: Decode}
generic x = apply_open decode x

fun at_text : Unit -> Int needs {Oops String}
at_text () = generic Text
",
    );
    rejected(
        &format!(
            "{DECODE}
fun generic : a -> Int where {{a: Decode}}
generic x = apply_open decode x
"
        ),
        &["does not forward its effects"],
    );
    rejected(
        &format!(
            "{DECODE}
fun generic : a -> Int where {{a: Decode}}
generic x = apply_pure decode x
"
        ),
        &[
            "`decode` is used here as a function value",
            "chosen by the caller",
        ],
    );
    // A handler cannot be installed around it either.
    rejected(
        &format!(
            "{DECODE}
fun generic : a -> Int needs {{..a}} where {{a: Decode}}
generic x = apply_open decode x with {{ oops n = resume (n + 1) }}
"
        ),
        &["cannot handle `Oops` here"],
    );
    // Returned from a generic function, as a reference or eta-expanded: the
    // returned function's `..a` is the impl's effects once `a` is known.
    for body in ["decode", "fun x -> decode x"] {
        let via = format!(
            "
fun via : a -> (a -> Int needs {{..a}}) where {{a: Decode}}
via _ = {body}
"
        );
        accepted_with_decode(&format!(
            "{via}
fun run : Unit -> Int needs {{Oops String}}
run () = {{
  let f = via Text
  f Text
}}

fun quiet : Unit -> Int
quiet () = apply_pure (via Quiet) Quiet
"
        ));
        rejected_naming_impl_effect(&format!(
            "{via}
fun run : Unit -> Int
run () = {{
  let f = via Text
  f Text
}}
"
        ));
        rejected_naming_impl_effect(&format!(
            "{via}
run () = catch_int (fun () -> apply_open (via Text) Text)
"
        ));
    }
    // And the caller of the generic function is checked at its impl.
    rejected_naming_impl_effect(
        "
fun generic : a -> Int needs {..a} where {a: Decode}
generic x = apply_open decode x

run () = catch_int (fun () -> generic Text)
",
    );
}
