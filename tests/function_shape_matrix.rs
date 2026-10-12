//! Function-shape matrix: generated programs for the calling convention of
//! function values.
//!
//! Step A1 of `docs/planning/sound-function-representation.md`. Each case
//! crosses a *producer* (how a function value is made), a *position* (where
//! it flows before it is called) and a *variant* (arity 1 or 2, pure or
//! effectful). Every case is a small `module Main` with
//! `pub fun result : Unit -> Int` whose value the generator knows in advance,
//! so a case passes only if it compiles, runs and returns that integer.
//!
//! A second family, with ids starting `param.`, covers effects that take a
//! type parameter (`Fail String` next to `Fail Int`). See the section
//! "Parameterised-effect family" below.
//!
//! Many cases fail today. The checked-in lists under `tests/fixtures/` pin
//! the current state:
//!
//! - `function_shape_matrix_expected_failures.txt`: `<case id> <class>` for
//!   every case that fails.
//! - `function_shape_matrix_typecheck_rejected.txt`: every case the
//!   typechecker rejects. These are skipped, not failed.
//!
//! The test fails when the observed sets differ from those files in either
//! direction: a new failure is a regression, and a case that started passing
//! must be removed from the list by whoever fixed it.
//!
//! Environment variables:
//!
//! - `SAGA_MATRIX_BLESS=1` rewrites both fixture files from this run.
//! - `SAGA_MATRIX_FILTER=<text>` runs only case ids containing `<text>`
//!   (comma separated alternatives), prints each result with its detail, and
//!   does not compare against the fixture files.
//! - `SAGA_MATRIX_DUMP=<dir>` writes every generated program to `<dir>`.
//! - `SAGA_MATRIX_DEADLINE_SECS=<n>` changes the overall time limit
//!   (default 300).
//!
//! Nothing here can run unbounded. A generated program that has not returned
//! after 5 seconds is killed and recorded with class `timeout`; each `erl`
//! and `erlc` child has a wall-clock limit and is killed with its process
//! group; and a watchdog aborts the test, naming the cases in progress, if
//! the whole run exceeds the overall limit.
//!
//! A full per-case report, including failure details and skip reasons, is
//! written to `target/tmp/function_shape_matrix_report.txt` on every run.
//!
//! Requires `erlc` and `erl` on PATH.
mod common;

use common::*;
use std::collections::{BTreeMap, BTreeSet};
use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

const EXPECTED_FAILURES_FILE: &str = "tests/fixtures/function_shape_matrix_expected_failures.txt";
const TYPECHECK_REJECTED_FILE: &str = "tests/fixtures/function_shape_matrix_typecheck_rejected.txt";

// ---------------------------------------------------------------------------
// Axes
// ---------------------------------------------------------------------------

/// Shape and effectfulness of the function type under test.
///
/// | name | type                              |
/// |------|-----------------------------------|
/// | `p1` | `Int -> Int`                      |
/// | `e1` | `Int -> Int needs {Skip}`         |
/// | `p2` | `Int -> Int -> Int`               |
/// | `e2` | `Int -> Int -> Int needs {Skip}`  |
/// | `pu` | `Unit -> Int`                     |
/// | `eu` | `Unit -> Int needs {Skip}`        |
#[derive(Clone, Copy)]
struct Variant {
    name: &'static str,
    arity: u8,
    /// The single parameter is `Unit`. Only with `arity == 1`.
    thunk: bool,
    eff: bool,
}

const fn variant(name: &'static str, arity: u8, thunk: bool, eff: bool) -> Variant {
    Variant {
        name,
        arity,
        thunk,
        eff,
    }
}

const VARIANTS: &[Variant] = &[
    variant("p1", 1, false, false),
    variant("e1", 1, false, true),
    variant("p2", 2, false, false),
    variant("e2", 2, false, true),
    variant("pu", 1, true, false),
    variant("eu", 1, true, true),
];

const PRODUCERS: &[&str] = &[
    "lambda",
    "lambda_multi",
    "lambda_nested",
    "named",
    "partial_named",
    "partial_lambda",
    "if_lambdas",
    "if_named",
    "if_lambda_named",
    "if_mixed_eff_chosen",
    "if_mixed_pure_chosen",
    "case_lambdas",
    "case_named",
    "case_lambda_named",
    "case_mixed_eff_chosen",
    "case_mixed_pure_chosen",
    "block",
    "poly_named",
    "poly_lambda",
    "dict_method",
    "dict_method_generic",
    "dict_method_partial",
    "dict_method_partial_generic",
    "eta_op",
    "pure_named_as_eff",
    "pure_lambda_as_eff",
];

const POSITIONS: &[&str] = &[
    "direct",
    "let_bound",
    "let_outside_handler",
    "hof_concrete",
    "hof_open",
    "poly_apply",
    "poly_apply_full",
    "poly_ident",
    "returned",
    "returned_let",
    "list_iter",
    "list_open",
    "list_returned_open",
    "record_field",
    "record_field_fn",
    "ctor_field",
    "cross_module_arg",
    "cross_module_open",
    "cross_module_ret",
];

// ---------------------------------------------------------------------------
// Shared program fragments
// ---------------------------------------------------------------------------

/// The effect an effectful case uses. Everything uses `Skip` except the
/// eta-reduced operation producer, whose operation must itself have the
/// function type under test.
#[derive(Clone, Copy, PartialEq)]
enum Effect {
    Skip,
    Bump,
}

impl Effect {
    fn name(self) -> &'static str {
        match self {
            Effect::Skip => "Skip",
            Effect::Bump => "Bump",
        }
    }

    fn decl(self, v: Variant, public: bool) -> String {
        let vis = if public { "pub " } else { "" };
        match self {
            Effect::Skip => format!("{vis}effect Skip {{ fun skip : Unit -> Int }}"),
            Effect::Bump => format!("{vis}effect Bump {{ fun bump : {} }}", base_ty(v)),
        }
    }

    fn handler(self, v: Variant) -> &'static str {
        match self {
            Effect::Skip => "with { skip () = resume 100 }",
            Effect::Bump if v.thunk => "with { bump () = resume 141 }",
            Effect::Bump if v.arity == 1 => "with { bump x = resume (x + 101) }",
            Effect::Bump => "with { bump a b = resume (a * 10 + b + 101) }",
        }
    }
}

const YES: &str = "fun yes : Unit -> Bool\nyes () = True";
const ONE: &str = "fun one : Unit -> Int\none () = 1";
const IDENT: &str = "fun ident : a -> a\nident x = x";
const APPLY_GEN: &str = "fun apply_gen : (a -> b) -> a -> b\napply_gen f x = f x";
const APPLY_GEN2: &str = "fun apply_gen2 : (a -> b -> c) -> a -> b -> c\napply_gen2 f x y = f x y";

fn base_ty(v: Variant) -> &'static str {
    if v.thunk {
        "Unit -> Int"
    } else if v.arity == 1 {
        "Int -> Int"
    } else {
        "Int -> Int -> Int"
    }
}

/// `needs` clause for a function that performs when `eff` is set.
fn needs(eff: bool, effect: Effect) -> String {
    if eff {
        format!(" needs {{{}}}", effect.name())
    } else {
        String::new()
    }
}

fn params(v: Variant) -> &'static str {
    if v.thunk {
        "()"
    } else if v.arity == 1 {
        "x"
    } else {
        "a b"
    }
}

fn call_args(v: Variant) -> &'static str {
    if v.thunk {
        "()"
    } else if v.arity == 1 {
        "5"
    } else {
        "2 3"
    }
}

/// Value of the target function at `call_args`, before any effect.
fn base_value(v: Variant) -> i64 {
    if v.thunk {
        40 + 1
    } else if v.arity == 1 {
        5 + 1
    } else {
        2 * 10 + 3 + 1
    }
}

fn skip_suffix(performs: bool) -> &'static str {
    if performs { " + skip! ()" } else { "" }
}

/// Body of the function every case is expected to end up calling. `k` is the
/// spelling of the constant 1, so producers can route it through a parameter
/// or a captured local.
fn target_body(v: Variant, k: &str, performs: bool) -> String {
    let core = if v.thunk {
        format!("40 + {k}")
    } else if v.arity == 1 {
        format!("x + {k}")
    } else {
        format!("a * 10 + b + {k}")
    };
    format!("{core}{}", skip_suffix(performs))
}

/// Body of the decoy function in the branch that must not be taken.
fn other_body(v: Variant, performs: bool) -> String {
    let core = if v.thunk {
        "7"
    } else if v.arity == 1 {
        "x - 1"
    } else {
        "a + b"
    };
    format!("{core}{}", skip_suffix(performs))
}

fn lambda(v: Variant, body: &str) -> String {
    format!("(fun {} -> {body})", params(v))
}

fn named(name: &str, v: Variant, eff: bool, body: &str) -> String {
    format!(
        "fun {name} : {}{}\n{name} {} = {body}",
        base_ty(v),
        needs(eff, Effect::Skip),
        params(v)
    )
}

// ---------------------------------------------------------------------------
// Producers
// ---------------------------------------------------------------------------

/// A function-valued expression plus the declarations it relies on.
struct Produced {
    decls: Vec<String>,
    /// Parenthesised where needed, so it can be used as an argument.
    expr: String,
    /// Whether calling the value performs the effect. False for pure
    /// variants and for pure values used at an effectful type.
    performs: bool,
    effect: Effect,
}

fn produced(decls: Vec<String>, expr: impl Into<String>, performs: bool) -> Produced {
    Produced {
        decls,
        expr: expr.into(),
        performs,
        effect: Effect::Skip,
    }
}

const NEEDS_EFFECT: &str = "n/a: only meaningful for effectful variants";
const NEEDS_ARITY1: &str = "n/a: producer is specific to arity 1";
const NEEDS_ARITY2: &str = "n/a: producer needs two parameters";

fn branch(kind: &str, taken: &str, not_taken: &str) -> (Vec<String>, String) {
    if kind == "if" {
        (
            vec![YES.to_string()],
            format!("(if yes () then {taken} else {not_taken})"),
        )
    } else {
        (
            vec![ONE.to_string()],
            format!("(case one () {{\n    0 -> {not_taken}\n    _ -> {taken}\n  }})"),
        )
    }
}

fn produce(producer: &str, v: Variant) -> Result<Produced, &'static str> {
    let e = v.eff;
    let tgt = |eff: bool| named("tgt", v, eff, &target_body(v, "1", eff));
    let oth = |eff: bool| named("oth", v, eff, &other_body(v, eff));
    let lam_t = |eff: bool| lambda(v, &target_body(v, "1", eff));
    let lam_o = |eff: bool| lambda(v, &other_body(v, eff));

    if let Some((kind, shape)) = producer
        .split_once('_')
        .filter(|(kind, _)| *kind == "if" || *kind == "case")
    {
        // (taken, not taken, decls, performs)
        let (taken, not_taken, mut decls, performs) = match shape {
            "lambdas" => (lam_t(e), lam_o(e), vec![], e),
            "named" => (
                "tgt".to_string(),
                "oth".to_string(),
                vec![tgt(e), oth(e)],
                e,
            ),
            "lambda_named" => (lam_t(e), "oth".to_string(), vec![oth(e)], e),
            "mixed_eff_chosen" => {
                if !e {
                    return Err(NEEDS_EFFECT);
                }
                (lam_t(true), "oth".to_string(), vec![oth(false)], true)
            }
            "mixed_pure_chosen" => {
                if !e {
                    return Err(NEEDS_EFFECT);
                }
                (lam_t(false), "oth".to_string(), vec![oth(true)], false)
            }
            other => panic!("unknown branch shape {other}"),
        };
        let (branch_decls, expr) = branch(kind, &taken, &not_taken);
        decls.extend(branch_decls);
        return Ok(produced(decls, expr, performs));
    }

    Ok(match producer {
        "lambda" => {
            if v.arity != 1 {
                return Err(NEEDS_ARITY1);
            }
            produced(vec![], lam_t(e), e)
        }
        "lambda_multi" => {
            if v.arity != 2 {
                return Err(NEEDS_ARITY2);
            }
            produced(vec![], lam_t(e), e)
        }
        "lambda_nested" => {
            if v.arity != 2 {
                return Err(NEEDS_ARITY2);
            }
            produced(
                vec![],
                format!("(fun a -> fun b -> {})", target_body(v, "1", e)),
                e,
            )
        }
        "named" => produced(vec![tgt(e)], "tgt", e),
        "partial_named" => {
            let decl = format!(
                "fun ptgt : Int -> {}{}\nptgt k {} = {}",
                base_ty(v),
                needs(e, Effect::Skip),
                params(v),
                target_body(v, "k", e)
            );
            produced(vec![decl], "(ptgt 1)", e)
        }
        "partial_lambda" => produced(
            vec![],
            format!("((fun k {} -> {}) 1)", params(v), target_body(v, "k", e)),
            e,
        ),
        "block" => produced(
            vec![],
            format!(
                "({{\n    let k = 1\n    fun {} -> {}\n  }})",
                params(v),
                target_body(v, "k", e)
            ),
            e,
        ),
        "poly_named" => produced(vec![tgt(e), IDENT.to_string()], "(ident tgt)", e),
        "poly_lambda" => produced(vec![IDENT.to_string()], format!("(ident {})", lam_t(e)), e),
        "dict_method" | "dict_method_generic" => {
            // The method's own type is the function type under test, at
            // `a = Int` (`a = Unit` for thunks): an unapplied dictionary
            // method.
            let (self_ty, witness) = if v.thunk {
                ("Unit", "()")
            } else {
                ("Int", "0")
            };
            let rest = if v.arity == 1 { "Int" } else { "Int -> Int" };
            let open = if e { " needs {..e}" } else { "" };
            let forwarded = if e { " needs {..a}" } else { "" };
            let mut decls = vec![
                format!("trait Shape a {{\n  fun meth : a -> {rest}{open}\n}}"),
                format!(
                    "impl Shape for {self_ty}{} {{\n  meth {} = {}\n}}",
                    needs(e, Effect::Skip),
                    params(v),
                    target_body(v, "1", e)
                ),
            ];
            if producer == "dict_method" {
                produced(decls, "meth", e)
            } else {
                decls.push(format!(
                    "fun via : a -> (a -> {rest}{forwarded}) where {{a: Shape}}\nvia _ = meth"
                ));
                produced(decls, format!("(via {witness})"), e)
            }
        }
        "dict_method_partial" | "dict_method_partial_generic" => {
            // The method takes a selector first; applying it to the selector
            // leaves the function type under test.
            let open = if e { " needs {..e}" } else { "" };
            let forwarded = if e { " needs {..a}" } else { "" };
            let mut decls = vec![
                format!("trait Op a {{\n  fun op : a -> {}{open}\n}}", base_ty(v)),
                "type Sel = Sel".to_string(),
                format!(
                    "impl Op for Sel{} {{\n  op _ {} = {}\n}}",
                    needs(e, Effect::Skip),
                    params(v),
                    target_body(v, "1", e)
                ),
            ];
            if producer == "dict_method_partial" {
                produced(decls, "(op Sel)", e)
            } else {
                decls.push(format!(
                    "fun get_op : a -> ({}{forwarded}) where {{a: Op}}\nget_op w = op w",
                    base_ty(v)
                ));
                produced(decls, "(get_op Sel)", e)
            }
        }
        "eta_op" => {
            if !e {
                return Err("n/a: an effect operation is never pure");
            }
            Produced {
                decls: vec![],
                expr: "bump!".to_string(),
                performs: true,
                effect: Effect::Bump,
            }
        }
        "pure_named_as_eff" => {
            if !e {
                return Err(NEEDS_EFFECT);
            }
            produced(vec![tgt(false)], "tgt", false)
        }
        "pure_lambda_as_eff" => {
            if !e {
                return Err(NEEDS_EFFECT);
            }
            produced(vec![], lam_t(false), false)
        }
        other => panic!("unknown producer {other}"),
    })
}

// ---------------------------------------------------------------------------
// Positions
// ---------------------------------------------------------------------------

/// Where the handler goes in `result`.
#[derive(PartialEq)]
enum Handler {
    /// Around the whole body, so the function value is created under it.
    Outer,
    /// Around the final call only; the function value is created outside.
    FinalCallOnly,
}

enum Layout {
    Single,
    /// `Lib` holds the consumer; `Main` holds the producer.
    LibConsumer {
        lib_decls: Vec<String>,
    },
    /// `Lib` holds the producer; `Main` calls what it returns.
    LibProducer {
        lib_decls: Vec<String>,
    },
}

struct Placed {
    decls: Vec<String>,
    stmts: Vec<String>,
    expr: String,
    handler: Handler,
    layout: Layout,
}

fn placed(decls: Vec<String>, stmts: Vec<String>, expr: impl Into<String>) -> Placed {
    Placed {
        decls,
        stmts,
        expr: expr.into(),
        handler: Handler::Outer,
        layout: Layout::Single,
    }
}

fn place(position: &str, v: Variant, effect: Effect, f: &str) -> Result<Placed, &'static str> {
    let args = call_args(v);
    // The function type under test, as written in a signature.
    let ty = format!("{}{}", base_ty(v), needs(v.eff, effect));
    let open_ty = format!("{} needs {{..e}}", base_ty(v));
    let ret_needs = needs(v.eff, effect);
    let list_body = |name: &str| {
        format!("{name} fs = case fs {{\n  [] -> 0\n  f :: rest -> f {args} + {name} rest\n}}")
    };
    let hof = |vis: &str, name: &str| {
        format!("{vis}fun {name} : ({ty}) -> Int{ret_needs}\n{name} f = f {args}")
    };
    let hof_open = |vis: &str, name: &str| {
        format!("{vis}fun {name} : ({open_ty}) -> Int needs {{..e}}\n{name} f = f {args}")
    };

    Ok(match position {
        "direct" => placed(vec![], vec![], format!("{f} {args}")),
        "let_bound" => placed(vec![], vec![format!("let f = {f}")], format!("f {args}")),
        "let_outside_handler" => {
            if !v.eff {
                return Err("n/a: pure variants have no handler");
            }
            Placed {
                handler: Handler::FinalCallOnly,
                ..placed(vec![], vec![format!("let f = {f}")], format!("f {args}"))
            }
        }
        "hof_concrete" => placed(vec![hof("", "hof")], vec![], format!("hof {f}")),
        "hof_open" => placed(
            vec![hof_open("", "hof_open")],
            vec![],
            format!("hof_open {f}"),
        ),
        "poly_apply" => {
            let expr = if v.arity == 1 {
                format!("apply_gen {f} {args}")
            } else {
                format!("(apply_gen {f} 2) 3")
            };
            placed(vec![APPLY_GEN.to_string()], vec![], expr)
        }
        "poly_apply_full" => {
            if v.arity != 2 {
                return Err("n/a: same as poly_apply at arity 1");
            }
            placed(
                vec![APPLY_GEN2.to_string()],
                vec![],
                format!("apply_gen2 {f} 2 3"),
            )
        }
        "poly_ident" => placed(
            vec![IDENT.to_string()],
            vec![],
            format!("(ident {f}) {args}"),
        ),
        "returned" | "returned_let" => {
            let decl = format!("fun make : Unit -> ({ty})\nmake () = {f}");
            if position == "returned" {
                placed(vec![decl], vec![], format!("(make ()) {args}"))
            } else {
                placed(
                    vec![decl],
                    vec!["let f = make ()".to_string()],
                    format!("f {args}"),
                )
            }
        }
        "list_iter" => placed(
            vec![format!(
                "fun run_list : List ({ty}) -> Int{ret_needs}\n{}",
                list_body("run_list")
            )],
            vec![],
            format!("run_list [{f}]"),
        ),
        "list_open" => placed(
            vec![format!(
                "fun run_open : List ({open_ty}) -> Int needs {{..e}}\n{}",
                list_body("run_open")
            )],
            vec![],
            format!("run_open [{f}]"),
        ),
        // The list is built at the closed type, then meets the open row
        // away from the literal, so no coercion position is involved.
        "list_returned_open" => placed(
            vec![
                format!("fun make_list : Unit -> List ({ty})\nmake_list () = [{f}]"),
                format!(
                    "fun run_open : List ({open_ty}) -> Int needs {{..e}}\n{}",
                    list_body("run_open")
                ),
            ],
            vec![],
            "run_open (make_list ())",
        ),
        // The field call sits directly under the handler in `result`. Today
        // that alone panics the compiler for every effectful variant,
        // whatever the producer; `record_field_fn` makes the same call inside
        // a function that declares the effect, which isolates the record.
        "record_field" => placed(
            vec![format!("record Box {{ run : {ty} }}")],
            vec![format!("let b = Box {{ run: {f} }}")],
            format!("b.run {args}"),
        ),
        "record_field_fn" => placed(
            vec![
                format!("record Box {{ run : {ty} }}"),
                format!("fun use_box : Box -> Int{ret_needs}\nuse_box b = b.run {args}"),
            ],
            vec![],
            format!("use_box (Box {{ run: {f} }})"),
        ),
        "ctor_field" => placed(
            vec![format!("type Wrap = Wrap ({ty})")],
            vec![format!("let w = Wrap {f}")],
            format!("case w {{\n    Wrap g -> g {args}\n  }}"),
        ),
        "cross_module_arg" => Placed {
            layout: Layout::LibConsumer {
                lib_decls: vec![hof("pub ", "lib_hof")],
            },
            ..placed(vec![], vec![], format!("lib_hof {f}"))
        },
        "cross_module_open" => Placed {
            layout: Layout::LibConsumer {
                lib_decls: vec![hof_open("pub ", "lib_hof_open")],
            },
            ..placed(vec![], vec![], format!("lib_hof_open {f}"))
        },
        "cross_module_ret" => Placed {
            layout: Layout::LibProducer {
                lib_decls: vec![format!(
                    "pub fun lib_make : Unit -> ({ty})\nlib_make () = {f}"
                )],
            },
            ..placed(vec![], vec![], format!("(lib_make ()) {args}"))
        },
        other => panic!("unknown position {other}"),
    })
}

// ---------------------------------------------------------------------------
// Case assembly
// ---------------------------------------------------------------------------

struct Program {
    main: String,
    lib: Option<String>,
    expected: i64,
}

struct Case {
    id: String,
    /// `SHAPE` or `PARAM`. The next three fields are that family's axes.
    family: &'static str,
    producer: &'static str,
    position: &'static str,
    variant: &'static str,
    /// `Err` holds the reason the combination is not generated.
    program: Result<Program, &'static str>,
}

fn join_decls(parts: &[String]) -> String {
    let mut seen = BTreeSet::new();
    let mut out = String::new();
    for part in parts {
        if seen.insert(part.as_str()) {
            out.push_str(part);
            out.push_str("\n\n");
        }
    }
    out
}

fn pub_name(decl: &str) -> Option<&str> {
    let rest = decl.strip_prefix("pub fun ")?;
    rest.split_whitespace().next()
}

fn build_program(producer: &str, position: &str, v: Variant) -> Result<Program, &'static str> {
    let p = produce(producer, v)?;
    let q = place(position, v, p.effect, &p.expr)?;
    let handler = p.effect.handler(v);

    let mut body = String::new();
    for stmt in &q.stmts {
        body.push_str("  ");
        body.push_str(stmt);
        body.push('\n');
    }
    let result = if !v.eff {
        format!("result () = {{\n{body}  {}\n}}\n", q.expr)
    } else if q.handler == Handler::FinalCallOnly {
        format!("result () = {{\n{body}  ({}) {handler}\n}}\n", q.expr)
    } else {
        format!("result () = {{\n{body}  {}\n}} {handler}\n", q.expr)
    };
    let result = format!("pub fun result : Unit -> Int\n{result}");
    let expected = base_value(v) + if p.performs { 100 } else { 0 };

    let effect_decl = |public: bool| -> Vec<String> {
        if v.eff {
            vec![p.effect.decl(v, public)]
        } else {
            vec![]
        }
    };
    let import = |lib_decls: &[String]| -> String {
        let mut names: Vec<&str> = Vec::new();
        if v.eff {
            names.push(p.effect.name());
        }
        names.extend(lib_decls.iter().filter_map(|d| pub_name(d)));
        format!("import Lib ({})", names.join(", "))
    };

    let (main, lib) = match &q.layout {
        Layout::Single => {
            let mut decls = effect_decl(false);
            decls.extend(p.decls.iter().cloned());
            decls.extend(q.decls.iter().cloned());
            (
                format!("module Main\n\n{}{result}", join_decls(&decls)),
                None,
            )
        }
        Layout::LibConsumer { lib_decls } => {
            let mut lib = effect_decl(true);
            lib.extend(lib_decls.iter().cloned());
            let mut decls = vec![import(lib_decls)];
            decls.extend(p.decls.iter().cloned());
            (
                format!("module Main\n\n{}{result}", join_decls(&decls)),
                Some(format!("module Lib\n\n{}", join_decls(&lib))),
            )
        }
        Layout::LibProducer { lib_decls } => {
            let mut lib = effect_decl(true);
            lib.extend(p.decls.iter().cloned());
            lib.extend(lib_decls.iter().cloned());
            let decls = vec![import(lib_decls)];
            (
                format!("module Main\n\n{}{result}", join_decls(&decls)),
                Some(format!("module Lib\n\n{}", join_decls(&lib))),
            )
        }
    };
    Ok(Program {
        main,
        lib,
        expected,
    })
}

// ---------------------------------------------------------------------------
// Parameterised-effect family
// ---------------------------------------------------------------------------
//
// `effect Fail e { fun fail : e -> Int }` used to make `Fail String` and
// `Fail Int` distinct effects that could sit in one row. An effect is now
// identified by its family alone and a row holds one application of it (see
// "Family-only effect identity" in the plan), so every case whose `body` has
// both in its row is rejected by the typechecker and listed as such. The
// cases are kept: the rest pin which single-application programs work. The
// runtime tag of an effect is its family name, so a handler installed by code
// that is generic in `e` goes in under the same tag as a concrete one.
//
// Case id is `param.<installer>.<route>.<instance>`:
//
// - *instance*: which `Fail` the function value under test performs. Called
//   `T` below; `O` is the other one.
// - *installer*: who handles `T`, and what else is installed around it.
// - *route*: how the function value reaches its call.
//
// Every handler resumes with its own number, so the result says which
// handler each `fail!` reached:
//
// | handler                                   | resumes with |
// |-------------------------------------------|--------------|
// | `text_fail`, concrete, for `Fail String`  | 100          |
// | `int_fail`, concrete, for `Fail Int`      | 2000         |
// | generic, the one that handles `T`         | 30000        |
// | generic, a second one that handles `O`    | 400000       |
//
// The function value itself contributes 1, and `catch_abort` returns 7
// without resuming.

const SHAPE: &str = "shape";
const PARAM: &str = "param";

/// Which `Fail` the function value performs.
///
/// | name      | function under test                             |
/// |-----------|-------------------------------------------------|
/// | `str`     | `String -> Int needs {Fail String}`             |
/// | `int`     | `Int -> Int needs {Fail Int}`                   |
/// | `gen_str` | `e -> Int needs {Fail e}`, used at `e = String` |
/// | `gen_int` | `e -> Int needs {Fail e}`, used at `e = Int`    |
///
/// For the generic instances every function on the route is generic in `e`
/// as well, so the argument stays unknown until `body`.
#[derive(Clone, Copy)]
struct Instance {
    name: &'static str,
    int: bool,
    generic: bool,
}

const fn instance(name: &'static str, int: bool, generic: bool) -> Instance {
    Instance { name, int, generic }
}

const PARAM_INSTANCES: &[Instance] = &[
    instance("str", false, false),
    instance("int", true, false),
    instance("gen_str", false, true),
    instance("gen_int", true, true),
];

/// Who installs the handlers. `body` makes the call under test; where its
/// row has both instantiations it also calls a helper that performs `O`.
///
/// | name                    | `result ()`                                               |
/// |-------------------------|-----------------------------------------------------------|
/// | `concrete`              | `body () with t`                                          |
/// | `both_t_first`          | `body () with {t, o}`                                     |
/// | `both_o_first`          | `body () with {o, t}`                                     |
/// | `nested_t_inner`        | `(body () with t) with o`                                 |
/// | `nested_t_outer`        | `(body () with o) with t`                                 |
/// | `generic`               | `catch_it body`                                           |
/// | `generic_abort`         | `catch_abort body`                                        |
/// | `generic_other_in_row`  | `catch_as T body with o`, `body` performs both            |
/// | `generic_other_outside` | `(catch_it body + other ()) with o`                       |
/// | `generic_same_outside`  | `(catch_it body + same ()) with t`                        |
/// | `generic_nested_in_row` | `catch_as O mid`, `mid = catch_as T body`, both in `body` |
/// | `generic_in_generic`    | `catch_as O mid`, `mid = catch_as T body + other ()`      |
/// | `concrete_in_generic`   | `catch_it mid`, `mid = body () with o`                    |
///
/// `catch_it : (Unit -> Int needs {Fail e, ..r}) -> Int needs {..r}`.
/// `catch_as` takes a value of type `e` first, to say which `Fail` it handles
/// when the row has both, and then the number to resume with.
const PARAM_INSTALLERS: &[&str] = &[
    "concrete",
    "both_t_first",
    "both_o_first",
    "nested_t_inner",
    "nested_t_outer",
    "generic",
    "generic_abort",
    "generic_other_in_row",
    "generic_other_outside",
    "generic_same_outside",
    "generic_nested_in_row",
    "generic_in_generic",
    "concrete_in_generic",
];

/// How the function value reaches its call inside `body`.
const PARAM_ROUTES: &[&str] = &[
    "direct",
    "lambda_arg",
    "named_arg",
    "let_named",
    "let_lambda",
    "open_fwd",
    "open_thunk",
    "list",
    "returned",
];

const CATCH_IT: &str = "fun catch_it : (Unit -> Int needs {Fail e, ..r}) -> Int needs {..r}\n\
                        catch_it f = f () with { fail _ = resume 30000 }";
const CATCH_ABORT: &str = "fun catch_abort : (Unit -> Int needs {Fail e, ..r}) -> Int needs {..r}\n\
                           catch_abort f = f () with { fail _ = 7 }";
const CATCH_AS: &str = "fun catch_as : e -> Int -> (Unit -> Int needs {Fail e, ..r}) -> Int needs {..r}\n\
                        catch_as _ v f = f () with { fail _ = resume v }";

/// The handler arrangement of one installer.
struct Install {
    /// `body` also performs `O`, so its row has both instantiations.
    body_has_other: bool,
    /// Type arguments of the concrete named handlers the program declares.
    handlers: Vec<&'static str>,
    decls: Vec<String>,
    result: String,
    expected: i64,
}

fn param_program(installer: &str, route: &str, inst: Instance) -> Program {
    let (t, o) = if inst.int {
        ("Int", "String")
    } else {
        ("String", "Int")
    };
    let lit = |ty: &str| if ty == "Int" { "3" } else { "\"s\"" };
    let handler = |ty: &str| if ty == "Int" { "int_fail" } else { "text_fail" };
    let resumed = |ty: &str| if ty == "Int" { 2000 } else { 100 };
    let (t_lit, o_lit) = (lit(t), lit(o));
    let (t_h, o_h) = (handler(t), handler(o));
    let (t_val, o_val) = (resumed(t), resumed(o));

    // The function value under test, and its type as the route spells it.
    let x = if inst.generic { "e" } else { t };
    let ty = format!("{x} -> Int needs {{Fail {x}}}");
    let lam = if inst.generic {
        "(fun x -> tgt x)"
    } else {
        "(fun x -> 1 + fail! x)"
    };
    let tgt = format!("fun tgt : {ty}\ntgt x = 1 + fail! x");

    let (route_decls, stmts, call): (Vec<String>, Vec<String>, String) = match route {
        "direct" => (vec![], vec![], format!("tgt {t_lit}")),
        "lambda_arg" | "named_arg" => {
            let f = if route == "lambda_arg" { lam } else { "tgt" };
            (
                vec![format!(
                    "fun apply_fn : ({ty}) -> {x} -> Int needs {{Fail {x}}}\napply_fn f x = f x"
                )],
                vec![],
                format!("apply_fn {f} {t_lit}"),
            )
        }
        "let_named" => (
            vec![],
            vec!["let f = tgt".to_string()],
            format!("f {t_lit}"),
        ),
        "let_lambda" => (vec![], vec![format!("let f = {lam}")], format!("f {t_lit}")),
        "open_fwd" => (
            vec![format!(
                "fun through : ({x} -> Int needs {{..r}}) -> {x} -> Int needs {{..r}}\n\
                 through f x = f x"
            )],
            vec![],
            format!("through tgt {t_lit}"),
        ),
        "open_thunk" => (
            vec![
                "fun through : (Unit -> Int needs {..r}) -> Int needs {..r}\nthrough f = f ()"
                    .to_string(),
            ],
            vec![],
            format!("through (fun () -> tgt {t_lit})"),
        ),
        "list" => (
            vec![format!(
                "fun run_list : List ({ty}) -> {x} -> Int needs {{Fail {x}}}\n\
                 run_list fs x = case fs {{\n  [] -> 0\n  f :: rest -> f x + run_list rest x\n}}"
            )],
            vec![],
            format!("run_list [tgt] {t_lit}"),
        ),
        "returned" => (
            vec![format!("fun make : Unit -> ({ty})\nmake () = tgt")],
            vec![],
            format!("(make ()) {t_lit}"),
        ),
        other => panic!("unknown route {other}"),
    };

    let other = format!("fun other : Unit -> Int needs {{Fail {o}}}\nother () = fail! {o_lit}");
    let same = format!("fun same : Unit -> Int needs {{Fail {t}}}\nsame () = fail! {t_lit}");
    let mid = |handled_outside: &str, expr: &str| {
        format!("fun mid : Unit -> Int needs {{Fail {handled_outside}}}\nmid () = {expr}")
    };
    let install = |body_has_other: bool,
                   handlers: &[&'static str],
                   decls: Vec<String>,
                   result: String,
                   expected: i64| Install {
        body_has_other,
        handlers: handlers.to_vec(),
        decls,
        result,
        expected,
    };
    let i = match installer {
        "concrete" => install(
            false,
            &[t],
            vec![],
            format!("(body ()) with {t_h}"),
            1 + t_val,
        ),
        "both_t_first" => install(
            true,
            &[t, o],
            vec![],
            format!("(body ()) with {{{t_h}, {o_h}}}"),
            1 + t_val + o_val,
        ),
        "both_o_first" => install(
            true,
            &[t, o],
            vec![],
            format!("(body ()) with {{{o_h}, {t_h}}}"),
            1 + t_val + o_val,
        ),
        "nested_t_inner" => install(
            true,
            &[t, o],
            vec![],
            format!("((body ()) with {t_h}) with {o_h}"),
            1 + t_val + o_val,
        ),
        "nested_t_outer" => install(
            true,
            &[t, o],
            vec![],
            format!("((body ()) with {o_h}) with {t_h}"),
            1 + t_val + o_val,
        ),
        "generic" => install(
            false,
            &[],
            vec![CATCH_IT.to_string()],
            "catch_it body".to_string(),
            1 + 30000,
        ),
        "generic_abort" => install(
            false,
            &[],
            vec![CATCH_ABORT.to_string()],
            "catch_abort body".to_string(),
            7,
        ),
        "generic_other_in_row" => install(
            true,
            &[o],
            vec![CATCH_AS.to_string()],
            format!("(catch_as {t_lit} 30000 body) with {o_h}"),
            1 + 30000 + o_val,
        ),
        "generic_other_outside" => install(
            false,
            &[o],
            vec![CATCH_IT.to_string(), other.clone()],
            format!("(catch_it body + other ()) with {o_h}"),
            1 + 30000 + o_val,
        ),
        "generic_same_outside" => install(
            false,
            &[t],
            vec![CATCH_IT.to_string(), same],
            format!("(catch_it body + same ()) with {t_h}"),
            1 + 30000 + t_val,
        ),
        "generic_nested_in_row" => install(
            true,
            &[],
            vec![
                CATCH_AS.to_string(),
                mid(o, &format!("catch_as {t_lit} 30000 body")),
            ],
            format!("catch_as {o_lit} 400000 mid"),
            1 + 30000 + 400000,
        ),
        "generic_in_generic" => install(
            false,
            &[],
            vec![
                CATCH_AS.to_string(),
                other.clone(),
                mid(o, &format!("catch_as {t_lit} 30000 body + other ()")),
            ],
            format!("catch_as {o_lit} 400000 mid"),
            1 + 30000 + 400000,
        ),
        "concrete_in_generic" => install(
            true,
            &[o],
            vec![
                CATCH_IT.to_string(),
                mid(t, &format!("(body ()) with {o_h}")),
            ],
            "catch_it mid".to_string(),
            1 + 30000 + o_val,
        ),
        other => panic!("unknown installer {other}"),
    };

    let mut decls = vec!["effect Fail e { fun fail : e -> Int }".to_string()];
    for ty in ["String", "Int"] {
        if i.handlers.contains(&ty) {
            decls.push(format!(
                "handler {} for Fail {ty} {{ fail _ = resume {} }}",
                handler(ty),
                resumed(ty)
            ));
        }
    }
    decls.push(tgt);
    decls.extend(route_decls);
    let (row, tail) = if i.body_has_other {
        decls.push(other);
        ("Fail String, Fail Int".to_string(), " + other ()")
    } else {
        (format!("Fail {t}"), "")
    };
    let mut body = format!("fun body : Unit -> Int needs {{{row}}}\nbody () = {{\n");
    for stmt in &stmts {
        body.push_str(&format!("  {stmt}\n"));
    }
    body.push_str(&format!("  {call}{tail}\n}}"));
    decls.push(body);
    decls.extend(i.decls);

    Program {
        main: format!(
            "module Main\n\n{}pub fun result : Unit -> Int\nresult () = {}\n",
            join_decls(&decls),
            i.result
        ),
        lib: None,
        expected: i.expected,
    }
}

fn generate() -> Vec<Case> {
    let mut cases = Vec::new();
    for producer in PRODUCERS {
        for position in POSITIONS {
            for v in VARIANTS {
                cases.push(Case {
                    id: format!("{producer}.{position}.{}", v.name),
                    family: SHAPE,
                    producer,
                    position,
                    variant: v.name,
                    program: build_program(producer, position, *v),
                });
            }
        }
    }
    for installer in PARAM_INSTALLERS {
        for route in PARAM_ROUTES {
            for inst in PARAM_INSTANCES {
                cases.push(Case {
                    id: format!("param.{installer}.{route}.{}", inst.name),
                    family: PARAM,
                    producer: installer,
                    position: route,
                    variant: inst.name,
                    program: Ok(param_program(installer, route, *inst)),
                });
            }
        }
    }
    cases
}

// ---------------------------------------------------------------------------
// Running
// ---------------------------------------------------------------------------

#[derive(Clone, Debug)]
enum Outcome {
    Pass,
    /// Failure class and a one-line detail.
    Fail(String, String),
    /// The generator does not produce this combination.
    NotApplicable(String),
    /// The typechecker rejected the program.
    Rejected(String),
    /// The generator emitted something that does not lex or parse.
    GeneratorBug(String),
}

/// A case that got through the Rust side and is waiting for the BEAM.
struct Compiled {
    index: usize,
    out_dir: PathBuf,
    modules: Vec<&'static str>,
}

fn one_line(s: &str) -> String {
    let flat: String = s
        .chars()
        .map(|c| if c == '\n' || c == '\t' { ' ' } else { c })
        .collect();
    let mut out: String = flat.chars().take(400).collect();
    if flat.chars().count() > 400 {
        out.push_str("...");
    }
    out
}

/// Typecheck and emit one case. `Ok` means its `.core` files are on disk.
fn compile_case(index: usize, program: &Program, work: &Path) -> Result<Compiled, Outcome> {
    let root = work.join(format!("case_{index}_root"));
    let out_dir = work.join(format!("case_{index}_out"));
    std::fs::create_dir_all(&root).unwrap();
    std::fs::create_dir_all(&out_dir).unwrap();
    std::fs::write(root.join("project.toml"), "[project]\nname=\"matrix\"\n").unwrap();
    if let Some(lib) = &program.lib {
        std::fs::create_dir_all(root.join("lib")).unwrap();
        std::fs::write(root.join("lib/Lib.saga"), lib).unwrap();
    }

    let compiled = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut checker = make_checker(root.clone());
        let main_program = match try_typecheck_source(&program.main, &mut checker) {
            Ok(p) => p,
            Err(e @ FrontendError::Typecheck(_)) => return Err(Outcome::Rejected(e.to_string())),
            Err(e) => return Err(Outcome::GeneratorBug(e.to_string())),
        };
        let mut modules = Vec::new();
        if program.lib.is_some() {
            let result = checker.to_result();
            let Some(lib_program) = result.programs().get("Lib") else {
                return Err(Outcome::GeneratorBug(
                    "checker did not load module Lib".to_string(),
                ));
            };
            let core = emit_program(lib_program, "lib", &checker, None);
            std::fs::write(out_dir.join("lib.core"), core).unwrap();
            modules.push("lib");
        }
        let core = emit_program(&main_program, "main", &checker, Some("main"));
        std::fs::write(out_dir.join("main.core"), core).unwrap();
        modules.push("main");
        Ok(modules)
    }));
    let _ = std::fs::remove_dir_all(&root);
    match compiled {
        Ok(Ok(modules)) => Ok(Compiled {
            index,
            out_dir,
            modules,
        }),
        Ok(Err(outcome)) => Err(outcome),
        Err(payload) => Err(Outcome::Fail(
            "compiler-panic".to_string(),
            one_line(&panic_message(payload)),
        )),
    }
}

/// Erlang side of the harness. Compiles each case's `.core` files in-process
/// (what `erlc` does for a `.core` input), loads them, calls
/// `main:result(unit)` in a fresh process, prints one line per case, then
/// unloads. One BEAM start per batch instead of two per case.
///
/// A case that has not returned after 5 seconds is killed and reported as
/// `timeout`; the batch carries on. The `@@S` line marks the case in
/// progress, so a batch that has to be killed from outside can be attributed.
const DRIVER: &str = r#"-module(matrix_driver).
-export([main/1]).

main([Manifest]) ->
    {ok, Cases} = file:consult(Manifest),
    lists:foreach(fun run_case/1, Cases),
    erlang:halt(0).

run_case({Id, Dir, Mods}) ->
    io:format("@@S\t~s~n", [Id]),
    Line = case load_all(Dir, Mods) of
        ok -> run_result();
        {error, Msg} -> ["erlc\t", clean(Msg)]
    end,
    io:format("@@\t~s\t~s~n", [Id, Line]),
    lists:foreach(fun unload/1, Mods).

load_all(_Dir, []) -> ok;
load_all(Dir, [M | Rest]) ->
    Path = filename:join(Dir, atom_to_list(M) ++ ".core"),
    Compiled = try compile:file(Path, [from_core, binary, return_errors])
               catch C:E -> {crash, C, E} end,
    case Compiled of
        {ok, Mod, Bin} ->
            case code:load_binary(Mod, Path, Bin) of
                {module, Mod} -> load_all(Dir, Rest);
                Other -> {error, io_lib:format("load failed: ~0p", [Other])}
            end;
        {error, Errors, _Warnings} -> {error, format_errors(Errors)};
        Other -> {error, io_lib:format("~0P", [Other, 30])}
    end.

format_errors(Errors) ->
    try
        [[io_lib:format("~s: ", [filename:basename(File)]), Mod:format_error(Desc), "; "]
         || {File, Infos} <- Errors, {_Loc, Mod, Desc} <- Infos]
    catch _:_ -> io_lib:format("~0P", [Errors, 30])
    end.

unload(M) ->
    code:purge(M),
    code:delete(M),
    code:purge(M).

run_result() ->
    {Pid, Ref} = spawn_monitor(fun() ->
        R = try main:result(unit) of
                V -> {ok, V}
            catch Class:Reason:Stack -> {crash, Class, Reason, Stack}
            end,
        exit({matrix_result, R})
    end),
    receive
        {'DOWN', Ref, process, Pid, {matrix_result, {ok, V}}} ->
            ["ok\t", clean(io_lib:format("~0P", [V, 20]))];
        {'DOWN', Ref, process, Pid, {matrix_result, {crash, Class, Reason, Stack}}} ->
            Top = case Stack of [F | _] -> F; _ -> none end,
            [class(Reason), "\t",
             clean(io_lib:format("~p:~0P at ~0P", [Class, Reason, 12, Top, 12]))];
        {'DOWN', Ref, process, Pid, Other} ->
            ["process-exit\t", clean(io_lib:format("~0P", [Other, 12]))]
    after 5000 ->
        exit(Pid, kill),
        receive {'DOWN', Ref, process, Pid, _} -> ok end,
        "timeout\tmain:result(unit) did not return within 5s"
    end.

class({badarity, _}) -> "badarity";
class(badfun) -> "badfun";
class({badfun, _}) -> "badfun";
class(A) when is_atom(A) -> atom_to_list(A);
class(T) when is_tuple(T), tuple_size(T) > 0, is_atom(element(1, T)) ->
    atom_to_list(element(1, T));
class(_) -> "runtime-error".

clean(IoList) ->
    [case C of $\n -> $\s; $\t -> $\s; _ -> C end
     || C <- lists:flatten(io_lib:format("~ts", [IoList]))].
"#;

fn build_driver(work: &Path) -> PathBuf {
    let dir = work.join("driver");
    std::fs::create_dir_all(&dir).unwrap();
    let src = dir.join("matrix_driver.erl");
    std::fs::write(&src, DRIVER).unwrap();
    let output = run_bounded(
        std::process::Command::new("erlc")
            .arg("-o")
            .arg(&dir)
            .arg(&src),
        SUBPROCESS_LIMIT,
    )
    .expect("failed to run erlc on the matrix driver");
    assert!(
        output.status.success(),
        "erlc failed on the matrix driver:\n{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    dir
}

/// What each worker is doing right now, for the watchdog's message.
static PROGRESS: Mutex<BTreeMap<String, String>> = Mutex::new(BTreeMap::new());

fn set_progress(worker: &str, what: Option<String>) {
    let mut progress = PROGRESS.lock().unwrap();
    match what {
        Some(what) => progress.insert(worker.to_string(), what),
        None => progress.remove(worker),
    };
}

/// Seconds the whole matrix may take before the watchdog aborts the test.
/// A normal run is about a minute.
fn overall_limit() -> Duration {
    let secs = std::env::var("SAGA_MATRIX_DEADLINE_SECS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(300);
    Duration::from_secs(secs)
}

/// Abort the test process if the matrix is still running at the overall
/// limit. Compilation runs in-process and cannot be cancelled, so this is
/// the only bound that holds against a hang in the compiler or in this
/// harness. Children are killed first so no `beam.smp` is left behind.
fn start_watchdog(limit: Duration) -> Arc<AtomicBool> {
    let done = Arc::new(AtomicBool::new(false));
    let flag = done.clone();
    let started = Instant::now();
    std::thread::spawn(move || {
        while !flag.load(Ordering::Relaxed) {
            if started.elapsed() >= limit {
                let progress = PROGRESS.lock().map(|p| p.clone()).unwrap_or_default();
                let mut stderr = std::io::stderr();
                let _ = writeln!(
                    stderr,
                    "\nfunction_shape_matrix: still running after {}s; aborting.\n\
                     Raise the limit with SAGA_MATRIX_DEADLINE_SECS if the machine is just slow.\n\
                     In progress:",
                    limit.as_secs()
                );
                for (worker, what) in &progress {
                    let _ = writeln!(stderr, "  {worker}: {what}");
                }
                if progress.is_empty() {
                    let _ = writeln!(
                        stderr,
                        "  (nothing registered; the harness itself is stuck)"
                    );
                }
                kill_live_children();
                std::process::exit(124);
            }
            std::thread::sleep(Duration::from_millis(100));
        }
    });
    done
}

/// Run one batch of compiled cases in a single BEAM. Returns
/// `(case index, class, detail)`; class `ok` carries the printed value.
fn run_batch(
    batch_no: usize,
    batch: &[&Compiled],
    cases: &[Case],
    driver_dir: &Path,
    work: &Path,
) -> Vec<(usize, String, String)> {
    let mut manifest = String::new();
    for c in batch {
        manifest.push_str(&format!(
            "{{\"{}\", {:?}, [{}]}}.\n",
            c.index,
            c.out_dir.to_str().expect("utf-8 temp path"),
            c.modules.join(", ")
        ));
    }
    let manifest_path = work.join(format!("manifest_{batch_no}.term"));
    std::fs::write(&manifest_path, manifest).unwrap();

    // The driver bounds each case at 5s. This bounds the BEAM itself, in
    // case it gets stuck somewhere the driver cannot interrupt.
    let limit = Duration::from_secs(30 + 6 * batch.len() as u64);
    let worker = format!("erl batch {batch_no}");
    let started: Mutex<Option<usize>> = Mutex::new(None);
    let on_line = |line: &str| {
        if let Some(index) = line
            .strip_prefix("@@S\t")
            .and_then(|i| i.parse::<usize>().ok())
        {
            *started.lock().unwrap() = Some(index);
            set_progress(&worker, Some(format!("running {}", cases[index].id)));
        }
    };
    set_progress(&worker, Some("starting erl".to_string()));
    let output = run_bounded_streaming(
        std::process::Command::new("erl")
            .arg("-noshell")
            .arg("-pa")
            .arg(stdlib_dir())
            .arg("-pa")
            .arg(driver_dir)
            .arg("-run")
            .arg("matrix_driver")
            .arg("main")
            .arg(&manifest_path),
        limit,
        &on_line,
    )
    .expect("failed to start erl");
    set_progress(&worker, None);

    let mut results = Vec::new();
    for line in output.stdout.lines() {
        let mut parts = line.splitn(4, '\t');
        if parts.next() != Some("@@") {
            continue;
        }
        let (Some(index), Some(class)) = (parts.next(), parts.next()) else {
            continue;
        };
        let Ok(index) = index.parse::<usize>() else {
            continue;
        };
        results.push((
            index,
            class.to_string(),
            parts.next().unwrap_or("").to_string(),
        ));
    }
    let seen: BTreeSet<usize> = results.iter().map(|r| r.0).collect();
    let in_progress = *started.lock().unwrap();
    for c in batch {
        if seen.contains(&c.index) {
            continue;
        }
        if output.timed_out && in_progress == Some(c.index) {
            results.push((
                c.index,
                "timeout".to_string(),
                format!(
                    "erl was killed at the {}s batch limit while this case was running",
                    limit.as_secs()
                ),
            ));
        } else {
            results.push((
                c.index,
                "no-result".to_string(),
                one_line(&format!(
                    "erl stopped ({}) before reaching this case; stderr: {}",
                    match output.status {
                        Some(status) => status.to_string(),
                        None => "killed at the batch limit".to_string(),
                    },
                    output.stderr
                )),
            ));
        }
    }
    results
}

const COMPILE_THREAD: &str = "matrix-compile";

/// Compiler panics on the compile workers are results, not test failures;
/// keep their messages out of the output. Installed once and scoped by
/// thread name, so panics anywhere else (including this test's own
/// assertions) still print.
fn quiet_compile_worker_panics() {
    static INSTALL: std::sync::Once = std::sync::Once::new();
    INSTALL.call_once(|| {
        let previous = std::panic::take_hook();
        std::panic::set_hook(Box::new(move |info| {
            if std::thread::current().name() != Some(COMPILE_THREAD) {
                previous(info);
            }
        }));
    });
}

fn worker_count() -> usize {
    std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(4)
        .clamp(1, 12)
}

fn run_cases(cases: &[Case], selected: &[usize]) -> BTreeMap<usize, Outcome> {
    let work = std::env::temp_dir().join(format!(
        "saga_shape_matrix_{}_{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("clock before epoch")
            .as_nanos()
    ));
    std::fs::create_dir_all(&work).unwrap();
    let watchdog_done = start_watchdog(overall_limit());
    // Build the stdlib before silencing panics, so a failure there is loud.
    let setup = format!("setup {:?}", std::thread::current().id());
    set_progress(
        &setup,
        Some("building the stdlib and the erl driver".to_string()),
    );
    let _ = stdlib_dir();
    let driver_dir = build_driver(&work);
    set_progress(&setup, None);

    let outcomes: Mutex<BTreeMap<usize, Outcome>> = Mutex::new(BTreeMap::new());
    let compiled: Mutex<Vec<Compiled>> = Mutex::new(Vec::new());
    let next = AtomicUsize::new(0);
    let workers = worker_count();

    quiet_compile_worker_panics();
    std::thread::scope(|scope| {
        for worker_no in 0..workers {
            let (next, outcomes, compiled, work) = (&next, &outcomes, &compiled, &work);
            let builder = std::thread::Builder::new().name(COMPILE_THREAD.to_string());
            let spawned = builder.spawn_scoped(scope, move || {
                let worker = format!("compile worker {worker_no}");
                loop {
                    let slot = next.fetch_add(1, Ordering::Relaxed);
                    let Some(&index) = selected.get(slot) else {
                        break;
                    };
                    set_progress(&worker, Some(format!("compiling {}", cases[index].id)));
                    match &cases[index].program {
                        Err(reason) => {
                            outcomes
                                .lock()
                                .unwrap()
                                .insert(index, Outcome::NotApplicable(reason.to_string()));
                        }
                        Ok(program) => match compile_case(index, program, work) {
                            Ok(c) => compiled.lock().unwrap().push(c),
                            Err(outcome) => {
                                outcomes.lock().unwrap().insert(index, outcome);
                            }
                        },
                    }
                }
                set_progress(&worker, None);
            });
            spawned.expect("spawn compile worker");
        }
    });

    let mut compiled = compiled.into_inner().unwrap();
    compiled.sort_by_key(|c| c.index);
    let mut batches: Vec<Vec<&Compiled>> = (0..workers).map(|_| Vec::new()).collect();
    for (i, c) in compiled.iter().enumerate() {
        batches[i % workers].push(c);
    }
    std::thread::scope(|scope| {
        for (batch_no, batch) in batches.iter().enumerate() {
            if batch.is_empty() {
                continue;
            }
            let outcomes = &outcomes;
            let driver_dir = &driver_dir;
            let work = &work;
            scope.spawn(move || {
                for (index, class, detail) in run_batch(batch_no, batch, cases, driver_dir, work) {
                    let expected = cases[index]
                        .program
                        .as_ref()
                        .map(|p| p.expected)
                        .unwrap_or_default();
                    let outcome = if class != "ok" {
                        Outcome::Fail(class, detail)
                    } else if detail.trim() == expected.to_string() {
                        Outcome::Pass
                    } else {
                        Outcome::Fail(
                            "wrong-value".to_string(),
                            format!("expected {expected}, got {}", detail.trim()),
                        )
                    };
                    outcomes.lock().unwrap().insert(index, outcome);
                }
            });
        }
    });

    watchdog_done.store(true, Ordering::Relaxed);
    let _ = std::fs::remove_dir_all(&work);
    outcomes.into_inner().unwrap()
}

// ---------------------------------------------------------------------------
// Reporting
// ---------------------------------------------------------------------------

#[derive(Default, Clone, Copy)]
struct Tally {
    total: usize,
    pass: usize,
    fail: usize,
    rejected: usize,
    not_applicable: usize,
}

impl Tally {
    fn add(&mut self, outcome: &Outcome) {
        self.total += 1;
        match outcome {
            Outcome::Pass => self.pass += 1,
            Outcome::Fail(..) | Outcome::GeneratorBug(_) => self.fail += 1,
            Outcome::Rejected(_) => self.rejected += 1,
            Outcome::NotApplicable(_) => self.not_applicable += 1,
        }
    }
}

fn tally_table(
    title: &str,
    family: &str,
    order: &[&str],
    key: impl Fn(&Case) -> &'static str,
    cases: &[Case],
    outcomes: &BTreeMap<usize, Outcome>,
) -> String {
    let mut tallies: BTreeMap<&str, Tally> = BTreeMap::new();
    for (index, outcome) in outcomes {
        let case = &cases[*index];
        if case.family == family {
            tallies.entry(key(case)).or_default().add(outcome);
        }
    }
    let mut out = format!(
        "{title:<28} {:>5} {:>5} {:>5} {:>9} {:>5}\n",
        "run", "pass", "fail", "rejected", "n/a"
    );
    for name in order {
        let Some(t) = tallies.get(name) else { continue };
        out.push_str(&format!(
            "  {name:<26} {:>5} {:>5} {:>5} {:>9} {:>5}\n",
            t.pass + t.fail,
            t.pass,
            t.fail,
            t.rejected,
            t.not_applicable
        ));
    }
    out
}

/// Totals and failure classes for one family.
fn family_totals(family: &str, cases: &[Case], outcomes: &BTreeMap<usize, Outcome>) -> String {
    let mut all = Tally::default();
    let mut classes: BTreeMap<&str, usize> = BTreeMap::new();
    for (index, outcome) in outcomes {
        if cases[*index].family != family {
            continue;
        }
        all.add(outcome);
        match outcome {
            Outcome::Fail(class, _) => *classes.entry(class.as_str()).or_default() += 1,
            Outcome::GeneratorBug(_) => *classes.entry("generator-bug").or_default() += 1,
            _ => {}
        }
    }
    let mut out = format!(
        "  considered {}: ran {} (passed {}, failed {}), skipped {} (typecheck-rejected {}, not applicable {})\n",
        all.total,
        all.pass + all.fail,
        all.pass,
        all.fail,
        all.rejected + all.not_applicable,
        all.rejected,
        all.not_applicable
    );
    out.push_str("  failures by class:");
    if classes.is_empty() {
        out.push_str(" none");
    }
    for (class, n) in &classes {
        out.push_str(&format!(" {class}={n}"));
    }
    out.push_str("\n\n");
    out
}

fn summary(cases: &[Case], outcomes: &BTreeMap<usize, Outcome>) -> String {
    let mut out = String::new();
    out.push_str(&format!(
        "function shape matrix: {} producers x {} positions x {} variants = {} combinations\n",
        PRODUCERS.len(),
        POSITIONS.len(),
        VARIANTS.len(),
        PRODUCERS.len() * POSITIONS.len() * VARIANTS.len()
    ));
    out.push_str(&family_totals(SHAPE, cases, outcomes));
    out.push_str(&tally_table(
        "by producer",
        SHAPE,
        PRODUCERS,
        |c| c.producer,
        cases,
        outcomes,
    ));
    out.push('\n');
    out.push_str(&tally_table(
        "by position",
        SHAPE,
        POSITIONS,
        |c| c.position,
        cases,
        outcomes,
    ));
    out.push('\n');
    let variant_names: Vec<&str> = VARIANTS.iter().map(|v| v.name).collect();
    out.push_str(&tally_table(
        "by variant",
        SHAPE,
        &variant_names,
        |c| c.variant,
        cases,
        outcomes,
    ));

    out.push_str(&format!(
        "\nparameterised effects: {} installers x {} routes x {} instances = {} combinations\n",
        PARAM_INSTALLERS.len(),
        PARAM_ROUTES.len(),
        PARAM_INSTANCES.len(),
        PARAM_INSTALLERS.len() * PARAM_ROUTES.len() * PARAM_INSTANCES.len()
    ));
    out.push_str(&family_totals(PARAM, cases, outcomes));
    out.push_str(&tally_table(
        "by installer",
        PARAM,
        PARAM_INSTALLERS,
        |c| c.producer,
        cases,
        outcomes,
    ));
    out.push('\n');
    out.push_str(&tally_table(
        "by route",
        PARAM,
        PARAM_ROUTES,
        |c| c.position,
        cases,
        outcomes,
    ));
    out.push('\n');
    let instance_names: Vec<&str> = PARAM_INSTANCES.iter().map(|i| i.name).collect();
    out.push_str(&tally_table(
        "by instance",
        PARAM,
        &instance_names,
        |c| c.variant,
        cases,
        outcomes,
    ));
    out
}

/// One row per producer, one column per position, one character per
/// variant. Goes in the report file; too wide for the terminal summary.
fn grid(cases: &[Case], outcomes: &BTreeMap<usize, Outcome>) -> String {
    let mut cells: BTreeMap<(&str, &str, &str), char> = BTreeMap::new();
    for (index, outcome) in outcomes {
        let case = &cases[*index];
        if case.family != SHAPE {
            continue;
        }
        let mark = match outcome {
            Outcome::Pass => '.',
            Outcome::NotApplicable(_) => ' ',
            Outcome::Rejected(_) => 'r',
            Outcome::GeneratorBug(_) => '!',
            Outcome::Fail(class, _) => match class.as_str() {
                "badarity" => 'A',
                "compiler-panic" => 'P',
                "erlc" => 'E',
                "wrong-value" => 'W',
                "timeout" => 'T',
                _ => 'X',
            },
        };
        cells.insert((case.producer, case.position, case.variant), mark);
    }
    let mut out = String::from(
        "grid: each cell is the variants in the order p1 e1 p2 e2 pu eu\n\
         . pass   A badarity   P compiler-panic   E erlc   W wrong-value   T timeout   X other failure\n\
         r typecheck-rejected   blank not applicable\n\ncolumns:\n",
    );
    for (i, position) in POSITIONS.iter().enumerate() {
        out.push_str(&format!("  {:>2} {position}\n", i + 1));
    }
    out.push_str(&format!("\n{:<28}", ""));
    for i in 0..POSITIONS.len() {
        out.push_str(&format!("{:<7}", i + 1));
    }
    out.push('\n');
    for producer in PRODUCERS {
        if !cells.keys().any(|(p, _, _)| p == producer) {
            continue;
        }
        out.push_str(&format!("{producer:<28}"));
        for position in POSITIONS {
            for v in VARIANTS {
                out.push(*cells.get(&(*producer, *position, v.name)).unwrap_or(&' '));
            }
            out.push(' ');
        }
        out.push('\n');
    }
    out
}

fn detailed_report(cases: &[Case], outcomes: &BTreeMap<usize, Outcome>) -> String {
    let mut out = String::new();
    for (index, outcome) in outcomes {
        let id = &cases[*index].id;
        let line = match outcome {
            Outcome::Pass => format!("{id}\tpass"),
            Outcome::Fail(class, detail) => format!("{id}\tFAIL\t{class}\t{detail}"),
            Outcome::NotApplicable(reason) => format!("{id}\tskip\t{reason}"),
            Outcome::Rejected(reason) => format!("{id}\tskip\trejected\t{}", one_line(reason)),
            Outcome::GeneratorBug(reason) => {
                format!("{id}\tFAIL\tgenerator-bug\t{}", one_line(reason))
            }
        };
        out.push_str(&line);
        out.push('\n');
    }
    out
}

/// Write the generated programs to `dir` for running by hand. A `main` that
/// prints `result ()` is appended, so `saga run` works on them; the programs
/// the matrix itself compiles do not have it.
fn dump_programs(dir: &Path, cases: &[Case], selected: &[usize]) {
    for &index in selected {
        let case = &cases[index];
        let Ok(program) = &case.program else { continue };
        let main = format!(
            "{}\n# expected: {}\nmain () = dbg (result ())\n",
            program.main, program.expected
        );
        match &program.lib {
            None => {
                std::fs::create_dir_all(dir).unwrap();
                std::fs::write(dir.join(format!("{}.saga", case.id)), main).unwrap();
            }
            Some(lib) => {
                let project = dir.join(&case.id);
                std::fs::create_dir_all(project.join("src")).unwrap();
                std::fs::write(project.join("project.toml"), "[project]\nname=\"matrix\"\n")
                    .unwrap();
                std::fs::write(project.join("src/Main.saga"), main).unwrap();
                std::fs::write(project.join("src/Lib.saga"), lib).unwrap();
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Fixture files
// ---------------------------------------------------------------------------

fn repo_path(rel: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(rel)
}

/// Parse `<case id> [<class>]` lines, ignoring blanks and `#` comments.
fn read_list(rel: &str) -> BTreeMap<String, String> {
    let text = std::fs::read_to_string(repo_path(rel)).unwrap_or_default();
    let mut out = BTreeMap::new();
    for line in text.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let mut parts = line.split_whitespace();
        let id = parts.next().unwrap().to_string();
        out.insert(id, parts.next().unwrap_or("").to_string());
    }
    out
}

fn write_list(rel: &str, header: &str, entries: &BTreeMap<String, String>) {
    let mut text = String::new();
    for line in header.lines() {
        text.push_str(&format!("# {line}\n"));
    }
    for (id, class) in entries {
        if class.is_empty() {
            text.push_str(&format!("{id}\n"));
        } else {
            text.push_str(&format!("{id} {class}\n"));
        }
    }
    std::fs::write(repo_path(rel), text).unwrap();
}

const FAILURES_HEADER: &str = "Cases of tests/function_shape_matrix.rs that fail today: `<case id> <failure class>`.\n\
Case id is `<producer>.<position>.<variant>`, or `param.<installer>.<route>.<instance>`.\n\
Generated. Regenerate with `SAGA_MATRIX_BLESS=1 cargo test --test function_shape_matrix`.";

const REJECTED_HEADER: &str = "Cases of tests/function_shape_matrix.rs that the typechecker rejects. They are skipped.\n\
Generated. Regenerate with `SAGA_MATRIX_BLESS=1 cargo test --test function_shape_matrix`.";

/// Lines describing how `actual` differs from the checked-in `expected`.
fn diff_lists(
    what: &str,
    expected: &BTreeMap<String, String>,
    actual: &BTreeMap<String, String>,
    new_msg: &str,
    gone_msg: &str,
) -> Vec<String> {
    let mut out = Vec::new();
    for (id, class) in actual {
        match expected.get(id) {
            None => out.push(format!("{new_msg}: {id} ({class})")),
            Some(old) if old != class => {
                out.push(format!("{what} changed class: {id} ({old} -> {class})"))
            }
            Some(_) => {}
        }
    }
    for id in expected.keys() {
        if !actual.contains_key(id) {
            out.push(format!("{gone_msg}: {id}"));
        }
    }
    out
}

// ---------------------------------------------------------------------------
// The test
// ---------------------------------------------------------------------------

#[test]
fn function_shape_matrix() {
    let cases = generate();
    let filter = std::env::var("SAGA_MATRIX_FILTER").ok();
    let selected: Vec<usize> = cases
        .iter()
        .enumerate()
        .filter(|(_, c)| match &filter {
            Some(f) => f.split(',').any(|part| c.id.contains(part.trim())),
            None => true,
        })
        .map(|(i, _)| i)
        .collect();

    if let Ok(dir) = std::env::var("SAGA_MATRIX_DUMP") {
        dump_programs(Path::new(&dir), &cases, &selected);
    }

    let started = std::time::Instant::now();
    let outcomes = run_cases(&cases, &selected);
    assert_eq!(
        outcomes.len(),
        selected.len(),
        "every selected case must have an outcome"
    );

    let report = detailed_report(&cases, &outcomes);
    let mut text = summary(&cases, &outcomes);
    text.push_str(&format!(
        "\n  elapsed: {:.1}s\n",
        started.elapsed().as_secs_f64()
    ));
    let report_path =
        Path::new(env!("CARGO_TARGET_TMPDIR")).join("function_shape_matrix_report.txt");
    let _ = std::fs::write(
        &report_path,
        format!("{text}\n{}\n{report}", grid(&cases, &outcomes)),
    );
    text.push_str(&format!("  full report: {}\n", report_path.display()));

    // Written straight to stdout so the summary shows without `--nocapture`.
    let mut stdout = std::io::stdout();
    let _ = writeln!(stdout, "\n{text}");

    let generator_bugs: Vec<String> = outcomes
        .iter()
        .filter_map(|(i, o)| match o {
            Outcome::GeneratorBug(reason) => Some(format!("{}: {reason}", cases[*i].id)),
            _ => None,
        })
        .collect();
    assert!(
        generator_bugs.is_empty(),
        "the generator produced programs that do not parse:\n{}",
        generator_bugs.join("\n")
    );

    if filter.is_some() {
        let _ = writeln!(stdout, "{report}");
        let _ = writeln!(
            stdout,
            "SAGA_MATRIX_FILTER is set: not comparing against the fixture files."
        );
        return;
    }

    let mut failing = BTreeMap::new();
    let mut rejected = BTreeMap::new();
    for (index, outcome) in &outcomes {
        let id = cases[*index].id.clone();
        match outcome {
            Outcome::Fail(class, _) => {
                failing.insert(id, class.clone());
            }
            Outcome::Rejected(_) => {
                rejected.insert(id, String::new());
            }
            _ => {}
        }
    }

    if std::env::var("SAGA_MATRIX_BLESS").is_ok_and(|v| !v.is_empty() && v != "0") {
        write_list(EXPECTED_FAILURES_FILE, FAILURES_HEADER, &failing);
        write_list(TYPECHECK_REJECTED_FILE, REJECTED_HEADER, &rejected);
        let _ = writeln!(
            stdout,
            "blessed: {} expected failures, {} typecheck-rejected",
            failing.len(),
            rejected.len()
        );
        return;
    }

    let mut problems = diff_lists(
        "expected failure",
        &read_list(EXPECTED_FAILURES_FILE),
        &failing,
        "REGRESSION, case fails but is not an expected failure",
        "FIXED, case no longer fails; remove it from the expected-failures file",
    );
    problems.extend(diff_lists(
        "typecheck rejection",
        &read_list(TYPECHECK_REJECTED_FILE),
        &rejected,
        "case is now rejected by the typechecker",
        "case is no longer rejected by the typechecker",
    ));
    assert!(
        problems.is_empty(),
        "function shape matrix differs from the checked-in lists ({} differences).\n\
         Details for each case are in {}.\n\
         If the change is intended, rerun with SAGA_MATRIX_BLESS=1 and commit the fixture files.\n\n{}",
        problems.len(),
        report_path.display(),
        problems.join("\n")
    );
}

// ---------------------------------------------------------------------------
// Harness self-tests
// ---------------------------------------------------------------------------

/// A compiled program that never returns is killed and classed `timeout`,
/// and the cases after it in the same batch still run.
#[test]
fn nonterminating_program_is_reported_as_timeout() {
    let program = |body: &str| Program {
        main: format!("module Main\n\n{body}"),
        lib: None,
        expected: 7,
    };
    let case = |id: &str, body: &str| Case {
        id: id.to_string(),
        family: SHAPE,
        producer: "self_test",
        position: "self_test",
        variant: "p1",
        program: Ok(program(body)),
    };
    let cases = vec![
        case(
            "self_test.spin",
            "fun spin : Int -> Int\nspin n = spin (n + 1)\n\n\
             pub fun result : Unit -> Int\nresult () = spin 0\n",
        ),
        case(
            "self_test.seven",
            "pub fun result : Unit -> Int\nresult () = 7\n",
        ),
    ];
    let started = Instant::now();
    let outcomes = run_cases(&cases, &[0, 1]);
    assert!(
        matches!(&outcomes[&0], Outcome::Fail(class, _) if class == "timeout"),
        "expected a timeout, got {:?}",
        outcomes[&0]
    );
    assert!(
        matches!(&outcomes[&1], Outcome::Pass),
        "the case after a timeout must still run, got {:?}",
        outcomes[&1]
    );
    assert!(
        started.elapsed() < Duration::from_secs(60),
        "a timeout must not stall the batch"
    );
}

/// A child that outlives its limit is killed together with the processes it
/// started.
#[test]
fn bounded_subprocess_kills_the_process_group() {
    let marker = format!("saga_matrix_selftest_{}", std::process::id());
    let started = Instant::now();
    // The shell starts a grandchild and waits on it, like `erl` does with
    // `beam.smp`. `$0` carries the marker so the grandchild can be found.
    let result = run_bounded(
        std::process::Command::new("sh")
            .arg("-c")
            .arg("sh -c 'sleep 30' \"$0\" & wait")
            .arg(&marker),
        Duration::from_millis(300),
    );
    assert!(result.is_err(), "expected the limit to be reported");
    assert!(
        started.elapsed() < Duration::from_secs(10),
        "the kill must be prompt"
    );
    let survivors = run_bounded(
        std::process::Command::new("pgrep").arg("-f").arg(&marker),
        Duration::from_secs(10),
    )
    .expect("pgrep");
    assert!(
        survivors.stdout.is_empty(),
        "processes left behind: {}",
        String::from_utf8_lossy(&survivors.stdout)
    );
}
