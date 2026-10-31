//! Tests for the codegen expression type table (`CheckResult::expr_types`).

use std::collections::HashMap;

use super::*;
use crate::ast::{self, NodeId};
use crate::lexer::Lexer;
use crate::parser::Parser;

/// Parse, derive, desugar and check `src` on top of the prelude, handing back
/// the checked program so tests can walk its expression nodes.
fn check_keeping_program(src: &str) -> (Checker, ast::Program) {
    let tokens = Lexer::new(src).lex().expect("lex error");
    let mut program = Parser::new(tokens).parse_program().expect("parse error");
    let imported = crate::derive::collect_imported_decls(&program, None);
    let derive_errors = crate::derive::expand_derives(&mut program, &imported);
    assert!(derive_errors.is_empty(), "derive errors");
    crate::desugar::desugar_program(&mut program);
    let mut checker = Checker::new();
    let prelude_src = include_str!("../stdlib/prelude.saga");
    let prelude_tokens = Lexer::new(prelude_src).lex().expect("prelude lex error");
    let mut prelude_program = Parser::new(prelude_tokens)
        .parse_program()
        .expect("prelude parse error");
    crate::derive::expand_derives(&mut prelude_program, &crate::derive::ImportedDecls::empty());
    crate::desugar::desugar_program(&mut prelude_program);
    checker
        .check_program_inner(&mut prelude_program)
        .unwrap_or_else(|e| panic!("prelude: {}", e[0].message));
    checker
        .check_program_inner(&mut program)
        .unwrap_or_else(|e| panic!("type error: {}", e[0].message));
    (checker, program)
}

type Node = (NodeId, Span, String);

/// Collects every `Expr` node in a checked program: `(id, span, kind name)`.
///
/// Subtrees that are deliberately not visited, because the typechecker never
/// infers them:
///
/// - `TraitMethod::default_body`: the trait's own copy of a default method
///   body is a template. Derive expansion clones it, with fresh `NodeId`s,
///   into every impl that omits the method, and only those copies are checked.
/// - `Decl::HandlerDef::recovered_arms`: parser error-recovery leftovers kept
///   for LSP hover; not typechecked by definition.
#[derive(Default)]
struct ExprCollector {
    nodes: Vec<Node>,
}

impl ExprCollector {
    fn program(&mut self, program: &[ast::Decl]) {
        use ast::Decl;
        for decl in program {
            match decl {
                Decl::FunBinding {
                    params,
                    guard,
                    body,
                    ..
                } => {
                    params.iter().for_each(|p| self.pat(p));
                    if let Some(g) = guard {
                        self.expr(g);
                    }
                    self.expr(body);
                }
                Decl::Let { value, .. } => self.expr(value),
                Decl::HandlerDef { body, .. } => self.handler_body(body),
                Decl::ImplDef { methods, .. } => {
                    for m in methods {
                        m.node.params.iter().for_each(|p| self.pat(p));
                        self.expr(&m.node.body);
                    }
                }
                _ => {}
            }
        }
    }

    fn handler_body(&mut self, body: &ast::HandlerBody) {
        for arm in &body.arms {
            self.handler_arm(&arm.node);
        }
        if let Some(rc) = &body.return_clause {
            self.handler_arm(rc);
        }
    }

    fn handler_arm(&mut self, arm: &ast::HandlerArm) {
        arm.params.iter().for_each(|p| self.pat(p));
        self.expr(&arm.body);
        if let Some(f) = &arm.finally_block {
            self.expr(f);
        }
    }

    fn case_arm(&mut self, arm: &ast::CaseArm) {
        self.pat(&arm.pattern);
        if let Some(g) = &arm.guard {
            self.expr(g);
        }
        self.expr(&arm.body);
    }

    /// Patterns hold expressions only in bitstring segment sizes.
    fn pat(&mut self, pat: &ast::Pat) {
        use ast::Pat;
        match pat {
            Pat::Wildcard { .. } | Pat::Var { .. } | Pat::Lit { .. } => {}
            Pat::Constructor { args, .. } => args.iter().for_each(|p| self.pat(p)),
            Pat::Record { fields, .. } | Pat::AnonRecord { fields, .. } => {
                for (_, alias) in fields {
                    if let Some(p) = alias {
                        self.pat(p);
                    }
                }
            }
            Pat::Tuple { elements, .. } | Pat::ListPat { elements, .. } => {
                elements.iter().for_each(|p| self.pat(p))
            }
            Pat::StringPrefix { rest, .. } => self.pat(rest),
            Pat::BitStringPat { segments, .. } => {
                for seg in segments {
                    self.pat(&seg.value);
                    if let Some(size) = &seg.size {
                        self.expr(size);
                    }
                }
            }
            Pat::ConsPat { head, tail, .. } => {
                self.pat(head);
                self.pat(tail);
            }
            Pat::Or { patterns, .. } => patterns.iter().for_each(|p| self.pat(p)),
        }
    }

    fn expr(&mut self, expr: &ast::Expr) {
        use ast::{ExprKind, Handler, HandlerItem, Stmt};
        let kind_name = format!("{:?}", expr.kind);
        let kind_name = kind_name
            .split(|c: char| !c.is_alphanumeric())
            .next()
            .unwrap_or("")
            .to_string();
        self.nodes.push((expr.id, expr.span, kind_name));
        match &expr.kind {
            ExprKind::Lit { .. }
            | ExprKind::Var { .. }
            | ExprKind::Constructor { .. }
            | ExprKind::QualifiedName { .. } => {}
            ExprKind::App { func, arg } => {
                self.expr(func);
                self.expr(arg);
            }
            ExprKind::BinOp { left, right, .. } => {
                self.expr(left);
                self.expr(right);
            }
            ExprKind::UnaryMinus { expr } => self.expr(expr),
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                self.expr(cond);
                self.expr(then_branch);
                self.expr(else_branch);
            }
            ExprKind::Case {
                scrutinee, arms, ..
            } => {
                self.expr(scrutinee);
                arms.iter().for_each(|a| self.case_arm(&a.node));
            }
            ExprKind::Block { stmts, .. } => {
                for stmt in stmts {
                    match &stmt.node {
                        Stmt::Let { pattern, value, .. } => {
                            self.pat(pattern);
                            self.expr(value);
                        }
                        Stmt::LetFun {
                            params,
                            guard,
                            body,
                            ..
                        } => {
                            params.iter().for_each(|p| self.pat(p));
                            if let Some(g) = guard {
                                self.expr(g);
                            }
                            self.expr(body);
                        }
                        Stmt::Expr(e) => self.expr(e),
                    }
                }
            }
            ExprKind::Lambda { params, body } => {
                params.iter().for_each(|p| self.pat(p));
                self.expr(body);
            }
            ExprKind::FieldAccess { expr, .. } => self.expr(expr),
            ExprKind::RecordCreate { fields, .. }
            | ExprKind::AnonRecordCreate { fields }
            | ExprKind::RecordBuild { fields, .. } => {
                fields.iter().for_each(|(_, _, e)| self.expr(e))
            }
            ExprKind::RecordUpdate { record, fields, .. } => {
                self.expr(record);
                fields.iter().for_each(|(_, _, e)| self.expr(e));
            }
            ExprKind::EffectCall { args, .. } => args.iter().for_each(|e| self.expr(e)),
            ExprKind::With { expr, handler } => {
                self.expr(expr);
                match handler.as_ref() {
                    // A named handler reference is not an `Expr`.
                    Handler::Named(_) => {}
                    Handler::Inline { items, .. } => {
                        for item in items {
                            match &item.node {
                                HandlerItem::Named(_) => {}
                                HandlerItem::Arm(arm) | HandlerItem::Return(arm) => {
                                    self.handler_arm(arm)
                                }
                            }
                        }
                    }
                }
            }
            ExprKind::Resume { value } => self.expr(value),
            ExprKind::Tuple { elements } => elements.iter().for_each(|e| self.expr(e)),
            ExprKind::Do {
                bindings,
                success,
                else_arms,
                ..
            } => {
                for (pat, e) in bindings {
                    self.pat(pat);
                    self.expr(e);
                }
                self.expr(success);
                else_arms.iter().for_each(|a| self.case_arm(&a.node));
            }
            ExprKind::Receive {
                arms, after_clause, ..
            } => {
                arms.iter().for_each(|a| self.case_arm(&a.node));
                if let Some((timeout, body)) = after_clause {
                    self.expr(timeout);
                    self.expr(body);
                }
            }
            ExprKind::BitString { segments } => {
                for seg in segments {
                    self.expr(&seg.value);
                    if let Some(size) = &seg.size {
                        self.expr(size);
                    }
                }
            }
            ExprKind::Ascription { expr, .. } => self.expr(expr),
            ExprKind::HandlerExpr { body } => self.handler_body(body),
            other => panic!(
                "surface or elaboration-only expression survived to the checked AST: {:?}",
                other
            ),
        }
    }
}

/// Checks `src` and asserts that every expression node of the checked AST has
/// an entry in the codegen type table. Returns the zonked table plus the
/// collected nodes for further assertions.
fn assert_expr_types_complete(src: &str) -> (HashMap<NodeId, Type>, Vec<Node>) {
    let (checker, program) = check_keeping_program(src);
    let result = checker.to_result();
    let mut collector = ExprCollector::default();
    collector.program(&program);
    assert!(!collector.nodes.is_empty());
    let missing: Vec<String> = collector
        .nodes
        .iter()
        .filter(|(id, _, _)| !result.expr_types.contains_key(id))
        .map(|(_, span, kind)| {
            format!(
                "{} `{}`",
                kind,
                src.get(span.start..span.end).unwrap_or("<synthetic>")
            )
        })
        .collect();
    assert!(
        missing.is_empty(),
        "{} of {} expression nodes have no expr_types entry:\n  {}",
        missing.len(),
        collector.nodes.len(),
        missing.join("\n  ")
    );
    (result.expr_types, collector.nodes)
}

/// The type recorded for the unique expression of kind `kind` that starts
/// where `text` (which must occur once in `src`) starts.
fn expr_type_of(
    src: &str,
    table: &HashMap<NodeId, Type>,
    nodes: &[Node],
    kind: &str,
    text: &str,
) -> String {
    // Match on kind and start offset: some spans (e.g. a lambda whose body
    // ends in `()`) stop short of the full source text.
    let start = src.find(text).expect("text not in source");
    assert_eq!(src.matches(text).count(), 1, "`{text}` is not unique");
    let matches: Vec<_> = nodes
        .iter()
        .filter(|(_, span, k)| k == kind && span.start == start)
        .collect();
    assert_eq!(
        matches.len(),
        1,
        "expected one {kind} node `{text}`; {kind} nodes: {:?}",
        nodes
            .iter()
            .filter(|(_, _, k)| k == kind)
            .map(|(_, span, _)| src.get(span.start..span.end))
            .collect::<Vec<_>>()
    );
    table[&matches[0].0].to_string()
}

#[test]
fn expr_types_cover_control_flow_and_literals() {
    let src = r#"
fun classify : Int -> String
classify n = if n < 0 then "neg" else {
  let doubled = n * 2
  let neg = -doubled
  case (doubled, neg) {
    (0, _) -> "zero"
    (x, _) when x > 100 && True -> "big"
    _ -> "small: $(show n)"
  }
}

fun nums : Unit -> List Float
nums () = [1.5, 2.5] |> List.map (fun x -> x * 2.0)

fun compose_all : Unit -> Int
compose_all () = {
  let inc x = x + 1
  let f = inc >> inc
  let xs = [x * 2 | x <- [1, 2, 3], x > 1]
  let ys = 0 :: xs
  let t = (1, "two", 2.5, (), [f])
  let (a, _, _, _, _) = t
  (a : Int) + f (List.length ys)
}
"#;
    assert_expr_types_complete(src);
}

#[test]
fn expr_types_cover_effects_handlers_and_records() {
    let src = r#"
effect Log {
  fun log : String -> Unit
}

effect Counter {
  fun next : Unit -> Int
}

record User { name : String, age : Int }

handler quiet for Log {
  log _ = resume ()
  return v = v
}

fun make_counter : Int -> Handler Counter
make_counter start = handler for Counter {
  next () = resume (start + 1)
}

fun describe : User -> String needs {Log}
describe u = {
  log! ("describing " <> u.name)
  let older = { u | age: u.age + 1 }
  let anon = { label: older.name, years: older.age }
  anon.label <> show anon.years
}

fun apply_twice : (Int -> Int needs {..e}) -> Int -> Int needs {..e}
apply_twice f x = f (f x)

fun run : Unit -> (String, Int)
run () = {
  let u = User { name: "ada", age: 36 }
  let s = describe u with quiet
  let n = apply_twice (fun x -> x + next! ()) 1 with {
    next () = resume 10
  }
  let counter = make_counter 5
  let m = apply_twice (fun x -> x + next! ()) 1 with counter
  let r = do {
    Ok a <- (Ok n : Result Int String)
    Ok b <- Ok m
    a + b
  } else {
    Err _ -> 0
  }
  (s, r)
}
"#;
    assert_expr_types_complete(src);
}

#[test]
fn expr_types_cover_traits_bitstrings_and_receive() {
    let src = r#"
import Std.Actor (Actor)

type Shape = Circle(Float) | Square(Float) deriving (Show, Eq)

trait Area a {
  fun area : a -> Float
  fun describe : a -> String
  describe _ = "a shape"
}

impl Area for Shape {
  area s = case s {
    Circle(r) -> r * r
    Square(w) -> w * w
  }
}

fun pack : Int -> BitString
pack n = <<n:16, 1, "ab">>

fun unpack : BitString -> Int
unpack bits = case bits {
  <<len:8, _rest:len/binary>> -> len
  _ -> 0
}

fun wait : Unit -> Int needs {Actor Int}
wait () = receive {
  n when n > 0 -> n
  _ -> 0
  after 10 -> -1
}

let total = area (Circle(1.5)) + area (Square(2.0))
"#;
    assert_expr_types_complete(src);
}

#[test]
fn expr_types_hold_the_kept_type_for_reinferred_nodes() {
    // Lambdas that are checked against an expected type (eagerly in
    // `infer_arg_against`, or deferred until the rest of the application
    // spine is known), and nodes that have no `type_at_node` entry at all
    // (`if`, `case`, literals, tuples, effect calls).
    let src = r#"
effect Skip {
  fun skip : Unit -> Int
}

fun hof : (Int -> Int needs {..e}) -> Int -> Int needs {..e}
hof f x = f x

fun pick : Bool -> Int needs {Skip}
pick b = {
  let pair = (1, "one")
  let n = if b then 1 else 2
  let m = case pair { (k, _) -> k }
  hof (fun x -> x + skip! ()) (n + m)
}
"#;
    let (table, nodes) = assert_expr_types_complete(src);
    let ty = |kind: &str, text: &str| expr_type_of(src, &table, &nodes, kind, text);
    assert_eq!(ty("If", "if b then 1 else 2"), "Int");
    assert_eq!(ty("Case", "case pair { (k, _) -> k }"), "Int");
    assert_eq!(ty("Tuple", "(1, \"one\")"), "(Int, String)");
    assert_eq!(ty("Lit", "\"one\""), "String");
    // An effect call node carries the operation's signature; the effect it
    // performs goes to the enclosing row, not onto this arrow.
    assert_eq!(ty("EffectCall", "skip!"), "Unit -> Int");
    // The deferred lambda is recorded with its own (effectful) type, and the
    // table is zonked: the callee's row variable is resolved.
    assert_eq!(
        ty("Lambda", "fun x -> x + skip! ()"),
        "Int -> Int needs {Skip}"
    );
    assert_eq!(
        ty("Var", "hof (fun"),
        "(Int -> Int needs {Skip}) -> Int -> Int needs {Skip}"
    );
}

#[test]
fn expr_types_skipped_when_disabled() {
    let mut checker = Checker::new();
    checker.disable_expr_types();
    let tokens = Lexer::new("let x = if True then 1 else 2")
        .lex()
        .expect("lex error");
    let mut program = Parser::new(tokens).parse_program().expect("parse error");
    crate::desugar::desugar_program(&mut program);
    checker
        .check_program_inner(&mut program)
        .unwrap_or_else(|e| panic!("type error: {}", e[0].message));
    assert!(checker.to_result().expr_types.is_empty());
}

/// Every single-file example under `examples/` must have a complete table.
/// This is the broad net: the examples exercise far more syntax (record
/// builders, actors, nested handlers, comprehensions, ...) than the targeted
/// programs above.
#[test]
fn expr_types_cover_every_single_file_example() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples");
    let mut paths: Vec<_> = std::fs::read_dir(&dir)
        .expect("examples dir")
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|ext| ext == "saga"))
        .collect();
    paths.sort();
    let mut total_nodes = 0usize;
    for path in &paths {
        let src = std::fs::read_to_string(path).expect("read example");
        let tokens = Lexer::new(&src).lex().expect("lex error");
        let mut program = Parser::new(tokens).parse_program().expect("parse error");
        let imported = crate::derive::collect_imported_decls(&program, None);
        let derive_errors = crate::derive::expand_derives(&mut program, &imported);
        assert!(derive_errors.is_empty(), "derive errors in {path:?}");
        crate::desugar::desugar_program(&mut program);
        let mut checker = Checker::with_prelude(None).expect("prelude");
        let result = checker.check_program(&mut program);
        assert!(
            !result.has_errors(),
            "{path:?} has type errors: {:?}",
            result
                .errors()
                .iter()
                .map(|d| &d.message)
                .collect::<Vec<_>>()
        );
        let mut collector = ExprCollector::default();
        collector.program(&program);
        let missing: Vec<String> = collector
            .nodes
            .iter()
            .filter(|(id, _, _)| !result.expr_types.contains_key(id))
            .map(|(_, span, kind)| {
                format!(
                    "{} `{}`",
                    kind,
                    src.get(span.start..span.end).unwrap_or("<synthetic>")
                )
            })
            .collect();
        assert!(
            missing.is_empty(),
            "{path:?}: {} of {} expression nodes have no expr_types entry:\n  {}",
            missing.len(),
            collector.nodes.len(),
            missing.join("\n  ")
        );
        total_nodes += collector.nodes.len();
    }
    assert!(paths.len() >= 50, "only {} examples found", paths.len());
    assert!(total_nodes > 5_000, "only {total_nodes} nodes were visited");
}

/// Imported modules are lowered from their own per-module `CheckResult`, so
/// the stdlib modules loaded by the prelude must each carry a complete table
/// for their own program.
#[test]
fn expr_types_cover_stdlib_modules() {
    let checker = Checker::with_prelude(None).expect("prelude");
    let result = checker.to_result();
    let mut modules = 0usize;
    let mut total_nodes = 0usize;
    for (name, mod_result) in result.module_check_results() {
        let program = result
            .programs()
            .get(name)
            .unwrap_or_else(|| panic!("no program for module {name}"));
        let mut collector = ExprCollector::default();
        collector.program(program);
        let missing = collector
            .nodes
            .iter()
            .filter(|(id, _, _)| !mod_result.expr_types.contains_key(id))
            .count();
        assert_eq!(
            missing,
            0,
            "module {name}: {missing} of {} expression nodes have no expr_types entry",
            collector.nodes.len()
        );
        modules += 1;
        total_nodes += collector.nodes.len();
    }
    assert!(modules >= 10, "only {modules} stdlib modules were checked");
    assert!(total_nodes > 500, "only {total_nodes} nodes were visited");
}
