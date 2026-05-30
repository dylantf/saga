//! Unit tests for the monadic translation pass.
//!
//! Tests build AST programs by hand (no parser dependency), construct an
//! empty `ResolutionMap` and a minimal `EffectInfo`, and assert structural
//! properties of the resulting `MProgram`.

use std::collections::{HashMap, HashSet};

use super::translate;
use crate::ast::{
    Annotated, BinOp, CaseArm, Decl, EffectOp, EffectRef, Expr, ExprKind, Handler, HandlerArm,
    HandlerBody, HandlerItem, Lit, NamedHandlerRef, NodeId, Pat, Stmt, TypeExpr,
};
use crate::codegen::monadic::ir::{Atom, EffectInfo, MDecl, MExpr, MHandler};
use crate::codegen::resolve::ResolutionMap;
use crate::token::Span;
use crate::typechecker::{ResolvedEffectOp, Type};

// ----- builders --------------------------------------------------------------

fn sp() -> Span {
    Span { start: 0, end: 0 }
}

fn var(name: &str) -> Expr {
    Expr::synth(sp(), ExprKind::Var { name: name.into() })
}

fn lit_int(n: i64) -> Expr {
    Expr::synth(
        sp(),
        ExprKind::Lit {
            value: Lit::Int(n.to_string(), n),
        },
    )
}

fn lit_unit() -> Expr {
    Expr::synth(sp(), ExprKind::Lit { value: Lit::Unit })
}

fn app2(f: Expr, a: Expr) -> Expr {
    Expr::synth(
        sp(),
        ExprKind::App {
            func: Box::new(f),
            arg: Box::new(a),
        },
    )
}

fn fun_binding(name: &str, body: Expr) -> Decl {
    Decl::FunBinding {
        id: NodeId::fresh(),
        name: name.into(),
        name_span: sp(),
        params: vec![Pat::Var {
            id: NodeId::fresh(),
            name: "_".into(),
            span: sp(),
        }],
        guard: None,
        body,
        span: sp(),
    }
}

fn unit_typeexpr() -> TypeExpr {
    // A minimal placeholder TypeExpr; the translator doesn't inspect type
    // exprs. Hijack `Var` since it's a common shape.
    TypeExpr::Var {
        id: NodeId::fresh(),
        name: "Unit".into(),
        span: sp(),
    }
}

fn effect_def(name: &str, ops: &[&str]) -> Decl {
    Decl::EffectDef {
        id: NodeId::fresh(),
        doc: Vec::new(),
        public: false,
        name: name.into(),
        name_span: sp(),
        type_params: Vec::new(),
        operations: ops
            .iter()
            .map(|n| {
                Annotated::bare(EffectOp {
                    doc: Vec::new(),
                    name: (*n).to_string(),
                    params: vec![("_".into(), unit_typeexpr())],
                    return_type: unit_typeexpr(),
                    effects: Vec::new(),
                    effect_row_var: None,
                    span: sp(),
                })
            })
            .collect(),
        dangling_trivia: Vec::new(),
        span: sp(),
    }
}

fn empty_info() -> EmptyInfo {
    EmptyInfo::default()
}

#[derive(Default)]
struct EmptyInfo {
    effect_calls: HashMap<NodeId, ResolvedEffectOp>,
    handler_arms: HashMap<NodeId, ResolvedEffectOp>,
    constructors: HashMap<NodeId, String>,
    fun_effects: HashMap<String, HashSet<String>>,
    let_effect_bindings: HashMap<String, Vec<String>>,
    type_at_node: HashMap<NodeId, Type>,
    effect_ops: HashMap<String, Vec<String>>,
    handler_effects: HashMap<String, Vec<String>>,
    let_handler_effects: HashMap<NodeId, Vec<String>>,
}

impl EmptyInfo {
    fn as_view(&self) -> EffectInfo<'_> {
        EffectInfo {
            effect_calls: &self.effect_calls,
            handler_arms: &self.handler_arms,
            constructors: &self.constructors,
            fun_effects: &self.fun_effects,
            let_effect_bindings: &self.let_effect_bindings,
            type_at_node: &self.type_at_node,
            effect_ops: &self.effect_ops,
            handler_effects: &self.handler_effects,
            let_handler_effects: &self.let_handler_effects,
        }
    }
}

fn run_decl(decl: Decl) -> MDecl {
    let program = vec![decl];
    let info = empty_info();
    let view = info.as_view();
    let rmap = ResolutionMap::new();
    let (mut out, _) = translate(&program, &rmap, &view);
    out.remove(0)
}

fn run_program(program: Vec<Decl>, info: &EmptyInfo) -> Vec<MDecl> {
    let view = info.as_view();
    let rmap = ResolutionMap::new();
    let (out, _) = translate(&program, &rmap, &view);
    out
}

fn fun_body(decl: MDecl) -> MExpr {
    match decl {
        MDecl::FunBinding(f) => f.body,
        _ => panic!("expected FunBinding"),
    }
}

// ----- atom leaves ----------------------------------------------------------

#[test]
fn atomic_var_tail_to_pure() {
    let id = NodeId::fresh();
    let mut v = var("x");
    v.id = id;
    let decl = fun_binding("f", v);
    let body = fun_body(run_decl(decl));
    match body {
        MExpr::Pure(Atom::Var { source, .. }) => assert_eq!(source, id),
        _ => panic!("expected Pure(Var)"),
    }
}

#[test]
fn atomic_lit_tail_to_pure() {
    let l = lit_int(42);
    let id = l.id;
    let body = fun_body(run_decl(fun_binding("f", l)));
    match body {
        MExpr::Pure(Atom::Lit { source, .. }) => assert_eq!(source, id),
        _ => panic!("expected Pure(Lit)"),
    }
}

#[test]
fn atomic_constructor_zero_args() {
    let c = Expr::synth(
        sp(),
        ExprKind::Constructor {
            name: "None".into(),
        },
    );
    let id = c.id;
    let body = fun_body(run_decl(fun_binding("f", c)));
    match body {
        MExpr::Pure(Atom::Ctor { name, args, source }) => {
            assert_eq!(name, "None");
            assert!(args.is_empty());
            assert_eq!(source, id);
        }
        _ => panic!("expected Pure(Ctor)"),
    }
}

// ----- let-sequence becomes Bind --------------------------------------------

#[test]
fn let_x_in_body_becomes_bind() {
    // { let x = (g y); x }
    let g = var("g");
    let y = var("y");
    let call = app2(g, y);
    let stmt_let = Annotated::bare(Stmt::Let {
        pattern: Pat::Var {
            id: NodeId::fresh(),
            name: "x".into(),
            span: sp(),
        },
        annotation: None,
        value: call,
        assert: false,
        span: sp(),
    });
    let tail = Annotated::bare(Stmt::Expr(var("x")));
    let block = Expr::synth(
        sp(),
        ExprKind::Block {
            stmts: vec![stmt_let, tail],
            dangling_trivia: Vec::new(),
        },
    );
    let body = fun_body(run_decl(fun_binding("f", block)));
    match body {
        MExpr::Bind {
            var, value, body, ..
        } => {
            assert_eq!(var.name, "x");
            // value is App(g, [y])
            match *value {
                MExpr::App { args, .. } => assert_eq!(args.len(), 1),
                _ => panic!("expected App in Bind.value"),
            }
            match *body {
                MExpr::Pure(Atom::Var { name, .. }) => assert_eq!(name.name, "x"),
                _ => panic!("expected Pure(Var) tail"),
            }
        }
        _ => panic!("expected Bind"),
    }
}

// ----- function call with atomic args ---------------------------------------

#[test]
fn curried_app_flattens() {
    // f a b -> App(App(f, a), b) -> App { head: f, args: [a, b] }
    let f = var("f");
    let a = var("a");
    let b = var("b");
    let inner = app2(f, a);
    let outer = app2(inner, b);
    let outer_id = outer.id;
    let body = fun_body(run_decl(fun_binding("g", outer)));
    match body {
        MExpr::App { head, args, source } => {
            match head {
                Atom::Var { name, .. } => assert_eq!(name.name, "f"),
                _ => panic!("head should be Var(f)"),
            }
            assert_eq!(args.len(), 2);
            assert_eq!(source, outer_id);
        }
        _ => panic!("expected App"),
    }
}

// ----- EffectCall -> Yield ---------------------------------------------------

#[test]
fn effect_call_yields_with_preresolved_op() {
    // log! "msg"
    let arg = Expr::synth(
        sp(),
        ExprKind::Lit {
            value: Lit::String("msg".into(), crate::token::StringKind::Normal),
        },
    );
    let call = Expr::synth(
        sp(),
        ExprKind::EffectCall {
            name: "log".into(),
            qualifier: None,
            args: vec![arg],
        },
    );
    let call_id = call.id;

    let mut info = EmptyInfo::default();
    info.effect_calls.insert(
        call_id,
        ResolvedEffectOp {
            effect: "Log".into(),
            op: "log".into(),
        },
    );

    // Include Log effect def so op_index is computable.
    let program = vec![effect_def("Log", &["log"]), fun_binding("f", call)];
    let out = run_program(program, &info);
    let body = match &out[1] {
        MDecl::FunBinding(f) => &f.body,
        _ => panic!(),
    };
    match body {
        MExpr::Yield { op, args, source } => {
            assert_eq!(op.effect, "Log");
            assert_eq!(op.op, "log");
            assert_eq!(op.op_index, 1);
            assert_eq!(args.len(), 1);
            assert_eq!(*source, call_id);
        }
        _ => panic!("expected Yield"),
    }
}

#[test]
fn op_index_alphabetical_sort() {
    // Build a Log effect with multiple ops; op_index must reflect sorted order.
    let mut info = EmptyInfo::default();
    let call = Expr::synth(
        sp(),
        ExprKind::EffectCall {
            name: "warn".into(),
            qualifier: None,
            args: vec![lit_unit()],
        },
    );
    let call_id = call.id;
    info.effect_calls.insert(
        call_id,
        ResolvedEffectOp {
            effect: "Log".into(),
            op: "warn".into(),
        },
    );
    let program = vec![
        // Define ops out-of-order to verify sorting.
        effect_def("Log", &["warn", "info", "log", "debug"]),
        fun_binding("f", call),
    ];
    let out = run_program(program, &info);
    let body = match &out[1] {
        MDecl::FunBinding(f) => &f.body,
        _ => panic!(),
    };
    match body {
        MExpr::Yield { op, .. } => {
            // sorted: [debug, info, log, warn] -> warn is index 4 (1-based).
            assert_eq!(op.op_index, 4);
        }
        _ => panic!(),
    }
}

// ----- If / Case -------------------------------------------------------------

#[test]
fn if_expects_atomic_cond() {
    let cond = Expr::synth(
        sp(),
        ExprKind::Lit {
            value: Lit::Bool(true),
        },
    );
    let then_b = lit_int(1);
    let else_b = lit_int(2);
    let if_expr = Expr::synth(
        sp(),
        ExprKind::If {
            cond: Box::new(cond),
            then_branch: Box::new(then_b),
            else_branch: Box::new(else_b),
            multiline: false,
        },
    );
    let if_id = if_expr.id;
    let body = fun_body(run_decl(fun_binding("f", if_expr)));
    match body {
        MExpr::If {
            cond,
            then_branch,
            else_branch,
            source,
        } => {
            assert!(matches!(cond, Atom::Lit { .. }));
            assert!(matches!(*then_branch, MExpr::Pure(Atom::Lit { .. })));
            assert!(matches!(*else_branch, MExpr::Pure(Atom::Lit { .. })));
            assert_eq!(source, if_id);
        }
        _ => panic!("expected If"),
    }
}

#[test]
fn case_translates_arms() {
    let scrutinee = var("x");
    let arm = Annotated::bare(CaseArm {
        pattern: Pat::Wildcard {
            id: NodeId::fresh(),
            span: sp(),
        },
        guard: None,
        body: lit_int(0),
        span: sp(),
    });
    let case = Expr::synth(
        sp(),
        ExprKind::Case {
            scrutinee: Box::new(scrutinee),
            arms: vec![arm],
            dangling_trivia: Vec::new(),
        },
    );
    let case_id = case.id;
    let body = fun_body(run_decl(fun_binding("f", case)));
    match body {
        MExpr::Case { arms, source, .. } => {
            assert_eq!(arms.len(), 1);
            assert_eq!(source, case_id);
        }
        _ => panic!("expected Case"),
    }
}

// ----- BinOp/Resume ----------------------------------------------------------

#[test]
fn binop_atomic_operands() {
    let lhs = var("a");
    let rhs = var("b");
    let bo = Expr::synth(
        sp(),
        ExprKind::BinOp {
            op: BinOp::Add,
            left: Box::new(lhs),
            right: Box::new(rhs),
        },
    );
    let bo_id = bo.id;
    let body = fun_body(run_decl(fun_binding("f", bo)));
    match body {
        MExpr::BinOp { source, .. } => assert_eq!(source, bo_id),
        _ => panic!("expected BinOp"),
    }
}

#[test]
fn resume_atomic_arg() {
    let v = lit_int(7);
    let r = Expr::synth(sp(), ExprKind::Resume { value: Box::new(v) });
    let r_id = r.id;
    let body = fun_body(run_decl(fun_binding("f", r)));
    match body {
        MExpr::Resume { value, source } => {
            assert!(matches!(value, Atom::Lit { .. }));
            assert_eq!(source, r_id);
        }
        _ => panic!("expected Resume"),
    }
}

// ----- With + handler classification ----------------------------------------

fn inline_arm(op_name: &str, body: Expr) -> HandlerArm {
    HandlerArm {
        id: NodeId::fresh(),
        op_name: op_name.into(),
        qualifier: None,
        params: vec![Pat::Var {
            id: NodeId::fresh(),
            name: "_".into(),
            span: sp(),
        }],
        body: Box::new(body),
        finally_block: None,
        span: sp(),
    }
}

#[test]
fn inline_handler_is_static() {
    // with body { log msg = resume () }
    let arm = inline_arm("log", lit_unit());
    let handler = Handler::Inline {
        items: vec![Annotated::bare(HandlerItem::Arm(arm))],
        dangling_trivia: Vec::new(),
    };
    let with_expr = Expr::synth(
        sp(),
        ExprKind::With {
            expr: Box::new(lit_int(1)),
            handler: Box::new(handler),
        },
    );
    let body = fun_body(run_decl(fun_binding("f", with_expr)));
    match body {
        MExpr::With { handler, .. } => match handler {
            MHandler::Static { arms, .. } => assert_eq!(arms.len(), 1),
            _ => panic!("expected Static"),
        },
        _ => panic!("expected With"),
    }
}

#[test]
fn named_handler_resolves_to_static_when_decl_present() {
    let arm = inline_arm("log", lit_unit());
    let handler_decl = Decl::HandlerDef {
        id: NodeId::fresh(),
        doc: Vec::new(),
        public: false,
        name: "console_log".into(),
        name_span: sp(),
        body: HandlerBody {
            effects: vec![EffectRef {
                id: NodeId::fresh(),
                name: "Log".into(),
                type_args: Vec::new(),
                span: sp(),
            }],
            needs: Vec::new(),
            where_clause: Vec::new(),
            arms: vec![Annotated::bare(arm)],
            return_clause: None,
        },
        recovered_arms: Vec::new(),
        dangling_trivia: Vec::new(),
        span: sp(),
    };
    let with_expr = Expr::synth(
        sp(),
        ExprKind::With {
            expr: Box::new(lit_int(1)),
            handler: Box::new(Handler::Named(NamedHandlerRef {
                id: NodeId::fresh(),
                name: "console_log".into(),
                span: sp(),
            })),
        },
    );
    let fb = fun_binding("f", with_expr);
    let program = vec![handler_decl, fb];
    let info = empty_info();
    let out = run_program(program, &info);
    let body = match &out[1] {
        MDecl::FunBinding(f) => &f.body,
        _ => panic!(),
    };
    match body {
        MExpr::With { handler, .. } => match handler {
            MHandler::Static { arms, effects, .. } => {
                assert_eq!(arms.len(), 1);
                assert_eq!(effects, &vec!["Log".to_string()]);
            }
            _ => panic!("expected Static"),
        },
        _ => panic!("expected With"),
    }
}

#[test]
fn named_handler_falls_back_to_dynamic_when_unknown() {
    let with_expr = Expr::synth(
        sp(),
        ExprKind::With {
            expr: Box::new(lit_int(1)),
            handler: Box::new(Handler::Named(NamedHandlerRef {
                id: NodeId::fresh(),
                name: "mystery_handler".into(),
                span: sp(),
            })),
        },
    );
    let body = fun_body(run_decl(fun_binding("f", with_expr)));
    match body {
        MExpr::With { handler, .. } => assert!(matches!(handler, MHandler::Dynamic { .. })),
        _ => panic!(),
    }
}

#[test]
fn alias_chase_let_h_is_static() {
    // { let h = handler for Log { ... }; (with () h) }
    let arm = inline_arm("log", lit_unit());
    let handler_body = HandlerBody {
        effects: Vec::new(),
        needs: Vec::new(),
        where_clause: Vec::new(),
        arms: vec![Annotated::bare(arm)],
        return_clause: None,
    };
    let handler_expr = Expr::synth(sp(), ExprKind::HandlerExpr { body: handler_body });
    let let_stmt = Annotated::bare(Stmt::Let {
        pattern: Pat::Var {
            id: NodeId::fresh(),
            name: "h".into(),
            span: sp(),
        },
        annotation: None,
        value: handler_expr,
        assert: false,
        span: sp(),
    });
    let with_expr = Expr::synth(
        sp(),
        ExprKind::With {
            expr: Box::new(lit_unit()),
            handler: Box::new(Handler::Named(NamedHandlerRef {
                id: NodeId::fresh(),
                name: "h".into(),
                span: sp(),
            })),
        },
    );
    let block = Expr::synth(
        sp(),
        ExprKind::Block {
            stmts: vec![let_stmt, Annotated::bare(Stmt::Expr(with_expr))],
            dangling_trivia: Vec::new(),
        },
    );
    let body = fun_body(run_decl(fun_binding("f", block)));
    // The translator records the alias in `local_static_handlers` so the
    // `with h` site resolves to the original handler arms directly. The
    // current pipeline still emits a `Bind h = HandlerValue { ... }` for
    // the let-binding (since `h` could in principle escape as a runtime
    // value); a future DCE pass over unused-as-value handler binds could
    // drop it. The behavior under test is that alias-chasing succeeded —
    // i.e. the with-site classifies as `Static`, not `Dynamic`.
    fn find_with_handler(e: &MExpr) -> Option<&MHandler> {
        match e {
            MExpr::With { handler, .. } => Some(handler),
            MExpr::Bind { body, .. } => find_with_handler(body),
            _ => None,
        }
    }
    let handler = find_with_handler(&body)
        .unwrap_or_else(|| panic!("expected With somewhere in block tail, got {body:?}"));
    match handler {
        MHandler::Static { arms, .. } => assert_eq!(
            arms.len(),
            1,
            "alias-chased Static handler must carry the original arm"
        ),
        other => panic!("expected Static handler from chased alias, got {other:?}"),
    }
}

// ----- NodeId preservation --------------------------------------------------

#[test]
fn structural_node_ids_preserved() {
    // App: source carries outer App id.
    let f = var("f");
    let a = var("a");
    let inner = app2(f, a);
    let outer_id = inner.id;
    let body = fun_body(run_decl(fun_binding("g", inner)));
    if let MExpr::App { source, head, .. } = body {
        assert_eq!(source, outer_id);
        if let Atom::Var {
            source: head_src, ..
        } = head
        {
            // Head's atom carries its own original NodeId (the Var's id).
            assert_ne!(head_src, outer_id);
        }
    } else {
        panic!("expected App");
    }
}
