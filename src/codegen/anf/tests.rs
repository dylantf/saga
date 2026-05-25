use super::{Anf, FreshNames, normalize};
use crate::ast::{Annotated, BinOp, CaseArm, Decl, Expr, ExprKind, Lit, NodeId, Pat, Stmt};
use crate::token::Span;

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

fn app(f: Expr, a: Expr) -> Expr {
    Expr::synth(
        sp(),
        ExprKind::App {
            func: Box::new(f),
            arg: Box::new(a),
        },
    )
}

fn run(e: Expr) -> Expr {
    let mut a = Anf {
        fresh: FreshNames::new(),
    };
    a.anf_expr(e)
}

#[test]
fn fresh_names_are_unique_and_prefixed() {
    let mut f = FreshNames::new();
    let a = f.fresh("v");
    let b = f.fresh("v");
    assert_ne!(a, b);
    assert!(a.starts_with("__anf_"));
    assert!(b.starts_with("__anf_"));
}

#[test]
fn atom_var_unchanged() {
    let v = var("x");
    let id_before = v.id;
    let out = run(v);
    assert!(matches!(out.kind, ExprKind::Var { ref name } if name == "x"));
    assert_eq!(out.id, id_before, "atom should preserve its NodeId");
}

#[test]
fn atom_lit_unchanged() {
    let out = run(lit_int(42));
    assert!(matches!(out.kind, ExprKind::Lit { .. }));
}

#[test]
fn atomic_tuple_stays_in_place() {
    let t = Expr::synth(
        sp(),
        ExprKind::Tuple {
            elements: vec![var("a"), var("b")],
        },
    );
    let out = run(t);
    match out.kind {
        ExprKind::Tuple { elements } => {
            assert_eq!(elements.len(), 2);
            assert!(matches!(elements[0].kind, ExprKind::Var { .. }));
            assert!(matches!(elements[1].kind, ExprKind::Var { .. }));
        }
        other => panic!("expected Tuple, got {other:?}"),
    }
}

#[test]
fn function_call_arg_lifted_preserves_inner_id() {
    // f(g(x))  →  let __anf_v0 = g(x); f(__anf_v0)
    let inner = app(var("g"), var("x"));
    let inner_id = inner.id;
    let out = run(app(var("f"), inner));
    let stmts = match out.kind {
        ExprKind::Block { stmts, .. } => stmts,
        other => panic!("expected Block, got {other:?}"),
    };
    assert_eq!(stmts.len(), 2);
    let (bind_name, bind_val_id) = match &stmts[0].node {
        Stmt::Let {
            pattern: Pat::Var { name, .. },
            value,
            ..
        } => (name.clone(), value.id),
        other => panic!("expected Stmt::Let with Pat::Var, got {other:?}"),
    };
    assert!(bind_name.starts_with("__anf_"));
    assert_eq!(bind_val_id, inner_id, "lifted source expr must keep NodeId");
    match &stmts[1].node {
        Stmt::Expr(e) => match &e.kind {
            ExprKind::App { func, arg } => {
                assert!(matches!(&func.kind, ExprKind::Var { name } if name == "f"));
                assert!(matches!(&arg.kind, ExprKind::Var { name } if name == &bind_name));
            }
            other => panic!("expected App, got {other:?}"),
        },
        other => panic!("expected tail Expr stmt, got {other:?}"),
    }
}

#[test]
fn case_scrutinee_lifted() {
    let case = Expr::synth(
        sp(),
        ExprKind::Case {
            scrutinee: Box::new(app(var("g"), var("x"))),
            arms: vec![Annotated::bare(CaseArm {
                pattern: Pat::Wildcard {
                    id: NodeId::fresh(),
                    span: sp(),
                },
                guard: None,
                body: lit_int(1),
                span: sp(),
            })],
            dangling_trivia: vec![],
        },
    );
    match run(case).kind {
        ExprKind::Block { stmts, .. } => {
            assert_eq!(stmts.len(), 2);
            match &stmts[1].node {
                Stmt::Expr(e) => match &e.kind {
                    ExprKind::Case { scrutinee, .. } => {
                        assert!(matches!(scrutinee.kind, ExprKind::Var { .. }));
                    }
                    other => panic!("expected Case, got {other:?}"),
                },
                other => panic!("expected Expr stmt, got {other:?}"),
            }
        }
        other => panic!("expected Block, got {other:?}"),
    }
}

#[test]
fn if_condition_lifted() {
    let ife = Expr::synth(
        sp(),
        ExprKind::If {
            cond: Box::new(app(var("g"), var("x"))),
            then_branch: Box::new(lit_int(1)),
            else_branch: Box::new(lit_int(2)),
            multiline: false,
        },
    );
    match run(ife).kind {
        ExprKind::Block { stmts, .. } => {
            assert_eq!(stmts.len(), 2);
            match &stmts[1].node {
                Stmt::Expr(e) => match &e.kind {
                    ExprKind::If { cond, .. } => {
                        assert!(matches!(cond.kind, ExprKind::Var { .. }));
                    }
                    other => panic!("expected If, got {other:?}"),
                },
                _ => panic!(),
            }
        }
        other => panic!("expected Block, got {other:?}"),
    }
}

#[test]
fn field_access_target_lifted() {
    let fa = Expr::synth(
        sp(),
        ExprKind::FieldAccess {
            expr: Box::new(app(var("g"), var("x"))),
            field: "name".into(),
            record_name: None,
        },
    );
    match run(fa).kind {
        ExprKind::Block { stmts, .. } => {
            assert_eq!(stmts.len(), 2);
            match &stmts[1].node {
                Stmt::Expr(e) => match &e.kind {
                    ExprKind::FieldAccess { expr, .. } => {
                        assert!(matches!(expr.kind, ExprKind::Var { .. }));
                    }
                    _ => panic!(),
                },
                _ => panic!(),
            }
        }
        other => panic!("expected Block, got {other:?}"),
    }
}

#[test]
fn binop_operands_lifted() {
    let bo = Expr::synth(
        sp(),
        ExprKind::BinOp {
            op: BinOp::Add,
            left: Box::new(app(var("g"), var("x"))),
            right: Box::new(app(var("h"), var("y"))),
        },
    );
    match run(bo).kind {
        ExprKind::Block { stmts, .. } => {
            assert_eq!(stmts.len(), 3, "two operand lifts + tail");
            match &stmts[2].node {
                Stmt::Expr(e) => match &e.kind {
                    ExprKind::BinOp { left, right, .. } => {
                        assert!(matches!(left.kind, ExprKind::Var { .. }));
                        assert!(matches!(right.kind, ExprKind::Var { .. }));
                    }
                    _ => panic!(),
                },
                _ => panic!(),
            }
        }
        other => panic!("expected Block, got {other:?}"),
    }
}

#[test]
fn non_atomic_tuple_lifts_elements() {
    // (g x, y) — first element is non-atomic, lift it.
    let t = Expr::synth(
        sp(),
        ExprKind::Tuple {
            elements: vec![app(var("g"), var("x")), var("y")],
        },
    );
    match run(t).kind {
        ExprKind::Block { stmts, .. } => {
            assert_eq!(stmts.len(), 2);
            match &stmts[1].node {
                Stmt::Expr(e) => match &e.kind {
                    ExprKind::Tuple { elements } => {
                        assert_eq!(elements.len(), 2);
                        assert!(matches!(elements[0].kind, ExprKind::Var { .. }));
                        assert!(matches!(elements[1].kind, ExprKind::Var { .. }));
                    }
                    _ => panic!(),
                },
                _ => panic!(),
            }
        }
        other => panic!("expected Block, got {other:?}"),
    }
}

#[test]
fn lambda_body_isolated_from_surrounding_context() {
    // fun x -> g(h(x)) applied to a literal. Lambda body anf'd in its own
    // context; the surrounding App sees an atomic lambda + atomic literal,
    // so no outer lifting happens.
    let body = app(var("g"), app(var("h"), var("x")));
    let lam = Expr::synth(
        sp(),
        ExprKind::Lambda {
            params: vec![Pat::Var {
                id: NodeId::fresh(),
                name: "x".into(),
                span: sp(),
            }],
            body: Box::new(body),
        },
    );
    let outer = app(lam, lit_int(1));
    let out = run(outer);
    match out.kind {
        ExprKind::App { func, arg } => {
            assert!(matches!(arg.kind, ExprKind::Lit { .. }));
            match func.kind {
                ExprKind::Lambda { body, .. } => match body.kind {
                    ExprKind::Block { stmts, .. } => {
                        // The lambda body got its own block: let v = h(x); g(v).
                        assert_eq!(stmts.len(), 2);
                    }
                    other => panic!("lambda body should be Block, got {other:?}"),
                },
                other => panic!("expected Lambda func, got {other:?}"),
            }
        }
        other => panic!("expected App at top level (no outer lift), got {other:?}"),
    }
}

#[test]
fn case_arm_body_isolated() {
    let arm = CaseArm {
        pattern: Pat::Wildcard {
            id: NodeId::fresh(),
            span: sp(),
        },
        guard: None,
        body: app(var("g"), app(var("h"), var("y"))),
        span: sp(),
    };
    let case = Expr::synth(
        sp(),
        ExprKind::Case {
            scrutinee: Box::new(var("x")),
            arms: vec![Annotated::bare(arm)],
            dangling_trivia: vec![],
        },
    );
    // scrutinee is atomic, so no outer block. Arm body got its own block.
    match run(case).kind {
        ExprKind::Case { arms, .. } => {
            assert_eq!(arms.len(), 1);
            match &arms[0].node.body.kind {
                ExprKind::Block { stmts, .. } => assert_eq!(stmts.len(), 2),
                other => panic!("expected Block in arm body, got {other:?}"),
            }
        }
        other => panic!("expected Case at top level, got {other:?}"),
    }
}

#[test]
fn if_branches_isolated() {
    // if c then g(x) else h(y) — each branch is its own context, so a
    // non-atomic branch lives inside the branch, not lifted out.
    let ife = Expr::synth(
        sp(),
        ExprKind::If {
            cond: Box::new(var("c")),
            then_branch: Box::new(app(var("g"), var("x"))),
            else_branch: Box::new(app(var("h"), var("y"))),
            multiline: false,
        },
    );
    match run(ife).kind {
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            assert!(matches!(cond.kind, ExprKind::Var { .. }));
            // Branch bodies are App in tail position of their own context;
            // no Block wrapping needed because no sub-position lifting
            // happened inside them.
            assert!(matches!(then_branch.kind, ExprKind::App { .. }));
            assert!(matches!(else_branch.kind, ExprKind::App { .. }));
        }
        other => panic!("expected If at top level, got {other:?}"),
    }
}

#[test]
fn do_lowers_to_case_with_else_arms() {
    // do { Some(x) <- m; x } else { None -> None }
    let pat = Pat::Constructor {
        id: NodeId::fresh(),
        name: "Some".into(),
        args: vec![Pat::Var {
            id: NodeId::fresh(),
            name: "x".into(),
            span: sp(),
        }],
        span: sp(),
    };
    let m_expr = var("m");
    let m_id = m_expr.id;
    let else_arm = CaseArm {
        pattern: Pat::Constructor {
            id: NodeId::fresh(),
            name: "None".into(),
            args: vec![],
            span: sp(),
        },
        guard: None,
        body: Expr::synth(
            sp(),
            ExprKind::Constructor {
                name: "None".into(),
            },
        ),
        span: sp(),
    };
    let do_expr = Expr::synth(
        sp(),
        ExprKind::Do {
            bindings: vec![(pat, m_expr)],
            success: Box::new(var("x")),
            else_arms: vec![Annotated::bare(else_arm)],
            dangling_trivia: vec![],
        },
    );
    // After lowering: case m { Some(x) -> x; None -> None }. `m` is a Var,
    // so it stays atomic — no outer Block.
    match run(do_expr).kind {
        ExprKind::Case {
            scrutinee, arms, ..
        } => {
            assert_eq!(arms.len(), 2);
            assert_eq!(scrutinee.id, m_id, "Do binding value NodeId preserved");
            match &arms[0].node.pattern {
                Pat::Constructor { name, .. } => assert_eq!(name, "Some"),
                _ => panic!(),
            }
            match &arms[1].node.pattern {
                Pat::Constructor { name, .. } => assert_eq!(name, "None"),
                _ => panic!(),
            }
        }
        other => panic!("expected Case from lowered Do, got {other:?}"),
    }
}

#[test]
fn do_with_non_atomic_binding_lifts_scrutinee() {
    // do { Some(x) <- get_thing(()); x } else {}
    let pat = Pat::Constructor {
        id: NodeId::fresh(),
        name: "Some".into(),
        args: vec![Pat::Var {
            id: NodeId::fresh(),
            name: "x".into(),
            span: sp(),
        }],
        span: sp(),
    };
    let value = app(var("get_thing"), lit_int(0));
    let value_id = value.id;
    let do_expr = Expr::synth(
        sp(),
        ExprKind::Do {
            bindings: vec![(pat, value)],
            success: Box::new(var("x")),
            else_arms: vec![],
            dangling_trivia: vec![],
        },
    );
    match run(do_expr).kind {
        ExprKind::Block { stmts, .. } => {
            assert_eq!(stmts.len(), 2);
            match &stmts[0].node {
                Stmt::Let { value, .. } => assert_eq!(value.id, value_id),
                _ => panic!(),
            }
            match &stmts[1].node {
                Stmt::Expr(e) => assert!(matches!(e.kind, ExprKind::Case { .. })),
                _ => panic!(),
            }
        }
        other => panic!("expected Block, got {other:?}"),
    }
}

#[test]
fn normalize_decl_program_runs() {
    // Sanity: pushing a small program through `normalize` returns the
    // same shape with the body anf'd.
    let decl = Decl::FunBinding {
        id: NodeId::fresh(),
        name: "main".into(),
        name_span: sp(),
        params: vec![Pat::Var {
            id: NodeId::fresh(),
            name: "_".into(),
            span: sp(),
        }],
        guard: None,
        body: app(var("f"), app(var("g"), var("x"))),
        span: sp(),
    };
    let out = normalize(vec![decl]);
    assert_eq!(out.len(), 1);
    match &out[0] {
        Decl::FunBinding { body, .. } => {
            assert!(matches!(body.kind, ExprKind::Block { .. }));
        }
        _ => panic!(),
    }
}

#[test]
fn receive_timeout_lifted_arm_bodies_isolated() {
    // receive { _ -> g(h(z)) after compute_timeout() -> body_complex() }
    //
    // The timeout `compute_timeout()` must be lifted above the Receive
    // (post-ANF invariant: timeout is atomic). Arm bodies and the timeout
    // body stay in their own ANF contexts — no cross-arm hoisting.
    let arm = CaseArm {
        pattern: Pat::Wildcard {
            id: NodeId::fresh(),
            span: sp(),
        },
        guard: None,
        body: app(var("g"), app(var("h"), var("z"))),
        span: sp(),
    };
    let timeout_expr = app(var("compute_timeout"), lit_int(0));
    let timeout_id = timeout_expr.id;
    let timeout_body = app(var("k"), app(var("m"), var("n")));
    let recv = Expr::synth(
        sp(),
        ExprKind::Receive {
            arms: vec![Annotated::bare(arm)],
            after_clause: Some((Box::new(timeout_expr), Box::new(timeout_body))),
            dangling_trivia: vec![],
        },
    );
    let out = run(recv);
    let stmts = match out.kind {
        ExprKind::Block { stmts, .. } => stmts,
        other => panic!("expected Block (timeout lifted), got {other:?}"),
    };
    assert_eq!(stmts.len(), 2, "one timeout lift + Receive tail");
    // Lifted timeout binding keeps the original NodeId on its value.
    match &stmts[0].node {
        Stmt::Let {
            pattern: Pat::Var { name, .. },
            value,
            ..
        } => {
            assert!(name.starts_with("__anf_"));
            assert_eq!(value.id, timeout_id);
        }
        other => panic!("expected lifted timeout let, got {other:?}"),
    }
    match &stmts[1].node {
        Stmt::Expr(e) => match &e.kind {
            ExprKind::Receive {
                arms, after_clause, ..
            } => {
                // Timeout itself is now an atomic Var.
                let (t, b) = after_clause.as_ref().expect("after_clause kept");
                assert!(matches!(t.kind, ExprKind::Var { .. }));
                // Timeout body's own context: its non-atomic inner App was
                // lifted, producing a Block. No hoisting into the outer
                // Receive's surrounding lets.
                assert!(matches!(b.kind, ExprKind::Block { .. }));
                // Arm body's own context: same — its lifts live inside the arm.
                assert_eq!(arms.len(), 1);
                assert!(matches!(arms[0].node.body.kind, ExprKind::Block { .. }));
            }
            other => panic!("expected Receive tail, got {other:?}"),
        },
        other => panic!("expected Expr stmt, got {other:?}"),
    }
}
