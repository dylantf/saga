use super::*;
use crate::codegen::monadic::ir::{EffectOpRef, MProgram};
use crate::typechecker::ResolvedEffectOp;
use std::collections::{HashMap, HashSet};

struct Fixture {
    h: HandlerAnalysis,
    effect_calls: HashMap<crate::ast::NodeId, ResolvedEffectOp>,
    handler_arms: HashMap<crate::ast::NodeId, ResolvedEffectOp>,
    constructors: HashMap<crate::ast::NodeId, String>,
    fun_effects: HashMap<String, HashSet<String>>,
    let_effect_bindings: HashMap<String, Vec<String>>,
    type_at_node: HashMap<crate::ast::NodeId, crate::typechecker::Type>,
    records: HashMap<String, crate::typechecker::RecordInfo>,
    effect_ops: HashMap<String, Vec<String>>,
    handler_effects: HashMap<String, Vec<String>>,
    handler_refs: HashMap<crate::ast::NodeId, crate::typechecker::ResolvedValue>,
    let_handler_effects: HashMap<crate::ast::NodeId, Vec<String>>,
}

impl Fixture {
    fn new() -> Self {
        Self {
            h: HandlerAnalysis::default(),
            effect_calls: HashMap::new(),
            handler_arms: HashMap::new(),
            constructors: HashMap::new(),
            fun_effects: HashMap::new(),
            let_effect_bindings: HashMap::new(),
            type_at_node: HashMap::new(),
            records: HashMap::new(),
            effect_ops: HashMap::new(),
            handler_effects: HashMap::new(),
            handler_refs: HashMap::new(),
            let_handler_effects: HashMap::new(),
        }
    }

    fn info(&self) -> EffectInfo<'_> {
        EffectInfo {
            effect_calls: &self.effect_calls,
            handler_arms: &self.handler_arms,
            constructors: &self.constructors,
            fun_effects: &self.fun_effects,
            let_effect_bindings: &self.let_effect_bindings,
            type_at_node: &self.type_at_node,
            records: &self.records,
            effect_ops: &self.effect_ops,
            handler_effects: &self.handler_effects,
            handler_refs: &self.handler_refs,
            let_handler_effects: &self.let_handler_effects,
        }
    }
}

#[test]
fn run_empty_program_is_identity() {
    let f = Fixture::new();
    let info = f.info();
    let prog: MProgram = vec![];
    assert_eq!(run(prog.clone(), &f.h, &info), prog);
}

#[test]
fn run_with_skip_preserves_bind_pure() {
    let f = Fixture::new();
    let info = f.info();
    let prog = val_program(bind_pure(
        mv("x", 1),
        lit_int("1", 1),
        MExpr::Pure(var("x", 1)),
    ));
    assert_eq!(
        run_with_options(prog.clone(), &f.h, &info, RunOptions { skip: true }),
        prog
    );
}

#[test]
fn mprogram_default_smoke() {
    let prog: MProgram = MProgram::default();
    assert!(prog.is_empty());
}

#[test]
fn bind_collapse_substitutes_pure_atom() {
    let f = Fixture::new();
    let info = f.info();
    let prog = val_program(bind_pure(
        mv("x", 1),
        lit_int("1", 1),
        MExpr::Pure(var("x", 1)),
    ));

    let out = run(prog, &f.h, &info);

    assert_eq!(out, val_program(MExpr::Pure(lit_int("1", 1))));
}

#[test]
fn bind_collapse_reaches_fixpoint() {
    let f = Fixture::new();
    let info = f.info();
    let prog = val_program(bind_pure(
        mv("x", 1),
        lit_int("1", 1),
        bind_pure(mv("y", 2), var("x", 1), MExpr::Pure(var("y", 2))),
    ));

    let out = run(prog, &f.h, &info);

    assert_eq!(out, val_program(MExpr::Pure(lit_int("1", 1))));
}

#[test]
fn bind_collapse_respects_shadowing_binder() {
    let f = Fixture::new();
    let info = f.info();
    let prog = val_program(bind_pure(
        mv("x", 1),
        lit_int("1", 1),
        bind_pure(mv("x", 2), lit_int("2", 2), MExpr::Pure(var("x", 2))),
    ));

    let out = run(prog, &f.h, &info);

    assert_eq!(out, val_program(MExpr::Pure(lit_int("2", 2))));
}

#[test]
fn bind_collapse_blocks_pattern_capture_but_promotes_to_let() {
    let f = Fixture::new();
    let info = f.info();
    let x = mv("x", 1);
    let replacement = var("y", 2);
    let body = MExpr::Case {
        scrutinee: var("scrut", 3),
        arms: vec![MArm {
            pattern: pat_var("y", 4),
            guard: None,
            body: MExpr::Pure(var("x", 1)),
            span: span(),
        }],
        source: crate::ast::NodeId(30),
    };
    let prog = val_program(bind_pure(x, replacement, body));

    let out = run(prog, &f.h, &info);

    assert_eq!(
        out,
        val_program(MExpr::Let {
            var: mv("x", 1),
            value: Box::new(MExpr::Pure(var("y", 2))),
            body: Box::new(MExpr::Case {
                scrutinee: var("scrut", 3),
                arms: vec![MArm {
                    pattern: pat_var("y", 4),
                    guard: None,
                    body: MExpr::Pure(var("x", 1)),
                    span: span(),
                }],
                source: crate::ast::NodeId(30),
            }),
        })
    );
}

#[test]
fn bind_to_let_promotes_structurally_pure_expression() {
    let f = Fixture::new();
    let info = f.info();
    let value = MExpr::BinOp {
        op: crate::ast::BinOp::Add,
        left: lit_int("1", 1),
        right: lit_int("2", 2),
        source: crate::ast::NodeId(40),
    };
    let body = MExpr::Pure(var("x", 1));
    let prog = val_program(bind_expr(mv("x", 1), value.clone(), body.clone()));

    let out = run(prog, &f.h, &info);

    assert_eq!(
        out,
        val_program(MExpr::Let {
            var: mv("x", 1),
            value: Box::new(value),
            body: Box::new(body),
        })
    );
}

#[test]
fn bind_to_let_keeps_yield_monadic() {
    let f = Fixture::new();
    let info = f.info();
    let value = MExpr::Yield {
        op: EffectOpRef {
            effect: "Log".to_string(),
            op: "log".to_string(),
            op_index: 1,
        },
        args: vec![lit_int("1", 1)],
        source: crate::ast::NodeId(50),
    };
    let body = MExpr::Pure(var("x", 1));
    let prog = val_program(bind_expr(mv("x", 1), value, body));

    let out = run(prog.clone(), &f.h, &info);

    assert_eq!(out, prog);
}

#[test]
fn bind_to_let_keeps_foreign_call_conservative() {
    let f = Fixture::new();
    let info = f.info();
    let value = MExpr::ForeignCall {
        module: "erlang".to_string(),
        func: "monotonic_time".to_string(),
        args: vec![],
        source: crate::ast::NodeId(60),
    };
    let body = MExpr::Pure(var("x", 1));
    let prog = val_program(bind_expr(mv("x", 1), value, body));

    let out = run(prog.clone(), &f.h, &info);

    assert_eq!(out, prog);
}

#[test]
fn bind_to_let_keeps_with_conservative() {
    let f = Fixture::new();
    let info = f.info();
    let value = MExpr::With {
        handler: MHandler::Static {
            effects: vec!["Log".to_string()],
            arms: vec![],
            return_clause: None,
            source: crate::ast::NodeId(65),
        },
        body: Box::new(MExpr::Pure(lit_int("1", 1))),
        source: crate::ast::NodeId(66),
    };
    let body = MExpr::Pure(var("x", 1));
    let prog = val_program(bind_expr(mv("x", 1), value, body));

    let out = run(prog.clone(), &f.h, &info);

    assert_eq!(out, prog);
}

#[test]
fn bind_to_let_keeps_app_with_closed_empty_effect_row_conservative() {
    let mut f = Fixture::new();
    let source = crate::ast::NodeId(70);
    let head_source = crate::ast::NodeId(71);
    f.type_at_node.insert(head_source, pure_fun_type());
    let info = f.info();
    let value = MExpr::App {
        head: var("pure_fun", 71),
        args: vec![lit_int("1", 1)],
        source,
    };
    let body = MExpr::Pure(var("x", 1));
    let prog = val_program(bind_expr(mv("x", 1), value, body));

    let out = run(prog.clone(), &f.h, &info);

    assert_eq!(out, prog);
}

#[test]
fn dead_pure_let_drops_unused_pure_value() {
    let f = Fixture::new();
    let info = f.info();
    let value = MExpr::BinOp {
        op: crate::ast::BinOp::Add,
        left: lit_int("1", 1),
        right: lit_int("2", 2),
        source: crate::ast::NodeId(75),
    };
    let prog = val_program(MExpr::Let {
        var: mv("unused", 76),
        value: Box::new(value),
        body: Box::new(MExpr::Pure(lit_int("3", 3))),
    });

    let out = run(prog, &f.h, &info);

    assert_eq!(out, val_program(MExpr::Pure(lit_int("3", 3))));
}

#[test]
fn dead_pure_let_keeps_used_value() {
    let f = Fixture::new();
    let info = f.info();
    let value = MExpr::BinOp {
        op: crate::ast::BinOp::Add,
        left: lit_int("1", 1),
        right: lit_int("2", 2),
        source: crate::ast::NodeId(77),
    };
    let prog = val_program(MExpr::Let {
        var: mv("x", 78),
        value: Box::new(value.clone()),
        body: Box::new(MExpr::Pure(var("x", 78))),
    });

    let out = run(prog, &f.h, &info);

    assert_eq!(
        out,
        val_program(MExpr::Let {
            var: mv("x", 78),
            value: Box::new(value),
            body: Box::new(MExpr::Pure(var("x", 78))),
        })
    );
}

#[test]
fn dead_pure_let_keeps_pattern_size_reference() {
    let f = Fixture::new();
    let info = f.info();
    let size_ref = crate::ast::Expr::synth(
        span(),
        crate::ast::ExprKind::Var {
            name: "i".to_string(),
        },
    );
    let pattern = Pat::BitStringPat {
        id: crate::ast::NodeId(180),
        segments: vec![crate::ast::BitSegment {
            value: pat_var("head", 181),
            size: Some(Box::new(size_ref)),
            specs: vec![],
            span: span(),
        }],
        span: span(),
    };
    let body = MExpr::Case {
        scrutinee: var("bits", 182),
        arms: vec![MArm {
            pattern,
            guard: None,
            body: MExpr::Pure(lit_int("1", 1)),
            span: span(),
        }],
        source: crate::ast::NodeId(183),
    };
    let prog = val_program(MExpr::Let {
        var: mv("i", 184),
        value: Box::new(MExpr::Pure(lit_int("2", 2))),
        body: Box::new(body.clone()),
    });

    let out = run(prog.clone(), &f.h, &info);

    assert_eq!(out, prog);
}

#[test]
fn dead_pure_let_keeps_unused_effectful_value() {
    let f = Fixture::new();
    let info = f.info();
    let value = MExpr::ForeignCall {
        module: "erlang".to_string(),
        func: "monotonic_time".to_string(),
        args: vec![],
        source: crate::ast::NodeId(79),
    };
    let prog = val_program(MExpr::Let {
        var: mv("unused", 80),
        value: Box::new(value.clone()),
        body: Box::new(MExpr::Pure(lit_int("3", 3))),
    });

    let out = run(prog, &f.h, &info);

    assert_eq!(
        out,
        val_program(MExpr::Let {
            var: mv("unused", 80),
            value: Box::new(value),
            body: Box::new(MExpr::Pure(lit_int("3", 3))),
        })
    );
}

#[test]
fn bind_to_let_keeps_app_with_effect_row() {
    let mut f = Fixture::new();
    let source = crate::ast::NodeId(80);
    let head_source = crate::ast::NodeId(81);
    f.type_at_node
        .insert(head_source, effectful_fun_type("Log"));
    let info = f.info();
    let value = MExpr::App {
        head: var("log_fun", 81),
        args: vec![lit_int("1", 1)],
        source,
    };
    let body = MExpr::Pure(var("x", 1));
    let prog = val_program(bind_expr(mv("x", 1), value, body));

    let out = run(prog.clone(), &f.h, &info);

    assert_eq!(out, prog);
}

#[test]
fn bind_to_let_does_not_treat_app_result_type_as_purity_evidence() {
    let mut f = Fixture::new();
    let source = crate::ast::NodeId(90);
    f.type_at_node.insert(
        source,
        crate::typechecker::Type::Con("Int".to_string(), vec![]),
    );
    let info = f.info();
    let value = MExpr::App {
        head: var("unknown_fun", 91),
        args: vec![lit_int("1", 1)],
        source,
    };
    let body = MExpr::Pure(var("x", 1));
    let prog = val_program(bind_expr(mv("x", 1), value, body));

    let out = run(prog.clone(), &f.h, &info);

    assert_eq!(out, prog);
}

#[test]
fn direct_call_inlines_static_tail_resumptive_yield() {
    let mut f = Fixture::new();
    let arm = tail_arm(100, vec![pat_unit(101)], resume(lit_int("42", 42)), None);
    f.h.resumption
        .insert(crate::ast::NodeId(100), ResumptionKind::TailResumptive);
    let handler = static_log_handler(vec![arm]);
    let prog = val_program(with_expr(
        handler.clone(),
        yield_log(vec![unit_atom()], crate::ast::NodeId(102)),
    ));
    let info = f.info();

    let out = run(prog, &f.h, &info);

    assert_eq!(
        out,
        val_program(with_expr(handler, MExpr::Pure(lit_int("42", 42))))
    );
}

#[test]
fn direct_call_exposes_bind_pure_collapse_in_same_fixpoint() {
    let mut f = Fixture::new();
    let arm = tail_arm(110, vec![pat_unit(111)], resume(lit_int("42", 42)), None);
    f.h.resumption
        .insert(crate::ast::NodeId(110), ResumptionKind::TailResumptive);
    let handler = static_log_handler(vec![arm]);
    let body = bind_expr(
        mv("x", 1),
        yield_log(vec![unit_atom()], crate::ast::NodeId(112)),
        MExpr::Pure(var("x", 1)),
    );
    let prog = val_program(with_expr(handler.clone(), body));
    let info = f.info();

    let out = run(prog, &f.h, &info);

    assert_eq!(
        out,
        val_program(with_expr(handler, MExpr::Pure(lit_int("42", 42))))
    );
}

#[test]
fn direct_call_substitutes_supported_var_params() {
    let mut f = Fixture::new();
    let arm = tail_arm(
        120,
        vec![pat_var("msg", 121)],
        resume(var("msg", 121)),
        None,
    );
    f.h.resumption
        .insert(crate::ast::NodeId(120), ResumptionKind::TailResumptive);
    let handler = static_log_handler(vec![arm]);
    let prog = val_program(with_expr(
        handler.clone(),
        yield_log(vec![lit_int("7", 7)], crate::ast::NodeId(122)),
    ));
    let info = f.info();

    let out = run(prog, &f.h, &info);

    assert_eq!(
        out,
        val_program(with_expr(handler, MExpr::Pure(lit_int("7", 7))))
    );
}

#[test]
fn direct_call_keeps_oneshot_and_multishot_monadic() {
    for (id, kind) in [
        (130, ResumptionKind::OneShot),
        (131, ResumptionKind::Multishot),
    ] {
        let mut f = Fixture::new();
        let arm = tail_arm(id, vec![pat_unit(id + 10)], resume(lit_int("1", 1)), None);
        f.h.resumption.insert(crate::ast::NodeId(id), kind);
        let handler = static_log_handler(vec![arm]);
        let yield_expr = yield_log(vec![unit_atom()], crate::ast::NodeId(id + 20));
        let prog = val_program(with_expr(handler.clone(), yield_expr.clone()));
        let info = f.info();

        let out = run(prog, &f.h, &info);

        assert_eq!(out, val_program(with_expr(handler, yield_expr)));
    }
}

#[test]
fn direct_call_skips_arm_with_finally() {
    let mut f = Fixture::new();
    let arm = tail_arm(
        140,
        vec![pat_unit(141)],
        resume(lit_int("1", 1)),
        Some(MExpr::Pure(unit_atom())),
    );
    f.h.resumption
        .insert(crate::ast::NodeId(140), ResumptionKind::TailResumptive);
    let handler = static_log_handler(vec![arm]);
    let yield_expr = yield_log(vec![unit_atom()], crate::ast::NodeId(142));
    let prog = val_program(with_expr(handler.clone(), yield_expr.clone()));
    let info = f.info();

    let out = run(prog, &f.h, &info);

    assert_eq!(out, val_program(with_expr(handler, yield_expr)));
}

#[test]
fn direct_call_with_finally_wraps_resumed_continuation_in_ensure() {
    let mut f = Fixture::new();
    let arm = tail_arm(
        143,
        vec![pat_unit(144)],
        resume(lit_int("1", 1)),
        Some(MExpr::Pure(unit_atom())),
    );
    f.h.resumption
        .insert(crate::ast::NodeId(143), ResumptionKind::TailResumptive);
    let handler = static_log_handler(vec![arm]);
    let body = bind_expr(
        mv("x", 145),
        yield_log(vec![unit_atom()], crate::ast::NodeId(146)),
        MExpr::Pure(var("x", 145)),
    );
    let prog = val_program(with_expr(handler.clone(), body));
    let info = f.info();

    let out = run(prog, &f.h, &info);

    assert_eq!(
        out,
        val_program(with_expr(
            handler,
            MExpr::Ensure {
                body: Box::new(MExpr::Pure(lit_int("1", 1))),
                cleanup: Box::new(MExpr::Pure(unit_atom())),
            }
        ))
    );
}

#[test]
fn direct_call_with_finally_skips_cleanup_that_uses_arm_local() {
    let mut f = Fixture::new();
    let arm_body = bind_expr(
        mv("resource", 148),
        MExpr::Pure(lit_int("1", 1)),
        resume(var("resource", 148)),
    );
    let arm = tail_arm(
        149,
        vec![pat_unit(150)],
        arm_body,
        Some(MExpr::Pure(var("resource", 148))),
    );
    f.h.resumption
        .insert(crate::ast::NodeId(149), ResumptionKind::TailResumptive);
    let handler = static_log_handler(vec![arm]);
    let body = bind_expr(
        mv("x", 151),
        yield_log(vec![unit_atom()], crate::ast::NodeId(152)),
        MExpr::Pure(var("x", 151)),
    );
    let prog = val_program(with_expr(handler.clone(), body.clone()));
    let info = f.info();

    let out = run(prog, &f.h, &info);

    let MDecl::Val(MVal {
        value: MExpr::With { body, .. },
        ..
    }) = &out[0]
    else {
        panic!("expected val with with-expression");
    };
    assert!(matches!(
        &**body,
        MExpr::Bind {
            value,
            ..
        } if matches!(&**value, MExpr::Yield { .. })
    ));
}

#[test]
fn direct_call_skips_multi_arm_same_op_dispatch() {
    let mut f = Fixture::new();
    let arm_a = tail_arm(145, vec![pat_unit(146)], resume(lit_int("1", 1)), None);
    let arm_b = tail_arm(147, vec![pat_unit(148)], resume(lit_int("2", 2)), None);
    f.h.resumption
        .insert(crate::ast::NodeId(145), ResumptionKind::TailResumptive);
    f.h.resumption
        .insert(crate::ast::NodeId(147), ResumptionKind::TailResumptive);
    let handler = static_log_handler(vec![arm_a, arm_b]);
    let yield_expr = yield_log(vec![unit_atom()], crate::ast::NodeId(149));
    let prog = val_program(with_expr(handler.clone(), yield_expr.clone()));
    let info = f.info();

    let out = run(prog, &f.h, &info);

    assert_eq!(out, val_program(with_expr(handler, yield_expr)));
}

#[test]
fn direct_call_skips_arm_body_with_yield_to_avoid_recursive_expansion() {
    let mut f = Fixture::new();
    let recursive_body = MExpr::Bind {
        var: mv("_", 151),
        value: Box::new(yield_log(vec![unit_atom()], crate::ast::NodeId(152))),
        body: Box::new(resume(unit_atom())),
        mode: crate::codegen::monadic::ir::BindMode::Sequence,
    };
    let arm = tail_arm(153, vec![pat_unit(154)], recursive_body, None);
    f.h.resumption
        .insert(crate::ast::NodeId(153), ResumptionKind::TailResumptive);
    let handler = static_log_handler(vec![arm]);
    let yield_expr = yield_log(vec![unit_atom()], crate::ast::NodeId(155));
    let prog = val_program(with_expr(handler.clone(), yield_expr.clone()));
    let info = f.info();

    let out = run(prog, &f.h, &info);

    assert_eq!(out, val_program(with_expr(handler, yield_expr)));
}

#[test]
fn direct_call_dynamic_same_effect_blocks_outer_static_handler() {
    let mut f = Fixture::new();
    let outer_arm = tail_arm(150, vec![pat_unit(151)], resume(lit_int("1", 1)), None);
    f.h.resumption
        .insert(crate::ast::NodeId(150), ResumptionKind::TailResumptive);
    let outer = static_log_handler(vec![outer_arm]);
    let inner = MHandler::Dynamic {
        effects: vec!["Log".to_string()],
        op_tuple: var("dynamic_ops", 152),
        return_lambda: None,
        source: crate::ast::NodeId(153),
    };
    let yield_expr = yield_log(vec![unit_atom()], crate::ast::NodeId(154));
    let prog = val_program(with_expr(
        outer.clone(),
        with_expr(inner.clone(), yield_expr.clone()),
    ));
    let info = f.info();

    let out = run(prog, &f.h, &info);

    assert_eq!(
        out,
        val_program(with_expr(outer, with_expr(inner, yield_expr)))
    );
}

#[test]
fn direct_call_native_same_effect_blocks_outer_static_handler() {
    let mut f = Fixture::new();
    let outer_arm = tail_arm(160, vec![pat_unit(161)], resume(lit_int("1", 1)), None);
    f.h.resumption
        .insert(crate::ast::NodeId(160), ResumptionKind::TailResumptive);
    let outer = static_log_handler(vec![outer_arm]);
    let inner = MHandler::Native {
        effects: vec!["Log".to_string()],
        handler: "native_log".to_string(),
        source: crate::ast::NodeId(162),
    };
    let yield_expr = yield_log(vec![unit_atom()], crate::ast::NodeId(163));
    let prog = val_program(with_expr(
        outer.clone(),
        with_expr(inner.clone(), yield_expr.clone()),
    ));
    let info = f.info();

    let out = run(prog, &f.h, &info);

    assert_eq!(
        out,
        val_program(with_expr(outer, with_expr(inner, yield_expr)))
    );
}

#[test]
fn direct_call_composite_same_effect_is_blocking_not_decomposed() {
    let mut f = Fixture::new();
    let inner_arm = tail_arm(170, vec![pat_unit(171)], resume(lit_int("1", 1)), None);
    f.h.resumption
        .insert(crate::ast::NodeId(170), ResumptionKind::TailResumptive);
    let inner_static = static_log_handler(vec![inner_arm]);
    let composite = MHandler::Composite {
        handlers: vec![inner_static],
        source: crate::ast::NodeId(172),
    };
    let yield_expr = yield_log(vec![unit_atom()], crate::ast::NodeId(173));
    let prog = val_program(with_expr(composite.clone(), yield_expr.clone()));
    let info = f.info();

    let out = run(prog, &f.h, &info);

    assert_eq!(out, val_program(with_expr(composite, yield_expr)));
}

#[test]
fn direct_call_does_not_inherit_handler_stack_into_lambda_body() {
    let mut f = Fixture::new();
    let arm = tail_arm(180, vec![pat_unit(181)], resume(lit_int("1", 1)), None);
    f.h.resumption
        .insert(crate::ast::NodeId(180), ResumptionKind::TailResumptive);
    let handler = static_log_handler(vec![arm]);
    let lambda = Atom::Lambda {
        params: vec![pat_unit(182)],
        body: Box::new(yield_log(vec![unit_atom()], crate::ast::NodeId(183))),
        source: crate::ast::NodeId(184),
    };
    let prog = val_program(with_expr(handler.clone(), MExpr::Pure(lambda.clone())));
    let info = f.info();

    let out = run(prog, &f.h, &info);

    assert_eq!(out, val_program(with_expr(handler, MExpr::Pure(lambda))));
}

#[test]
fn direct_call_skips_unsupported_param_patterns() {
    let mut f = Fixture::new();
    let arm = tail_arm(
        190,
        vec![Pat::Tuple {
            id: crate::ast::NodeId(191),
            elements: vec![pat_var("x", 192)],
            span: span(),
        }],
        resume(var("x", 192)),
        None,
    );
    f.h.resumption
        .insert(crate::ast::NodeId(190), ResumptionKind::TailResumptive);
    let handler = static_log_handler(vec![arm]);
    let yield_expr = yield_log(
        vec![Atom::Tuple {
            elements: vec![lit_int("1", 1)],
            source: crate::ast::NodeId(193),
        }],
        crate::ast::NodeId(194),
    );
    let prog = val_program(with_expr(handler.clone(), yield_expr.clone()));
    let info = f.info();

    let out = run(prog, &f.h, &info);

    assert_eq!(out, val_program(with_expr(handler, yield_expr)));
}

#[test]
fn native_direct_call_rewrites_identity_op() {
    let f = Fixture::new();
    let handler = native_handler("Std.Actor.Timer", "beam_actor", 200);
    let yield_expr = yield_native("Std.Actor.Timer", "sleep", vec![lit_int("10", 10)], 201);
    let prog = val_program(with_expr(handler.clone(), yield_expr));
    let info = f.info();

    let out = run(prog, &f.h, &info);

    assert_eq!(
        out,
        val_program(with_expr(
            handler,
            MExpr::ForeignCall {
                module: "timer".to_string(),
                func: "sleep".to_string(),
                args: vec![lit_int("10", 10)],
                source: crate::ast::NodeId(201),
            }
        ))
    );
}

#[test]
fn native_direct_call_rewrites_no_args_op() {
    let f = Fixture::new();
    let handler = native_handler("Std.Actor.Actor", "beam_actor", 210);
    let yield_expr = yield_native("Std.Actor.Actor", "self", vec![unit_atom()], 211);
    let prog = val_program(with_expr(handler.clone(), yield_expr));
    let info = f.info();

    let out = run(prog, &f.h, &info);

    assert_eq!(
        out,
        val_program(with_expr(
            handler,
            MExpr::ForeignCall {
                module: "erlang".to_string(),
                func: "self".to_string(),
                args: vec![],
                source: crate::ast::NodeId(211),
            }
        ))
    );
}

#[test]
fn native_direct_call_rewrites_reordered_args() {
    let f = Fixture::new();
    let handler = native_handler("Std.Actor.Timer", "beam_actor", 220);
    let yield_expr = yield_native(
        "Std.Actor.Timer",
        "send_after",
        vec![lit_int("1", 1), lit_int("2", 2), lit_int("3", 3)],
        221,
    );
    let prog = val_program(with_expr(handler.clone(), yield_expr));
    let info = f.info();

    let out = run(prog, &f.h, &info);

    assert_eq!(
        out,
        val_program(with_expr(
            handler,
            MExpr::ForeignCall {
                module: "erlang".to_string(),
                func: "send_after".to_string(),
                args: vec![lit_int("2", 2), lit_int("1", 1), lit_int("3", 3)],
                source: crate::ast::NodeId(221),
            }
        ))
    );
}

#[test]
fn native_direct_call_rewrites_prepend_atom_op() {
    let f = Fixture::new();
    let handler = native_handler("Std.Actor.Monitor", "beam_actor", 222);
    let yield_expr = yield_native("Std.Actor.Monitor", "monitor", vec![lit_int("1", 1)], 223);
    let prog = val_program(with_expr(handler.clone(), yield_expr));
    let info = f.info();

    let out = run(prog, &f.h, &info);

    assert_eq!(
        out,
        val_program(with_expr(
            handler,
            MExpr::ForeignCall {
                module: "erlang".to_string(),
                func: "monitor".to_string(),
                args: vec![
                    backend_atom_at("process", crate::ast::NodeId(223)),
                    lit_int("1", 1)
                ],
                source: crate::ast::NodeId(223),
            }
        ))
    );
}

#[test]
fn native_direct_call_rewrites_beam_ref_get() {
    let f = Fixture::new();
    let handler = native_handler("Std.Ref.Ref", "beam_ref", 223);
    let yield_expr = yield_native("Std.Ref.Ref", "get", vec![lit_int("1", 1)], 224);
    let prog = val_program(with_expr(handler.clone(), yield_expr));
    let info = f.info();

    let out = run(prog, &f.h, &info);

    assert_eq!(
        out,
        val_program(with_expr(
            handler,
            MExpr::ForeignCall {
                module: "erlang".to_string(),
                func: "get".to_string(),
                args: vec![lit_int("1", 1)],
                source: crate::ast::NodeId(224),
            }
        ))
    );
}

#[test]
fn native_direct_call_rewrites_beam_ref_set() {
    let f = Fixture::new();
    let handler = native_handler("Std.Ref.Ref", "beam_ref", 225);
    let yield_expr = yield_native(
        "Std.Ref.Ref",
        "set",
        vec![lit_int("1", 1), lit_int("2", 2)],
        226,
    );
    let prog = val_program(with_expr(handler.clone(), yield_expr));
    let info = f.info();

    let out = run(prog, &f.h, &info);

    assert_eq!(
        out,
        val_program(with_expr(
            handler,
            MExpr::Bind {
                var: MVar {
                    name: "__native_ref_set_226".to_string(),
                    id: 226,
                },
                value: Box::new(MExpr::ForeignCall {
                    module: "erlang".to_string(),
                    func: "put".to_string(),
                    args: vec![lit_int("1", 1), lit_int("2", 2)],
                    source: crate::ast::NodeId(226),
                }),
                body: Box::new(MExpr::Pure(unit_atom_at(crate::ast::NodeId(226)))),
                mode: crate::codegen::monadic::ir::BindMode::Sequence,
            }
        ))
    );
}

#[test]
fn native_direct_call_rewrites_beam_ref_new() {
    let f = Fixture::new();
    let handler = native_handler("Std.Ref.Ref", "beam_ref", 227);
    let yield_expr = yield_native("Std.Ref.Ref", "new", vec![lit_int("42", 42)], 228);
    let key = MVar {
        name: "__native_ref_key_228".to_string(),
        id: 228,
    };
    let prog = val_program(with_expr(handler.clone(), yield_expr));
    let info = f.info();

    let out = run(prog, &f.h, &info);

    assert_eq!(
        out,
        val_program(with_expr(
            handler,
            MExpr::Bind {
                var: key.clone(),
                value: Box::new(MExpr::ForeignCall {
                    module: "erlang".to_string(),
                    func: "make_ref".to_string(),
                    args: vec![],
                    source: crate::ast::NodeId(228),
                }),
                body: Box::new(MExpr::Bind {
                    var: MVar {
                        name: "__native_ref_put_228".to_string(),
                        id: 229,
                    },
                    value: Box::new(MExpr::ForeignCall {
                        module: "erlang".to_string(),
                        func: "put".to_string(),
                        args: vec![
                            Atom::Var {
                                name: key.clone(),
                                source: crate::ast::NodeId(228),
                            },
                            lit_int("42", 42),
                        ],
                        source: crate::ast::NodeId(228),
                    }),
                    body: Box::new(MExpr::Pure(Atom::Var {
                        name: key,
                        source: crate::ast::NodeId(228),
                    })),
                    mode: crate::codegen::monadic::ir::BindMode::Sequence,
                }),
                mode: crate::codegen::monadic::ir::BindMode::Sequence,
            }
        ))
    );
}

#[test]
fn native_direct_call_rewrites_spawn_with_backend_thunk() {
    let f = Fixture::new();
    let handler = native_handler("Std.Actor.Process", "beam_actor", 241);
    let callback = var("callback", 230);
    let yield_expr = yield_native("Std.Actor.Process", "spawn", vec![callback.clone()], 231);
    let prog = val_program(with_expr(handler.clone(), yield_expr));
    let info = f.info();

    let out = run(prog, &f.h, &info);

    assert_eq!(
        out,
        val_program(with_expr(
            handler,
            MExpr::ForeignCall {
                module: "erlang".to_string(),
                func: "spawn".to_string(),
                args: vec![Atom::BackendSpawnThunk {
                    callback: Box::new(callback),
                    source: crate::ast::NodeId(231),
                }],
                source: crate::ast::NodeId(231),
            }
        ))
    );
}

#[test]
fn native_direct_call_skips_ref_vec_and_unknown_handler_backends() {
    for (effect, handler_name, op, args, source) in [
        (
            "Std.Ref.Ref",
            "ets_ref",
            "get",
            vec![lit_int("1", 1)],
            crate::ast::NodeId(241),
        ),
        (
            "Std.Vec.Vec",
            "beam_vec",
            "vec_len",
            vec![lit_int("1", 1)],
            crate::ast::NodeId(242),
        ),
        (
            "Std.Ref.Ref",
            "beam_ref",
            "modify",
            vec![lit_int("1", 1), unit_atom()],
            crate::ast::NodeId(243),
        ),
    ] {
        let f = Fixture::new();
        let handler = native_handler(effect, handler_name, source.0 + 10);
        let yield_expr = yield_native(effect, op, args, source.0);
        let prog = val_program(with_expr(handler.clone(), yield_expr.clone()));
        let info = f.info();

        let out = run(prog, &f.h, &info);

        assert_eq!(out, val_program(with_expr(handler, yield_expr)));
    }
}

#[test]
fn native_direct_call_respects_inner_blockers() {
    let f = Fixture::new();
    let outer = native_handler("Std.Actor.Timer", "beam_actor", 250);
    let dynamic = MHandler::Dynamic {
        effects: vec!["Std.Actor.Timer".to_string()],
        op_tuple: var("ops", 251),
        return_lambda: None,
        source: crate::ast::NodeId(252),
    };
    let yield_expr = yield_native("Std.Actor.Timer", "sleep", vec![lit_int("10", 10)], 253);
    let prog = val_program(with_expr(
        outer.clone(),
        with_expr(dynamic.clone(), yield_expr.clone()),
    ));
    let info = f.info();

    let out = run(prog, &f.h, &info);

    assert_eq!(
        out,
        val_program(with_expr(outer, with_expr(dynamic, yield_expr)))
    );
}

#[test]
fn native_direct_call_respects_static_and_composite_blockers() {
    let f = Fixture::new();
    let outer = native_handler("Std.Actor.Timer", "beam_actor", 260);
    let blocking_arm = MHandlerArm {
        id: crate::ast::NodeId(261),
        op: effect_op("Std.Actor.Timer", "sleep", 2),
        params: vec![pat_var("ms", 262)],
        body: Box::new(resume(var("ms", 262))),
        finally_block: None,
        span: span(),
    };
    let static_inner = MHandler::Static {
        effects: vec!["Std.Actor.Timer".to_string()],
        arms: vec![blocking_arm],
        return_clause: None,
        source: crate::ast::NodeId(263),
    };
    let composite = MHandler::Composite {
        handlers: vec![native_handler("Std.Actor.Timer", "beam_actor", 264)],
        source: crate::ast::NodeId(265),
    };

    for inner in [static_inner, composite] {
        let yield_expr = yield_native("Std.Actor.Timer", "sleep", vec![lit_int("10", 10)], 266);
        let prog = val_program(with_expr(
            outer.clone(),
            with_expr(inner.clone(), yield_expr.clone()),
        ));
        let info = f.info();

        let out = run(prog, &f.h, &info);

        assert_eq!(
            out,
            val_program(with_expr(outer.clone(), with_expr(inner, yield_expr)))
        );
    }
}

#[test]
fn native_direct_call_skips_unknown_op_and_arg_mismatch() {
    for (op, args, source) in [
        ("missing", vec![lit_int("1", 1)], crate::ast::NodeId(270)),
        ("sleep", vec![], crate::ast::NodeId(271)),
    ] {
        let f = Fixture::new();
        let handler = native_handler("Std.Actor.Timer", "beam_actor", source.0 + 10);
        let yield_expr = yield_native("Std.Actor.Timer", op, args, source.0);
        let prog = val_program(with_expr(handler.clone(), yield_expr.clone()));
        let info = f.info();

        let out = run(prog, &f.h, &info);

        assert_eq!(out, val_program(with_expr(handler, yield_expr)));
    }
}

#[test]
fn helper_inline_exposes_yield_to_static_direct_call() {
    let mut f = Fixture::new();
    let arm = tail_arm(280, vec![pat_unit(281)], resume(lit_int("42", 42)), None);
    f.h.resumption
        .insert(crate::ast::NodeId(280), ResumptionKind::TailResumptive);
    let handler = static_log_handler(vec![arm]);
    let helper = helper_fun(
        "helper",
        282,
        vec![pat_unit(283)],
        yield_log(vec![unit_atom()], crate::ast::NodeId(284)),
    );
    let caller = MDecl::Val(MVal {
        id: crate::ast::NodeId(285),
        public: false,
        name: "caller".to_string(),
        value: with_expr(
            handler.clone(),
            MExpr::App {
                head: var("helper", 286),
                args: vec![unit_atom()],
                source: crate::ast::NodeId(287),
            },
        ),
        span: span(),
    });
    let info = f.info();

    let out = run(vec![helper.clone(), caller], &f.h, &info);

    assert_eq!(
        out,
        vec![
            helper,
            MDecl::Val(MVal {
                id: crate::ast::NodeId(285),
                public: false,
                name: "caller".to_string(),
                value: with_expr(handler, MExpr::Pure(lit_int("42", 42))),
                span: span(),
            })
        ]
    );
}

#[test]
fn helper_inline_skips_multi_clause_function() {
    let mut f = Fixture::new();
    let arm = tail_arm(290, vec![pat_unit(291)], resume(lit_int("42", 42)), None);
    f.h.resumption
        .insert(crate::ast::NodeId(290), ResumptionKind::TailResumptive);
    let handler = static_log_handler(vec![arm]);
    let helper_a = helper_fun(
        "helper",
        292,
        vec![pat_unit(293)],
        yield_log(vec![unit_atom()], crate::ast::NodeId(294)),
    );
    let helper_b = helper_fun(
        "helper",
        295,
        vec![pat_var("x", 296)],
        MExpr::Pure(var("x", 296)),
    );
    let call = MExpr::App {
        head: var("helper", 297),
        args: vec![unit_atom()],
        source: crate::ast::NodeId(298),
    };
    let caller = MDecl::Val(MVal {
        id: crate::ast::NodeId(299),
        public: false,
        name: "caller".to_string(),
        value: with_expr(handler.clone(), call.clone()),
        span: span(),
    });
    let info = f.info();

    let out = run(
        vec![helper_a.clone(), helper_b.clone(), caller],
        &f.h,
        &info,
    );

    assert_eq!(
        out,
        vec![
            helper_a,
            helper_b,
            MDecl::Val(MVal {
                id: crate::ast::NodeId(299),
                public: false,
                name: "caller".to_string(),
                value: with_expr(handler, call),
                span: span(),
            })
        ]
    );
}

#[test]
fn helper_inline_respects_dynamic_same_effect_blocker() {
    let mut f = Fixture::new();
    let arm = tail_arm(300, vec![pat_unit(301)], resume(lit_int("42", 42)), None);
    f.h.resumption
        .insert(crate::ast::NodeId(300), ResumptionKind::TailResumptive);
    let outer = static_log_handler(vec![arm]);
    let dynamic = MHandler::Dynamic {
        effects: vec!["Log".to_string()],
        op_tuple: var("ops", 302),
        return_lambda: None,
        source: crate::ast::NodeId(303),
    };
    let helper = helper_fun(
        "helper",
        304,
        vec![pat_unit(305)],
        yield_log(vec![unit_atom()], crate::ast::NodeId(306)),
    );
    let caller = MDecl::Val(MVal {
        id: crate::ast::NodeId(307),
        public: false,
        name: "caller".to_string(),
        value: with_expr(
            outer.clone(),
            with_expr(
                dynamic.clone(),
                MExpr::App {
                    head: var("helper", 308),
                    args: vec![unit_atom()],
                    source: crate::ast::NodeId(309),
                },
            ),
        ),
        span: span(),
    });
    let info = f.info();

    let out = run(vec![helper.clone(), caller], &f.h, &info);

    assert_eq!(
        out,
        vec![
            helper,
            MDecl::Val(MVal {
                id: crate::ast::NodeId(307),
                public: false,
                name: "caller".to_string(),
                value: with_expr(
                    outer,
                    with_expr(
                        dynamic,
                        MExpr::App {
                            head: var("helper", 308),
                            args: vec![unit_atom()],
                            source: crate::ast::NodeId(309),
                        }
                    )
                ),
                span: span(),
            })
        ]
    );
}

#[test]
fn helper_inline_skips_multi_yield_helper() {
    let mut f = Fixture::new();
    let arm = tail_arm(310, vec![pat_unit(311)], resume(lit_int("42", 42)), None);
    f.h.resumption
        .insert(crate::ast::NodeId(310), ResumptionKind::TailResumptive);
    let handler = static_log_handler(vec![arm]);
    let helper_body = bind_expr(
        mv("_", 312),
        yield_log(vec![unit_atom()], crate::ast::NodeId(313)),
        yield_fail(vec![lit_int("1", 1)], crate::ast::NodeId(314)),
    );
    let helper = helper_fun("helper", 315, vec![pat_unit(316)], helper_body);
    let call = MExpr::App {
        head: var("helper", 317),
        args: vec![unit_atom()],
        source: crate::ast::NodeId(318),
    };
    let caller = MDecl::Val(MVal {
        id: crate::ast::NodeId(319),
        public: false,
        name: "caller".to_string(),
        value: with_expr(handler.clone(), call.clone()),
        span: span(),
    });
    let info = f.info();

    let out = run(vec![helper.clone(), caller], &f.h, &info);

    assert_eq!(
        out,
        vec![
            helper,
            MDecl::Val(MVal {
                id: crate::ast::NodeId(319),
                public: false,
                name: "caller".to_string(),
                value: with_expr(handler, call),
                span: span(),
            })
        ]
    );
}

#[test]
fn native_function_variant_specializes_same_module_call_under_native_handler() {
    let f = Fixture::new();
    let handler = native_handler("Std.Actor.Timer", "beam_actor", 330);
    let helper_body = bind_expr(
        mv("_first", 331),
        yield_native("Std.Actor.Timer", "sleep", vec![lit_int("10", 10)], 332),
        yield_native("Std.Actor.Timer", "sleep", vec![lit_int("20", 20)], 333),
    );
    let helper = helper_fun("helper", 334, vec![pat_unit(335)], helper_body);
    let caller = MDecl::Val(MVal {
        id: crate::ast::NodeId(336),
        public: true,
        name: "caller".to_string(),
        value: with_expr(
            handler,
            MExpr::App {
                head: var("helper", 337),
                args: vec![unit_atom()],
                source: crate::ast::NodeId(338),
            },
        ),
        span: span(),
    });
    let info = f.info();

    let out = run(vec![helper.clone(), caller], &f.h, &info);

    let variant_name = out
        .iter()
        .find_map(|decl| match decl {
            MDecl::FunBinding(f) if is_generated_variant_name(&f.name) => Some(f.name.clone()),
            _ => None,
        })
        .expect("expected generated native function variant");
    assert_ne!(variant_name, "helper");
    assert!(!out.iter().any(|decl| decl == &helper));

    let caller = find_val(&out, "caller");
    let MExpr::With { body, .. } = &caller.value else {
        panic!("expected caller with-expression");
    };
    assert_eq!(
        body.as_ref(),
        &MExpr::App {
            head: Atom::Var {
                name: mv(&variant_name, 337),
                source: crate::ast::NodeId(334),
            },
            args: vec![unit_atom()],
            source: crate::ast::NodeId(338),
        }
    );

    let variant = out
        .iter()
        .find_map(|decl| match decl {
            MDecl::FunBinding(f) if f.name == variant_name => Some(f),
            _ => None,
        })
        .expect("expected generated variant decl");
    assert_eq!(
        variant.body,
        bind_expr(
            mv("_first", 331),
            MExpr::ForeignCall {
                module: "timer".to_string(),
                func: "sleep".to_string(),
                args: vec![lit_int("10", 10)],
                source: crate::ast::NodeId(332),
            },
            MExpr::ForeignCall {
                module: "timer".to_string(),
                func: "sleep".to_string(),
                args: vec![lit_int("20", 20)],
                source: crate::ast::NodeId(333),
            }
        )
    );
}

#[test]
fn native_function_variant_rewrites_direct_self_recursion_to_variant() {
    let f = Fixture::new();
    let handler = native_handler("Std.Actor.Timer", "beam_actor", 340);
    let helper_body = bind_expr(
        mv("_first", 341),
        yield_native("Std.Actor.Timer", "sleep", vec![lit_int("10", 10)], 342),
        MExpr::App {
            head: var("helper", 343),
            args: vec![unit_atom()],
            source: crate::ast::NodeId(344),
        },
    );
    let helper = helper_fun("helper", 345, vec![pat_unit(346)], helper_body);
    let call = MExpr::App {
        head: var("helper", 347),
        args: vec![unit_atom()],
        source: crate::ast::NodeId(348),
    };
    let caller = MDecl::Val(MVal {
        id: crate::ast::NodeId(349),
        public: true,
        name: "caller".to_string(),
        value: with_expr(handler.clone(), call.clone()),
        span: span(),
    });
    let info = f.info();

    let out = run(vec![helper.clone(), caller], &f.h, &info);

    let variant_name = out
        .iter()
        .find_map(|decl| match decl {
            MDecl::FunBinding(f) if is_generated_variant_name(&f.name) => Some(f.name.clone()),
            _ => None,
        })
        .expect("expected generated native function variant");
    assert!(!out.iter().any(|decl| decl == &helper));
    let caller = find_val(&out, "caller");
    let MExpr::With { body, .. } = &caller.value else {
        panic!("expected caller with-expression");
    };
    assert_eq!(
        body.as_ref(),
        &MExpr::App {
            head: Atom::Var {
                name: mv(&variant_name, 347),
                source: crate::ast::NodeId(345),
            },
            args: vec![unit_atom()],
            source: crate::ast::NodeId(348),
        }
    );

    let variant = out
        .iter()
        .find_map(|decl| match decl {
            MDecl::FunBinding(f) if f.name == variant_name => Some(f),
            _ => None,
        })
        .expect("expected generated variant decl");
    assert_eq!(
        variant.body,
        bind_expr(
            mv("_first", 341),
            MExpr::ForeignCall {
                module: "timer".to_string(),
                func: "sleep".to_string(),
                args: vec![lit_int("10", 10)],
                source: crate::ast::NodeId(342),
            },
            MExpr::App {
                head: Atom::Var {
                    name: mv(&variant_name, 343),
                    source: crate::ast::NodeId(345),
                },
                args: vec![unit_atom()],
                source: crate::ast::NodeId(344),
            }
        )
    );
}

#[test]
fn imported_native_function_variant_specializes_public_call_under_native_handler() {
    let f = Fixture::new();
    let handler = native_handler("Std.Actor.Timer", "beam_actor", 350);
    let imported = imported_candidate(
        "Lib",
        "worker",
        351,
        bind_expr(
            mv("_first", 352),
            yield_native("Std.Actor.Timer", "sleep", vec![lit_int("10", 10)], 353),
            yield_native("Std.Actor.Timer", "sleep", vec![lit_int("20", 20)], 354),
        ),
    );
    let caller = MDecl::Val(MVal {
        id: crate::ast::NodeId(355),
        public: true,
        name: "caller".to_string(),
        value: with_expr(
            handler,
            MExpr::App {
                head: var("worker", 356),
                args: vec![unit_atom()],
                source: crate::ast::NodeId(357),
            },
        ),
        span: span(),
    });
    let mut context = OptimizerContext::default();
    context.resolution.insert(
        crate::ast::NodeId(356),
        resolved_beam("worker", Some("Lib"), "Lib.worker"),
    );
    context
        .imported_function_variants
        .insert("Lib.worker".to_string(), imported);
    let info = f.info();

    let out = run_with_context(vec![caller], &f.h, &info, context);

    let variant_name = out
        .iter()
        .find_map(|decl| match decl {
            MDecl::FunBinding(f) if is_generated_variant_name(&f.name) => Some(f.name.clone()),
            _ => None,
        })
        .expect("expected generated imported native function variant");
    assert!(variant_name.contains("xmod"));
    assert!(variant_name.contains("Lib"));

    let caller = find_val(&out, "caller");
    let MExpr::With { body, .. } = &caller.value else {
        panic!("expected caller with-expression");
    };
    assert_eq!(
        body.as_ref(),
        &MExpr::App {
            head: Atom::Var {
                name: mv(&variant_name, 356),
                source: crate::ast::NodeId(351),
            },
            args: vec![unit_atom()],
            source: crate::ast::NodeId(357),
        }
    );

    let variant = out
        .iter()
        .find_map(|decl| match decl {
            MDecl::FunBinding(f) if f.name == variant_name => Some(f),
            _ => None,
        })
        .expect("expected generated variant decl");
    assert!(!variant.public);
    assert_eq!(
        variant.body,
        bind_expr(
            mv("_first", 352),
            MExpr::ForeignCall {
                module: "timer".to_string(),
                func: "sleep".to_string(),
                args: vec![lit_int("10", 10)],
                source: crate::ast::NodeId(353),
            },
            MExpr::ForeignCall {
                module: "timer".to_string(),
                func: "sleep".to_string(),
                args: vec![lit_int("20", 20)],
                source: crate::ast::NodeId(354),
            }
        )
    );
}

#[test]
fn imported_native_function_variant_rewrites_self_recursion_to_caller_variant() {
    let f = Fixture::new();
    let handler = native_handler("Std.Actor.Timer", "beam_actor", 358);
    let imported = imported_candidate(
        "Lib",
        "worker",
        359,
        bind_expr(
            mv("_first", 360),
            yield_native("Std.Actor.Timer", "sleep", vec![lit_int("10", 10)], 361),
            MExpr::App {
                head: var("worker", 362),
                args: vec![unit_atom()],
                source: crate::ast::NodeId(363),
            },
        ),
    );
    let caller = MDecl::Val(MVal {
        id: crate::ast::NodeId(364),
        public: true,
        name: "caller".to_string(),
        value: with_expr(
            handler,
            MExpr::App {
                head: var("worker", 365),
                args: vec![unit_atom()],
                source: crate::ast::NodeId(366),
            },
        ),
        span: span(),
    });
    let mut context = OptimizerContext::default();
    context.resolution.insert(
        crate::ast::NodeId(365),
        resolved_beam("worker", Some("Lib"), "Lib.worker"),
    );
    context
        .imported_function_variants
        .insert("Lib.worker".to_string(), imported);
    let info = f.info();

    let out = run_with_context(vec![caller], &f.h, &info, context);

    let variant = out
        .iter()
        .find_map(|decl| match decl {
            MDecl::FunBinding(f) if is_generated_variant_name(&f.name) => Some(f),
            _ => None,
        })
        .expect("expected generated imported native function variant");
    assert_eq!(
        variant.body,
        bind_expr(
            mv("_first", 360),
            MExpr::ForeignCall {
                module: "timer".to_string(),
                func: "sleep".to_string(),
                args: vec![lit_int("10", 10)],
                source: crate::ast::NodeId(361),
            },
            MExpr::App {
                head: Atom::Var {
                    name: mv(&variant.name, 362),
                    source: crate::ast::NodeId(359),
                },
                args: vec![unit_atom()],
                source: crate::ast::NodeId(363),
            }
        )
    );
}

#[test]
fn imported_native_function_variant_skips_static_handler_stack() {
    let mut f = Fixture::new();
    let arm = tail_arm(367, vec![pat_unit(368)], resume(lit_int("42", 42)), None);
    f.h.resumption
        .insert(crate::ast::NodeId(367), ResumptionKind::TailResumptive);
    let handler = static_log_handler(vec![arm]);
    let imported = imported_candidate(
        "Lib",
        "worker",
        369,
        yield_native("Std.Actor.Timer", "sleep", vec![lit_int("10", 10)], 370),
    );
    let call = MExpr::App {
        head: var("worker", 371),
        args: vec![unit_atom()],
        source: crate::ast::NodeId(372),
    };
    let caller = MDecl::Val(MVal {
        id: crate::ast::NodeId(373),
        public: true,
        name: "caller".to_string(),
        value: with_expr(handler.clone(), call.clone()),
        span: span(),
    });
    let mut context = OptimizerContext::default();
    context.resolution.insert(
        crate::ast::NodeId(371),
        resolved_beam("worker", Some("Lib"), "Lib.worker"),
    );
    context
        .imported_function_variants
        .insert("Lib.worker".to_string(), imported);
    let info = f.info();

    let out = run_with_context(vec![caller], &f.h, &info, context);

    assert_eq!(
        out,
        vec![MDecl::Val(MVal {
            id: crate::ast::NodeId(373),
            public: true,
            name: "caller".to_string(),
            value: with_expr(handler, call),
            span: span(),
        })]
    );
}

#[test]
fn imported_static_function_variant_specializes_when_all_yields_are_removed() {
    let mut f = Fixture::new();
    let arm = tail_arm(390, vec![pat_unit(391)], resume(lit_int("42", 42)), None);
    f.h.resumption
        .insert(crate::ast::NodeId(390), ResumptionKind::TailResumptive);
    let handler = static_log_handler(vec![arm]);
    let imported = imported_candidate(
        "Lib",
        "worker",
        392,
        bind_expr(
            mv("_first", 393),
            yield_log(vec![unit_atom()], crate::ast::NodeId(394)),
            yield_log(vec![unit_atom()], crate::ast::NodeId(395)),
        ),
    );
    let caller = MDecl::Val(MVal {
        id: crate::ast::NodeId(396),
        public: true,
        name: "caller".to_string(),
        value: with_expr(
            handler,
            MExpr::App {
                head: var("worker", 397),
                args: vec![unit_atom()],
                source: crate::ast::NodeId(398),
            },
        ),
        span: span(),
    });
    let mut context = OptimizerContext::default();
    context.resolution.insert(
        crate::ast::NodeId(397),
        resolved_beam("worker", Some("Lib"), "Lib.worker"),
    );
    context
        .imported_function_variants
        .insert("Lib.worker".to_string(), imported);
    let info = f.info();

    let out = run_with_context(vec![caller], &f.h, &info, context);

    let variant = out
        .iter()
        .find_map(|decl| match decl {
            MDecl::FunBinding(f) if f.name.starts_with(STATIC_VARIANT_PREFIX) => Some(f),
            _ => None,
        })
        .expect("expected generated imported static function variant");
    assert!(variant.name.contains("xmod"));
    assert_eq!(expr_yield_count(&variant.body), 0);
    assert_eq!(variant.body, MExpr::Pure(lit_int("42", 42)));
}

#[test]
fn imported_static_function_variant_skips_when_residual_yield_remains() {
    let mut f = Fixture::new();
    let arm = tail_arm(400, vec![pat_unit(401)], resume(lit_int("42", 42)), None);
    f.h.resumption
        .insert(crate::ast::NodeId(400), ResumptionKind::TailResumptive);
    let handler = static_log_handler(vec![arm]);
    let imported = imported_candidate(
        "Lib",
        "worker",
        402,
        bind_expr(
            mv("_first", 403),
            yield_log(vec![unit_atom()], crate::ast::NodeId(404)),
            yield_fail(vec![lit_int("1", 1)], crate::ast::NodeId(405)),
        ),
    );
    let call = MExpr::App {
        head: var("worker", 406),
        args: vec![unit_atom()],
        source: crate::ast::NodeId(407),
    };
    let caller = MDecl::Val(MVal {
        id: crate::ast::NodeId(408),
        public: true,
        name: "caller".to_string(),
        value: with_expr(handler.clone(), call.clone()),
        span: span(),
    });
    let mut context = OptimizerContext::default();
    context.resolution.insert(
        crate::ast::NodeId(406),
        resolved_beam("worker", Some("Lib"), "Lib.worker"),
    );
    context
        .imported_function_variants
        .insert("Lib.worker".to_string(), imported);
    let info = f.info();

    let out = run_with_context(vec![caller], &f.h, &info, context);

    assert_eq!(
        out,
        vec![MDecl::Val(MVal {
            id: crate::ast::NodeId(408),
            public: true,
            name: "caller".to_string(),
            value: with_expr(handler, call),
            span: span(),
        })]
    );
}

#[test]
fn imported_native_candidate_collection_skips_private_helper_dependency() {
    let worker = public_helper_fun(
        "worker",
        374,
        MExpr::App {
            head: var("private_helper", 375),
            args: vec![unit_atom()],
            source: crate::ast::NodeId(376),
        },
    );
    let private_helper = helper_fun(
        "private_helper",
        377,
        vec![pat_unit(378)],
        yield_native("Std.Actor.Timer", "sleep", vec![lit_int("10", 10)], 379),
    );
    let mut resolution = ResolutionMap::new();
    resolution.insert(
        crate::ast::NodeId(375),
        resolved_beam("private_helper", None, "private_helper"),
    );
    let info = module_info_with_exports(&["worker"]);

    let candidates = collect_imported_function_variant_candidates(
        "Lib",
        &vec![worker, private_helper],
        &resolution,
        &info,
    );

    assert!(!candidates.contains_key("Lib.worker"));
}

#[test]
fn imported_native_candidate_collection_allows_public_helper_dependency() {
    let worker = public_helper_fun(
        "worker",
        380,
        MExpr::App {
            head: var("public_helper", 381),
            args: vec![unit_atom()],
            source: crate::ast::NodeId(382),
        },
    );
    let public_helper = public_helper_fun(
        "public_helper",
        383,
        yield_native("Std.Actor.Timer", "sleep", vec![lit_int("10", 10)], 384),
    );
    let mut resolution = ResolutionMap::new();
    resolution.insert(
        crate::ast::NodeId(381),
        resolved_beam("public_helper", None, "public_helper"),
    );
    let info = module_info_with_exports(&["worker", "public_helper"]);

    let candidates = collect_imported_function_variant_candidates(
        "Lib",
        &vec![worker, public_helper],
        &resolution,
        &info,
    );

    assert!(candidates.contains_key("Lib.worker"));
    assert!(!candidates.contains_key("worker"));
}

#[test]
fn imported_variant_lookup_does_not_use_ambiguous_bare_name() {
    let f = Fixture::new();
    let mut context = OptimizerContext::default();
    context.imported_function_variants.insert(
        "LibA.worker".to_string(),
        imported_candidate(
            "LibA",
            "worker",
            3860,
            yield_native("Std.Actor.Timer", "sleep", vec![lit_int("10", 10)], 3861),
        ),
    );
    context.imported_function_variants.insert(
        "LibB.worker".to_string(),
        imported_candidate(
            "LibB",
            "worker",
            3862,
            yield_native("Std.Actor.Timer", "sleep", vec![lit_int("20", 20)], 3863),
        ),
    );
    let optimizer = Optimizer::new(RunOptions::default(), &f.h, context);
    let resolved = resolved_beam("worker", None, "worker");

    assert!(
        optimizer
            .lookup_imported_function_variant(&resolved)
            .is_none()
    );
}

#[test]
fn effect_name_matching_never_conflates_distinct_qualified_effects() {
    assert!(effect_names_match("Log", "Some.Module.Log"));
    assert!(effect_names_match("Some.Module.Log", "Log"));
    assert!(effect_names_match("Some.Module.Log", "Some.Module.Log"));
    assert!(!effect_names_match("Other.Module.Log", "Some.Module.Log"));
}

#[test]
fn imported_native_candidate_collection_skips_external_wrapper() {
    let worker = public_helper_fun(
        "worker",
        385,
        yield_native("Std.Actor.Timer", "sleep", vec![lit_int("10", 10)], 386),
    );
    let mut info = module_info_with_exports(&["worker"]);
    info.external_funs.push((
        "worker".to_string(),
        "lib".to_string(),
        "worker".to_string(),
        1,
    ));

    let candidates = collect_imported_function_variant_candidates(
        "Lib",
        &vec![worker],
        &ResolutionMap::new(),
        &info,
    );

    assert!(!candidates.contains_key("Lib.worker"));
}

#[test]
fn static_function_variant_specializes_multi_yield_same_module_call() {
    let mut f = Fixture::new();
    let arm = tail_arm(360, vec![pat_unit(361)], resume(lit_int("42", 42)), None);
    f.h.resumption
        .insert(crate::ast::NodeId(360), ResumptionKind::TailResumptive);
    let handler = static_log_handler(vec![arm]);
    let helper_body = bind_expr(
        mv("_first", 362),
        yield_log(vec![unit_atom()], crate::ast::NodeId(363)),
        yield_log(vec![unit_atom()], crate::ast::NodeId(364)),
    );
    let helper = helper_fun("helper", 365, vec![pat_unit(366)], helper_body);
    let caller = MDecl::Val(MVal {
        id: crate::ast::NodeId(367),
        public: true,
        name: "caller".to_string(),
        value: with_expr(
            handler,
            MExpr::App {
                head: var("helper", 368),
                args: vec![unit_atom()],
                source: crate::ast::NodeId(369),
            },
        ),
        span: span(),
    });
    let info = f.info();

    let out = run(vec![helper.clone(), caller], &f.h, &info);

    let variant_name = out
        .iter()
        .find_map(|decl| match decl {
            MDecl::FunBinding(f) if f.name.starts_with(STATIC_VARIANT_PREFIX) => {
                Some(f.name.clone())
            }
            _ => None,
        })
        .expect("expected generated static function variant");
    assert!(!out.iter().any(|decl| decl == &helper));

    let caller = find_val(&out, "caller");
    let MExpr::With { body, .. } = &caller.value else {
        panic!("expected caller with-expression");
    };
    assert_eq!(
        body.as_ref(),
        &MExpr::App {
            head: Atom::Var {
                name: mv(&variant_name, 368),
                source: crate::ast::NodeId(365),
            },
            args: vec![unit_atom()],
            source: crate::ast::NodeId(369),
        }
    );

    let variant = out
        .iter()
        .find_map(|decl| match decl {
            MDecl::FunBinding(f) if f.name == variant_name => Some(f),
            _ => None,
        })
        .expect("expected generated variant decl");
    assert_eq!(variant.body, MExpr::Pure(lit_int("42", 42)));
}

#[test]
fn generated_variant_cleanup_keeps_public_source_function() {
    let f = Fixture::new();
    let handler = native_handler("Std.Actor.Timer", "beam_actor", 380);
    let helper_body = yield_native("Std.Actor.Timer", "sleep", vec![lit_int("10", 10)], 381);
    let mut helper = helper_fun("helper", 382, vec![pat_unit(383)], helper_body);
    let MDecl::FunBinding(helper_fun) = &mut helper else {
        panic!("expected helper fun");
    };
    helper_fun.public = true;
    let caller = MDecl::Val(MVal {
        id: crate::ast::NodeId(384),
        public: false,
        name: "caller".to_string(),
        value: with_expr(
            handler,
            MExpr::App {
                head: var("helper", 385),
                args: vec![unit_atom()],
                source: crate::ast::NodeId(386),
            },
        ),
        span: span(),
    });
    let info = f.info();

    let out = run(vec![helper.clone(), caller], &f.h, &info);

    assert!(out.iter().any(|decl| decl == &helper));
    assert!(out.iter().any(|decl| {
        matches!(decl, MDecl::FunBinding(f) if is_generated_variant_name(&f.name))
    }));
}

#[test]
fn static_function_variant_skips_multishot_arm() {
    let mut f = Fixture::new();
    let arm = tail_arm(370, vec![pat_unit(371)], resume(lit_int("42", 42)), None);
    f.h.resumption
        .insert(crate::ast::NodeId(370), ResumptionKind::Multishot);
    let handler = static_log_handler(vec![arm]);
    let helper_body = bind_expr(
        mv("_first", 372),
        yield_log(vec![unit_atom()], crate::ast::NodeId(373)),
        yield_log(vec![unit_atom()], crate::ast::NodeId(374)),
    );
    let helper = helper_fun("helper", 375, vec![pat_unit(376)], helper_body);
    let call = MExpr::App {
        head: var("helper", 377),
        args: vec![unit_atom()],
        source: crate::ast::NodeId(378),
    };
    let caller = MDecl::Val(MVal {
        id: crate::ast::NodeId(379),
        public: false,
        name: "caller".to_string(),
        value: with_expr(handler.clone(), call.clone()),
        span: span(),
    });
    let info = f.info();

    let out = run(vec![helper.clone(), caller], &f.h, &info);

    assert_eq!(
        out,
        vec![
            helper,
            MDecl::Val(MVal {
                id: crate::ast::NodeId(379),
                public: false,
                name: "caller".to_string(),
                value: with_expr(handler, call),
                span: span(),
            })
        ]
    );
}

fn val_program(value: MExpr) -> MProgram {
    vec![MDecl::Val(MVal {
        id: crate::ast::NodeId(1),
        public: false,
        name: "test_val".to_string(),
        value,
        span: span(),
    })]
}

fn helper_fun(name: &str, id: u32, params: Vec<Pat>, body: MExpr) -> MDecl {
    MDecl::FunBinding(MFunBinding {
        id: crate::ast::NodeId(id),
        public: false,
        name: name.to_string(),
        name_span: span(),
        params,
        guard: None,
        body,
        span: span(),
    })
}

fn public_helper_fun(name: &str, id: u32, body: MExpr) -> MDecl {
    let mut decl = helper_fun(name, id, vec![pat_unit(id + 1000)], body);
    let MDecl::FunBinding(f) = &mut decl else {
        panic!("expected helper fun");
    };
    f.public = true;
    decl
}

fn imported_candidate(
    source_module: &str,
    name: &str,
    id: u32,
    body: MExpr,
) -> ImportedFunctionVariantCandidate {
    let binding = MFunBinding {
        id: crate::ast::NodeId(id),
        public: true,
        name: name.to_string(),
        name_span: span(),
        params: vec![pat_unit(id + 1000)],
        guard: None,
        body,
        span: span(),
    };
    ImportedFunctionVariantCandidate {
        source_module: source_module.to_string(),
        binding,
        public_names: HashSet::from([name.to_string()]),
    }
}

fn resolved_beam(
    name: &str,
    source_module: Option<&str>,
    canonical_name: &str,
) -> crate::codegen::resolve::ResolvedSymbol {
    crate::codegen::resolve::ResolvedSymbol {
        name: name.to_string(),
        source_module: source_module.map(str::to_string),
        canonical_name: canonical_name.to_string(),
        kind: ResolvedCodegenKind::BeamFunction {
            erlang_mod: source_module.map(|module| module.to_lowercase().replace('.', "_")),
            name: name.to_string(),
            arity: 1,
            effects: vec!["Std.Actor.Timer".to_string()],
        },
    }
}

fn module_info_with_exports(names: &[&str]) -> ModuleCodegenInfo {
    ModuleCodegenInfo {
        exports: names
            .iter()
            .map(|name| {
                (
                    (*name).to_string(),
                    crate::typechecker::Scheme {
                        forall: vec![],
                        constraints: vec![],
                        ty: crate::typechecker::Type::int(),
                    },
                )
            })
            .collect(),
        ..Default::default()
    }
}

fn find_val<'a>(program: &'a MProgram, name: &str) -> &'a MVal {
    program
        .iter()
        .find_map(|decl| match decl {
            MDecl::Val(v) if v.name == name => Some(v),
            _ => None,
        })
        .unwrap_or_else(|| panic!("expected val `{name}`"))
}

fn bind_pure(var: MVar, value: Atom, body: MExpr) -> MExpr {
    bind_expr(var, MExpr::Pure(value), body)
}

fn bind_expr(var: MVar, value: MExpr, body: MExpr) -> MExpr {
    MExpr::Bind {
        var,
        value: Box::new(value),
        body: Box::new(body),
        mode: crate::codegen::monadic::ir::BindMode::Sequence,
    }
}

fn mv(name: &str, id: u32) -> MVar {
    MVar {
        name: name.to_string(),
        id,
    }
}

fn var(name: &str, id: u32) -> Atom {
    Atom::Var {
        name: mv(name, id),
        source: crate::ast::NodeId(id),
    }
}

fn lit_int(raw: &str, value: i64) -> Atom {
    Atom::Lit {
        value: crate::ast::Lit::Int(raw.to_string(), value),
        source: crate::ast::NodeId(value as u32),
    }
}

fn unit_atom() -> Atom {
    Atom::Lit {
        value: crate::ast::Lit::Unit,
        source: crate::ast::NodeId(0),
    }
}

fn pat_var(name: &str, id: u32) -> Pat {
    Pat::Var {
        name: name.to_string(),
        id: crate::ast::NodeId(id),
        span: span(),
    }
}

fn pat_unit(id: u32) -> Pat {
    Pat::Lit {
        id: crate::ast::NodeId(id),
        value: crate::ast::Lit::Unit,
        span: span(),
    }
}

fn resume(value: Atom) -> MExpr {
    MExpr::Resume {
        value,
        source: crate::ast::NodeId(999),
    }
}

fn yield_log(args: Vec<Atom>, source: crate::ast::NodeId) -> MExpr {
    MExpr::Yield {
        op: log_op(),
        args,
        source,
    }
}

fn yield_fail(args: Vec<Atom>, source: crate::ast::NodeId) -> MExpr {
    MExpr::Yield {
        op: effect_op("Std.Fail.Fail", "fail", 1),
        args,
        source,
    }
}

fn yield_native(effect: &str, op: &str, args: Vec<Atom>, source: u32) -> MExpr {
    MExpr::Yield {
        op: effect_op(effect, op, 0),
        args,
        source: crate::ast::NodeId(source),
    }
}

fn effect_op(effect: &str, op: &str, op_index: u32) -> EffectOpRef {
    EffectOpRef {
        effect: effect.to_string(),
        op: op.to_string(),
        op_index,
    }
}

fn with_expr(handler: MHandler, body: MExpr) -> MExpr {
    MExpr::With {
        handler,
        body: Box::new(body),
        source: crate::ast::NodeId(998),
    }
}

fn static_log_handler(arms: Vec<MHandlerArm>) -> MHandler {
    MHandler::Static {
        effects: vec!["Log".to_string()],
        arms,
        return_clause: None,
        source: crate::ast::NodeId(997),
    }
}

fn native_handler(effect: &str, handler: &str, source: u32) -> MHandler {
    MHandler::Native {
        effects: vec![effect.to_string()],
        handler: handler.to_string(),
        source: crate::ast::NodeId(source),
    }
}

fn tail_arm(id: u32, params: Vec<Pat>, body: MExpr, finally_block: Option<MExpr>) -> MHandlerArm {
    MHandlerArm {
        id: crate::ast::NodeId(id),
        op: log_op(),
        params,
        body: Box::new(body),
        finally_block: finally_block.map(Box::new),
        span: span(),
    }
}

fn log_op() -> EffectOpRef {
    EffectOpRef {
        effect: "Log".to_string(),
        op: "log".to_string(),
        op_index: 1,
    }
}

fn pure_fun_type() -> crate::typechecker::Type {
    crate::typechecker::Type::Fun(
        Box::new(crate::typechecker::Type::Con("Int".to_string(), vec![])),
        Box::new(crate::typechecker::Type::Con("Int".to_string(), vec![])),
        crate::typechecker::EffectRow::empty(),
    )
}

fn effectful_fun_type(effect: &str) -> crate::typechecker::Type {
    crate::typechecker::Type::Fun(
        Box::new(crate::typechecker::Type::Con("Int".to_string(), vec![])),
        Box::new(crate::typechecker::Type::Con("Int".to_string(), vec![])),
        crate::typechecker::EffectRow::closed(vec![crate::typechecker::EffectEntry::unnamed(
            effect.to_string(),
            vec![],
        )]),
    )
}

fn span() -> crate::token::Span {
    crate::token::Span { start: 0, end: 0 }
}
