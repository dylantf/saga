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
fn bind_of_pure_computations_counts_as_pure() {
    let expr = bind_pure(
        mv("x", 11),
        Atom::Ctor {
            name: "Box".to_string(),
            args: vec![lit_int("1", 1)],
            source: crate::ast::NodeId(12),
        },
        MExpr::Case {
            scrutinee: var("x", 11),
            arms: vec![MArm {
                pattern: Pat::Wildcard {
                    id: crate::ast::NodeId(13),
                    span: span(),
                },
                guard: None,
                body: bind_pure(
                    mv("y", 14),
                    Atom::Ctor {
                        name: "Inner".to_string(),
                        args: vec![var("x", 11)],
                        source: crate::ast::NodeId(15),
                    },
                    MExpr::Pure(var("y", 14)),
                ),
                span: span(),
            }],
            source: crate::ast::NodeId(16),
        },
    );

    assert!(expr_is_pure(&expr));
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
fn bind_to_let_promotes_dict_constructor_app() {
    let f = Fixture::new();
    let info = f.info();
    let value = MExpr::App {
        head: Atom::DictRef {
            name: "__dict_Show_Int".to_string(),
            source: crate::ast::NodeId(61),
        },
        args: vec![],
        source: crate::ast::NodeId(62),
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
fn dead_pure_static_with_removes_handler_around_plain_value() {
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

    let out = run(prog, &f.h, &info);

    assert_eq!(out, val_program(MExpr::Pure(lit_int("1", 1))));
}

#[test]
fn bind_to_let_promotes_app_with_closed_empty_effect_row() {
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
fn bind_to_let_keeps_app_with_open_effect_row() {
    let mut f = Fixture::new();
    let source = crate::ast::NodeId(82);
    let head_source = crate::ast::NodeId(83);
    f.type_at_node.insert(head_source, open_fun_type());
    let info = f.info();
    let value = MExpr::App {
        head: var("poly_fun", 83),
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
fn immediate_lambda_app_inlines_when_params_are_supported() {
    let f = Fixture::new();
    let info = f.info();
    let prog = val_program(MExpr::App {
        head: Atom::Lambda {
            params: vec![pat_var("x", 2956)],
            body: Box::new(MExpr::Pure(var("x", 2956))),
            source: crate::ast::NodeId(2957),
        },
        args: vec![lit_int("9", 9)],
        source: crate::ast::NodeId(2958),
    });

    let out = run(prog, &f.h, &info);

    assert_eq!(out, val_program(MExpr::Pure(lit_int("9", 9))));
}

#[test]
fn lambda_argument_app_remains_conservative() {
    let f = Fixture::new();
    let info = f.info();
    let prog = val_program(MExpr::App {
        head: var("map", 2959),
        args: vec![Atom::Lambda {
            params: vec![pat_var("x", 2960)],
            body: Box::new(MExpr::Pure(var("x", 2960))),
            source: crate::ast::NodeId(2961),
        }],
        source: crate::ast::NodeId(2962),
    });

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

    assert_eq!(out, val_program(MExpr::Pure(lit_int("42", 42))));
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

    assert_eq!(out, val_program(MExpr::Pure(lit_int("42", 42))));
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

    assert_eq!(out, val_program(MExpr::Pure(lit_int("7", 7))));
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
fn let_bound_handler_value_specializes_to_static_handler() {
    let mut f = Fixture::new();
    let arm = tail_arm(156, vec![pat_unit(157)], resume(lit_int("1", 1)), None);
    f.h.resumption
        .insert(crate::ast::NodeId(156), ResumptionKind::TailResumptive);
    let handler_value = MExpr::HandlerValue {
        effects: vec!["Log".to_string()],
        arms: vec![arm],
        return_clause: None,
        source: crate::ast::NodeId(158),
    };
    let handler_var = mv("h", 159);
    let body = MExpr::Let {
        var: handler_var.clone(),
        value: Box::new(handler_value),
        body: Box::new(with_expr(
            MHandler::Dynamic {
                effects: vec!["Log".to_string()],
                op_tuple: Atom::Var {
                    name: handler_var,
                    source: crate::ast::NodeId(160),
                },
                return_lambda: None,
                source: crate::ast::NodeId(161),
            },
            yield_log(vec![unit_atom()], crate::ast::NodeId(162)),
        )),
    };
    let info = f.info();

    let out = run(val_program(body), &f.h, &info);

    assert_eq!(out, val_program(MExpr::Pure(lit_int("1", 1))));
}

#[test]
fn let_bound_handler_factory_specializes_to_static_handler() {
    let mut f = Fixture::new();
    let arm = tail_arm(
        163,
        vec![pat_unit(164)],
        resume(var("configured", 165)),
        None,
    );
    f.h.resumption
        .insert(crate::ast::NodeId(163), ResumptionKind::TailResumptive);
    let factory = helper_fun(
        "make_handler",
        166,
        vec![pat_var("configured", 167)],
        MExpr::HandlerValue {
            effects: vec!["Log".to_string()],
            arms: vec![arm],
            return_clause: None,
            source: crate::ast::NodeId(168),
        },
    );
    let handler_var = mv("h", 169);
    let caller = MDecl::Val(MVal {
        id: crate::ast::NodeId(170),
        public: false,
        name: "caller".to_string(),
        value: MExpr::Let {
            var: handler_var.clone(),
            value: Box::new(MExpr::App {
                head: var("make_handler", 166),
                args: vec![lit_int("42", 42)],
                source: crate::ast::NodeId(171),
            }),
            body: Box::new(with_expr(
                MHandler::Dynamic {
                    effects: vec!["Log".to_string()],
                    op_tuple: Atom::Var {
                        name: handler_var,
                        source: crate::ast::NodeId(172),
                    },
                    return_lambda: None,
                    source: crate::ast::NodeId(173),
                },
                yield_log(vec![unit_atom()], crate::ast::NodeId(174)),
            )),
        },
        span: span(),
    });
    let info = f.info();

    let out = run(vec![factory.clone(), caller], &f.h, &info);

    assert_eq!(
        out,
        vec![
            factory,
            MDecl::Val(MVal {
                id: crate::ast::NodeId(170),
                public: false,
                name: "caller".to_string(),
                value: MExpr::Pure(lit_int("42", 42)),
                span: span(),
            })
        ]
    );
}

#[test]
fn handler_factory_prefix_binding_is_computed_once_before_handler_install() {
    let mut f = Fixture::new();
    let opts = mv("opts", 185);
    let arm = tail_arm(183, vec![pat_unit(184)], resume(var("opts", 185)), None);
    f.h.resumption
        .insert(crate::ast::NodeId(183), ResumptionKind::TailResumptive);
    let factory = helper_fun(
        "make_handler",
        186,
        vec![pat_var("configured", 187)],
        MExpr::Bind {
            var: opts.clone(),
            value: Box::new(MExpr::App {
                head: var("configure", 188),
                args: vec![var("configured", 187)],
                source: crate::ast::NodeId(189),
            }),
            body: Box::new(MExpr::HandlerValue {
                effects: vec!["Log".to_string()],
                arms: vec![arm],
                return_clause: None,
                source: crate::ast::NodeId(190),
            }),
            mode: crate::codegen::monadic::ir::BindMode::Sequence,
        },
    );
    let handler_var = mv("h", 191);
    let caller = MDecl::Val(MVal {
        id: crate::ast::NodeId(192),
        public: false,
        name: "caller".to_string(),
        value: MExpr::Let {
            var: handler_var.clone(),
            value: Box::new(MExpr::App {
                head: var("make_handler", 186),
                args: vec![lit_int("42", 42)],
                source: crate::ast::NodeId(193),
            }),
            body: Box::new(with_expr(
                MHandler::Dynamic {
                    effects: vec!["Log".to_string()],
                    op_tuple: Atom::Var {
                        name: handler_var,
                        source: crate::ast::NodeId(194),
                    },
                    return_lambda: None,
                    source: crate::ast::NodeId(195),
                },
                yield_log(vec![unit_atom()], crate::ast::NodeId(196)),
            )),
        },
        span: span(),
    });
    let info = f.info();

    let out = run(vec![factory.clone(), caller], &f.h, &info);

    assert_eq!(
        out,
        vec![
            factory,
            MDecl::Val(MVal {
                id: crate::ast::NodeId(192),
                public: false,
                name: "caller".to_string(),
                value: MExpr::Bind {
                    var: opts,
                    value: Box::new(MExpr::App {
                        head: var("configure", 188),
                        args: vec![lit_int("42", 42)],
                        source: crate::ast::NodeId(189),
                    }),
                    body: Box::new(MExpr::Pure(var("opts", 185))),
                    mode: crate::codegen::monadic::ir::BindMode::Sequence,
                },
                span: span(),
            })
        ]
    );
}

#[test]
fn imported_handler_factory_specializes_to_static_handler() {
    let mut f = Fixture::new();
    let arm = tail_arm(197, vec![pat_unit(198)], resume(var("defaults", 199)), None);
    f.h.resumption
        .insert(crate::ast::NodeId(197), ResumptionKind::TailResumptive);
    let defaults = MDecl::Val(MVal {
        id: crate::ast::NodeId(200),
        public: true,
        name: "defaults".to_string(),
        value: MExpr::Pure(lit_int("42", 42)),
        span: span(),
    });
    let factory = MDecl::FunBinding(MFunBinding {
        id: crate::ast::NodeId(201),
        public: true,
        name: "make_handler".to_string(),
        name_span: span(),
        params: vec![pat_unit(202)],
        guard: None,
        body: MExpr::HandlerValue {
            effects: vec!["Log".to_string()],
            arms: vec![arm],
            return_clause: None,
            source: crate::ast::NodeId(203),
        },
        span: span(),
    });
    let imported_program = vec![defaults, factory];
    let imported_candidates = collect_imported_handler_factory_candidates(
        "Lib",
        &imported_program,
        &ResolutionMap::new(),
        &module_info_with_exports(&["defaults", "make_handler"]),
    );
    let handler_var = mv("h", 204);
    let caller = MDecl::Val(MVal {
        id: crate::ast::NodeId(205),
        public: false,
        name: "caller".to_string(),
        value: MExpr::Let {
            var: handler_var.clone(),
            value: Box::new(MExpr::App {
                head: var("make_handler", 206),
                args: vec![unit_atom()],
                source: crate::ast::NodeId(207),
            }),
            body: Box::new(with_expr(
                MHandler::Dynamic {
                    effects: vec!["Log".to_string()],
                    op_tuple: Atom::Var {
                        name: handler_var,
                        source: crate::ast::NodeId(208),
                    },
                    return_lambda: None,
                    source: crate::ast::NodeId(209),
                },
                yield_log(vec![unit_atom()], crate::ast::NodeId(210)),
            )),
        },
        span: span(),
    });
    let mut context = OptimizerContext::default();
    context.resolution.insert(
        crate::ast::NodeId(206),
        resolved_beam("make_handler", Some("Lib"), "Lib.make_handler"),
    );
    context.imported_handler_factories = imported_candidates;
    let info = f.info();

    let out = run_with_context(vec![caller], &f.h, &info, context);

    assert_eq!(
        out,
        vec![MDecl::Val(MVal {
            id: crate::ast::NodeId(205),
            public: false,
            name: "caller".to_string(),
            value: MExpr::Pure(lit_int("42", 42)),
            span: span(),
        })]
    );
}

#[test]
fn non_handler_binding_shadows_outer_handler_value_binding() {
    let mut f = Fixture::new();
    let arm = tail_arm(175, vec![pat_unit(176)], resume(lit_int("1", 1)), None);
    f.h.resumption
        .insert(crate::ast::NodeId(175), ResumptionKind::TailResumptive);
    let outer_handler = MExpr::HandlerValue {
        effects: vec!["Log".to_string()],
        arms: vec![arm],
        return_clause: None,
        source: crate::ast::NodeId(177),
    };
    let outer = mv("h", 178);
    let inner = mv("h", 179);
    let body = MExpr::Let {
        var: outer.clone(),
        value: Box::new(outer_handler),
        body: Box::new(MExpr::Let {
            var: inner.clone(),
            value: Box::new(MExpr::Pure(lit_int("0", 0))),
            body: Box::new(with_expr(
                MHandler::Dynamic {
                    effects: vec!["Log".to_string()],
                    op_tuple: Atom::Var {
                        name: inner,
                        source: crate::ast::NodeId(180),
                    },
                    return_lambda: None,
                    source: crate::ast::NodeId(181),
                },
                yield_log(vec![unit_atom()], crate::ast::NodeId(182)),
            )),
        }),
    };
    let info = f.info();

    let out = run(val_program(body.clone()), &f.h, &info);

    assert_eq!(
        out,
        val_program(with_expr(
            MHandler::Dynamic {
                effects: vec!["Log".to_string()],
                op_tuple: lit_int("0", 0),
                return_lambda: None,
                source: crate::ast::NodeId(181),
            },
            yield_log(vec![unit_atom()], crate::ast::NodeId(182)),
        ))
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
                value: MExpr::Pure(lit_int("42", 42)),
                span: span(),
            })
        ]
    );
}

#[test]
fn dict_method_inline_exposes_yield_to_static_function_variant() {
    let mut f = Fixture::new();
    let arm = tail_arm(2810, vec![pat_unit(2811)], resume(lit_int("42", 42)), None);
    f.h.resumption
        .insert(crate::ast::NodeId(2810), ResumptionKind::TailResumptive);
    let handler = static_log_handler(vec![arm]);
    let dict = MDecl::DictConstructor(MDictConstructor {
        id: crate::ast::NodeId(2812),
        name: "__dict_Encodable_Int".to_string(),
        dict_params: vec![],
        methods: vec![MExpr::Pure(Atom::Lambda {
            params: vec![pat_var("x", 2813)],
            body: Box::new(bind_expr(
                mv("opts", 2814),
                yield_log(vec![unit_atom()], crate::ast::NodeId(2815)),
                MExpr::BinOp {
                    op: crate::ast::BinOp::Add,
                    left: var("x", 2813),
                    right: var("opts", 2814),
                    source: crate::ast::NodeId(2816),
                },
            )),
            source: crate::ast::NodeId(2817),
        })],
        method_effects: vec![],
        method_open_rows: vec![],
        impl_effects: vec![],
        span: span(),
    });
    let compute = helper_fun(
        "compute",
        2818,
        vec![pat_var("x", 2819)],
        bind_expr(
            mv("dict", 2820),
            MExpr::App {
                head: Atom::DictRef {
                    name: "__dict_Encodable_Int".to_string(),
                    source: crate::ast::NodeId(2821),
                },
                args: vec![],
                source: crate::ast::NodeId(2822),
            },
            bind_expr(
                mv("method", 2823),
                MExpr::DictMethodAccess {
                    dict: var("dict", 2820),
                    trait_name: "Encodable".to_string(),
                    method_index: 0,
                    source: crate::ast::NodeId(2824),
                },
                MExpr::App {
                    head: var("method", 2823),
                    args: vec![var("x", 2819)],
                    source: crate::ast::NodeId(2825),
                },
            ),
        ),
    );
    let caller = MDecl::Val(MVal {
        id: crate::ast::NodeId(2826),
        public: false,
        name: "caller".to_string(),
        value: with_expr(
            handler,
            MExpr::App {
                head: var("compute", 2827),
                args: vec![lit_int("5", 5)],
                source: crate::ast::NodeId(2828),
            },
        ),
        span: span(),
    });
    let info = f.info();

    let out = run(vec![dict, compute, caller], &f.h, &info);
    let variant = out
        .iter()
        .find_map(|decl| match decl {
            MDecl::FunBinding(fun) if is_generated_variant_name(&fun.name) => Some(fun),
            _ => None,
        })
        .expect("expected generated static variant");

    assert_eq!(
        variant.body,
        MExpr::BinOp {
            op: crate::ast::BinOp::Add,
            left: var("x", 2819),
            right: lit_int("42", 42),
            source: crate::ast::NodeId(2816),
        }
    );
    assert_eq!(expr_yield_count(&variant.body), 0);
}

#[test]
fn dict_method_inline_supports_constructor_param_by_case_wrapping() {
    let mut f = Fixture::new();
    let arm = tail_arm(2829, vec![pat_unit(2830)], resume(lit_int("42", 42)), None);
    f.h.resumption
        .insert(crate::ast::NodeId(2829), ResumptionKind::TailResumptive);
    let handler = static_log_handler(vec![arm]);
    let dict = MDecl::DictConstructor(MDictConstructor {
        id: crate::ast::NodeId(2831),
        name: "__dict_Encodable_Box".to_string(),
        dict_params: vec![],
        methods: vec![MExpr::Pure(Atom::Lambda {
            params: vec![Pat::Constructor {
                id: crate::ast::NodeId(2832),
                name: "Box".to_string(),
                args: vec![pat_var("x", 2833)],
                span: span(),
            }],
            body: Box::new(bind_expr(
                mv("opts", 2834),
                yield_log(vec![unit_atom()], crate::ast::NodeId(2835)),
                MExpr::BinOp {
                    op: crate::ast::BinOp::Add,
                    left: var("x", 2833),
                    right: var("opts", 2834),
                    source: crate::ast::NodeId(2836),
                },
            )),
            source: crate::ast::NodeId(2837),
        })],
        method_effects: vec![],
        method_open_rows: vec![],
        impl_effects: vec![],
        span: span(),
    });
    let caller = MDecl::Val(MVal {
        id: crate::ast::NodeId(2838),
        public: false,
        name: "caller".to_string(),
        value: with_expr(
            handler,
            bind_expr(
                mv("dict", 2839),
                MExpr::App {
                    head: Atom::DictRef {
                        name: "__dict_Encodable_Box".to_string(),
                        source: crate::ast::NodeId(2840),
                    },
                    args: vec![],
                    source: crate::ast::NodeId(2841),
                },
                bind_expr(
                    mv("method", 2842),
                    MExpr::DictMethodAccess {
                        dict: var("dict", 2839),
                        trait_name: "Encodable".to_string(),
                        method_index: 0,
                        source: crate::ast::NodeId(2843),
                    },
                    MExpr::App {
                        head: var("method", 2842),
                        args: vec![Atom::Ctor {
                            name: "Box".to_string(),
                            args: vec![lit_int("5", 5)],
                            source: crate::ast::NodeId(2844),
                        }],
                        source: crate::ast::NodeId(2845),
                    },
                ),
            ),
        ),
        span: span(),
    });
    let info = f.info();

    let out = run(vec![dict, caller], &f.h, &info);
    let val = find_val(&out, "caller");

    assert_eq!(expr_yield_count(&val.value), 0);
}

#[test]
fn dict_argument_specializes_generated_static_variant() {
    let mut f = Fixture::new();
    let arm = tail_arm(2830, vec![pat_unit(2831)], resume(lit_int("42", 42)), None);
    f.h.resumption
        .insert(crate::ast::NodeId(2830), ResumptionKind::TailResumptive);
    let handler = static_log_handler(vec![arm]);
    let dict = MDecl::DictConstructor(MDictConstructor {
        id: crate::ast::NodeId(2832),
        name: "__dict_Encodable_Int".to_string(),
        dict_params: vec![],
        methods: vec![MExpr::Pure(Atom::Lambda {
            params: vec![pat_var("x", 2833)],
            body: Box::new(bind_expr(
                mv("opts", 2834),
                yield_log(vec![unit_atom()], crate::ast::NodeId(2835)),
                MExpr::BinOp {
                    op: crate::ast::BinOp::Add,
                    left: var("x", 2833),
                    right: var("opts", 2834),
                    source: crate::ast::NodeId(2836),
                },
            )),
            source: crate::ast::NodeId(2837),
        })],
        method_effects: vec![],
        method_open_rows: vec![],
        impl_effects: vec![],
        span: span(),
    });
    let serialize = helper_fun(
        "serialize",
        2838,
        vec![pat_var("__dict_Encodable_a", 2839), pat_var("x", 2840)],
        bind_expr(
            mv("method", 2841),
            MExpr::DictMethodAccess {
                dict: var("__dict_Encodable_a", 2839),
                trait_name: "Encodable".to_string(),
                method_index: 0,
                source: crate::ast::NodeId(2842),
            },
            MExpr::App {
                head: var("method", 2841),
                args: vec![var("x", 2840)],
                source: crate::ast::NodeId(2843),
            },
        ),
    );
    let caller = MDecl::Val(MVal {
        id: crate::ast::NodeId(2844),
        public: false,
        name: "caller".to_string(),
        value: with_expr(
            handler,
            bind_expr(
                mv("dict", 2845),
                MExpr::App {
                    head: Atom::DictRef {
                        name: "__dict_Encodable_Int".to_string(),
                        source: crate::ast::NodeId(2846),
                    },
                    args: vec![],
                    source: crate::ast::NodeId(2847),
                },
                MExpr::App {
                    head: var("serialize", 2848),
                    args: vec![var("dict", 2845), lit_int("5", 5)],
                    source: crate::ast::NodeId(2849),
                },
            ),
        ),
        span: span(),
    });
    let info = f.info();

    let out = run(vec![dict, serialize, caller], &f.h, &info);
    let variant = out
        .iter()
        .find_map(|decl| match decl {
            MDecl::FunBinding(fun) if is_generated_variant_name(&fun.name) => Some(fun),
            _ => None,
        })
        .expect("expected generated static variant");

    assert!(variant.name.contains("__dict_"));
    assert_eq!(
        variant.body,
        MExpr::BinOp {
            op: crate::ast::BinOp::Add,
            left: var("x", 2840),
            right: lit_int("42", 42),
            source: crate::ast::NodeId(2836),
        }
    );
    assert_eq!(expr_yield_count(&variant.body), 0);
}

#[test]
fn parameterized_dict_argument_specializes_nested_method_dispatch() {
    let mut f = Fixture::new();
    let arm = tail_arm(2850, vec![pat_unit(2851)], resume(lit_int("42", 42)), None);
    f.h.resumption
        .insert(crate::ast::NodeId(2850), ResumptionKind::TailResumptive);
    let handler = static_log_handler(vec![arm]);
    let int_dict = MDecl::DictConstructor(MDictConstructor {
        id: crate::ast::NodeId(2852),
        name: "__dict_Encodable_Int".to_string(),
        dict_params: vec![],
        methods: vec![MExpr::Pure(Atom::Lambda {
            params: vec![pat_var("x", 2853)],
            body: Box::new(bind_expr(
                mv("opts", 2854),
                yield_log(vec![unit_atom()], crate::ast::NodeId(2855)),
                MExpr::BinOp {
                    op: crate::ast::BinOp::Add,
                    left: var("x", 2853),
                    right: var("opts", 2854),
                    source: crate::ast::NodeId(2856),
                },
            )),
            source: crate::ast::NodeId(2857),
        })],
        method_effects: vec![],
        method_open_rows: vec![],
        impl_effects: vec![],
        span: span(),
    });
    let box_dict = MDecl::DictConstructor(MDictConstructor {
        id: crate::ast::NodeId(2858),
        name: "__dict_Encodable_Box".to_string(),
        dict_params: vec!["__dict_Encodable_a".to_string()],
        methods: vec![MExpr::Pure(Atom::Lambda {
            params: vec![pat_var("boxed", 2859)],
            body: Box::new(MExpr::Case {
                scrutinee: var("boxed", 2859),
                arms: vec![MArm {
                    pattern: Pat::Constructor {
                        id: crate::ast::NodeId(2860),
                        name: "Box".to_string(),
                        args: vec![pat_var("value", 2861)],
                        span: span(),
                    },
                    guard: None,
                    body: bind_expr(
                        mv("method", 2862),
                        MExpr::DictMethodAccess {
                            dict: var("__dict_Encodable_a", 0),
                            trait_name: "Encodable".to_string(),
                            method_index: 0,
                            source: crate::ast::NodeId(2863),
                        },
                        bind_expr(
                            mv("encoded", 2864),
                            MExpr::App {
                                head: var("method", 2862),
                                args: vec![var("value", 2861)],
                                source: crate::ast::NodeId(2865),
                            },
                            MExpr::BinOp {
                                op: crate::ast::BinOp::Add,
                                left: var("encoded", 2864),
                                right: lit_int("1", 1),
                                source: crate::ast::NodeId(2866),
                            },
                        ),
                    ),
                    span: span(),
                }],
                source: crate::ast::NodeId(2867),
            }),
            source: crate::ast::NodeId(2868),
        })],
        method_effects: vec![],
        method_open_rows: vec![],
        impl_effects: vec![],
        span: span(),
    });
    let serialize = helper_fun(
        "serialize",
        2869,
        vec![pat_var("__dict_Encodable_a", 2870), pat_var("x", 2871)],
        bind_expr(
            mv("method", 2872),
            MExpr::DictMethodAccess {
                dict: var("__dict_Encodable_a", 2870),
                trait_name: "Encodable".to_string(),
                method_index: 0,
                source: crate::ast::NodeId(2873),
            },
            MExpr::App {
                head: var("method", 2872),
                args: vec![var("x", 2871)],
                source: crate::ast::NodeId(2874),
            },
        ),
    );
    let caller = MDecl::Val(MVal {
        id: crate::ast::NodeId(2875),
        public: false,
        name: "caller".to_string(),
        value: with_expr(
            handler,
            bind_expr(
                mv("int_dict", 2876),
                MExpr::App {
                    head: Atom::DictRef {
                        name: "__dict_Encodable_Int".to_string(),
                        source: crate::ast::NodeId(2877),
                    },
                    args: vec![],
                    source: crate::ast::NodeId(2878),
                },
                bind_expr(
                    mv("box_dict", 2879),
                    MExpr::App {
                        head: Atom::DictRef {
                            name: "__dict_Encodable_Box".to_string(),
                            source: crate::ast::NodeId(2880),
                        },
                        args: vec![var("int_dict", 2876)],
                        source: crate::ast::NodeId(2881),
                    },
                    MExpr::App {
                        head: var("serialize", 2882),
                        args: vec![
                            var("box_dict", 2879),
                            Atom::Ctor {
                                name: "Box".to_string(),
                                args: vec![lit_int("5", 5)],
                                source: crate::ast::NodeId(2883),
                            },
                        ],
                        source: crate::ast::NodeId(2884),
                    },
                ),
            ),
        ),
        span: span(),
    });
    let info = f.info();

    let out = run(vec![int_dict, box_dict, serialize, caller], &f.h, &info);
    let variant = out
        .iter()
        .find_map(|decl| match decl {
            MDecl::FunBinding(fun) if is_generated_variant_name(&fun.name) => Some(fun),
            _ => None,
        })
        .expect("expected generated static variant");

    assert!(variant.name.contains("__dict_"));
    assert_eq!(expr_yield_count(&variant.body), 0);
    assert!(!expr_contains_dict_method_access(&variant.body));
}

#[test]
fn imported_dict_constructor_argument_specializes_generated_static_variant() {
    let mut f = Fixture::new();
    let arm = tail_arm(2913, vec![pat_unit(2914)], resume(lit_int("42", 42)), None);
    f.h.resumption
        .insert(crate::ast::NodeId(2913), ResumptionKind::TailResumptive);
    let handler = static_log_handler(vec![arm]);
    let int_dict = MDecl::DictConstructor(MDictConstructor {
        id: crate::ast::NodeId(2915),
        name: "__dict_Encodable_Int".to_string(),
        dict_params: vec![],
        methods: vec![MExpr::Pure(Atom::Lambda {
            params: vec![pat_var("x", 2916)],
            body: Box::new(bind_expr(
                mv("opts", 2917),
                yield_log(vec![unit_atom()], crate::ast::NodeId(2918)),
                MExpr::BinOp {
                    op: crate::ast::BinOp::Add,
                    left: var("x", 2916),
                    right: var("opts", 2917),
                    source: crate::ast::NodeId(2919),
                },
            )),
            source: crate::ast::NodeId(2920),
        })],
        method_effects: vec![],
        method_open_rows: vec![],
        impl_effects: vec![],
        span: span(),
    });
    let imported_box_dict = MDictConstructor {
        id: crate::ast::NodeId(2921),
        name: "__dict_Encodable_Box".to_string(),
        dict_params: vec!["__dict_Encodable_a".to_string()],
        methods: vec![MExpr::Pure(Atom::Lambda {
            params: vec![Pat::Constructor {
                id: crate::ast::NodeId(2922),
                name: "Box".to_string(),
                args: vec![pat_var("value", 2923)],
                span: span(),
            }],
            body: Box::new(bind_expr(
                mv("method", 2924),
                MExpr::DictMethodAccess {
                    dict: var("__dict_Encodable_a", 0),
                    trait_name: "Encodable".to_string(),
                    method_index: 0,
                    source: crate::ast::NodeId(2925),
                },
                MExpr::App {
                    head: var("method", 2924),
                    args: vec![var("value", 2923)],
                    source: crate::ast::NodeId(2926),
                },
            )),
            source: crate::ast::NodeId(2927),
        })],
        method_effects: vec![],
        method_open_rows: vec![],
        impl_effects: vec![],
        span: span(),
    };
    let serialize = helper_fun(
        "serialize",
        2928,
        vec![pat_var("__dict_Encodable_a", 2929), pat_var("x", 2930)],
        bind_expr(
            mv("method", 2931),
            MExpr::DictMethodAccess {
                dict: var("__dict_Encodable_a", 2929),
                trait_name: "Encodable".to_string(),
                method_index: 0,
                source: crate::ast::NodeId(2932),
            },
            MExpr::App {
                head: var("method", 2931),
                args: vec![var("x", 2930)],
                source: crate::ast::NodeId(2933),
            },
        ),
    );
    let caller = MDecl::Val(MVal {
        id: crate::ast::NodeId(2934),
        public: false,
        name: "caller".to_string(),
        value: with_expr(
            handler,
            bind_expr(
                mv("int_dict", 2935),
                MExpr::App {
                    head: Atom::DictRef {
                        name: "__dict_Encodable_Int".to_string(),
                        source: crate::ast::NodeId(2936),
                    },
                    args: vec![],
                    source: crate::ast::NodeId(2937),
                },
                bind_expr(
                    mv("box_dict", 2938),
                    MExpr::App {
                        head: Atom::QualifiedRef {
                            module: "Lib".to_string(),
                            name: "__dict_Encodable_Box".to_string(),
                            source: crate::ast::NodeId(2939),
                        },
                        args: vec![var("int_dict", 2935)],
                        source: crate::ast::NodeId(2940),
                    },
                    MExpr::App {
                        head: var("serialize", 2941),
                        args: vec![
                            var("box_dict", 2938),
                            Atom::Ctor {
                                name: "Box".to_string(),
                                args: vec![lit_int("5", 5)],
                                source: crate::ast::NodeId(2942),
                            },
                        ],
                        source: crate::ast::NodeId(2943),
                    },
                ),
            ),
        ),
        span: span(),
    });
    let mut context = OptimizerContext::default();
    context
        .imported_dict_constructors
        .insert(imported_box_dict.name.clone(), imported_box_dict);
    let info = f.info();

    let out = run_with_context(vec![int_dict, serialize, caller], &f.h, &info, context);
    let variant = out
        .iter()
        .find_map(|decl| match decl {
            MDecl::FunBinding(fun) if is_generated_variant_name(&fun.name) => Some(fun),
            _ => None,
        })
        .expect("expected generated static variant");

    assert_eq!(expr_yield_count(&variant.body), 0);
    assert!(
        !expr_contains_dict_method_access(&variant.body),
        "{:?}",
        variant.body
    );
}

#[test]
fn imported_dict_constructor_var_head_specializes_generated_static_variant() {
    let mut f = Fixture::new();
    let arm = tail_arm(3020, vec![pat_unit(3021)], resume(lit_int("42", 42)), None);
    f.h.resumption
        .insert(crate::ast::NodeId(3020), ResumptionKind::TailResumptive);
    let handler = static_log_handler(vec![arm]);
    let imported_int_dict = MDictConstructor {
        id: crate::ast::NodeId(3022),
        name: "__dict_Encodable_Int".to_string(),
        dict_params: vec![],
        methods: vec![MExpr::Pure(Atom::Lambda {
            params: vec![pat_var("x", 3023)],
            body: Box::new(bind_expr(
                mv("opts", 3024),
                yield_log(vec![unit_atom()], crate::ast::NodeId(3025)),
                MExpr::BinOp {
                    op: crate::ast::BinOp::Add,
                    left: var("x", 3023),
                    right: var("opts", 3024),
                    source: crate::ast::NodeId(3026),
                },
            )),
            source: crate::ast::NodeId(3027),
        })],
        method_effects: vec![],
        method_open_rows: vec![],
        impl_effects: vec![],
        span: span(),
    };
    let serialize = helper_fun(
        "serialize",
        3028,
        vec![pat_var("__dict_Encodable_a", 3029), pat_var("x", 3030)],
        bind_expr(
            mv("method", 3031),
            MExpr::DictMethodAccess {
                dict: var("__dict_Encodable_a", 3029),
                trait_name: "Encodable".to_string(),
                method_index: 0,
                source: crate::ast::NodeId(3032),
            },
            MExpr::App {
                head: var("method", 3031),
                args: vec![var("x", 3030)],
                source: crate::ast::NodeId(3033),
            },
        ),
    );
    let caller = MDecl::Val(MVal {
        id: crate::ast::NodeId(3034),
        public: false,
        name: "caller".to_string(),
        value: with_expr(
            handler,
            bind_expr(
                mv("dict", 3035),
                MExpr::App {
                    head: var("__dict_Encodable_Int", 3036),
                    args: vec![],
                    source: crate::ast::NodeId(3037),
                },
                MExpr::App {
                    head: var("serialize", 3038),
                    args: vec![var("dict", 3035), lit_int("5", 5)],
                    source: crate::ast::NodeId(3039),
                },
            ),
        ),
        span: span(),
    });
    let mut context = OptimizerContext::default();
    context
        .imported_dict_constructors
        .insert(imported_int_dict.name.clone(), imported_int_dict);
    let info = f.info();

    let out = run_with_context(vec![serialize, caller], &f.h, &info, context);
    let variant = out
        .iter()
        .find_map(|decl| match decl {
            MDecl::FunBinding(fun) if is_generated_variant_name(&fun.name) => Some(fun),
            _ => None,
        })
        .expect("expected generated static variant");

    assert_eq!(
        variant.body,
        MExpr::BinOp {
            op: crate::ast::BinOp::Add,
            left: var("x", 3030),
            right: lit_int("42", 42),
            source: crate::ast::NodeId(3026),
        }
    );
    assert_eq!(expr_yield_count(&variant.body), 0);
    assert!(!expr_contains_dict_method_access(&variant.body));
}

#[test]
fn dict_method_access_can_read_zero_arg_dict_ref() {
    let mut f = Fixture::new();
    let arm = tail_arm(3040, vec![pat_unit(3041)], resume(lit_int("7", 7)), None);
    f.h.resumption
        .insert(crate::ast::NodeId(3040), ResumptionKind::TailResumptive);
    let handler = static_log_handler(vec![arm]);
    let int_dict = MDecl::DictConstructor(MDictConstructor {
        id: crate::ast::NodeId(3042),
        name: "__dict_Encodable_Int".to_string(),
        dict_params: vec![],
        methods: vec![MExpr::Pure(Atom::Lambda {
            params: vec![pat_var("x", 3043)],
            body: Box::new(bind_expr(
                mv("opts", 3044),
                yield_log(vec![unit_atom()], crate::ast::NodeId(3045)),
                MExpr::BinOp {
                    op: crate::ast::BinOp::Add,
                    left: var("x", 3043),
                    right: var("opts", 3044),
                    source: crate::ast::NodeId(3046),
                },
            )),
            source: crate::ast::NodeId(3047),
        })],
        method_effects: vec![],
        method_open_rows: vec![],
        impl_effects: vec![],
        span: span(),
    });
    let caller = MDecl::Val(MVal {
        id: crate::ast::NodeId(3048),
        public: false,
        name: "caller".to_string(),
        value: with_expr(
            handler,
            bind_expr(
                mv("method", 3049),
                MExpr::DictMethodAccess {
                    dict: Atom::DictRef {
                        name: "__dict_Encodable_Int".to_string(),
                        source: crate::ast::NodeId(3050),
                    },
                    trait_name: "Encodable".to_string(),
                    method_index: 0,
                    source: crate::ast::NodeId(3051),
                },
                MExpr::App {
                    head: var("method", 3049),
                    args: vec![lit_int("5", 5)],
                    source: crate::ast::NodeId(3052),
                },
            ),
        ),
        span: span(),
    });
    let info = f.info();

    let out = run(vec![int_dict, caller], &f.h, &info);
    let val = out
        .iter()
        .find_map(|decl| match decl {
            MDecl::Val(val) if val.name == "caller" => Some(val),
            _ => None,
        })
        .expect("expected caller val");

    assert_eq!(
        val.value,
        MExpr::BinOp {
            op: crate::ast::BinOp::Add,
            left: lit_int("5", 5),
            right: lit_int("7", 7),
            source: crate::ast::NodeId(3046),
        }
    );
}

#[test]
fn imported_dict_constructor_collection_allows_immediate_supported_lambda_app() {
    let dict = MDecl::DictConstructor(MDictConstructor {
        id: crate::ast::NodeId(2963),
        name: "__dict_Encodable_Label".to_string(),
        dict_params: vec![],
        methods: vec![MExpr::Pure(Atom::Lambda {
            params: vec![pat_var("value", 2964)],
            body: Box::new(MExpr::App {
                head: Atom::Lambda {
                    params: vec![pat_var("_proxy", 2965)],
                    body: Box::new(MExpr::Pure(var("value", 2964))),
                    source: crate::ast::NodeId(2968),
                },
                args: vec![unit_atom()],
                source: crate::ast::NodeId(2969),
            }),
            source: crate::ast::NodeId(2970),
        })],
        method_effects: vec![],
        method_open_rows: vec![],
        impl_effects: vec![],
        span: span(),
    });
    let info = module_info_with_exports(&[]);

    let candidates = collect_imported_dict_constructors(
        "Lib",
        &vec![dict],
        &ResolutionMap::new(),
        &info,
        &HashSet::new(),
    );

    assert!(candidates.contains_key("__dict_Encodable_Label"));
}

#[test]
fn imported_dict_constructor_collection_rejects_escaping_lambda_arg() {
    let dict = MDecl::DictConstructor(MDictConstructor {
        id: crate::ast::NodeId(2971),
        name: "__dict_Encodable_List".to_string(),
        dict_params: vec![],
        methods: vec![MExpr::Pure(Atom::Lambda {
            params: vec![pat_var("xs", 2972)],
            body: Box::new(MExpr::App {
                head: var("map", 2973),
                args: vec![
                    Atom::Lambda {
                        params: vec![pat_var("x", 2974)],
                        body: Box::new(MExpr::Pure(var("x", 2974))),
                        source: crate::ast::NodeId(2975),
                    },
                    var("xs", 2972),
                ],
                source: crate::ast::NodeId(2976),
            }),
            source: crate::ast::NodeId(2977),
        })],
        method_effects: vec![],
        method_open_rows: vec![],
        impl_effects: vec![],
        span: span(),
    });
    let info = module_info_with_exports(&[]);

    let candidates = collect_imported_dict_constructors(
        "Lib",
        &vec![dict],
        &ResolutionMap::new(),
        &info,
        &HashSet::new(),
    );

    assert!(!candidates.contains_key("__dict_Encodable_List"));
}

#[test]
fn imported_dict_constructor_collection_allows_lambda_arg_to_resolved_saga_hof() {
    let dict = MDecl::DictConstructor(MDictConstructor {
        id: crate::ast::NodeId(3011),
        name: "__dict_Encodable_List".to_string(),
        dict_params: vec![],
        methods: vec![MExpr::Pure(Atom::Lambda {
            params: vec![pat_var("xs", 3012)],
            body: Box::new(MExpr::App {
                head: var("map", 3013),
                args: vec![
                    Atom::Lambda {
                        params: vec![pat_var("x", 3014)],
                        body: Box::new(bind_expr(
                            mv("opts", 3015),
                            yield_log(vec![unit_atom()], crate::ast::NodeId(3016)),
                            MExpr::Pure(var("x", 3014)),
                        )),
                        source: crate::ast::NodeId(3017),
                    },
                    var("xs", 3012),
                ],
                source: crate::ast::NodeId(3018),
            }),
            source: crate::ast::NodeId(3019),
        })],
        method_effects: vec![],
        method_open_rows: vec![],
        impl_effects: vec![],
        span: span(),
    });
    let mut resolution = ResolutionMap::new();
    resolution.insert(
        crate::ast::NodeId(3013),
        resolved_beam("map", Some("Std.List"), "Std.List.map"),
    );
    let info = module_info_with_exports(&[]);

    let candidates =
        collect_imported_dict_constructors("Lib", &vec![dict], &resolution, &info, &HashSet::new());

    assert!(candidates.contains_key("__dict_Encodable_List"));
}

#[test]
fn let_bound_handler_factory_specializes_generic_dict_dispatch() {
    let mut f = Fixture::new();
    let arm = tail_arm(
        2885,
        vec![pat_unit(2886)],
        resume(var("configured", 2887)),
        None,
    );
    f.h.resumption
        .insert(crate::ast::NodeId(2885), ResumptionKind::TailResumptive);
    let factory = helper_fun(
        "make_options",
        2888,
        vec![pat_var("configured", 2889)],
        MExpr::HandlerValue {
            effects: vec!["Log".to_string()],
            arms: vec![arm],
            return_clause: None,
            source: crate::ast::NodeId(2890),
        },
    );
    let dict = MDecl::DictConstructor(MDictConstructor {
        id: crate::ast::NodeId(2891),
        name: "__dict_Encodable_Int".to_string(),
        dict_params: vec![],
        methods: vec![MExpr::Pure(Atom::Lambda {
            params: vec![pat_var("x", 2892)],
            body: Box::new(bind_expr(
                mv("opts", 2893),
                yield_log(vec![unit_atom()], crate::ast::NodeId(2894)),
                MExpr::BinOp {
                    op: crate::ast::BinOp::Add,
                    left: var("x", 2892),
                    right: var("opts", 2893),
                    source: crate::ast::NodeId(2895),
                },
            )),
            source: crate::ast::NodeId(2896),
        })],
        method_effects: vec![],
        method_open_rows: vec![],
        impl_effects: vec![],
        span: span(),
    });
    let serialize = helper_fun(
        "serialize",
        2897,
        vec![pat_var("__dict_Encodable_a", 2898), pat_var("x", 2899)],
        bind_expr(
            mv("method", 2900),
            MExpr::DictMethodAccess {
                dict: var("__dict_Encodable_a", 2898),
                trait_name: "Encodable".to_string(),
                method_index: 0,
                source: crate::ast::NodeId(2901),
            },
            MExpr::App {
                head: var("method", 2900),
                args: vec![var("x", 2899)],
                source: crate::ast::NodeId(2902),
            },
        ),
    );
    let handler_var = mv("options", 2903);
    let caller = MDecl::Val(MVal {
        id: crate::ast::NodeId(2904),
        public: false,
        name: "caller".to_string(),
        value: MExpr::Let {
            var: handler_var.clone(),
            value: Box::new(MExpr::App {
                head: var("make_options", 2888),
                args: vec![lit_int("10", 10)],
                source: crate::ast::NodeId(2905),
            }),
            body: Box::new(with_expr(
                MHandler::Dynamic {
                    effects: vec!["Log".to_string()],
                    op_tuple: Atom::Var {
                        name: handler_var,
                        source: crate::ast::NodeId(2906),
                    },
                    return_lambda: None,
                    source: crate::ast::NodeId(2907),
                },
                bind_expr(
                    mv("dict", 2908),
                    MExpr::App {
                        head: Atom::DictRef {
                            name: "__dict_Encodable_Int".to_string(),
                            source: crate::ast::NodeId(2909),
                        },
                        args: vec![],
                        source: crate::ast::NodeId(2910),
                    },
                    MExpr::App {
                        head: var("serialize", 2911),
                        args: vec![var("dict", 2908), lit_int("5", 5)],
                        source: crate::ast::NodeId(2912),
                    },
                ),
            )),
        },
        span: span(),
    });
    let info = f.info();

    let out = run(vec![factory, dict, serialize, caller], &f.h, &info);
    let variant = out
        .iter()
        .find_map(|decl| match decl {
            MDecl::FunBinding(fun) if is_generated_variant_name(&fun.name) => Some(fun),
            _ => None,
        })
        .expect("expected generated static variant");

    assert_eq!(
        variant.body,
        MExpr::BinOp {
            op: crate::ast::BinOp::Add,
            left: var("x", 2899),
            right: lit_int("10", 10),
            source: crate::ast::NodeId(2895),
        }
    );
    assert_eq!(expr_yield_count(&variant.body), 0);
    assert!(!expr_contains_dict_method_access(&variant.body));
}

#[test]
fn effect_summary_generates_variant_for_call_hidden_erasable_yield() {
    let mut f = Fixture::new();
    let arm = tail_arm(2944, vec![pat_unit(2945)], resume(lit_int("42", 42)), None);
    f.h.resumption
        .insert(crate::ast::NodeId(2944), ResumptionKind::TailResumptive);
    let handler = static_log_handler(vec![arm]);
    let inner = helper_fun(
        "inner",
        2946,
        vec![pat_unit(2947)],
        yield_log(vec![unit_atom()], crate::ast::NodeId(2948)),
    );
    let outer = helper_fun(
        "outer",
        2949,
        vec![pat_unit(2950)],
        MExpr::App {
            head: var("inner", 2951),
            args: vec![unit_atom()],
            source: crate::ast::NodeId(2952),
        },
    );
    let caller = MDecl::Val(MVal {
        id: crate::ast::NodeId(2953),
        public: false,
        name: "caller".to_string(),
        value: with_expr(
            handler,
            MExpr::App {
                head: var("outer", 2954),
                args: vec![unit_atom()],
                source: crate::ast::NodeId(2955),
            },
        ),
        span: span(),
    });
    let info = f.info();

    let out = run(vec![inner, outer, caller], &f.h, &info);
    let variant = out
        .iter()
        .find_map(|decl| match decl {
            MDecl::FunBinding(fun) if is_generated_variant_name(&fun.name) => Some(fun),
            _ => None,
        })
        .expect("expected generated static variant");

    assert_eq!(variant.body, MExpr::Pure(lit_int("42", 42)));
    assert_eq!(expr_yield_count(&variant.body), 0);
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
fn static_function_variant_key_distinguishes_recovered_handler_bodies() {
    let mut f = Fixture::new();
    let arm_one = tail_arm(409, vec![pat_unit(410)], resume(lit_int("1", 1)), None);
    let arm_two = tail_arm(409, vec![pat_unit(410)], resume(lit_int("2", 2)), None);
    f.h.resumption
        .insert(crate::ast::NodeId(409), ResumptionKind::TailResumptive);
    let imported = imported_candidate(
        "Lib",
        "worker",
        411,
        yield_log(vec![unit_atom()], crate::ast::NodeId(412)),
    );
    let caller_one = MDecl::Val(MVal {
        id: crate::ast::NodeId(413),
        public: true,
        name: "caller_one".to_string(),
        value: with_expr(
            static_log_handler(vec![arm_one]),
            MExpr::App {
                head: var("worker", 414),
                args: vec![unit_atom()],
                source: crate::ast::NodeId(415),
            },
        ),
        span: span(),
    });
    let caller_two = MDecl::Val(MVal {
        id: crate::ast::NodeId(416),
        public: true,
        name: "caller_two".to_string(),
        value: with_expr(
            static_log_handler(vec![arm_two]),
            MExpr::App {
                head: var("worker", 417),
                args: vec![unit_atom()],
                source: crate::ast::NodeId(418),
            },
        ),
        span: span(),
    });
    let mut context = OptimizerContext::default();
    context.resolution.insert(
        crate::ast::NodeId(414),
        resolved_beam("worker", Some("Lib"), "Lib.worker"),
    );
    context.resolution.insert(
        crate::ast::NodeId(417),
        resolved_beam("worker", Some("Lib"), "Lib.worker"),
    );
    context
        .imported_function_variants
        .insert("Lib.worker".to_string(), imported);
    let info = f.info();

    let out = run_with_context(vec![caller_one, caller_two], &f.h, &info, context);
    let mut variant_bodies = out
        .iter()
        .filter_map(|decl| match decl {
            MDecl::FunBinding(f) if f.name.starts_with(STATIC_VARIANT_PREFIX) => {
                Some(f.body.clone())
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    variant_bodies.sort_by_key(|body| format!("{body:?}"));

    assert_eq!(
        variant_bodies,
        vec![MExpr::Pure(lit_int("1", 1)), MExpr::Pure(lit_int("2", 2))]
    );
}

#[test]
fn imported_static_function_variant_specializes_closed_constructor_args() {
    let mut f = Fixture::new();
    let arm = tail_arm(410, vec![pat_unit(411)], resume(lit_int("42", 42)), None);
    f.h.resumption
        .insert(crate::ast::NodeId(410), ResumptionKind::TailResumptive);
    let handler = static_log_handler(vec![arm]);
    let imported = imported_candidate_with_params(
        "Lib",
        "worker",
        412,
        vec![pat_var("x", 413)],
        MExpr::Case {
            scrutinee: var("x", 413),
            arms: vec![MArm {
                pattern: Pat::Constructor {
                    id: crate::ast::NodeId(414),
                    name: "Box".to_string(),
                    args: vec![pat_var("y", 415)],
                    span: span(),
                },
                guard: None,
                body: yield_log(vec![unit_atom()], crate::ast::NodeId(416)),
                span: span(),
            }],
            source: crate::ast::NodeId(417),
        },
    );
    let caller = MDecl::Val(MVal {
        id: crate::ast::NodeId(418),
        public: true,
        name: "caller".to_string(),
        value: with_expr(
            handler,
            MExpr::App {
                head: var("worker", 419),
                args: vec![Atom::Ctor {
                    name: "Box".to_string(),
                    args: vec![lit_int("5", 5)],
                    source: crate::ast::NodeId(420),
                }],
                source: crate::ast::NodeId(421),
            },
        ),
        span: span(),
    });
    let mut context = OptimizerContext::default();
    context.resolution.insert(
        crate::ast::NodeId(419),
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
    assert!(variant.name.contains("__value_"));
    assert_eq!(variant.body, MExpr::Pure(lit_int("42", 42)));
}

#[test]
fn imported_static_function_variant_specializes_let_bound_closed_constructor_args() {
    let mut f = Fixture::new();
    let arm = tail_arm(4180, vec![pat_unit(4181)], resume(lit_int("42", 42)), None);
    f.h.resumption
        .insert(crate::ast::NodeId(4180), ResumptionKind::TailResumptive);
    let handler = static_log_handler(vec![arm]);
    let imported = imported_candidate_with_params(
        "Lib",
        "worker",
        4182,
        vec![pat_var("x", 4183)],
        MExpr::Case {
            scrutinee: var("x", 4183),
            arms: vec![MArm {
                pattern: Pat::Constructor {
                    id: crate::ast::NodeId(4184),
                    name: "Box".to_string(),
                    args: vec![pat_var("y", 4185)],
                    span: span(),
                },
                guard: None,
                body: yield_log(vec![unit_atom()], crate::ast::NodeId(4186)),
                span: span(),
            }],
            source: crate::ast::NodeId(4187),
        },
    );
    let caller = MDecl::Val(MVal {
        id: crate::ast::NodeId(4188),
        public: true,
        name: "caller".to_string(),
        value: MExpr::Let {
            var: mv("boxed", 4189),
            value: Box::new(MExpr::Pure(Atom::Ctor {
                name: "Box".to_string(),
                args: vec![lit_int("5", 5)],
                source: crate::ast::NodeId(4190),
            })),
            body: Box::new(with_expr(
                handler,
                MExpr::App {
                    head: var("worker", 4191),
                    args: vec![var("boxed", 4189)],
                    source: crate::ast::NodeId(4192),
                },
            )),
        },
        span: span(),
    });
    let mut context = OptimizerContext::default();
    context.resolution.insert(
        crate::ast::NodeId(4191),
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
    assert!(variant.name.contains("__value_"));
    assert_eq!(variant.body, MExpr::Pure(lit_int("42", 42)));
}

#[test]
fn imported_static_function_variant_specializes_dict_method_under_inner_handler() {
    let mut f = Fixture::new();
    let outer_arm = tail_arm(3910, vec![pat_unit(3911)], resume(lit_int("1", 1)), None);
    let inner_arm = tail_arm(3912, vec![pat_unit(3913)], resume(lit_int("2", 2)), None);
    f.h.resumption
        .insert(crate::ast::NodeId(3910), ResumptionKind::TailResumptive);
    f.h.resumption
        .insert(crate::ast::NodeId(3912), ResumptionKind::TailResumptive);
    let outer_handler = static_log_handler(vec![outer_arm]);
    let inner_handler = static_log_handler(vec![inner_arm]);
    let imported_int_dict = MDictConstructor {
        id: crate::ast::NodeId(3914),
        name: "__dict_Encodable_Int".to_string(),
        dict_params: vec![],
        methods: vec![MExpr::Pure(Atom::Lambda {
            params: vec![pat_var("x", 3915)],
            body: Box::new(bind_expr(
                mv("opts", 3916),
                yield_log(vec![unit_atom()], crate::ast::NodeId(3917)),
                MExpr::BinOp {
                    op: crate::ast::BinOp::Add,
                    left: var("x", 3915),
                    right: var("opts", 3916),
                    source: crate::ast::NodeId(3918),
                },
            )),
            source: crate::ast::NodeId(3919),
        })],
        method_effects: vec![],
        method_open_rows: vec![],
        impl_effects: vec![],
        span: span(),
    };
    let worker_body = bind_expr(
        mv("_snapshot", 3920),
        yield_log(vec![unit_atom()], crate::ast::NodeId(3921)),
        with_expr(
            inner_handler,
            bind_expr(
                mv("dict", 3922),
                MExpr::App {
                    head: Atom::QualifiedRef {
                        module: "Lib".to_string(),
                        name: "__dict_Encodable_Int".to_string(),
                        source: crate::ast::NodeId(3923),
                    },
                    args: vec![],
                    source: crate::ast::NodeId(3924),
                },
                bind_expr(
                    mv("method", 3925),
                    MExpr::DictMethodAccess {
                        dict: var("dict", 3922),
                        trait_name: "Encodable".to_string(),
                        method_index: 0,
                        source: crate::ast::NodeId(3926),
                    },
                    MExpr::App {
                        head: var("method", 3925),
                        args: vec![var("x", 3927)],
                        source: crate::ast::NodeId(3928),
                    },
                ),
            ),
        ),
    );
    let imported = imported_candidate_with_params(
        "Lib",
        "worker",
        3929,
        vec![pat_var("x", 3927)],
        worker_body,
    );
    let caller = MDecl::Val(MVal {
        id: crate::ast::NodeId(3930),
        public: true,
        name: "caller".to_string(),
        value: with_expr(
            outer_handler,
            MExpr::App {
                head: var("worker", 3931),
                args: vec![lit_int("40", 40)],
                source: crate::ast::NodeId(3932),
            },
        ),
        span: span(),
    });
    let mut context = OptimizerContext::default();
    context.resolution.insert(
        crate::ast::NodeId(3931),
        resolved_beam("worker", Some("Lib"), "Lib.worker"),
    );
    context
        .imported_function_variants
        .insert("Lib.worker".to_string(), imported);
    context
        .imported_dict_constructors
        .insert(imported_int_dict.name.clone(), imported_int_dict);
    let info = f.info();

    let out = run_with_context(vec![caller], &f.h, &info, context);
    let variant = out
        .iter()
        .find_map(|decl| match decl {
            MDecl::FunBinding(fun) if fun.name.starts_with(STATIC_VARIANT_PREFIX) => Some(fun),
            _ => None,
        })
        .expect("expected generated imported static function variant");

    assert_eq!(expr_yield_count(&variant.body), 0, "{:?}", variant.body);
    assert!(!expr_contains_dict_method_access(&variant.body));
    assert_eq!(
        variant.body,
        MExpr::BinOp {
            op: crate::ast::BinOp::Add,
            left: var("x", 3927),
            right: lit_int("2", 2),
            source: crate::ast::NodeId(3918),
        }
    );
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
fn imported_static_function_variant_threads_handler_stack_captures_as_params() {
    let mut f = Fixture::new();
    let arm = tail_arm(
        2978,
        vec![pat_unit(2979)],
        resume(var("configured", 2980)),
        None,
    );
    f.h.resumption
        .insert(crate::ast::NodeId(2978), ResumptionKind::TailResumptive);
    let handler = static_log_handler(vec![arm]);
    let imported = imported_candidate(
        "Lib",
        "worker",
        2981,
        yield_log(vec![unit_atom()], crate::ast::NodeId(2983)),
    );
    let caller = MDecl::Val(MVal {
        id: crate::ast::NodeId(2984),
        public: false,
        name: "caller".to_string(),
        value: MExpr::Let {
            var: mv("configured", 2985),
            value: Box::new(MExpr::Pure(lit_int("10", 10))),
            body: Box::new(with_expr(
                handler,
                MExpr::App {
                    head: var("worker", 2986),
                    args: vec![unit_atom()],
                    source: crate::ast::NodeId(2987),
                },
            )),
        },
        span: span(),
    });
    let mut context = OptimizerContext::default();
    context.resolution.insert(
        crate::ast::NodeId(2986),
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
            MDecl::FunBinding(fun) if fun.name.starts_with(STATIC_VARIANT_PREFIX) => Some(fun),
            _ => None,
        })
        .expect("expected generated static variant");

    assert!(
        variant
            .params
            .iter()
            .any(|param| matches!(param, Pat::Var { name, .. } if name == "configured"))
    );
    assert_eq!(variant.body, MExpr::Pure(var("configured", 2980)));
}

#[test]
fn imported_static_function_variant_inlines_callback_param_and_threads_captures() {
    let mut f = Fixture::new();
    let arm = tail_arm(2990, vec![pat_unit(2991)], resume(lit_int("1", 1)), None);
    f.h.resumption
        .insert(crate::ast::NodeId(2990), ResumptionKind::TailResumptive);
    let handler = static_log_handler(vec![arm]);
    let map_body = bind_expr(
        mv("mapped", 2992),
        MExpr::App {
            head: var("f", 2993),
            args: vec![unit_atom()],
            source: crate::ast::NodeId(2994),
        },
        MExpr::App {
            head: var("map", 2995),
            args: vec![var("f", 2996), unit_atom()],
            source: crate::ast::NodeId(2997),
        },
    );
    let imported = imported_candidate_with_params(
        "Std.List",
        "map",
        2998,
        vec![pat_var("f", 2999), pat_unit(3000)],
        map_body,
    );
    let callback = Atom::Lambda {
        params: vec![pat_unit(3001)],
        body: Box::new(bind_expr(
            mv("opts", 3002),
            yield_log(vec![unit_atom()], crate::ast::NodeId(3003)),
            MExpr::BinOp {
                op: crate::ast::BinOp::Add,
                left: var("configured", 3004),
                right: var("opts", 3002),
                source: crate::ast::NodeId(3005),
            },
        )),
        source: crate::ast::NodeId(3006),
    };
    let caller = MDecl::Val(MVal {
        id: crate::ast::NodeId(3007),
        public: false,
        name: "caller".to_string(),
        value: MExpr::Let {
            var: mv("configured", 3008),
            value: Box::new(MExpr::Pure(lit_int("10", 10))),
            body: Box::new(with_expr(
                handler,
                MExpr::App {
                    head: var("map", 3009),
                    args: vec![callback, unit_atom()],
                    source: crate::ast::NodeId(3010),
                },
            )),
        },
        span: span(),
    });
    let mut context = OptimizerContext::default();
    context.resolution.insert(
        crate::ast::NodeId(3009),
        resolved_beam("map", Some("Std.List"), "Std.List.map"),
    );
    context
        .imported_function_variants
        .insert("Std.List.map".to_string(), imported);
    let info = f.info();

    let out = run_with_context(vec![caller], &f.h, &info, context);
    let variant = out
        .iter()
        .find_map(|decl| match decl {
            MDecl::FunBinding(fun) if fun.name.starts_with(STATIC_VARIANT_PREFIX) => Some(fun),
            _ => None,
        })
        .expect("expected generated static variant");

    assert_eq!(expr_yield_count(&variant.body), 0);
    assert!(
        variant
            .params
            .iter()
            .any(|param| matches!(param, Pat::Var { name, .. } if name == "configured"))
    );
    assert!(expr_contains_app_with_arg_count(
        &variant.body,
        &variant.name,
        3
    ));
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
    let info = f.info();
    let optimizer = Optimizer::new(RunOptions::default(), &f.h, &info, context);
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
    imported_candidate_with_params(source_module, name, id, vec![pat_unit(id + 1000)], body)
}

fn imported_candidate_with_params(
    source_module: &str,
    name: &str,
    id: u32,
    params: Vec<Pat>,
    body: MExpr,
) -> ImportedFunctionVariantCandidate {
    let binding = MFunBinding {
        id: crate::ast::NodeId(id),
        public: true,
        name: name.to_string(),
        name_span: span(),
        params,
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

fn expr_contains_app_with_arg_count(expr: &MExpr, name: &str, arg_count: usize) -> bool {
    match expr {
        MExpr::App { head, args, .. } => {
            matches!(head, Atom::Var { name: var, .. } if var.name == name)
                && args.len() == arg_count
        }
        MExpr::Pure(atom) => atom_contains_app_with_arg_count(atom, name, arg_count),
        MExpr::Yield { args, .. } | MExpr::ForeignCall { args, .. } => args
            .iter()
            .any(|atom| atom_contains_app_with_arg_count(atom, name, arg_count)),
        MExpr::Bind { value, body, .. } | MExpr::Let { value, body, .. } => {
            expr_contains_app_with_arg_count(value, name, arg_count)
                || expr_contains_app_with_arg_count(body, name, arg_count)
        }
        MExpr::Ensure { body, cleanup } => {
            expr_contains_app_with_arg_count(body, name, arg_count)
                || expr_contains_app_with_arg_count(cleanup, name, arg_count)
        }
        MExpr::Case {
            scrutinee, arms, ..
        } => {
            atom_contains_app_with_arg_count(scrutinee, name, arg_count)
                || arms.iter().any(|arm| {
                    arm.guard.as_ref().is_some_and(|guard| {
                        expr_contains_app_with_arg_count(guard, name, arg_count)
                    }) || expr_contains_app_with_arg_count(&arm.body, name, arg_count)
                })
        }
        MExpr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            atom_contains_app_with_arg_count(cond, name, arg_count)
                || expr_contains_app_with_arg_count(then_branch, name, arg_count)
                || expr_contains_app_with_arg_count(else_branch, name, arg_count)
        }
        MExpr::With { handler, body, .. } => {
            handler_contains_app_with_arg_count(handler, name, arg_count)
                || expr_contains_app_with_arg_count(body, name, arg_count)
        }
        MExpr::Resume { value, .. }
        | MExpr::FieldAccess { record: value, .. }
        | MExpr::DictMethodAccess { dict: value, .. }
        | MExpr::UnaryMinus { value, .. } => {
            atom_contains_app_with_arg_count(value, name, arg_count)
        }
        MExpr::RecordUpdate { record, fields, .. } => {
            atom_contains_app_with_arg_count(record, name, arg_count)
                || fields
                    .iter()
                    .any(|(_, atom)| atom_contains_app_with_arg_count(atom, name, arg_count))
        }
        MExpr::BinOp { left, right, .. } => {
            atom_contains_app_with_arg_count(left, name, arg_count)
                || atom_contains_app_with_arg_count(right, name, arg_count)
        }
        MExpr::BitString { segments, .. } => segments.iter().any(|segment| {
            atom_contains_app_with_arg_count(&segment.value, name, arg_count)
                || segment
                    .size
                    .as_ref()
                    .is_some_and(|size| atom_contains_app_with_arg_count(size, name, arg_count))
        }),
        MExpr::Receive { arms, after, .. } => {
            arms.iter().any(|arm| {
                arm.guard
                    .as_ref()
                    .is_some_and(|guard| expr_contains_app_with_arg_count(guard, name, arg_count))
                    || expr_contains_app_with_arg_count(&arm.body, name, arg_count)
            }) || after.as_ref().is_some_and(|(timeout, body)| {
                atom_contains_app_with_arg_count(timeout, name, arg_count)
                    || expr_contains_app_with_arg_count(body, name, arg_count)
            })
        }
        MExpr::LetFun { body, rest, .. } => {
            expr_contains_app_with_arg_count(body, name, arg_count)
                || expr_contains_app_with_arg_count(rest, name, arg_count)
        }
        MExpr::HandlerValue {
            arms,
            return_clause,
            ..
        } => {
            arms.iter()
                .any(|arm| handler_arm_contains_app_with_arg_count(arm, name, arg_count))
                || return_clause.as_ref().is_some_and(|arm| {
                    handler_arm_contains_app_with_arg_count(arm, name, arg_count)
                })
        }
    }
}

fn atom_contains_app_with_arg_count(atom: &Atom, name: &str, arg_count: usize) -> bool {
    match atom {
        Atom::Ctor { args, .. } | Atom::Tuple { elements: args, .. } => args
            .iter()
            .any(|atom| atom_contains_app_with_arg_count(atom, name, arg_count)),
        Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. } => fields
            .iter()
            .any(|(_, atom)| atom_contains_app_with_arg_count(atom, name, arg_count)),
        Atom::Lambda { body, .. } => expr_contains_app_with_arg_count(body, name, arg_count),
        Atom::BackendSpawnThunk { callback, .. } => {
            atom_contains_app_with_arg_count(callback, name, arg_count)
        }
        Atom::Var { .. }
        | Atom::Lit { .. }
        | Atom::DictRef { .. }
        | Atom::QualifiedRef { .. }
        | Atom::Symbol { .. }
        | Atom::BackendAtom { .. } => false,
    }
}

fn handler_contains_app_with_arg_count(handler: &MHandler, name: &str, arg_count: usize) -> bool {
    match handler {
        MHandler::Static {
            arms,
            return_clause,
            ..
        } => {
            arms.iter()
                .any(|arm| handler_arm_contains_app_with_arg_count(arm, name, arg_count))
                || return_clause.as_ref().is_some_and(|arm| {
                    handler_arm_contains_app_with_arg_count(arm, name, arg_count)
                })
        }
        MHandler::Dynamic {
            op_tuple,
            return_lambda,
            ..
        } => {
            atom_contains_app_with_arg_count(op_tuple, name, arg_count)
                || return_lambda
                    .as_ref()
                    .is_some_and(|atom| atom_contains_app_with_arg_count(atom, name, arg_count))
        }
        MHandler::Composite { handlers, .. } => handlers
            .iter()
            .any(|handler| handler_contains_app_with_arg_count(handler, name, arg_count)),
        MHandler::Native { .. } => false,
    }
}

fn handler_arm_contains_app_with_arg_count(
    arm: &MHandlerArm,
    name: &str,
    arg_count: usize,
) -> bool {
    expr_contains_app_with_arg_count(&arm.body, name, arg_count)
        || arm
            .finally_block
            .as_ref()
            .is_some_and(|cleanup| expr_contains_app_with_arg_count(cleanup, name, arg_count))
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

fn open_fun_type() -> crate::typechecker::Type {
    crate::typechecker::Type::Fun(
        Box::new(crate::typechecker::Type::Con("Int".to_string(), vec![])),
        Box::new(crate::typechecker::Type::Con("Int".to_string(), vec![])),
        crate::typechecker::EffectRow {
            effects: vec![],
            tail: Some(Box::new(crate::typechecker::Type::Var(99))),
        },
    )
}

fn span() -> crate::token::Span {
    crate::token::Span { start: 0, end: 0 }
}
