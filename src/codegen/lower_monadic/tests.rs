//! Tests for the new lowerer's atom + decl scaffolding (sub-steps 7a, 7b).
//!
//! Split out of `mod.rs` to keep the per-file size discipline (~800 LOC).
//! Declared from `mod.rs` under `#[cfg(test)]` — no inner `cfg(test)` here.

use std::collections::HashMap;

use super::*;
use crate::ast::{self, Lit, NodeId, Pat};
use crate::codegen::cerl::CExpr;
use crate::codegen::handler_analysis::HandlerAnalysis;
use crate::codegen::monadic::ir::{
    Atom, EffectInfo, MDecl, MDictConstructor, MExpr, MFunBinding, MVal,
};
use crate::token::Span;

fn span() -> Span {
    Span { start: 0, end: 0 }
}

fn dummy_node() -> NodeId {
    NodeId::fresh()
}

fn pure_unit() -> MExpr {
    MExpr::Pure(Atom::Lit {
        value: Lit::Unit,
        source: dummy_node(),
    })
}

/// EffectInfo borrows; tests stash the backing storage here so the
/// references stay alive for the Lowerer's lifetime.
struct EffectInfoStorage {
    effect_calls: HashMap<NodeId, crate::typechecker::ResolvedEffectOp>,
    handler_arms: HashMap<NodeId, crate::typechecker::ResolvedEffectOp>,
    fun_effects: HashMap<String, std::collections::HashSet<String>>,
    let_effect_bindings: HashMap<String, Vec<String>>,
    type_at_node: HashMap<NodeId, crate::typechecker::Type>,
}

impl EffectInfoStorage {
    fn empty() -> Self {
        Self {
            effect_calls: HashMap::new(),
            handler_arms: HashMap::new(),
            fun_effects: HashMap::new(),
            let_effect_bindings: HashMap::new(),
            type_at_node: HashMap::new(),
        }
    }

    fn view(&self) -> EffectInfo<'_> {
        EffectInfo {
            effect_calls: &self.effect_calls,
            handler_arms: &self.handler_arms,
            fun_effects: &self.fun_effects,
            let_effect_bindings: &self.let_effect_bindings,
            type_at_node: &self.type_at_node,
        }
    }
}

fn lower(program: &MProgram, module_name: &str) -> CModule {
    let resolution = ResolutionMap::new();
    let ctors = ConstructorAtoms::new();
    let ctx = CodegenContext::default();
    let handler_info = HandlerAnalysis::default();
    let storage = EffectInfoStorage::empty();
    let effect_info = storage.view();
    let mut lowerer = Lowerer::new(&resolution, &ctors, &ctx, &handler_info, &effect_info);
    lowerer.lower_module(module_name, program)
}

fn extract_stub_body(fun: &CExpr) -> &CExpr {
    match fun {
        CExpr::Fun(_, body) => body,
        _ => panic!("expected CExpr::Fun at top of CFunDef body, got {fun:?}"),
    }
}

fn assert_stub_body(body: &CExpr) {
    // Expected: apply _ReturnK('unit')
    match body {
        CExpr::Apply(callee, args) => {
            match callee.as_ref() {
                CExpr::Var(name) => assert_eq!(name, "_ReturnK"),
                other => panic!("expected Var(_ReturnK) callee, got {other:?}"),
            }
            assert_eq!(args.len(), 1);
            match &args[0] {
                CExpr::Lit(crate::codegen::cerl::CLit::Atom(a)) => assert_eq!(a, "unit"),
                other => panic!("expected Lit(Atom(unit)) arg, got {other:?}"),
            }
        }
        other => panic!("expected stub Apply, got {other:?}"),
    }
}

#[test]
fn fun_binding_with_two_user_params_emits_arity_four() {
    let fb = MFunBinding {
        id: dummy_node(),
        name: "add".to_string(),
        name_span: span(),
        params: vec![
            Pat::Var {
                id: dummy_node(),
                name: "x".to_string(),
                span: span(),
            },
            Pat::Var {
                id: dummy_node(),
                name: "y".to_string(),
                span: span(),
            },
        ],
        body: pure_unit(),
        span: span(),
    };
    let program = vec![MDecl::FunBinding(fb)];
    let cmod = lower(&program, "test_mod");

    assert_eq!(cmod.name, "test_mod");
    assert_eq!(cmod.funs.len(), 1);
    let f = &cmod.funs[0];
    assert_eq!(f.name, "add");
    // 2 user params + _Evidence + _ReturnK = 4
    assert_eq!(f.arity, 4);
    let params = match &f.body {
        CExpr::Fun(p, _) => p.clone(),
        other => panic!("expected CExpr::Fun, got {other:?}"),
    };
    assert_eq!(params, vec!["X", "Y", "_Evidence", "_ReturnK"]);
    assert_stub_body(extract_stub_body(&f.body));
    // Export shape:
    assert_eq!(cmod.exports, vec![("add".to_string(), 4)]);
}

#[test]
fn multiple_fun_bindings_emit_in_source_order() {
    let mk = |name: &str| {
        MDecl::FunBinding(MFunBinding {
            id: dummy_node(),
            name: name.to_string(),
            name_span: span(),
            params: vec![Pat::Var {
                id: dummy_node(),
                name: "a".to_string(),
                span: span(),
            }],
            body: pure_unit(),
            span: span(),
        })
    };
    let program = vec![mk("first"), mk("second"), mk("third")];
    let cmod = lower(&program, "ordered");
    let names: Vec<_> = cmod.funs.iter().map(|f| f.name.as_str()).collect();
    assert_eq!(names, vec!["first", "second", "third"]);
    for f in &cmod.funs {
        // 1 user param + _Evidence + _ReturnK
        assert_eq!(f.arity, 3);
    }
}

#[test]
fn val_emits_arity_zero_constant() {
    let v = MVal {
        id: dummy_node(),
        public: true,
        name: "pi".to_string(),
        value: pure_unit(),
        span: span(),
    };
    let program = vec![MDecl::Val(v)];
    let cmod = lower(&program, "vals");
    assert_eq!(cmod.funs.len(), 1);
    let f = &cmod.funs[0];
    assert_eq!(f.name, "pi");
    assert_eq!(f.arity, 0);
    let (params, body) = match &f.body {
        CExpr::Fun(p, b) => (p.clone(), b.as_ref()),
        other => panic!("expected CExpr::Fun, got {other:?}"),
    };
    assert!(params.is_empty(), "vals take no params");
    match body {
        CExpr::Lit(crate::codegen::cerl::CLit::Atom(a)) => assert_eq!(a, "unit"),
        other => panic!("expected val stub body 'unit', got {other:?}"),
    }
    // public val → exported at /0
    assert_eq!(cmod.exports, vec![("pi".to_string(), 0)]);
}

#[test]
fn private_val_not_exported() {
    let v = MVal {
        id: dummy_node(),
        public: false,
        name: "secret".to_string(),
        value: pure_unit(),
        span: span(),
    };
    let program = vec![MDecl::Val(v)];
    let cmod = lower(&program, "vals");
    assert!(
        cmod.exports.is_empty(),
        "private val should not be exported"
    );
    assert_eq!(cmod.funs.len(), 1);
}

#[test]
fn passthrough_typedef_emits_nothing() {
    let decl = ast::Decl::TypeDef {
        id: dummy_node(),
        doc: vec![],
        public: true,
        opaque: false,
        name: "Foo".to_string(),
        name_span: span(),
        type_params: vec![],
        variants: vec![],
        deriving: vec![],
        multiline: false,
        span: span(),
    };
    let program = vec![MDecl::Passthrough(decl)];
    let cmod = lower(&program, "m");
    assert!(cmod.funs.is_empty());
    assert!(cmod.exports.is_empty());
}

#[test]
fn passthrough_effectdef_emits_nothing() {
    let decl = ast::Decl::EffectDef {
        id: dummy_node(),
        doc: vec![],
        public: true,
        name: "Log".to_string(),
        name_span: span(),
        type_params: vec![],
        operations: vec![],
        dangling_trivia: vec![],
        span: span(),
    };
    let program = vec![MDecl::Passthrough(decl)];
    let cmod = lower(&program, "m");
    assert!(cmod.funs.is_empty());
    assert!(cmod.exports.is_empty());
}

#[test]
fn dict_constructor_emits_uniform_signature_and_tuple_body() {
    // Per 7c: DictConstructor methods are Pure(Atom::Lambda{..}); the body
    // is a tuple of the methods, returned through _ReturnK.
    let method = || {
        MExpr::Pure(Atom::Lambda {
            params: vec![Pat::Var {
                id: dummy_node(),
                name: "x".to_string(),
                span: span(),
            }],
            body: Box::new(pure_unit()),
            source: dummy_node(),
        })
    };
    let dc = MDictConstructor {
        id: dummy_node(),
        name: "__dict_Show_Int".to_string(),
        dict_params: vec!["sub_a".to_string()],
        methods: vec![method(), method()],
        method_effects: vec![vec![], vec![]],
        method_open_rows: vec![false, false],
        impl_effects: vec![],
        span: span(),
    };
    let program = vec![MDecl::DictConstructor(dc)];
    let cmod = lower(&program, "dicts");
    assert_eq!(cmod.funs.len(), 1);
    let f = &cmod.funs[0];
    assert_eq!(f.name, "__dict_Show_Int");
    // 1 dict param + _Evidence + _ReturnK = 3
    assert_eq!(f.arity, 3);
    let (params, body) = match &f.body {
        CExpr::Fun(p, b) => (p.clone(), b.as_ref()),
        other => panic!("expected CExpr::Fun, got {other:?}"),
    };
    assert_eq!(params, vec!["Sub_a", "_Evidence", "_ReturnK"]);
    // body: apply _ReturnK({fun(...), fun(...)})
    match body {
        CExpr::Apply(callee, args) => {
            assert!(matches!(callee.as_ref(), CExpr::Var(n) if n == "_ReturnK"));
            assert_eq!(args.len(), 1);
            match &args[0] {
                CExpr::Tuple(elems) => {
                    assert_eq!(elems.len(), 2);
                    for e in elems {
                        assert!(matches!(e, CExpr::Fun(_, _)));
                    }
                }
                other => panic!("expected tuple of methods, got {other:?}"),
            }
        }
        other => panic!("expected Apply(_ReturnK, {{...}}), got {other:?}"),
    }
    assert_eq!(cmod.exports, vec![("__dict_Show_Int".to_string(), 3)]);
}

#[test]
fn module_shell_name_matches_input() {
    let cmod = lower(&vec![], "my_app_server");
    assert_eq!(cmod.name, "my_app_server");
    assert!(cmod.exports.is_empty());
    assert!(cmod.funs.is_empty());
}

// ----------------------------------------------------------------------
// Atom lowering (sub-step 7b)
// ----------------------------------------------------------------------

use crate::codegen::cerl::{CBinSeg, CLit};
use crate::codegen::monadic::ir::MVar;
use crate::codegen::resolve::{ResolvedCodegenKind, ResolvedSymbol};
use crate::token::StringKind;

/// Build a `Lowerer` against caller-provided resolution + constructor
/// tables, then return both the result of `op(lowerer)` and... well,
/// just the result. The storage outlives the call by being scoped
/// outside.
fn with_lowerer<F, R>(resolution: &ResolutionMap, ctors: &ConstructorAtoms, op: F) -> R
where
    F: FnOnce(&mut Lowerer<'_>) -> R,
{
    let ctx = CodegenContext::default();
    let handler_info = HandlerAnalysis::default();
    let storage = EffectInfoStorage::empty();
    let effect_info = storage.view();
    let mut lowerer = Lowerer::new(resolution, ctors, &ctx, &handler_info, &effect_info);
    op(&mut lowerer)
}

fn lower_atom_in(atom: &Atom, resolution: &ResolutionMap, ctors: &ConstructorAtoms) -> CExpr {
    with_lowerer(resolution, ctors, |l| l.lower_atom(atom))
}

fn lower_atom_default(atom: &Atom) -> CExpr {
    let r = ResolutionMap::new();
    let c = ConstructorAtoms::new();
    lower_atom_in(atom, &r, &c)
}

fn mvar(name: &str) -> MVar {
    MVar {
        name: name.to_string(),
        id: 0,
    }
}

fn atom_lit(lit: Lit) -> Atom {
    Atom::Lit {
        value: lit,
        source: dummy_node(),
    }
}

fn atom_var(name: &str) -> Atom {
    Atom::Var {
        name: mvar(name),
        source: dummy_node(),
    }
}

#[test]
fn var_lowers_to_core_var_name() {
    // lowercase source name → capitalized Erlang var
    let ce = lower_atom_default(&atom_var("x"));
    assert!(matches!(ce, CExpr::Var(ref n) if n == "X"));
    // already-uppercase source name → underscore-prefixed
    let ce = lower_atom_default(&atom_var("X"));
    assert!(matches!(ce, CExpr::Var(ref n) if n == "_X"));
}

#[test]
fn lit_lowers_int_float_bool_unit() {
    let int = lower_atom_default(&atom_lit(Lit::Int("42".into(), 42)));
    assert!(matches!(int, CExpr::Lit(CLit::Int(42))));

    let flt = lower_atom_default(&atom_lit(Lit::Float("1.5".into(), 1.5)));
    match flt {
        CExpr::Lit(CLit::Float(f)) => assert!((f - 1.5).abs() < f64::EPSILON),
        other => panic!("expected Float lit, got {other:?}"),
    }

    let t = lower_atom_default(&atom_lit(Lit::Bool(true)));
    assert!(matches!(t, CExpr::Lit(CLit::Atom(ref a)) if a == "true"));

    let f = lower_atom_default(&atom_lit(Lit::Bool(false)));
    assert!(matches!(f, CExpr::Lit(CLit::Atom(ref a)) if a == "false"));

    let u = lower_atom_default(&atom_lit(Lit::Unit));
    assert!(matches!(u, CExpr::Lit(CLit::Atom(ref a)) if a == "unit"));
}

#[test]
fn lit_string_lowers_to_binary_bytes() {
    let ce = lower_atom_default(&atom_lit(Lit::String("hi".into(), StringKind::Normal)));
    match ce {
        CExpr::Binary(segs) => {
            assert_eq!(segs.len(), 2);
            assert!(matches!(segs[0], CBinSeg::Byte(b'h')));
            assert!(matches!(segs[1], CBinSeg::Byte(b'i')));
        }
        other => panic!("expected Binary, got {other:?}"),
    }
}

#[test]
fn ctor_nullary_nil_true_false() {
    let nil = lower_atom_default(&Atom::Ctor {
        name: "Nil".into(),
        args: vec![],
        source: dummy_node(),
    });
    assert!(matches!(nil, CExpr::Nil));

    let t = lower_atom_default(&Atom::Ctor {
        name: "True".into(),
        args: vec![],
        source: dummy_node(),
    });
    assert!(matches!(t, CExpr::Lit(CLit::Atom(ref a)) if a == "true"));

    let f = lower_atom_default(&Atom::Ctor {
        name: "False".into(),
        args: vec![],
        source: dummy_node(),
    });
    assert!(matches!(f, CExpr::Lit(CLit::Atom(ref a)) if a == "false"));
}

#[test]
fn ctor_cons_lowers_to_cons() {
    let cons = lower_atom_default(&Atom::Ctor {
        name: "Cons".into(),
        args: vec![
            atom_lit(Lit::Int("1".into(), 1)),
            Atom::Ctor {
                name: "Nil".into(),
                args: vec![],
                source: dummy_node(),
            },
        ],
        source: dummy_node(),
    });
    match cons {
        CExpr::Cons(h, t) => {
            assert!(matches!(*h, CExpr::Lit(CLit::Int(1))));
            assert!(matches!(*t, CExpr::Nil));
        }
        other => panic!("expected Cons, got {other:?}"),
    }
}

#[test]
fn ctor_adt_uses_mangled_atom_table_and_recurses() {
    // Some 'Foo.Bar' → table entry → tagged tuple
    let mut ctors = ConstructorAtoms::new();
    ctors.insert("Some".into(), "some_mangled".into());
    let resolution = ResolutionMap::new();
    let ce = lower_atom_in(
        &Atom::Ctor {
            name: "Some".into(),
            args: vec![atom_lit(Lit::Int("7".into(), 7))],
            source: dummy_node(),
        },
        &resolution,
        &ctors,
    );
    match ce {
        CExpr::Tuple(elems) => {
            assert_eq!(elems.len(), 2);
            assert!(matches!(elems[0], CExpr::Lit(CLit::Atom(ref a)) if a == "some_mangled"));
            assert!(matches!(elems[1], CExpr::Lit(CLit::Int(7))));
        }
        other => panic!("expected Tuple, got {other:?}"),
    }
}

#[test]
fn ctor_unknown_name_falls_back_to_source_name() {
    let ce = lower_atom_default(&Atom::Ctor {
        name: "NoEntry".into(),
        args: vec![],
        source: dummy_node(),
    });
    match ce {
        CExpr::Tuple(elems) => {
            assert_eq!(elems.len(), 1);
            assert!(matches!(elems[0], CExpr::Lit(CLit::Atom(ref a)) if a == "NoEntry"));
        }
        other => panic!("expected single-elem tagged tuple, got {other:?}"),
    }
}

#[test]
fn tuple_empty_and_nested_atomics() {
    let empty = lower_atom_default(&Atom::Tuple {
        elements: vec![],
        source: dummy_node(),
    });
    assert!(matches!(empty, CExpr::Tuple(ref es) if es.is_empty()));

    let ce = lower_atom_default(&Atom::Tuple {
        elements: vec![
            atom_lit(Lit::Int("1".into(), 1)),
            atom_var("y"),
            Atom::Tuple {
                elements: vec![atom_lit(Lit::Bool(true))],
                source: dummy_node(),
            },
        ],
        source: dummy_node(),
    });
    match ce {
        CExpr::Tuple(elems) => {
            assert_eq!(elems.len(), 3);
            assert!(matches!(elems[0], CExpr::Lit(CLit::Int(1))));
            assert!(matches!(elems[1], CExpr::Var(ref n) if n == "Y"));
            match &elems[2] {
                CExpr::Tuple(inner) => {
                    assert_eq!(inner.len(), 1);
                    assert!(matches!(inner[0], CExpr::Lit(CLit::Atom(ref a)) if a == "true"));
                }
                other => panic!("expected nested Tuple, got {other:?}"),
            }
        }
        other => panic!("expected Tuple, got {other:?}"),
    }
}

#[test]
fn anon_record_sorted_by_field_name() {
    // Construct in declaration order ["b", "a"]; lowered should sort to ["a", "b"]
    // and use the anon_record_tag of the sorted name list.
    let ce = lower_atom_default(&Atom::AnonRecord {
        fields: vec![
            ("b".to_string(), atom_lit(Lit::Int("2".into(), 2))),
            ("a".to_string(), atom_lit(Lit::Int("1".into(), 1))),
        ],
        source: dummy_node(),
    });
    let expected_tag = crate::ast::anon_record_tag(&["a", "b"]);
    match ce {
        CExpr::Tuple(elems) => {
            assert_eq!(elems.len(), 3);
            assert!(matches!(elems[0], CExpr::Lit(CLit::Atom(ref a)) if a == &expected_tag));
            // a's value (1) sorts before b's (2)
            assert!(matches!(elems[1], CExpr::Lit(CLit::Int(1))));
            assert!(matches!(elems[2], CExpr::Lit(CLit::Int(2))));
        }
        other => panic!("expected Tuple, got {other:?}"),
    }
}

#[test]
fn named_record_uses_constructor_atom_and_preserves_field_order() {
    // 7b limitation: declared field order is the source-supplied order
    // (translator preserves it). See lower_record_atom doc-comment.
    let mut ctors = ConstructorAtoms::new();
    ctors.insert("User".into(), "user_atom".into());
    let resolution = ResolutionMap::new();
    let ce = lower_atom_in(
        &Atom::Record {
            name: "User".into(),
            fields: vec![
                ("name".to_string(), atom_lit(Lit::Int("0".into(), 0))),
                ("age".to_string(), atom_lit(Lit::Int("42".into(), 42))),
            ],
            source: dummy_node(),
        },
        &resolution,
        &ctors,
    );
    match ce {
        CExpr::Tuple(elems) => {
            assert_eq!(elems.len(), 3);
            assert!(matches!(elems[0], CExpr::Lit(CLit::Atom(ref a)) if a == "user_atom"));
            assert!(matches!(elems[1], CExpr::Lit(CLit::Int(0))));
            assert!(matches!(elems[2], CExpr::Lit(CLit::Int(42))));
        }
        other => panic!("expected Tuple, got {other:?}"),
    }
}

#[test]
fn lambda_atom_has_uniform_signature_and_stub_body() {
    let ce = lower_atom_default(&Atom::Lambda {
        params: vec![Pat::Var {
            id: dummy_node(),
            name: "x".to_string(),
            span: span(),
        }],
        body: Box::new(pure_unit()),
        source: dummy_node(),
    });
    match ce {
        CExpr::Fun(params, body) => {
            assert_eq!(params, vec!["X", "_Evidence", "_ReturnK"]);
            assert_stub_body(&body);
        }
        other => panic!("expected Fun, got {other:?}"),
    }
}

#[test]
fn dict_ref_falls_back_to_local_var() {
    // No resolution map entry → treated as a dict-parameter variable.
    let ce = lower_atom_default(&Atom::DictRef {
        name: "sub_a".into(),
        source: dummy_node(),
    });
    assert!(matches!(ce, CExpr::Var(ref n) if n == "Sub_a"));
}

#[test]
fn dict_ref_uses_resolution_for_external_funref() {
    let node = dummy_node();
    let mut resolution = ResolutionMap::new();
    resolution.insert(
        node,
        ResolvedSymbol {
            name: "__dict_Show_Int".to_string(),
            source_module: Some("Other".to_string()),
            canonical_name: "Other.__dict_Show_Int".to_string(),
            kind: ResolvedCodegenKind::BeamFunction {
                erlang_mod: Some("other".to_string()),
                name: "__dict_Show_Int".to_string(),
                arity: 0,
                effects: vec![],
            },
        },
    );
    let ctors = ConstructorAtoms::new();
    let ce = lower_atom_in(
        &Atom::DictRef {
            name: "__dict_Show_Int".into(),
            source: node,
        },
        &resolution,
        &ctors,
    );
    // arity 0 → call other:__dict_Show_Int()
    match ce {
        CExpr::Call(m, f, args) => {
            assert_eq!(m, "other");
            assert_eq!(f, "__dict_Show_Int");
            assert!(args.is_empty());
        }
        other => panic!("expected Call, got {other:?}"),
    }
}

#[test]
fn qualified_ref_resolves_to_make_fun_for_arity_n() {
    let node = dummy_node();
    let mut resolution = ResolutionMap::new();
    resolution.insert(
        node,
        ResolvedSymbol {
            name: "abs".to_string(),
            source_module: Some("Math".to_string()),
            canonical_name: "Math.abs".to_string(),
            kind: ResolvedCodegenKind::BeamFunction {
                erlang_mod: Some("math_mod".to_string()),
                name: "abs".to_string(),
                arity: 1,
                effects: vec![],
            },
        },
    );
    let ctors = ConstructorAtoms::new();
    let ce = lower_atom_in(
        &Atom::QualifiedRef {
            module: "Math".to_string(),
            name: "abs".to_string(),
            source: node,
        },
        &resolution,
        &ctors,
    );
    // arity 1 → erlang:make_fun('math_mod', 'abs', 1)
    match ce {
        CExpr::Call(m, f, args) => {
            assert_eq!(m, "erlang");
            assert_eq!(f, "make_fun");
            assert_eq!(args.len(), 3);
            assert!(matches!(&args[0], CExpr::Lit(CLit::Atom(a)) if a == "math_mod"));
            assert!(matches!(&args[1], CExpr::Lit(CLit::Atom(a)) if a == "abs"));
            assert!(matches!(&args[2], CExpr::Lit(CLit::Int(1))));
        }
        other => panic!("expected Call, got {other:?}"),
    }
}

#[test]
fn qualified_ref_without_resolution_falls_back_to_bare_var() {
    let ce = lower_atom_default(&Atom::QualifiedRef {
        module: "Mystery".to_string(),
        name: "thing".to_string(),
        source: dummy_node(),
    });
    assert!(matches!(ce, CExpr::Var(ref n) if n == "Thing"));
}

#[test]
fn symbol_lowers_to_binary() {
    let ce = lower_atom_default(&Atom::Symbol {
        symbol: "ok".to_string(),
        source: dummy_node(),
    });
    match ce {
        CExpr::Binary(segs) => {
            assert_eq!(segs.len(), 2);
            assert!(matches!(segs[0], CBinSeg::Byte(b'o')));
            assert!(matches!(segs[1], CBinSeg::Byte(b'k')));
        }
        other => panic!("expected Binary, got {other:?}"),
    }
}

// ----------------------------------------------------------------------
// MExpr lowering (sub-step 7c)
// ----------------------------------------------------------------------

fn lower_expr_default(expr: &MExpr) -> CExpr {
    let r = ResolutionMap::new();
    let c = ConstructorAtoms::new();
    with_lowerer(&r, &c, |l| l.lower_expr(expr))
}

#[test]
fn pure_lit_lowers_to_apply_return_k() {
    let e = MExpr::Pure(Atom::Lit {
        value: Lit::Int("1".into(), 1),
        source: dummy_node(),
    });
    let ce = lower_expr_default(&e);
    // apply _ReturnK(1)
    match ce {
        CExpr::Apply(callee, args) => {
            assert!(matches!(callee.as_ref(), CExpr::Var(n) if n == "_ReturnK"));
            assert_eq!(args.len(), 1);
            assert!(matches!(args[0], CExpr::Lit(CLit::Int(1))));
        }
        other => panic!("expected Apply, got {other:?}"),
    }
}

#[test]
fn let_with_pure_value_lowers_to_plain_let() {
    // Let { x = Pure(Lit 1), body = Pure(Var x) }
    let e = MExpr::Let {
        var: mvar("x"),
        value: Box::new(MExpr::Pure(Atom::Lit {
            value: Lit::Int("1".into(), 1),
            source: dummy_node(),
        })),
        body: Box::new(MExpr::Pure(atom_var("x"))),
    };
    let ce = lower_expr_default(&e);
    match ce {
        CExpr::Let(name, value, body) => {
            assert_eq!(name, "X");
            assert!(matches!(value.as_ref(), CExpr::Lit(CLit::Int(1))));
            // body: apply _ReturnK(X)
            match body.as_ref() {
                CExpr::Apply(callee, args) => {
                    assert!(matches!(callee.as_ref(), CExpr::Var(n) if n == "_ReturnK"));
                    assert_eq!(args.len(), 1);
                    assert!(matches!(&args[0], CExpr::Var(n) if n == "X"));
                }
                other => panic!("expected Apply body, got {other:?}"),
            }
        }
        other => panic!("expected Let, got {other:?}"),
    }
}

#[test]
fn bind_lowers_to_let_with_continuation_fun() {
    // Bind { x = Pure(Lit 1), body = Pure(Var x) }
    // expected:
    //   let _K0 = fun(X) -> apply _ReturnK(X) in apply _K0(1)
    let e = MExpr::Bind {
        var: mvar("x"),
        value: Box::new(MExpr::Pure(Atom::Lit {
            value: Lit::Int("1".into(), 1),
            source: dummy_node(),
        })),
        body: Box::new(MExpr::Pure(atom_var("x"))),
    };
    let ce = lower_expr_default(&e);
    match ce {
        CExpr::Let(k_name, k_fun, value_ce) => {
            assert_eq!(k_name, "_K0");
            // k_fun: fun(X) -> apply _ReturnK(X)
            match k_fun.as_ref() {
                CExpr::Fun(params, body) => {
                    assert_eq!(params, &vec!["X".to_string()]);
                    match body.as_ref() {
                        CExpr::Apply(callee, args) => {
                            assert!(matches!(callee.as_ref(), CExpr::Var(n) if n == "_ReturnK"));
                            assert_eq!(args.len(), 1);
                            assert!(matches!(&args[0], CExpr::Var(n) if n == "X"));
                        }
                        other => panic!("expected Apply in k_fun body, got {other:?}"),
                    }
                }
                other => panic!("expected Fun for K, got {other:?}"),
            }
            // value_ce: apply _K0(1)
            match value_ce.as_ref() {
                CExpr::Apply(callee, args) => {
                    assert!(matches!(callee.as_ref(), CExpr::Var(n) if n == "_K0"));
                    assert_eq!(args.len(), 1);
                    assert!(matches!(&args[0], CExpr::Lit(CLit::Int(1))));
                }
                other => panic!("expected Apply(_K0, [1]), got {other:?}"),
            }
        }
        other => panic!("expected Let, got {other:?}"),
    }
}

#[test]
fn case_with_two_arms_lowers_to_cel_case() {
    // case x of 1 -> Pure(Lit 10); 2 -> Pure(Lit 20) end
    let e = MExpr::Case {
        scrutinee: atom_var("x"),
        arms: vec![
            crate::codegen::monadic::ir::MArm {
                pattern: Pat::Lit {
                    id: dummy_node(),
                    value: Lit::Int("1".into(), 1),
                    span: span(),
                },
                guard: None,
                body: MExpr::Pure(Atom::Lit {
                    value: Lit::Int("10".into(), 10),
                    source: dummy_node(),
                }),
                span: span(),
            },
            crate::codegen::monadic::ir::MArm {
                pattern: Pat::Lit {
                    id: dummy_node(),
                    value: Lit::Int("2".into(), 2),
                    span: span(),
                },
                guard: None,
                body: MExpr::Pure(Atom::Lit {
                    value: Lit::Int("20".into(), 20),
                    source: dummy_node(),
                }),
                span: span(),
            },
        ],
        source: dummy_node(),
    };
    let ce = lower_expr_default(&e);
    match ce {
        CExpr::Case(scrut, arms) => {
            assert!(matches!(scrut.as_ref(), CExpr::Var(n) if n == "X"));
            assert_eq!(arms.len(), 2);
            for (arm, expected_val) in arms.iter().zip([10i64, 20]) {
                assert!(matches!(
                    &arm.pat,
                    crate::codegen::cerl::CPat::Lit(CLit::Int(_))
                ));
                match &arm.body {
                    CExpr::Apply(callee, args) => {
                        assert!(matches!(callee.as_ref(), CExpr::Var(n) if n == "_ReturnK"));
                        assert!(matches!(&args[0], CExpr::Lit(CLit::Int(v)) if *v == expected_val));
                    }
                    other => panic!("expected Apply, got {other:?}"),
                }
            }
        }
        other => panic!("expected Case, got {other:?}"),
    }
}

#[test]
fn if_lowers_to_case_true_false() {
    let e = MExpr::If {
        cond: atom_var("b"),
        then_branch: Box::new(MExpr::Pure(Atom::Lit {
            value: Lit::Int("1".into(), 1),
            source: dummy_node(),
        })),
        else_branch: Box::new(MExpr::Pure(Atom::Lit {
            value: Lit::Int("2".into(), 2),
            source: dummy_node(),
        })),
        source: dummy_node(),
    };
    let ce = lower_expr_default(&e);
    match ce {
        CExpr::Case(scrut, arms) => {
            assert!(matches!(scrut.as_ref(), CExpr::Var(n) if n == "B"));
            assert_eq!(arms.len(), 2);
            match &arms[0].pat {
                crate::codegen::cerl::CPat::Lit(CLit::Atom(a)) => assert_eq!(a, "true"),
                other => panic!("expected 'true' pat, got {other:?}"),
            }
            match &arms[1].pat {
                crate::codegen::cerl::CPat::Lit(CLit::Atom(a)) => assert_eq!(a, "false"),
                other => panic!("expected 'false' pat, got {other:?}"),
            }
        }
        other => panic!("expected Case, got {other:?}"),
    }
}

#[test]
fn app_threads_evidence_and_return_k() {
    let e = MExpr::App {
        head: atom_var("f"),
        args: vec![
            atom_lit(Lit::Int("1".into(), 1)),
            atom_lit(Lit::Int("2".into(), 2)),
        ],
        source: dummy_node(),
    };
    let ce = lower_expr_default(&e);
    // apply F(1, 2, _Evidence, _ReturnK)
    match ce {
        CExpr::Apply(callee, args) => {
            assert!(matches!(callee.as_ref(), CExpr::Var(n) if n == "F"));
            assert_eq!(args.len(), 4);
            assert!(matches!(&args[0], CExpr::Lit(CLit::Int(1))));
            assert!(matches!(&args[1], CExpr::Lit(CLit::Int(2))));
            assert!(matches!(&args[2], CExpr::Var(n) if n == "_Evidence"));
            assert!(matches!(&args[3], CExpr::Var(n) if n == "_ReturnK"));
        }
        other => panic!("expected Apply, got {other:?}"),
    }
}

#[test]
fn lambda_atom_body_lowers_with_real_expr() {
    // Lambda { params=[x], body = Pure(Var x) }
    let l = Atom::Lambda {
        params: vec![Pat::Var {
            id: dummy_node(),
            name: "x".to_string(),
            span: span(),
        }],
        body: Box::new(MExpr::Pure(atom_var("x"))),
        source: dummy_node(),
    };
    let ce = lower_atom_default(&l);
    match ce {
        CExpr::Fun(params, body) => {
            assert_eq!(params, vec!["X", "_Evidence", "_ReturnK"]);
            match body.as_ref() {
                CExpr::Apply(callee, args) => {
                    assert!(matches!(callee.as_ref(), CExpr::Var(n) if n == "_ReturnK"));
                    assert_eq!(args.len(), 1);
                    assert!(matches!(&args[0], CExpr::Var(n) if n == "X"));
                }
                other => panic!("expected Apply body, got {other:?}"),
            }
        }
        other => panic!("expected Fun, got {other:?}"),
    }
}

#[test]
#[should_panic(expected = "Yield lowering deferred")]
fn yield_panics_with_deferred_message() {
    use crate::codegen::monadic::ir::EffectOpRef;
    let e = MExpr::Yield {
        op: EffectOpRef {
            effect: "Log".to_string(),
            op: "info".to_string(),
            op_index: 1,
        },
        args: vec![],
        source: dummy_node(),
    };
    let _ = lower_expr_default(&e);
}

#[test]
#[should_panic(expected = "Resume lowering deferred")]
fn resume_panics_with_deferred_message() {
    let e = MExpr::Resume {
        value: atom_lit(Lit::Unit),
        source: dummy_node(),
    };
    let _ = lower_expr_default(&e);
}
