//! Tests for the new lowerer's atom + decl scaffolding (sub-steps 7a, 7b).
//!
//! Split out of `mod.rs` to keep the per-file size discipline (~800 LOC).
//! Declared from `mod.rs` under `#[cfg(test)]` — no inner `cfg(test)` here.

use std::collections::HashMap;

use super::*;
use crate::ast::{self, Lit, NodeId, Pat};
use crate::codegen::cerl::{CExpr, CLit, CPat};
use crate::codegen::handler_analysis::HandlerAnalysis;
use crate::codegen::monadic::ir::{
    Atom, BindMode, EffectInfo, MArm, MBitSegment, MDecl, MDictConstructor, MExpr, MFunBinding,
    MVal,
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

fn contains_apply_to(expr: &CExpr, name: &str) -> bool {
    match expr {
        CExpr::Apply(callee, args) => {
            matches!(callee.as_ref(), CExpr::Var(n) if n == name)
                || contains_apply_to(callee, name)
                || args.iter().any(|arg| contains_apply_to(arg, name))
        }
        CExpr::Let(_, value, body) => {
            contains_apply_to(value, name) || contains_apply_to(body, name)
        }
        CExpr::Case(scrutinee, arms) => {
            contains_apply_to(scrutinee, name)
                || arms.iter().any(|arm| contains_apply_to(&arm.body, name))
        }
        CExpr::Fun(_, body) => contains_apply_to(body, name),
        CExpr::Tuple(values) | CExpr::Values(values) => {
            values.iter().any(|v| contains_apply_to(v, name))
        }
        _ => false,
    }
}

fn eventually_applies_return_k(expr: &CExpr) -> bool {
    contains_apply_to(expr, "_ReturnK")
}

fn contains_call(expr: &CExpr, module: &str, function: &str) -> bool {
    match expr {
        CExpr::Call(m, f, args) => {
            (m == module && f == function)
                || args.iter().any(|a| contains_call(a, module, function))
        }
        CExpr::Apply(callee, args) => {
            contains_call(callee, module, function)
                || args.iter().any(|a| contains_call(a, module, function))
        }
        CExpr::Let(_, value, body) => {
            contains_call(value, module, function) || contains_call(body, module, function)
        }
        CExpr::Case(scrutinee, arms) => {
            contains_call(scrutinee, module, function)
                || arms
                    .iter()
                    .any(|arm| contains_call(&arm.body, module, function))
        }
        CExpr::Fun(_, body) => contains_call(body, module, function),
        CExpr::Tuple(values) | CExpr::Values(values) => {
            values.iter().any(|v| contains_call(v, module, function))
        }
        _ => false,
    }
}

fn contains_element_access_index(expr: &CExpr, index: i64) -> bool {
    match expr {
        CExpr::Call(m, f, args) if m == "erlang" && f == "element" => {
            matches!(args.first(), Some(CExpr::Lit(CLit::Int(i))) if *i == index)
                || args.iter().any(|a| contains_element_access_index(a, index))
        }
        CExpr::Call(_, _, args) => args.iter().any(|a| contains_element_access_index(a, index)),
        CExpr::Apply(callee, args) => {
            contains_element_access_index(callee, index)
                || args.iter().any(|a| contains_element_access_index(a, index))
        }
        CExpr::Let(_, value, body) => {
            contains_element_access_index(value, index)
                || contains_element_access_index(body, index)
        }
        CExpr::Case(scrutinee, arms) => {
            contains_element_access_index(scrutinee, index)
                || arms
                    .iter()
                    .any(|arm| contains_element_access_index(&arm.body, index))
        }
        CExpr::Fun(_, body) => contains_element_access_index(body, index),
        CExpr::Tuple(values) | CExpr::Values(values) => values
            .iter()
            .any(|v| contains_element_access_index(v, index)),
        _ => false,
    }
}

fn contains_apply_with_args(expr: &CExpr, callee_name: &str, arg_names: &[&str]) -> bool {
    match expr {
        CExpr::Apply(callee, args) => {
            let matches_here = matches!(callee.as_ref(), CExpr::Var(n) if n == callee_name)
                && args.len() == arg_names.len()
                && args
                    .iter()
                    .zip(arg_names)
                    .all(|(arg, expected)| matches!(arg, CExpr::Var(n) if n == expected));
            matches_here
                || contains_apply_with_args(callee, callee_name, arg_names)
                || args
                    .iter()
                    .any(|arg| contains_apply_with_args(arg, callee_name, arg_names))
        }
        CExpr::Let(_, value, body) => {
            contains_apply_with_args(value, callee_name, arg_names)
                || contains_apply_with_args(body, callee_name, arg_names)
        }
        CExpr::Case(scrutinee, arms) => {
            contains_apply_with_args(scrutinee, callee_name, arg_names)
                || arms
                    .iter()
                    .any(|arm| contains_apply_with_args(&arm.body, callee_name, arg_names))
        }
        CExpr::Fun(_, body) => contains_apply_with_args(body, callee_name, arg_names),
        CExpr::Tuple(values) | CExpr::Values(values) => values
            .iter()
            .any(|v| contains_apply_with_args(v, callee_name, arg_names)),
        CExpr::Call(_, _, args) => args
            .iter()
            .any(|arg| contains_apply_with_args(arg, callee_name, arg_names)),
        _ => false,
    }
}

fn contains_apply_with_first_arg(expr: &CExpr, callee_name: &str, first_arg_name: &str) -> bool {
    match expr {
        CExpr::Apply(callee, args) => {
            let matches_here = matches!(callee.as_ref(), CExpr::Var(n) if n == callee_name)
                && matches!(args.first(), Some(CExpr::Var(n)) if n == first_arg_name);
            matches_here
                || contains_apply_with_first_arg(callee, callee_name, first_arg_name)
                || args
                    .iter()
                    .any(|arg| contains_apply_with_first_arg(arg, callee_name, first_arg_name))
        }
        CExpr::Let(_, value, body) => {
            contains_apply_with_first_arg(value, callee_name, first_arg_name)
                || contains_apply_with_first_arg(body, callee_name, first_arg_name)
        }
        CExpr::Case(scrutinee, arms) => {
            contains_apply_with_first_arg(scrutinee, callee_name, first_arg_name)
                || arms.iter().any(|arm| {
                    contains_apply_with_first_arg(&arm.body, callee_name, first_arg_name)
                })
        }
        CExpr::Fun(_, body) => contains_apply_with_first_arg(body, callee_name, first_arg_name),
        CExpr::Tuple(values) | CExpr::Values(values) => values
            .iter()
            .any(|v| contains_apply_with_first_arg(v, callee_name, first_arg_name)),
        CExpr::Call(_, _, args) => args
            .iter()
            .any(|arg| contains_apply_with_first_arg(arg, callee_name, first_arg_name)),
        _ => false,
    }
}

/// EffectInfo borrows; tests stash the backing storage here so the
/// references stay alive for the Lowerer's lifetime.
struct EffectInfoStorage {
    effect_calls: HashMap<NodeId, crate::typechecker::ResolvedEffectOp>,
    handler_arms: HashMap<NodeId, crate::typechecker::ResolvedEffectOp>,
    constructors: HashMap<NodeId, String>,
    fun_effects: HashMap<String, std::collections::HashSet<String>>,
    let_effect_bindings: HashMap<String, Vec<String>>,
    type_at_node: HashMap<NodeId, crate::typechecker::Type>,
    records: HashMap<String, crate::typechecker::RecordInfo>,
    effect_ops: HashMap<String, Vec<String>>,
    handler_effects: HashMap<String, Vec<String>>,
    handler_refs: HashMap<NodeId, crate::typechecker::ResolvedValue>,
    let_handler_effects: HashMap<NodeId, Vec<String>>,
}

impl EffectInfoStorage {
    fn empty() -> Self {
        Self {
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

    fn view(&self) -> EffectInfo<'_> {
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

fn lower(program: &MProgram, module_name: &str) -> CModule {
    let resolution = ResolutionMap::new();
    let ctors = ConstructorAtoms::new();
    let ctx = CodegenContext::default();
    let handler_info = HandlerAnalysis::default();
    let storage = EffectInfoStorage::empty();
    let effect_info = storage.view();
    let hvm = crate::codegen::monadic::ir::HandlerValueMap::new();
    let mut lowerer = Lowerer::new(&resolution, &ctors, &ctx, &handler_info, &effect_info, &hvm);
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
        guard: None,
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
            guard: None,
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
    // Body shape: let <_Evidence> = 'unit' in let <_ReturnK> = fun (_X) -> _X
    // in apply _ReturnK('unit').
    let inner_k_let = match body {
        CExpr::Let(name, _val, inner) => {
            assert_eq!(name, "_Evidence");
            inner.as_ref()
        }
        other => panic!("expected outer Let(_Evidence, ..), got {other:?}"),
    };
    let body_inner = match inner_k_let {
        CExpr::Let(name, _val, inner) => {
            assert_eq!(name, "_ReturnK");
            inner.as_ref()
        }
        other => panic!("expected inner Let(_ReturnK, ..), got {other:?}"),
    };
    match body_inner {
        CExpr::Apply(callee, args) => {
            assert!(matches!(callee.as_ref(), CExpr::Var(n) if n == "_ReturnK"));
            assert_eq!(args.len(), 1);
            assert!(
                matches!(&args[0], CExpr::Lit(crate::codegen::cerl::CLit::Atom(a)) if a == "unit")
            );
        }
        other => panic!("expected apply _ReturnK('unit'), got {other:?}"),
    }
    // public val → exported at /0
    assert_eq!(cmod.exports, vec![("pi".to_string(), 0)]);
}

#[test]
fn val_with_bind_sequenced_body_lowers_without_panic() {
    // Simulates `val x = 1 + 2` post-translation: a Bind that sequences a
    // pure computation. The body shape is non-trivial but pure — must lower
    // through lower_expr cleanly under the val's identity-K wrapper.
    let bind = MExpr::Bind {
        var: MVar {
            name: "tmp".to_string(),
            id: 0,
        },
        value: Box::new(MExpr::Pure(atom_lit(Lit::Int("1".into(), 1)))),
        body: Box::new(MExpr::Pure(atom_lit(Lit::Int("2".into(), 2)))),
        mode: BindMode::Sequence,
    };
    let v = MVal {
        id: dummy_node(),
        public: true,
        name: "sum".to_string(),
        value: bind,
        span: span(),
    };
    let cmod = lower(&vec![MDecl::Val(v)], "vals");
    assert_eq!(cmod.funs.len(), 1);
    let f = &cmod.funs[0];
    assert_eq!(f.arity, 0);
    // Outer wrappers present: arity-0 Fun, then let _Evidence, then let _ReturnK.
    match &f.body {
        CExpr::Fun(params, inner) => {
            assert!(params.is_empty());
            match inner.as_ref() {
                CExpr::Let(n, _, _) => assert_eq!(n, "_Evidence"),
                other => panic!("expected Let(_Evidence, ..), got {other:?}"),
            }
        }
        other => panic!("expected Fun, got {other:?}"),
    }
}

#[test]
fn val_with_if_body_lowers_without_panic() {
    // Simulates `val x = if true then 1 else 2`: structural If, pure.
    let if_expr = MExpr::If {
        cond: Atom::Lit {
            value: Lit::Bool(true),
            source: dummy_node(),
        },
        then_branch: Box::new(MExpr::Pure(atom_lit(Lit::Int("1".into(), 1)))),
        else_branch: Box::new(MExpr::Pure(atom_lit(Lit::Int("2".into(), 2)))),
        source: dummy_node(),
    };
    let v = MVal {
        id: dummy_node(),
        public: true,
        name: "choice".to_string(),
        value: if_expr,
        span: span(),
    };
    let cmod = lower(&vec![MDecl::Val(v)], "vals");
    assert_eq!(cmod.funs.len(), 1);
    assert_eq!(cmod.funs[0].arity, 0);
    // Smoke: no panic, arity-0 preserved.
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
fn passthrough_recorddef_populates_local_record_fields() {
    // Regression: the construction-time pass only sees IMPORTED modules
    // via `module_ctx.modules`; the currently-compiling module's records
    // must be absorbed from the program's Passthrough(RecordDef) entries.
    let mk_field = |name: &str| ast::Annotated {
        node: (name.to_string(), type_named("Int")),
        leading_trivia: vec![],
        trailing_comment: None,
        trailing_trivia: vec![],
    };
    let decl = ast::Decl::RecordDef {
        id: dummy_node(),
        doc: vec![],
        public: true,
        name: "TestCaseData".to_string(),
        name_span: span(),
        type_params: vec![],
        fields: vec![mk_field("name"), mk_field("body")],
        deriving: vec![],
        multiline: false,
        dangling_trivia: vec![],
        span: span(),
    };
    let program = vec![MDecl::Passthrough(decl)];

    let resolution = ResolutionMap::new();
    let ctors = ConstructorAtoms::new();
    let ctx = CodegenContext::default();
    let handler_info = HandlerAnalysis::default();
    let storage = EffectInfoStorage::empty();
    let effect_info = storage.view();
    let hvm = crate::codegen::monadic::ir::HandlerValueMap::new();
    let mut lowerer = Lowerer::new(&resolution, &ctors, &ctx, &handler_info, &effect_info, &hvm);
    let _ = lowerer.lower_module("Std.Test", &program);

    // Both qualified and bare keys should now resolve.
    let order_qual = lowerer
        .record_fields
        .get("Std.Test.TestCaseData")
        .expect("qualified record_fields entry should be populated");
    assert_eq!(order_qual, &vec!["name".to_string(), "body".to_string()]);
    assert_eq!(
        lowerer.record_fields.get("TestCaseData"),
        Some(&vec!["name".to_string(), "body".to_string()])
    );

    // lower_field_access must resolve declared order without panicking.
    let access = lowerer.lower_field_access(
        &atom_var("rec"),
        "body",
        Some("Std.Test.TestCaseData"),
        None,
        &crate::codegen::lower_monadic::LowerCtx::fresh(),
    );
    // The access path wraps the element/2 call in apply _ReturnK(...).
    match access {
        CExpr::Apply(callee, args) => {
            assert!(matches!(callee.as_ref(), CExpr::Var(n) if n == "_ReturnK"));
            assert_eq!(args.len(), 1);
            match &args[0] {
                CExpr::Call(m, f, call_args) => {
                    assert_eq!(m, "erlang");
                    assert_eq!(f, "element");
                    // index = position_of("body") + 2 = 1 + 2 = 3
                    assert!(matches!(call_args[0], CExpr::Lit(CLit::Int(3))));
                }
                other => panic!("expected erlang:element call, got {other:?}"),
            }
        }
        other => panic!("expected Apply, got {other:?}"),
    }
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

use crate::codegen::cerl::CBinSeg;
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
    let hvm = crate::codegen::monadic::ir::HandlerValueMap::new();
    let mut lowerer = Lowerer::new(resolution, ctors, &ctx, &handler_info, &effect_info, &hvm);
    op(&mut lowerer)
}

fn lower_atom_in(atom: &Atom, resolution: &ResolutionMap, ctors: &ConstructorAtoms) -> CExpr {
    with_lowerer(resolution, ctors, |l| {
        l.lower_atom(atom, &super::ctx::LowerCtx::fresh())
    })
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
fn local_var_shadows_stale_global_resolution() {
    let node = dummy_node();
    let mut resolution = ResolutionMap::new();
    resolution.insert(
        node,
        ResolvedSymbol {
            name: "next".to_string(),
            source_module: Some("Std.Stream".to_string()),
            canonical_name: "Std.Stream.next".to_string(),
            kind: ResolvedCodegenKind::BeamFunction {
                erlang_mod: Some("std_stream".to_string()),
                name: "next".to_string(),
                arity: 1,
                effects: vec![],
            },
        },
    );
    let ctors = ConstructorAtoms::new();
    let ce = with_lowerer(&resolution, &ctors, |lowerer| {
        lowerer.lower_atom(
            &Atom::Var {
                name: mvar("next"),
                source: node,
            },
            &super::ctx::LowerCtx::fresh().with_local("next"),
        )
    });
    assert!(matches!(ce, CExpr::Var(ref n) if n == "Next"));
}

#[test]
fn unresolved_unqualified_var_does_not_scan_all_imported_exports() {
    let atom = Atom::Var {
        name: mvar("next"),
        source: dummy_node(),
    };
    let ce = lower_atom_default(&atom);
    assert!(matches!(ce, CExpr::Var(ref n) if n == "Next"));
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
    // Uniform arity for callable values includes evidence + return K.
    match ce {
        CExpr::Call(m, f, args) => {
            assert_eq!(m, "erlang");
            assert_eq!(f, "make_fun");
            assert_eq!(args.len(), 3);
            assert!(matches!(&args[0], CExpr::Lit(CLit::Atom(a)) if a == "other"));
            assert!(matches!(&args[1], CExpr::Lit(CLit::Atom(a)) if a == "__dict_Show_Int"));
            assert!(matches!(&args[2], CExpr::Lit(CLit::Int(2))));
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
    // arity 1 plus uniform evidence/return-K slots.
    match ce {
        CExpr::Call(m, f, args) => {
            assert_eq!(m, "erlang");
            assert_eq!(f, "make_fun");
            assert_eq!(args.len(), 3);
            assert!(matches!(&args[0], CExpr::Lit(CLit::Atom(a)) if a == "math_mod"));
            assert!(matches!(&args[1], CExpr::Lit(CLit::Atom(a)) if a == "abs"));
            assert!(matches!(&args[2], CExpr::Lit(CLit::Int(3))));
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

#[test]
fn backend_spawn_thunk_lowers_to_zero_arity_callback_wrapper() {
    let ce = lower_atom_default(&Atom::BackendSpawnThunk {
        callback: Box::new(atom_var("callback")),
        source: dummy_node(),
    });

    let CExpr::Fun(params, body) = ce else {
        panic!("expected zero-arity Fun, got {ce:?}");
    };
    assert!(params.is_empty());
    let CExpr::Let(k_name, identity_k, apply_callback) = body.as_ref() else {
        panic!("expected thunk to bind identity K, got {body:?}");
    };
    assert!(k_name.starts_with("_SpawnK"));
    assert!(matches!(identity_k.as_ref(), CExpr::Fun(p, _) if p.len() == 1));
    let CExpr::Apply(callee, args) = apply_callback.as_ref() else {
        panic!("expected thunk to apply callback, got {apply_callback:?}");
    };
    assert!(matches!(callee.as_ref(), CExpr::Var(n) if n == "Callback"));
    assert_eq!(args.len(), 3);
    assert!(matches!(args[0], CExpr::Lit(CLit::Atom(ref a)) if a == "unit"));
    assert!(matches!(args[1], CExpr::Var(ref n) if n == "_Evidence"));
    assert!(matches!(args[2], CExpr::Var(ref n) if n == k_name));
}

// ----------------------------------------------------------------------
// MExpr lowering (sub-step 7c)
// ----------------------------------------------------------------------

fn lower_expr_default(expr: &MExpr) -> CExpr {
    let r = ResolutionMap::new();
    let c = ConstructorAtoms::new();
    with_lowerer(&r, &c, |l| {
        l.lower_expr(expr, &crate::codegen::lower_monadic::LowerCtx::fresh())
    })
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
        mode: BindMode::Sequence,
    };
    let ce = lower_expr_default(&e);
    let ce = skip_control_result_bubble(&ce);
    match ce {
        CExpr::Let(k_name, k_fun, value_ce) => {
            assert_eq!(k_name, "_K0");
            // k_fun: fun(X) -> apply _ReturnK(X)
            match k_fun.as_ref() {
                CExpr::Fun(params, body) => {
                    assert_eq!(params.len(), 1);
                    let other = body.as_ref();
                    assert!(
                        contains_apply_to(other, "_ReturnK"),
                        "expected K body to eventually apply _ReturnK, got {other:?}"
                    )
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

fn skip_control_result_bubble(ce: &CExpr) -> &CExpr {
    match ce {
        CExpr::Let(_, value, body) if looks_like_control_result_case(body.as_ref()) => {
            skip_identity_k_lets(value.as_ref())
        }
        _ => skip_identity_k_lets(ce),
    }
}

fn looks_like_control_result_case(ce: &CExpr) -> bool {
    matches!(ce, CExpr::Case(_, arms) if arms.iter().any(|arm| matches!(
        &arm.pat,
        CPat::Tuple(parts)
            if matches!(parts.first(), Some(CPat::Lit(CLit::Atom(tag)))
                if tag == "__saga_handler_abort" || tag == "__saga_value_result")
    )))
}

#[test]
fn case_with_two_arms_lowers_to_cel_case() {
    // case x of 1 -> Pure(Lit 10); 2 -> Pure(Lit 20) end
    let e = MExpr::Case {
        scrutinee: atom_var("x"),
        arms: vec![
            MArm {
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
            MArm {
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
            assert!(arms.len() >= 2);
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

// `Resume` lowering is covered by the 7e tests below (Resume == Pure under
// uniform K-threading; tested via the arm-body shape).

// ----------------------------------------------------------------------
// Effect machinery lowering (sub-step 7d)
// ----------------------------------------------------------------------

use crate::codegen::monadic::ir::{EffectOpRef, MHandler, MHandlerArm};

fn op_ref(effect: &str, op: &str, op_index: u32) -> EffectOpRef {
    EffectOpRef {
        effect: effect.to_string(),
        op: op.to_string(),
        op_index,
    }
}

fn handler_arm(effect: &str, op: &str, op_index: u32, n_params: usize) -> MHandlerArm {
    MHandlerArm {
        id: dummy_node(),
        op: op_ref(effect, op, op_index),
        params: (0..n_params)
            .map(|i| Pat::Var {
                id: dummy_node(),
                name: format!("p{i}"),
                span: span(),
            })
            .collect(),
        body: Box::new(pure_unit()),
        finally_block: None,
        span: span(),
    }
}

fn skip_identity_k_lets(mut ce: &CExpr) -> &CExpr {
    loop {
        match ce {
            CExpr::Let(_, value, body) if is_identity_fun(value.as_ref()) => {
                ce = body.as_ref();
            }
            _ => return ce,
        }
    }
}

fn is_identity_fun(ce: &CExpr) -> bool {
    match ce {
        CExpr::Fun(params, body) if params.len() == 1 => {
            matches!(body.as_ref(), CExpr::Var(n) if n == &params[0])
        }
        _ => false,
    }
}

fn find_yield_apply(ce: &CExpr) -> Option<(&CExpr, &[CExpr])> {
    match ce {
        CExpr::Apply(callee, args) if is_yield_callee(callee.as_ref()) => {
            Some((callee.as_ref(), args.as_slice()))
        }
        CExpr::Apply(callee, args) => {
            find_yield_apply(callee).or_else(|| args.iter().find_map(find_yield_apply))
        }
        CExpr::Let(_, value, body) => find_yield_apply(value).or_else(|| find_yield_apply(body)),
        CExpr::Case(scrutinee, arms) => find_yield_apply(scrutinee)
            .or_else(|| arms.iter().find_map(|arm| find_yield_apply(&arm.body))),
        CExpr::Fun(_, body) => find_yield_apply(body),
        CExpr::Tuple(values) | CExpr::Values(values) => values.iter().find_map(find_yield_apply),
        CExpr::Call(_, _, args) => args.iter().find_map(find_yield_apply),
        _ => None,
    }
}

fn is_yield_callee(ce: &CExpr) -> bool {
    matches!(ce, CExpr::Call(m, f, _) if m == "erlang" && f == "element")
}

/// Walk an emitted Yield CExpr and assert its shape:
///   apply (call erlang:element(<idx>, call std_evidence_bridge:find_evidence(EV_VAR, 'Effect'))) (args..., EV_VAR, K_VAR)
fn assert_yield_shape<'a>(
    ce: &'a CExpr,
    expected_effect: &str,
    expected_op_index: i64,
    expected_ev_var: &str,
    expected_k_var: &str,
) -> &'a [CExpr] {
    let ce = skip_identity_k_lets(ce);
    let (callee, args) =
        find_yield_apply(ce).unwrap_or_else(|| panic!("expected Apply for Yield, got {ce:?}"));
    // Last arg is the K var; penultimate arg is the perform-site evidence.
    let k = args.last().expect("Yield apply must have at least K");
    match k {
        CExpr::Var(n) => assert_eq!(n, expected_k_var, "K var"),
        CExpr::Fun(_, body) => assert!(
            contains_apply_to(body, expected_k_var),
            "expected delimited K to eventually apply {expected_k_var}, got {k:?}"
        ),
        other => panic!("expected K Var/Fun, got {other:?}"),
    }
    let ev_arg = args
        .get(args.len().saturating_sub(2))
        .expect("Yield apply must include perform-site evidence");
    match ev_arg {
        CExpr::Var(n) => assert_eq!(n, expected_ev_var, "perform-site evidence arg"),
        other => panic!("expected perform-site evidence Var, got {other:?}"),
    }
    // Callee: call erlang:element(idx, <find_call>)
    match callee {
        CExpr::Call(m, f, eargs) => {
            assert_eq!(m, "erlang");
            assert_eq!(f, "element");
            assert_eq!(eargs.len(), 2);
            match &eargs[0] {
                CExpr::Lit(CLit::Int(i)) => assert_eq!(*i, expected_op_index),
                other => panic!("expected op index Int, got {other:?}"),
            }
            match &eargs[1] {
                CExpr::Call(m2, f2, fargs) => {
                    assert_eq!(m2, "std_evidence_bridge");
                    assert_eq!(f2, "find_evidence");
                    assert_eq!(fargs.len(), 2);
                    match &fargs[0] {
                        CExpr::Var(n) => assert_eq!(n, expected_ev_var, "evidence var"),
                        other => panic!("expected ev Var, got {other:?}"),
                    }
                    match &fargs[1] {
                        CExpr::Lit(CLit::Atom(a)) => assert_eq!(a, expected_effect),
                        other => panic!("expected effect atom, got {other:?}"),
                    }
                }
                other => panic!("expected find_evidence Call, got {other:?}"),
            }
        }
        other => panic!("expected erlang:element callee, got {other:?}"),
    }
    &args[..args.len() - 2]
}

#[test]
fn yield_single_var_arg_lowers_to_find_evidence_apply() {
    let e = MExpr::Yield {
        op: op_ref("Std.IO.Stdio", "print", 1),
        args: vec![atom_var("msg")],
        source: dummy_node(),
    };
    let ce = lower_expr_default(&e);
    let user_args = assert_yield_shape(&ce, "Std.IO.Stdio", 1, "_Evidence", "_ReturnK");
    assert_eq!(user_args.len(), 1);
    assert!(matches!(&user_args[0], CExpr::Var(n) if n == "Msg"));
}

#[test]
fn yield_multiple_atomic_args_pass_all_through() {
    let e = MExpr::Yield {
        op: op_ref("Std.State.State", "set", 2),
        args: vec![
            atom_lit(Lit::Int("7".into(), 7)),
            atom_var("k"),
            atom_lit(Lit::Bool(true)),
        ],
        source: dummy_node(),
    };
    let ce = lower_expr_default(&e);
    let user_args = assert_yield_shape(&ce, "Std.State.State", 2, "_Evidence", "_ReturnK");
    assert_eq!(user_args.len(), 3);
    assert!(matches!(&user_args[0], CExpr::Lit(CLit::Int(7))));
    assert!(matches!(&user_args[1], CExpr::Var(n) if n == "K"));
    assert!(matches!(&user_args[2], CExpr::Lit(CLit::Atom(a)) if a == "true"));
}

#[test]
fn yield_in_bind_position_threads_bind_k_as_op_continuation() {
    // Bind { x = Yield(Log.info ()), body = Pure(Var x) }
    // Expected: outer let _K0 = fun(X) -> apply _ReturnK(X) in
    //           apply (... find_evidence ...) (_K0)
    let e = MExpr::Bind {
        var: mvar("x"),
        value: Box::new(MExpr::Yield {
            op: op_ref("Log", "info", 1),
            args: vec![],
            source: dummy_node(),
        }),
        body: Box::new(MExpr::Pure(atom_var("x"))),
        mode: BindMode::Sequence,
    };
    let ce = lower_expr_default(&e);
    let ce = skip_control_result_bubble(&ce);
    let (k_name, value_ce) = match ce {
        CExpr::Let(name, _k_fun, value) => (name, value),
        other => panic!("expected Let, got {other:?}"),
    };
    assert_eq!(k_name, "_K0");
    // value_ce: Yield apply with _K0 as the K var
    let user_args = assert_yield_shape(value_ce, "Log", 1, "_Evidence", "_K0");
    assert!(user_args.is_empty());
}

#[test]
fn with_static_single_arm_emits_real_arm_closure() {
    // Arm: handler Log { info p0 -> Pure(unit) }
    // Closure shape: fun(P0, _Ev_perform, _K_arm0) -> apply _K_arm0('unit')
    let handler = MHandler::Static {
        effects: vec!["Log".to_string()],
        arms: vec![handler_arm("Log", "info", 1, 1)],
        return_clause: None,
        source: dummy_node(),
    };
    let e = MExpr::With {
        handler,
        body: Box::new(pure_unit()),
        source: dummy_node(),
    };
    let ce = lower_expr_default(&e);
    let ops = extract_op_tuple_at(&ce, 0, "_Evidence", "Log");
    assert_eq!(ops.len(), 1);
    match &ops[0] {
        CExpr::Fun(ps, fbody) => {
            assert_eq!(
                ps,
                &vec!["P0".to_string(), "_H0".to_string(), "_K_arm0".to_string()]
            );
            // Body: apply the raw-result K — arm body is `Pure(unit)`,
            // which escapes to the with delimiter, not the arm K.
            assert!(
                contains_apply_to(fbody, "_K_ret0"),
                "arm body should apply raw-result K, got {fbody:?}"
            );
        }
        other => panic!("expected arm Fun, got {other:?}"),
    }
    // body: apply _ReturnK('unit') — no return clause, so body K is outer K.
    assert!(
        eventually_applies_return_k(&ce),
        "expected wrapper to apply outer K, got {ce:?}"
    );
}

#[test]
fn with_dynamic_uses_op_tuple_atom_directly() {
    // Dynamic handler values carry `{__saga_handler_value, OpTuple, Return}`.
    // The evidence entry must install element(2, H), not H itself.
    let handler = MHandler::Dynamic {
        effects: vec!["Std.Fail.Fail".to_string()],
        op_tuple: atom_var("h"),
        return_lambda: None,
        source: dummy_node(),
    };
    let e = MExpr::With {
        handler,
        body: Box::new(pure_unit()),
        source: dummy_node(),
    };
    let ce = lower_expr_default(&e);
    assert!(
        contains_call(&ce, "std_evidence_bridge", "insert_canonical"),
        "expected dynamic with to install evidence, got {ce:?}"
    );
    assert!(
        contains_element_access_index(&ce, 2),
        "expected dynamic with to install element(2, handler value), got {ce:?}"
    );
}

#[test]
fn with_dynamic_multi_effect_installs_evidence_per_effect() {
    // Multi-effect dynamic handlers extract each per-effect op tuple from
    // the runtime value's OpsByEffect tuple (element 2 of the handler value
    // is a tuple of {EffectAtom, OpTuple} pairs in canonical alphabetical
    // order) and chain `insert_canonical` calls — one per effect.
    let handler = MHandler::Dynamic {
        effects: vec!["B".to_string(), "A".to_string()],
        op_tuple: atom_var("h"),
        return_lambda: None,
        source: dummy_node(),
    };
    let e = MExpr::With {
        handler,
        body: Box::new(pure_unit()),
        source: dummy_node(),
    };
    let ce = lower_expr_default(&e);
    // Count `insert_canonical` Calls — one per effect.
    fn count_inserts(e: &CExpr) -> usize {
        match e {
            CExpr::Call(m, f, args) => {
                let here = (m == "std_evidence_bridge" && f == "insert_canonical") as usize;
                here + args.iter().map(count_inserts).sum::<usize>()
            }
            CExpr::Apply(c, args) => {
                count_inserts(c) + args.iter().map(count_inserts).sum::<usize>()
            }
            CExpr::Let(_, v, b) => count_inserts(v) + count_inserts(b),
            CExpr::Case(s, arms) => {
                count_inserts(s) + arms.iter().map(|a| count_inserts(&a.body)).sum::<usize>()
            }
            CExpr::Fun(_, b) => count_inserts(b),
            CExpr::Tuple(vs) | CExpr::Values(vs) => vs.iter().map(count_inserts).sum(),
            _ => 0,
        }
    }
    let inserts = count_inserts(&ce);
    assert_eq!(
        inserts, 2,
        "expected two insert_canonical calls (one per effect), got {inserts} in {ce:?}"
    );
    // Both effect atoms must appear as literals somewhere in the lowered
    // tree — they're emitted as the first element of each install entry's
    // tagged tuple.
    let rendered = format!("{ce:?}");
    assert!(
        rendered.contains("Atom(\"A\")") && rendered.contains("Atom(\"B\")"),
        "expected literal effect atoms for A and B, got {ce:?}"
    );
}

#[test]
fn with_body_sees_extended_evidence_var() {
    // body is an App — verifies that the App threads _Ev0 (not _Evidence) as the evidence arg
    let handler = MHandler::Static {
        effects: vec!["Log".to_string()],
        arms: vec![handler_arm("Log", "info", 1, 0)],
        return_clause: None,
        source: dummy_node(),
    };
    let body = MExpr::App {
        head: atom_var("f"),
        args: vec![],
        source: dummy_node(),
    };
    let e = MExpr::With {
        handler,
        body: Box::new(body),
        source: dummy_node(),
    };
    let ce = lower_expr_default(&e);
    assert!(
        contains_apply_with_first_arg(&ce, "F", "_Ev0"),
        "body app should use extended evidence _Ev0, got {ce:?}"
    );
}

#[test]
fn yield_inside_with_uses_extended_evidence() {
    // with H (Yield Log.info()) — Yield's find_evidence should reference _Ev0.
    let handler = MHandler::Static {
        effects: vec!["Log".to_string()],
        arms: vec![handler_arm("Log", "info", 1, 0)],
        return_clause: None,
        source: dummy_node(),
    };
    let e = MExpr::With {
        handler,
        body: Box::new(MExpr::Yield {
            op: op_ref("Log", "info", 1),
            args: vec![],
            source: dummy_node(),
        }),
        source: dummy_node(),
    };
    let ce = lower_expr_default(&e);
    let _ = assert_yield_shape(&ce, "Log", 1, "_Ev0", "_K_ret1");
}

#[test]
fn multi_effect_static_emits_one_insert_per_effect() {
    let handler = MHandler::Static {
        effects: vec!["A".to_string(), "B".to_string()],
        arms: vec![
            handler_arm("A", "op_a", 1, 0),
            handler_arm("B", "op_b", 1, 0),
        ],
        return_clause: None,
        source: dummy_node(),
    };
    let e = MExpr::With {
        handler,
        body: Box::new(pure_unit()),
        source: dummy_node(),
    };
    let ce = lower_expr_default(&e);
    // outer Let _Ev0 = insert(_Evidence, {'A', ...}) in
    //   Let _Ev1 = insert(_Ev0, {'B', ...}) in body
    let _ = extract_op_tuple_at(&ce, 0, "_Evidence", "A");
    let _ = extract_op_tuple_at(&ce, 1, "_Ev0", "B");
}

#[test]
fn nested_with_chains_two_inserts_with_inner_seeing_both() {
    // with H1 (with H2 (Yield E2.op()))
    let h1 = MHandler::Static {
        effects: vec!["E1".to_string()],
        arms: vec![handler_arm("E1", "op", 1, 0)],
        return_clause: None,
        source: dummy_node(),
    };
    let h2 = MHandler::Static {
        effects: vec!["E2".to_string()],
        arms: vec![handler_arm("E2", "op", 1, 0)],
        return_clause: None,
        source: dummy_node(),
    };
    let inner_with = MExpr::With {
        handler: h2,
        body: Box::new(MExpr::Yield {
            op: op_ref("E2", "op", 1),
            args: vec![],
            source: dummy_node(),
        }),
        source: dummy_node(),
    };
    let outer_with = MExpr::With {
        handler: h1,
        body: Box::new(inner_with),
        source: dummy_node(),
    };
    let ce = lower_expr_default(&outer_with);
    // outer: Let _Ev0 = insert(_Evidence, ...) in <inner>
    let _ = extract_op_tuple_at(&ce, 0, "_Evidence", "E1");
    let _ = extract_op_tuple_at(&ce, 1, "_Ev0", "E2");
    let _ = assert_yield_shape(&ce, "E2", 1, "_Ev1", "_K_ret3");
}

// ----------------------------------------------------------------------
// Handler emission (sub-step 7e)
// ----------------------------------------------------------------------

fn handler_arm_with_body(
    effect: &str,
    op: &str,
    op_index: u32,
    params: Vec<Pat>,
    body: MExpr,
) -> MHandlerArm {
    MHandlerArm {
        id: dummy_node(),
        op: op_ref(effect, op, op_index),
        params,
        body: Box::new(body),
        finally_block: None,
        span: span(),
    }
}

/// Walk an outer `with` lowering and extract its OpTuple closures for the
/// effect at `effect_idx` (first effect = index 0).
fn extract_op_tuple_at(
    ce: &CExpr,
    effect_idx: usize,
    expected_ev_var: &str,
    expected_effect: &str,
) -> Vec<CExpr> {
    let mut inserts = Vec::new();
    collect_insert_canonical_calls(skip_identity_k_lets(ce), &mut inserts);
    let (ev_arg, entry) = inserts
        .get(effect_idx)
        .unwrap_or_else(|| panic!("expected insert_canonical call #{effect_idx}, got {inserts:?}"));
    assert!(matches!(ev_arg, CExpr::Var(n) if n == expected_ev_var));
    match entry {
        CExpr::Tuple(t) => {
            assert!(matches!(&t[0], CExpr::Lit(CLit::Atom(a)) if a == expected_effect));
            match &t[1] {
                CExpr::Tuple(ops) => ops.clone(),
                other => panic!("expected OpTuple, got {other:?}"),
            }
        }
        other => panic!("expected entry Tuple, got {other:?}"),
    }
}

fn collect_insert_canonical_calls<'a>(ce: &'a CExpr, out: &mut Vec<(&'a CExpr, &'a CExpr)>) {
    match ce {
        CExpr::Call(m, f, args)
            if m == "std_evidence_bridge" && f == "insert_canonical" && args.len() == 2 =>
        {
            out.push((&args[0], &args[1]));
            for arg in args {
                collect_insert_canonical_calls(arg, out);
            }
        }
        CExpr::Call(_, _, args) => {
            for arg in args {
                collect_insert_canonical_calls(arg, out);
            }
        }
        CExpr::Apply(callee, args) => {
            collect_insert_canonical_calls(callee, out);
            for arg in args {
                collect_insert_canonical_calls(arg, out);
            }
        }
        CExpr::Let(_, value, body) => {
            collect_insert_canonical_calls(value, out);
            collect_insert_canonical_calls(body, out);
        }
        CExpr::Case(scrutinee, arms) => {
            collect_insert_canonical_calls(scrutinee, out);
            for arm in arms {
                collect_insert_canonical_calls(&arm.body, out);
            }
        }
        CExpr::Fun(_, body) => collect_insert_canonical_calls(body, out),
        CExpr::Tuple(values) | CExpr::Values(values) => {
            for value in values {
                collect_insert_canonical_calls(value, out);
            }
        }
        _ => {}
    }
}

#[test]
fn pure_in_arm_tail_escapes_to_with_site_k() {
    // arm: { p0 -> Pure p0 } — Pure in arm tail must escape to the
    // with delimiter K, NOT resume the perform-site K
    // (`_K_arm0`). This is abort-style semantics: a handler arm that
    // returns a Pure value aborts the handled computation.
    let arm = handler_arm_with_body(
        "E",
        "op",
        1,
        vec![Pat::Var {
            id: dummy_node(),
            name: "p0".to_string(),
            span: span(),
        }],
        MExpr::Pure(atom_var("p0")),
    );
    let handler = MHandler::Static {
        effects: vec!["E".to_string()],
        arms: vec![arm],
        return_clause: None,
        source: dummy_node(),
    };
    let e = MExpr::With {
        handler,
        body: Box::new(pure_unit()),
        source: dummy_node(),
    };
    let ce = lower_expr_default(&e);
    let ops = extract_op_tuple_at(&ce, 0, "_Evidence", "E");
    match &ops[0] {
        CExpr::Fun(ps, body) => {
            assert_eq!(
                ps,
                &vec!["P0".to_string(), "_H0".to_string(), "_K_arm0".to_string()]
            );
            assert!(
                contains_apply_to(body, "_K_ret0"),
                "Pure in arm tail must apply raw-result K (_K_ret0), got {body:?}"
            );
        }
        other => panic!("expected arm Fun, got {other:?}"),
    }
}

#[test]
fn pure_and_resume_emit_different_cel_at_arm_tail() {
    // Pure(v) in arm tail must escape to the with-site K (`_ReturnK`),
    // while Resume(v) in arm tail must continue the perform-site K
    // (`_K_arm0`). These have distinct semantics and must lower to
    // distinct CEL. (Previously this test asserted identity, which
    // encoded the abort-bug; the new lowerer correctly distinguishes.)
    let p_arm = handler_arm_with_body(
        "E",
        "op",
        1,
        vec![Pat::Var {
            id: dummy_node(),
            name: "p0".to_string(),
            span: span(),
        }],
        MExpr::Pure(atom_var("p0")),
    );
    let r_arm = handler_arm_with_body(
        "E",
        "op",
        1,
        vec![Pat::Var {
            id: dummy_node(),
            name: "p0".to_string(),
            span: span(),
        }],
        MExpr::Resume {
            value: atom_var("p0"),
            source: dummy_node(),
        },
    );
    let mk = |arm| MExpr::With {
        handler: MHandler::Static {
            effects: vec!["E".to_string()],
            arms: vec![arm],
            return_clause: None,
            source: dummy_node(),
        },
        body: Box::new(pure_unit()),
        source: dummy_node(),
    };
    let pce = lower_expr_default(&mk(p_arm));
    let rce = lower_expr_default(&mk(r_arm));
    assert_ne!(
        format!("{:?}", pce),
        format!("{:?}", rce),
        "Pure(v) (escape) and Resume(v) (continue) must lower to distinct CEL"
    );
}

#[test]
fn multi_arm_per_op_emits_single_closure_with_case() {
    // Two arms on the same op (op_index 1). Single closure:
    // fun(_HArg0, _Ev_perform, _K_arm0) -> case ...
    let arms = vec![
        handler_arm_with_body(
            "E",
            "op",
            1,
            vec![Pat::Constructor {
                id: dummy_node(),
                name: "True".to_string(),
                args: vec![],
                span: span(),
            }],
            MExpr::Pure(atom_lit(Lit::Int("1".into(), 1))),
        ),
        handler_arm_with_body(
            "E",
            "op",
            1,
            vec![Pat::Constructor {
                id: dummy_node(),
                name: "False".to_string(),
                args: vec![],
                span: span(),
            }],
            MExpr::Pure(atom_lit(Lit::Int("2".into(), 2))),
        ),
    ];
    let handler = MHandler::Static {
        effects: vec!["E".to_string()],
        arms,
        return_clause: None,
        source: dummy_node(),
    };
    let e = MExpr::With {
        handler,
        body: Box::new(pure_unit()),
        source: dummy_node(),
    };
    let ce = lower_expr_default(&e);
    let ops = extract_op_tuple_at(&ce, 0, "_Evidence", "E");
    assert_eq!(ops.len(), 1, "multi-arm-per-op collapses to one closure");
    match &ops[0] {
        CExpr::Fun(ps, body) => {
            assert_eq!(
                ps,
                &vec![
                    "_HArg0".to_string(),
                    "_H0".to_string(),
                    "_K_arm0".to_string()
                ]
            );
            match body.as_ref() {
                CExpr::Case(scrut, case_arms) => {
                    assert!(matches!(scrut.as_ref(), CExpr::Var(n) if n == "_HArg0"));
                    assert_eq!(case_arms.len(), 2);
                    // Neither arm resumes, so each escapes its `Pure(...)` to
                    // the raw-result K (`_K_ret0`), then — because the with site
                    // has an abort marker — tags the result so nested `with`
                    // boundaries can propagate the abort. This matches the
                    // single-arm aborting-arm shape (`lower_captured_arm_body`).
                    for arm in case_arms {
                        match &arm.body {
                            CExpr::Let(_, value, body) => {
                                match value.as_ref() {
                                    CExpr::Apply(c, _) => assert!(
                                        matches!(c.as_ref(), CExpr::Var(n) if n == "_K_ret0")
                                    ),
                                    other => {
                                        panic!(
                                            "expected Apply(_K_ret0, _) bound value, got {other:?}"
                                        )
                                    }
                                }
                                // The wrapping case carries an `_AbortValue` arm
                                // that builds an abort tuple with the with-site
                                // marker.
                                let has_abort_arm = matches!(body.as_ref(), CExpr::Case(_, wrap)
                                    if wrap.iter().any(|a| matches!(&a.pat, CPat::Var(n) if n == "_AbortValue")));
                                assert!(has_abort_arm, "expected abort-tagging case, got {body:?}");
                            }
                            other => panic!("expected Let(abort-tag) arm body, got {other:?}"),
                        }
                    }
                }
                other => panic!("expected Case body, got {other:?}"),
            }
        }
        other => panic!("expected arm Fun, got {other:?}"),
    }
}

#[test]
fn multi_op_static_handler_orders_closures_by_op_index() {
    // Two ops on the same effect; arms supplied out of order to verify sort.
    let arms = vec![
        handler_arm("E", "b_op", 2, 0),
        handler_arm("E", "a_op", 1, 0),
    ];
    let handler = MHandler::Static {
        effects: vec!["E".to_string()],
        arms,
        return_clause: None,
        source: dummy_node(),
    };
    let e = MExpr::With {
        handler,
        body: Box::new(pure_unit()),
        source: dummy_node(),
    };
    let ce = lower_expr_default(&e);
    let ops = extract_op_tuple_at(&ce, 0, "_Evidence", "E");
    assert_eq!(ops.len(), 2);
    // Both are zero-arg arms, so closures have perform-site evidence + K_arm params.
    for (i, op) in ops.iter().enumerate() {
        let arm_k = format!("_K_arm{}", i);
        match op {
            CExpr::Fun(ps, _) => {
                assert_eq!(ps.len(), 2);
                assert!(ps[0].starts_with("_H"));
                assert_eq!(ps[1], arm_k);
            }
            other => panic!("expected Fun, got {other:?}"),
        }
    }
}

#[test]
#[should_panic(expected = "missing arm for op_index 1")]
fn missing_arm_for_op_index_panics() {
    // Arm with op_index 2 but no op_index 1 — gap, must panic.
    let arms = vec![handler_arm("E", "op_b", 2, 0)];
    let handler = MHandler::Static {
        effects: vec!["E".to_string()],
        arms,
        return_clause: None,
        source: dummy_node(),
    };
    let e = MExpr::With {
        handler,
        body: Box::new(pure_unit()),
        source: dummy_node(),
    };
    let _ = lower_expr_default(&e);
}

#[test]
fn multi_effect_static_emits_one_op_tuple_per_effect() {
    let arms = vec![
        handler_arm("A", "op_a", 1, 0),
        handler_arm("B", "op_b", 1, 0),
    ];
    let handler = MHandler::Static {
        effects: vec!["A".to_string(), "B".to_string()],
        arms,
        return_clause: None,
        source: dummy_node(),
    };
    let e = MExpr::With {
        handler,
        body: Box::new(pure_unit()),
        source: dummy_node(),
    };
    let ce = lower_expr_default(&e);
    let a_ops = extract_op_tuple_at(&ce, 0, "_Evidence", "A");
    let b_ops = extract_op_tuple_at(&ce, 1, "_Ev0", "B");
    assert_eq!(a_ops.len(), 1);
    assert_eq!(b_ops.len(), 1);
}

#[test]
fn return_clause_wraps_body_k() {
    // Handler: arm + return v -> Pure(v). Body's K must be _K_ret0,
    // bound to a closure whose body applies _ReturnK to its param.
    let ret = handler_arm_with_body(
        "E",
        "op",
        1,
        vec![Pat::Var {
            id: dummy_node(),
            name: "v".to_string(),
            span: span(),
        }],
        MExpr::Pure(atom_var("v")),
    );
    let handler = MHandler::Static {
        effects: vec!["E".to_string()],
        arms: vec![handler_arm("E", "op", 1, 0)],
        return_clause: Some(ret),
        source: dummy_node(),
    };
    let e = MExpr::With {
        handler,
        body: Box::new(MExpr::Pure(atom_lit(Lit::Int("42".into(), 42)))),
        source: dummy_node(),
    };
    let ce = lower_expr_default(&e);
    let _ = extract_op_tuple_at(&ce, 0, "_Evidence", "E");
    assert!(
        contains_apply_to(&ce, "_K_ret0"),
        "return clause should forward through raw-result K, got {ce:?}"
    );
    assert!(
        eventually_applies_return_k(&ce),
        "with wrapper should eventually apply outer _ReturnK, got {ce:?}"
    );
}

#[test]
fn no_return_clause_passes_outer_k_through() {
    let handler = MHandler::Static {
        effects: vec!["E".to_string()],
        arms: vec![handler_arm("E", "op", 1, 0)],
        return_clause: None,
        source: dummy_node(),
    };
    let e = MExpr::With {
        handler,
        body: Box::new(MExpr::Pure(atom_lit(Lit::Int("7".into(), 7)))),
        source: dummy_node(),
    };
    let ce = lower_expr_default(&e);
    // The raw-result K is an identity wrapper; after it, the evidence Let remains.
    let _ = extract_op_tuple_at(&ce, 0, "_Evidence", "E");
    assert!(
        eventually_applies_return_k(&ce),
        "expected outer K apply, got {ce:?}"
    );
}

#[test]
fn nested_with_composes_return_clauses_inner_first() {
    // ((expr with R1) with R2) — body's K = innermost _K_ret. Innermost
    // _K_ret closes over the next-outer's _K_ret, which closes over _ReturnK.
    let r1 = handler_arm_with_body(
        "E1",
        "op",
        1,
        vec![Pat::Var {
            id: dummy_node(),
            name: "v".to_string(),
            span: span(),
        }],
        MExpr::Pure(atom_var("v")),
    );
    let r2 = handler_arm_with_body(
        "E2",
        "op",
        1,
        vec![Pat::Var {
            id: dummy_node(),
            name: "v".to_string(),
            span: span(),
        }],
        MExpr::Pure(atom_var("v")),
    );
    let inner = MExpr::With {
        handler: MHandler::Static {
            effects: vec!["E1".to_string()],
            arms: vec![handler_arm("E1", "op", 1, 0)],
            return_clause: Some(r1),
            source: dummy_node(),
        },
        body: Box::new(MExpr::Pure(atom_lit(Lit::Int("1".into(), 1)))),
        source: dummy_node(),
    };
    let outer = MExpr::With {
        handler: MHandler::Static {
            effects: vec!["E2".to_string()],
            arms: vec![handler_arm("E2", "op", 1, 0)],
            return_clause: Some(r2),
            source: dummy_node(),
        },
        body: Box::new(inner),
        source: dummy_node(),
    };
    let ce = lower_expr_default(&outer);
    let _ = extract_op_tuple_at(&ce, 0, "_Evidence", "E2");
    let _ = extract_op_tuple_at(&ce, 1, "_Ev0", "E1");
    assert!(
        contains_apply_to(&ce, "_K_ret2"),
        "inner return-K must forward to outer return-K, got {ce:?}"
    );
}

#[test]
fn dynamic_return_lambda_composes_via_wrapper() {
    // Dynamic handler with return_lambda = h_ret (atom Var). Wrapper:
    //   _K_ret0 = fun(_H0) -> apply H_Ret(_H0, _Evidence, _ReturnK)
    let handler = MHandler::Dynamic {
        effects: vec!["E".to_string()],
        op_tuple: atom_var("h"),
        return_lambda: Some(atom_var("h_ret")),
        source: dummy_node(),
    };
    let e = MExpr::With {
        handler,
        body: Box::new(MExpr::Pure(atom_lit(Lit::Int("9".into(), 9)))),
        source: dummy_node(),
    };
    let ce = lower_expr_default(&e);
    assert!(
        contains_apply_to(&ce, "H_ret"),
        "expected explicit dynamic return lambda to be applied, got {ce:?}"
    );
    assert!(
        contains_apply_to(&ce, "_K_ret0"),
        "expected return lambda wrapper to target raw-result K, got {ce:?}"
    );
    assert!(
        eventually_applies_return_k(&ce),
        "expected dynamic with to eventually apply outer continuation, got {ce:?}"
    );
}

#[test]
fn resume_inside_lambda_in_arm_body_uses_arm_k_via_closure() {
    // Arm body: Pure(lambda{ () -> Resume(unit) }). The inner lambda's
    // Resume must apply the *enclosing arm's* `_K_arm0` via lexical
    // closure capture — that's what makes value-producing resume work
    // (e.g. `(resume v) x` patterns in state-threading handlers). The
    // lambda's own `_ReturnK` is its tail K for `Pure`, but `Resume`
    // resolves to the captured arm K through `LowerCtx.arm_k`
    // propagation in `lower_lambda_atom`.
    let lambda_atom = Atom::Lambda {
        params: vec![Pat::Var {
            id: dummy_node(),
            name: "u".to_string(),
            span: span(),
        }],
        body: Box::new(MExpr::Resume {
            value: atom_lit(Lit::Unit),
            source: dummy_node(),
        }),
        source: dummy_node(),
    };
    let arm = handler_arm_with_body("E", "op", 1, vec![], MExpr::Pure(lambda_atom));
    let handler = MHandler::Static {
        effects: vec!["E".to_string()],
        arms: vec![arm],
        return_clause: None,
        source: dummy_node(),
    };
    let e = MExpr::With {
        handler,
        body: Box::new(pure_unit()),
        source: dummy_node(),
    };
    let ce = lower_expr_default(&e);
    let ops = extract_op_tuple_at(&ce, 0, "_Evidence", "E");
    // Outer: fun(_Ev_perform, _K_arm0) -> apply _K_arm0(<lambda>).
    let arm_body = match &ops[0] {
        CExpr::Fun(ps, body) => {
            assert_eq!(ps, &vec!["_H0".to_string(), "_K_arm0".to_string()]);
            body.as_ref()
        }
        other => panic!("expected arm Fun, got {other:?}"),
    };
    // arm body: apply raw-result K(<inner lambda>) — the outer Pure escapes
    // to the with delimiter, not the arm K.
    let inner_lambda = match arm_body {
        CExpr::Apply(c, args) => {
            assert!(matches!(c.as_ref(), CExpr::Var(n) if n == "_K_ret0"));
            &args[0]
        }
        other => panic!("expected arm body apply, got {other:?}"),
    };
    // Lambda signature: (U, _Evidence, _ReturnK) and body `apply _ReturnK('unit')`.
    match inner_lambda {
        CExpr::Fun(ps, lbody) => {
            assert_eq!(
                ps,
                &vec![
                    "U".to_string(),
                    "_Evidence".to_string(),
                    "_ReturnK".to_string()
                ]
            );
            match lbody.as_ref() {
                CExpr::Let(_, value, next) => {
                    assert!(
                        contains_apply_to(value, "_K_arm0"),
                        "Resume inside lambda must use enclosing arm's _K_arm0 \
                         (captured via closure), not lambda's own _ReturnK; got {value:?}"
                    );
                    assert!(
                        contains_apply_to(next, "_ReturnK"),
                        "resume result must continue through the lambda's local _ReturnK \
                         after abort-marker unwrapping; got {next:?}"
                    );
                }
                other => panic!("expected lambda body Let, got {other:?}"),
            }
        }
        other => panic!("expected lambda Fun, got {other:?}"),
    }
}

#[test]
fn resume_in_bind_position_calls_arm_k_directly() {
    // Arm body: Bind { x = Resume(unit), body = Pure(Var x) }.
    //
    // Resume is value-producing: it applies the perform-site continuation
    // (`_K_arm0`) and then feeds the returned handled-body value into the
    // local Bind continuation (`_K0`). Abort-marker unwrapping may insert a
    // case between the two, but the captured arm K must still be the call
    // target and the local K must still receive the result.
    let arm_body = MExpr::Bind {
        var: mvar("x"),
        value: Box::new(MExpr::Resume {
            value: atom_lit(Lit::Unit),
            source: dummy_node(),
        }),
        body: Box::new(MExpr::Pure(atom_var("x"))),
        mode: BindMode::Sequence,
    };
    let arm = handler_arm_with_body("E", "op", 1, vec![], arm_body);
    let handler = MHandler::Static {
        effects: vec!["E".to_string()],
        arms: vec![arm],
        return_clause: None,
        source: dummy_node(),
    };
    let e = MExpr::With {
        handler,
        body: Box::new(pure_unit()),
        source: dummy_node(),
    };
    let ce = lower_expr_default(&e);
    let ops = extract_op_tuple_at(&ce, 0, "_Evidence", "E");
    let inner = match &ops[0] {
        CExpr::Fun(ps, body) => {
            assert_eq!(ps, &vec!["_H0".to_string(), "_K_arm0".to_string()]);
            body.as_ref()
        }
        other => panic!("expected arm Fun, got {other:?}"),
    };
    assert!(
        contains_apply_to(inner, "_K_arm0"),
        "Resume must apply the perform-site K (_K_arm0), got {inner:?}"
    );
    assert!(
        contains_apply_to(inner, "_K0"),
        "resume result must continue through the bind continuation _K0 \
         after abort-marker unwrapping; got {inner:?}"
    );
}

// ----------------------------------------------------------------------
// Sub-step 7g — remaining MExpr variants
// ----------------------------------------------------------------------

fn atom_int(n: i64) -> Atom {
    atom_lit(Lit::Int(n.to_string(), n))
}

/// Build a lowerer with a pre-seeded `record_fields` cache; lets tests
/// drive `FieldAccess`/`RecordUpdate` without standing up a full
/// `CodegenContext` of modules.
fn lower_with_records<F, R>(fields_by_record: &[(&str, Vec<&str>)], op: F) -> R
where
    F: FnOnce(&mut Lowerer<'_>) -> R,
{
    let resolution = ResolutionMap::new();
    let ctors = ConstructorAtoms::new();
    let ctx = CodegenContext::default();
    let handler_info = HandlerAnalysis::default();
    let storage = EffectInfoStorage::empty();
    let effect_info = storage.view();
    let hvm = crate::codegen::monadic::ir::HandlerValueMap::new();
    let mut lowerer = Lowerer::new(&resolution, &ctors, &ctx, &handler_info, &effect_info, &hvm);
    for (rec, fields) in fields_by_record {
        lowerer.record_fields.insert(
            rec.to_string(),
            fields.iter().map(|f| f.to_string()).collect(),
        );
    }
    op(&mut lowerer)
}

#[test]
fn field_access_emits_element_call_wrapped_in_return_k() {
    // record Foo { a, b, c }; lowering of .b → element(3, R) wrapped in K.
    let expr = MExpr::FieldAccess {
        record: atom_var("r"),
        field: "b".to_string(),
        record_name: Some("Foo".to_string()),
        anon_fields: None,
        source: dummy_node(),
    };
    let ce = lower_with_records(&[("Foo", vec!["a", "b", "c"])], |l| {
        l.lower_expr(&expr, &crate::codegen::lower_monadic::LowerCtx::fresh())
    });
    match ce {
        CExpr::Apply(callee, args) => {
            assert!(matches!(callee.as_ref(), CExpr::Var(n) if n == "_ReturnK"));
            assert_eq!(args.len(), 1);
            match &args[0] {
                CExpr::Call(m, f, call_args) => {
                    assert_eq!(m, "erlang");
                    assert_eq!(f, "element");
                    assert!(matches!(&call_args[0], CExpr::Lit(CLit::Int(3))));
                    assert!(matches!(&call_args[1], CExpr::Var(n) if n == "R"));
                }
                other => panic!("expected element call, got {other:?}"),
            }
        }
        other => panic!("expected Apply, got {other:?}"),
    }
}

#[test]
fn field_access_uses_anon_fields_without_record_fields_entry() {
    // Anonymous record `{ a_b, c }`: field order comes from `anon_fields`,
    // not from any `record_fields` entry and not by decoding the tag. A field
    // name containing `_` must still resolve. `.c` → element(3, R).
    let ce = lower_with_records(&[], |l| {
        l.lower_field_access(
            &atom_var("r"),
            "c",
            Some("__anon_3_a_b_1_c"),
            Some(&["a_b".to_string(), "c".to_string()]),
            &crate::codegen::lower_monadic::LowerCtx::fresh(),
        )
    });
    match ce {
        CExpr::Apply(_, args) => match &args[0] {
            CExpr::Call(m, f, call_args) => {
                assert_eq!(m, "erlang");
                assert_eq!(f, "element");
                // position_of("c") in [a_b, c] = 1; index = 1 + 2 = 3.
                assert!(matches!(&call_args[0], CExpr::Lit(CLit::Int(3))));
            }
            other => panic!("expected element call, got {other:?}"),
        },
        other => panic!("expected Apply, got {other:?}"),
    }
}

#[test]
fn record_update_rebuilds_tuple_with_tag_preserved() {
    // record Pair { x, y }; update {r | y = 9}.
    // Expected: apply _ReturnK(let _H0 = R in {element(1,_H0), element(2,_H0), 9})
    let expr = MExpr::RecordUpdate {
        record: atom_var("r"),
        fields: vec![("y".to_string(), atom_int(9))],
        record_name: Some("Pair".to_string()),
        anon_fields: None,
        source: dummy_node(),
    };
    let ce = lower_with_records(&[("Pair", vec!["x", "y"])], |l| {
        l.lower_expr(&expr, &crate::codegen::lower_monadic::LowerCtx::fresh())
    });
    let arg = match ce {
        CExpr::Apply(callee, args) => {
            assert!(matches!(callee.as_ref(), CExpr::Var(n) if n == "_ReturnK"));
            args.into_iter().next().expect("apply arg")
        }
        other => panic!("expected Apply, got {other:?}"),
    };
    let (let_name, let_val, let_body) = match arg {
        CExpr::Let(n, v, b) => (n, v, b),
        other => panic!("expected Let, got {other:?}"),
    };
    assert_eq!(let_name, "_H0");
    assert!(matches!(let_val.as_ref(), CExpr::Var(n) if n == "R"));
    let elems = match *let_body {
        CExpr::Tuple(e) => e,
        other => panic!("expected Tuple body, got {other:?}"),
    };
    // tag, x (untouched), y (updated)
    assert_eq!(elems.len(), 3);
    match &elems[0] {
        CExpr::Call(_, f, args) => {
            assert_eq!(f, "element");
            assert!(matches!(&args[0], CExpr::Lit(CLit::Int(1))));
        }
        other => panic!("expected tag element call, got {other:?}"),
    }
    match &elems[1] {
        CExpr::Call(_, f, args) => {
            assert_eq!(f, "element");
            assert!(matches!(&args[0], CExpr::Lit(CLit::Int(2))));
        }
        other => panic!("expected x element call, got {other:?}"),
    }
    assert!(matches!(&elems[2], CExpr::Lit(CLit::Int(9))));
}

#[test]
fn dict_method_access_emits_element_call_one_based() {
    let expr = MExpr::DictMethodAccess {
        dict: atom_var("d"),
        trait_name: "Show".to_string(),
        method_index: 2,
        source: dummy_node(),
    };
    let ce = lower_expr_default(&expr);
    match ce {
        CExpr::Apply(_, args) => match &args[0] {
            CExpr::Call(m, f, ca) => {
                assert_eq!(m, "erlang");
                assert_eq!(f, "element");
                // method_index 2 → element 3 (skips name tag at idx 1)
                assert!(matches!(&ca[0], CExpr::Lit(CLit::Int(3))));
                assert!(matches!(&ca[1], CExpr::Var(n) if n == "D"));
            }
            other => panic!("expected element call, got {other:?}"),
        },
        other => panic!("expected Apply, got {other:?}"),
    }
}

#[test]
fn foreign_call_lowers_to_module_call_wrapped_in_k() {
    // ForeignCall("lists", "reverse", [x])
    let expr = MExpr::ForeignCall {
        module: "lists".to_string(),
        func: "reverse".to_string(),
        args: vec![atom_var("x")],
        source: dummy_node(),
    };
    let ce = lower_expr_default(&expr);
    match ce {
        CExpr::Apply(callee, args) => {
            assert!(matches!(callee.as_ref(), CExpr::Var(n) if n == "_ReturnK"));
            match &args[0] {
                CExpr::Call(m, f, ca) => {
                    assert_eq!(m, "lists");
                    assert_eq!(f, "reverse");
                    assert_eq!(ca.len(), 1);
                    assert!(matches!(&ca[0], CExpr::Var(n) if n == "X"));
                }
                other => panic!("expected Call, got {other:?}"),
            }
        }
        other => panic!("expected Apply, got {other:?}"),
    }
}

#[test]
fn foreign_call_no_args_emits_zero_arg_call() {
    let expr = MExpr::ForeignCall {
        module: "erlang".to_string(),
        func: "self".to_string(),
        args: vec![],
        source: dummy_node(),
    };
    let ce = lower_expr_default(&expr);
    let arg = match ce {
        CExpr::Apply(_, mut args) => args.remove(0),
        other => panic!("expected Apply, got {other:?}"),
    };
    match arg {
        CExpr::Call(m, f, ca) => {
            assert_eq!(m, "erlang");
            assert_eq!(f, "self");
            assert!(ca.is_empty());
        }
        other => panic!("expected Call, got {other:?}"),
    }
}

#[test]
fn binop_add_emits_erlang_plus_wrapped_in_k() {
    let expr = MExpr::BinOp {
        op: ast::BinOp::Add,
        left: atom_int(1),
        right: atom_int(2),
        source: dummy_node(),
    };
    let ce = lower_expr_default(&expr);
    match ce {
        CExpr::Apply(_, args) => match &args[0] {
            CExpr::Call(m, f, ca) => {
                assert_eq!(m, "erlang");
                assert_eq!(f, "+");
                assert_eq!(ca.len(), 2);
                assert!(matches!(&ca[0], CExpr::Lit(CLit::Int(1))));
                assert!(matches!(&ca[1], CExpr::Lit(CLit::Int(2))));
            }
            other => panic!("expected Call, got {other:?}"),
        },
        other => panic!("expected Apply, got {other:?}"),
    }
}

#[test]
fn unary_minus_emits_zero_minus_value() {
    let expr = MExpr::UnaryMinus {
        value: atom_int(7),
        source: dummy_node(),
    };
    let ce = lower_expr_default(&expr);
    match ce {
        CExpr::Apply(_, args) => match &args[0] {
            CExpr::Call(m, f, ca) => {
                assert_eq!(m, "erlang");
                assert_eq!(f, "-");
                assert!(matches!(&ca[0], CExpr::Lit(CLit::Int(0))));
                assert!(matches!(&ca[1], CExpr::Lit(CLit::Int(7))));
            }
            other => panic!("expected Call, got {other:?}"),
        },
        other => panic!("expected Apply, got {other:?}"),
    }
}

#[test]
fn bitstring_string_literal_segment_expands_to_byte_run() {
    let expr = MExpr::BitString {
        segments: vec![MBitSegment {
            value: atom_lit(Lit::String(
                "hi".to_string(),
                crate::token::StringKind::Normal,
            )),
            size: None,
            specs: vec![],
            span: span(),
        }],
        source: dummy_node(),
    };
    let ce = lower_expr_default(&expr);
    match ce {
        CExpr::Apply(_, args) => match &args[0] {
            CExpr::Binary(segs) => {
                assert_eq!(segs.len(), 2);
                assert!(matches!(segs[0], CBinSeg::Byte(b'h')));
                assert!(matches!(segs[1], CBinSeg::Byte(b'i')));
            }
            other => panic!("expected Binary, got {other:?}"),
        },
        other => panic!("expected Apply, got {other:?}"),
    }
}

#[test]
fn bitstring_integer_segment_with_size_emits_sized_segment() {
    let expr = MExpr::BitString {
        segments: vec![MBitSegment {
            value: atom_int(255),
            size: Some(atom_int(16)),
            specs: vec![],
            span: span(),
        }],
        source: dummy_node(),
    };
    let ce = lower_expr_default(&expr);
    match ce {
        CExpr::Apply(_, args) => match &args[0] {
            CExpr::Binary(segs) => {
                assert_eq!(segs.len(), 1);
                match &segs[0] {
                    CBinSeg::Segment { value, size, .. } => {
                        assert!(matches!(value, CExpr::Lit(CLit::Int(255))));
                        match size {
                            crate::codegen::cerl::BinSegSize::Expr(CExpr::Lit(CLit::Int(16))) => {}
                            other => panic!("expected explicit size 16, got {other:?}"),
                        }
                    }
                    other => panic!("expected Segment, got {other:?}"),
                }
            }
            other => panic!("expected Binary, got {other:?}"),
        },
        other => panic!("expected Apply, got {other:?}"),
    }
}

#[test]
fn receive_without_after_defaults_to_infinity_and_true() {
    // receive { x -> x }
    let expr = MExpr::Receive {
        arms: vec![MArm {
            pattern: Pat::Var {
                id: dummy_node(),
                name: "x".to_string(),
                span: span(),
            },
            guard: None,
            body: MExpr::Pure(atom_var("x")),
            span: span(),
        }],
        after: None,
        source: dummy_node(),
    };
    let ce = lower_expr_default(&expr);
    match ce {
        CExpr::Receive(arms, timeout, body) => {
            assert_eq!(arms.len(), 1);
            assert!(matches!(timeout.as_ref(), CExpr::Lit(CLit::Atom(a)) if a == "infinity"));
            assert!(matches!(body.as_ref(), CExpr::Lit(CLit::Atom(a)) if a == "true"));
            // arm body shares the enclosing K
            match &arms[0].body {
                CExpr::Apply(c, _) => {
                    assert!(matches!(c.as_ref(), CExpr::Var(n) if n == "_ReturnK"));
                }
                other => panic!("expected arm body Apply, got {other:?}"),
            }
        }
        other => panic!("expected Receive, got {other:?}"),
    }
}

#[test]
fn receive_with_after_lowers_timeout_atom_and_body_under_outer_k() {
    let expr = MExpr::Receive {
        arms: vec![MArm {
            pattern: Pat::Wildcard {
                id: dummy_node(),
                span: span(),
            },
            guard: None,
            body: MExpr::Pure(atom_int(1)),
            span: span(),
        }],
        after: Some((atom_int(5000), Box::new(MExpr::Pure(atom_int(0))))),
        source: dummy_node(),
    };
    let ce = lower_expr_default(&expr);
    match ce {
        CExpr::Receive(arms, timeout, body) => {
            assert_eq!(arms.len(), 1);
            assert!(matches!(timeout.as_ref(), CExpr::Lit(CLit::Int(5000))));
            // after-body lowers under the outer K too
            match body.as_ref() {
                CExpr::Apply(c, args) => {
                    assert!(matches!(c.as_ref(), CExpr::Var(n) if n == "_ReturnK"));
                    assert!(matches!(args[0], CExpr::Lit(CLit::Int(0))));
                }
                other => panic!("expected after-body Apply, got {other:?}"),
            }
        }
        other => panic!("expected Receive, got {other:?}"),
    }
}

#[test]
fn case_arm_guard_lowers_to_pure_binop() {
    // case x of y when y > 0 -> y end
    let expr = MExpr::Case {
        scrutinee: atom_var("x"),
        arms: vec![MArm {
            pattern: Pat::Var {
                id: dummy_node(),
                name: "y".to_string(),
                span: span(),
            },
            guard: Some(MExpr::BinOp {
                op: ast::BinOp::Gt,
                left: atom_var("y"),
                right: atom_int(0),
                source: dummy_node(),
            }),
            body: MExpr::Pure(atom_var("y")),
            span: span(),
        }],
        source: dummy_node(),
    };
    let ce = lower_expr_default(&expr);
    let arms = match ce {
        CExpr::Case(_, arms) => arms,
        other => panic!("expected Case, got {other:?}"),
    };
    let guard = arms[0]
        .guard
        .as_ref()
        .expect("guard should be lowered, not None");
    match guard {
        CExpr::Call(m, f, args) => {
            assert_eq!(m, "erlang");
            assert_eq!(f, ">");
            assert!(matches!(&args[0], CExpr::Var(n) if n == "Y"));
            assert!(matches!(&args[1], CExpr::Lit(CLit::Int(0))));
        }
        other => panic!("expected guard Call, got {other:?}"),
    }
}

// ----------------------------------------------------------------------
// Sub-step 7g part B — pattern coverage, external wrapper, bootstrap,
// visibility resolution
// ----------------------------------------------------------------------

fn pat_var(name: &str) -> Pat {
    Pat::Var {
        id: dummy_node(),
        name: name.to_string(),
        span: span(),
    }
}

fn pat_wild() -> Pat {
    Pat::Wildcard {
        id: dummy_node(),
        span: span(),
    }
}

/// Lower a case-scrutinee with a single arm carrying `pat` as its pattern;
/// return the lowered CPat. Lets pattern tests focus on the CPat shape
/// without re-asserting the surrounding Case wrap.
fn lower_pat_in_case(pat: Pat, lowerer_setup: impl FnOnce(&mut Lowerer<'_>)) -> CPat {
    let resolution = ResolutionMap::new();
    let ctors = ConstructorAtoms::new();
    let ctx = CodegenContext::default();
    let handler_info = HandlerAnalysis::default();
    let storage = EffectInfoStorage::empty();
    let effect_info = storage.view();
    let hvm = crate::codegen::monadic::ir::HandlerValueMap::new();
    let mut lowerer = Lowerer::new(&resolution, &ctors, &ctx, &handler_info, &effect_info, &hvm);
    lowerer_setup(&mut lowerer);
    let expr = MExpr::Case {
        scrutinee: atom_var("x"),
        arms: vec![MArm {
            pattern: pat,
            guard: None,
            body: MExpr::Pure(atom_lit(Lit::Unit)),
            span: span(),
        }],
        source: dummy_node(),
    };
    let ce = lowerer.lower_expr(&expr, &crate::codegen::lower_monadic::LowerCtx::fresh());
    match ce {
        CExpr::Case(_, mut arms) => arms.remove(0).pat,
        other => panic!("expected Case, got {other:?}"),
    }
}

#[test]
fn pat_record_uses_declared_field_order() {
    // record Pt { x, y }; pattern { x = a, y = b } should lower to
    // CPat::Tuple([Atom("Pt"), Var(A), Var(B)]) — declared field order.
    let pat = Pat::Record {
        id: dummy_node(),
        name: "Pt".to_string(),
        fields: vec![
            ("y".to_string(), Some(pat_var("b"))),
            ("x".to_string(), Some(pat_var("a"))),
        ],
        rest: false,
        as_name: None,
        span: span(),
    };
    let cpat = lower_pat_in_case(pat, |l| {
        l.record_fields
            .insert("Pt".to_string(), vec!["x".to_string(), "y".to_string()]);
    });
    let elems = match cpat {
        CPat::Tuple(es) => es,
        other => panic!("expected Tuple, got {other:?}"),
    };
    assert_eq!(elems.len(), 3);
    assert!(matches!(&elems[0], CPat::Lit(CLit::Atom(a)) if a == "Pt"));
    assert!(matches!(&elems[1], CPat::Var(n) if n == "A"));
    assert!(matches!(&elems[2], CPat::Var(n) if n == "B"));
}

#[test]
fn pat_record_with_as_name_aliases_tuple() {
    let pat = Pat::Record {
        id: dummy_node(),
        name: "Pt".to_string(),
        fields: vec![("x".to_string(), None), ("y".to_string(), None)],
        rest: false,
        as_name: Some("whole".to_string()),
        span: span(),
    };
    let cpat = lower_pat_in_case(pat, |l| {
        l.record_fields
            .insert("Pt".to_string(), vec!["x".to_string(), "y".to_string()]);
    });
    match cpat {
        CPat::Alias(var, inner) => {
            assert_eq!(var, "Whole");
            assert!(matches!(inner.as_ref(), CPat::Tuple(_)));
        }
        other => panic!("expected Alias, got {other:?}"),
    }
}

#[test]
fn pat_anon_record_sorts_fields_alphabetically() {
    // Source-order: y, x. Sorted: x, y. Tag depends on sorted names.
    let pat = Pat::AnonRecord {
        id: dummy_node(),
        fields: vec![
            ("y".to_string(), Some(pat_var("b"))),
            ("x".to_string(), Some(pat_var("a"))),
        ],
        rest: false,
        span: span(),
    };
    let cpat = lower_pat_in_case(pat, |_| {});
    let elems = match cpat {
        CPat::Tuple(es) => es,
        other => panic!("expected Tuple, got {other:?}"),
    };
    assert_eq!(elems.len(), 3);
    // Sorted order x, y → element[1] is A, element[2] is B.
    assert!(matches!(&elems[1], CPat::Var(n) if n == "A"));
    assert!(matches!(&elems[2], CPat::Var(n) if n == "B"));
}

#[test]
fn pat_string_prefix_lowers_to_binary_with_byte_run_and_tail() {
    let pat = Pat::StringPrefix {
        id: dummy_node(),
        prefix: "ok".to_string(),
        rest: Box::new(pat_var("tail")),
        span: span(),
    };
    let cpat = lower_pat_in_case(pat, |_| {});
    match cpat {
        CPat::Binary(segs) => {
            assert_eq!(segs.len(), 3);
            assert!(matches!(segs[0], CBinSeg::Byte(b'o')));
            assert!(matches!(segs[1], CBinSeg::Byte(b'k')));
            match &segs[2] {
                CBinSeg::BinaryAll(p) => {
                    assert!(matches!(p, CPat::Var(n) if n == "Tail"))
                }
                other => panic!("expected BinaryAll tail, got {other:?}"),
            }
        }
        other => panic!("expected Binary, got {other:?}"),
    }
}

#[test]
fn pat_bitstring_with_int_size_emits_sized_segment() {
    use crate::ast::BitSegment;
    let int_size_expr = ast::Expr::synth(
        span(),
        ast::ExprKind::Lit {
            value: Lit::Int("16".to_string(), 16),
        },
    );
    let pat = Pat::BitStringPat {
        id: dummy_node(),
        segments: vec![BitSegment {
            value: pat_var("x"),
            size: Some(Box::new(int_size_expr)),
            specs: vec![],
            span: span(),
        }],
        span: span(),
    };
    let cpat = lower_pat_in_case(pat, |_| {});
    match cpat {
        CPat::Binary(segs) => {
            assert_eq!(segs.len(), 1);
            match &segs[0] {
                CBinSeg::Segment { value, size, .. } => {
                    assert!(matches!(value, CPat::Var(n) if n == "X"));
                    match size {
                        crate::codegen::cerl::BinSegSize::Expr(CExpr::Lit(CLit::Int(16))) => {}
                        other => panic!("expected size 16, got {other:?}"),
                    }
                }
                other => panic!("expected Segment, got {other:?}"),
            }
        }
        other => panic!("expected Binary, got {other:?}"),
    }
}

#[test]
fn pat_bitstring_binary_no_size_emits_binary_all() {
    use crate::ast::{BitSegSpec, BitSegment};
    let pat = Pat::BitStringPat {
        id: dummy_node(),
        segments: vec![BitSegment {
            value: pat_var("rest"),
            size: None,
            specs: vec![BitSegSpec::Binary],
            span: span(),
        }],
        span: span(),
    };
    let cpat = lower_pat_in_case(pat, |_| {});
    match cpat {
        CPat::Binary(segs) => match &segs[0] {
            CBinSeg::BinaryAll(p) => {
                assert!(matches!(p, CPat::Var(n) if n == "Rest"))
            }
            other => panic!("expected BinaryAll, got {other:?}"),
        },
        other => panic!("expected Binary, got {other:?}"),
    }
}

#[test]
#[should_panic(expected = "desugared")]
fn pat_or_is_unreachable_post_desugar() {
    let pat = Pat::Or {
        id: dummy_node(),
        patterns: vec![pat_var("a"), pat_var("b")],
        span: span(),
    };
    let _ = lower_pat_in_case(pat, |_| {});
}

#[test]
#[should_panic(expected = "desugared")]
fn pat_list_is_unreachable_post_desugar() {
    let pat = Pat::ListPat {
        id: dummy_node(),
        elements: vec![pat_var("a")],
        span: span(),
    };
    let _ = lower_pat_in_case(pat, |_| {});
}

// --- @external wrapper -------------------------------------------------

fn type_named(name: &str) -> ast::TypeExpr {
    ast::TypeExpr::Named {
        id: dummy_node(),
        name: name.to_string(),
        span: span(),
    }
}

fn type_arrow(from: ast::TypeExpr, to: ast::TypeExpr) -> ast::TypeExpr {
    ast::TypeExpr::Arrow {
        id: dummy_node(),
        from: Box::new(from),
        to: Box::new(to),
        effects: vec![],
        effect_row_var: None,
        span: span(),
    }
}

fn external_annotation(module: &str, function: &str) -> ast::Annotation {
    ast::Annotation {
        name: "external".to_string(),
        name_span: span(),
        args: vec![
            Lit::String("runtime".to_string(), crate::token::StringKind::Normal),
            Lit::String(module.to_string(), crate::token::StringKind::Normal),
            Lit::String(function.to_string(), crate::token::StringKind::Normal),
        ],
        span: span(),
    }
}

#[test]
fn external_fun_signature_emits_uniform_wrapper() {
    let decl = ast::Decl::FunSignature {
        id: dummy_node(),
        doc: vec![],
        public: true,
        name: "reverse".to_string(),
        name_span: span(),
        params: vec![("xs".to_string(), type_named("List"))],
        return_type: type_named("List"),
        effects: vec![],
        effect_row_var: None,
        where_clause: vec![],
        annotations: vec![external_annotation("lists", "reverse")],
        span: span(),
    };
    let program = vec![MDecl::Passthrough(decl)];
    let cmod = lower(&program, "m");
    assert_eq!(cmod.funs.len(), 1);
    let f = &cmod.funs[0];
    assert_eq!(f.name, "reverse");
    // 1 user param + _Evidence + _ReturnK = 3
    assert_eq!(f.arity, 3);
    // public → exported.
    assert_eq!(cmod.exports, vec![("reverse".to_string(), 3)]);
    let (params, body) = match &f.body {
        CExpr::Fun(p, b) => (p.clone(), b.as_ref()),
        other => panic!("expected Fun, got {other:?}"),
    };
    assert_eq!(params, vec!["_Ext0", "_Evidence", "_ReturnK"]);
    // body: apply _ReturnK(call 'lists':'reverse'(_Ext0))
    let arg = match body {
        CExpr::Apply(c, args) => {
            assert!(matches!(c.as_ref(), CExpr::Var(n) if n == "_ReturnK"));
            &args[0]
        }
        other => panic!("expected Apply, got {other:?}"),
    };
    match arg {
        CExpr::Call(m, f, call_args) => {
            assert_eq!(m, "lists");
            assert_eq!(f, "reverse");
            assert_eq!(call_args.len(), 1);
            assert!(matches!(&call_args[0], CExpr::Var(n) if n == "_Ext0"));
        }
        other => panic!("expected Call inside Apply, got {other:?}"),
    }
}

#[test]
fn external_wrapper_filters_unit_params_from_call() {
    // fun foo : Unit -> Int; @external("runtime", "m", "f")
    // Wrapper arity is still 3 (unit param + Evidence + ReturnK),
    // but the call site to 'm':'f' takes 0 args.
    let decl = ast::Decl::FunSignature {
        id: dummy_node(),
        doc: vec![],
        public: true,
        name: "foo".to_string(),
        name_span: span(),
        params: vec![("u".to_string(), type_named("Unit"))],
        return_type: type_named("Int"),
        effects: vec![],
        effect_row_var: None,
        where_clause: vec![],
        annotations: vec![external_annotation("m", "f")],
        span: span(),
    };
    let cmod = lower(&vec![MDecl::Passthrough(decl)], "m");
    let f = &cmod.funs[0];
    assert_eq!(f.arity, 3);
    let body = match &f.body {
        CExpr::Fun(_, b) => b.as_ref(),
        _ => unreachable!(),
    };
    let call = match body {
        CExpr::Apply(_, args) => &args[0],
        _ => unreachable!(),
    };
    match call {
        CExpr::Call(_, _, ca) => assert!(
            ca.is_empty(),
            "Unit param must be filtered from BIF call args"
        ),
        other => panic!("expected Call, got {other:?}"),
    }
}

#[test]
fn external_wrapper_adapts_function_typed_params() {
    let decl = ast::Decl::FunSignature {
        id: dummy_node(),
        doc: vec![],
        public: true,
        name: "map_ext".to_string(),
        name_span: span(),
        params: vec![
            (
                "f".to_string(),
                type_arrow(type_named("Int"), type_named("Int")),
            ),
            ("xs".to_string(), type_named("List")),
        ],
        return_type: type_named("List"),
        effects: vec![],
        effect_row_var: None,
        where_clause: vec![],
        annotations: vec![external_annotation("lists", "map")],
        span: span(),
    };
    let cmod = lower(&vec![MDecl::Passthrough(decl)], "m");
    let f = &cmod.funs[0];
    let body = match &f.body {
        CExpr::Fun(_, b) => b.as_ref(),
        _ => unreachable!(),
    };
    let CExpr::Let(adapter_name, adapter, body) = body else {
        panic!("expected adapter let, got {body:?}");
    };
    assert_eq!(adapter_name, "_Adapter0");
    let CExpr::Fun(cb_params, _) = adapter.as_ref() else {
        panic!("expected adapter fun, got {adapter:?}");
    };
    assert_eq!(cb_params, &vec!["_CbArg0".to_string()]);
    let call = match body.as_ref() {
        CExpr::Apply(_, args) => &args[0],
        other => panic!("expected return-k apply, got {other:?}"),
    };
    match call {
        CExpr::Call(module, function, args) => {
            assert_eq!(module, "lists");
            assert_eq!(function, "map");
            assert!(matches!(&args[0], CExpr::Var(name) if name == "_Adapter0"));
            assert!(matches!(&args[1], CExpr::Var(name) if name == "_Ext1"));
        }
        other => panic!("expected native call, got {other:?}"),
    }
}

#[test]
fn external_wrapper_not_emitted_for_non_external_signature() {
    let decl = ast::Decl::FunSignature {
        id: dummy_node(),
        doc: vec![],
        public: true,
        name: "no_ext".to_string(),
        name_span: span(),
        params: vec![],
        return_type: type_named("Int"),
        effects: vec![],
        effect_row_var: None,
        where_clause: vec![],
        annotations: vec![],
        span: span(),
    };
    let cmod = lower(&vec![MDecl::Passthrough(decl)], "m");
    assert!(cmod.funs.is_empty());
    assert!(cmod.exports.is_empty());
}

#[test]
fn private_external_signature_not_exported() {
    let decl = ast::Decl::FunSignature {
        id: dummy_node(),
        doc: vec![],
        public: false,
        name: "priv".to_string(),
        name_span: span(),
        params: vec![],
        return_type: type_named("Int"),
        effects: vec![],
        effect_row_var: None,
        where_clause: vec![],
        annotations: vec![external_annotation("m", "f")],
        span: span(),
    };
    let cmod = lower(&vec![MDecl::Passthrough(decl)], "m");
    assert_eq!(cmod.funs.len(), 1, "private external still emits fundef");
    assert!(cmod.exports.is_empty(), "but is not exported");
}

// --- Bootstrap ---------------------------------------------------------

#[test]
fn bootstrap_emits_initial_evidence_fn_when_enabled() {
    let resolution = ResolutionMap::new();
    let ctors = ConstructorAtoms::new();
    let ctx = CodegenContext::default();
    let handler_info = HandlerAnalysis::default();
    let storage = EffectInfoStorage::empty();
    let effect_info = storage.view();
    let hvm = crate::codegen::monadic::ir::HandlerValueMap::new();
    let mut lowerer = Lowerer::new(&resolution, &ctors, &ctx, &handler_info, &effect_info, &hvm)
        .with_bootstrap_emission(true);
    let cmod = lowerer.lower_module("entry", &vec![]);
    let names: Vec<&str> = cmod.funs.iter().map(|f| f.name.as_str()).collect();
    assert!(
        names.contains(&"__saga_initial_evidence"),
        "expected bootstrap fn in emitted funs, got {names:?}"
    );
    let f = cmod
        .funs
        .iter()
        .find(|f| f.name == "__saga_initial_evidence")
        .unwrap();
    assert_eq!(f.arity, 0);
}

#[test]
fn bootstrap_not_emitted_when_disabled() {
    let cmod = lower(&vec![], "m");
    assert!(
        cmod.funs.is_empty(),
        "no bootstrap when emit_bootstrap is off"
    );
}

#[test]
fn bootstrap_evidence_vector_has_canonical_effect_entries() {
    let resolution = ResolutionMap::new();
    let ctors = ConstructorAtoms::new();
    let ctx = CodegenContext::default();
    let handler_info = HandlerAnalysis::default();
    let storage = EffectInfoStorage::empty();
    let effect_info = storage.view();
    let hvm = crate::codegen::monadic::ir::HandlerValueMap::new();
    let mut lowerer = Lowerer::new(&resolution, &ctors, &ctx, &handler_info, &effect_info, &hvm)
        .with_bootstrap_emission(true);
    let cmod = lowerer.lower_module("entry", &vec![]);
    let f = cmod
        .funs
        .iter()
        .find(|f| f.name == "__saga_initial_evidence")
        .unwrap();
    let body = match &f.body {
        CExpr::Fun(_, b) => b.as_ref(),
        _ => panic!("expected Fun"),
    };
    // Body is a tuple of {EffectAtom, OpTuple} pairs.
    let entries = match body {
        CExpr::Tuple(es) => es,
        other => panic!("expected Tuple body, got {other:?}"),
    };
    assert_eq!(entries.len(), super::bootstrap::native_effect_count());
    // Each entry: {EffectAtom, OpTuple}
    for (entry, &expected_tag) in entries
        .iter()
        .zip(super::bootstrap::native_effect_tags().iter())
    {
        match entry {
            CExpr::Tuple(pair) => {
                assert_eq!(pair.len(), 2);
                match &pair[0] {
                    CExpr::Lit(CLit::Atom(a)) => assert_eq!(a, expected_tag),
                    other => panic!("expected EffectAtom tag, got {other:?}"),
                }
                let op_count = super::bootstrap::ops_for_effect(expected_tag)
                    .unwrap()
                    .len();
                match &pair[1] {
                    CExpr::Tuple(ops) => assert_eq!(ops.len(), op_count),
                    other => panic!("expected OpTuple, got {other:?}"),
                }
            }
            other => panic!("expected entry tuple, got {other:?}"),
        }
    }
}

#[test]
fn bootstrap_native_op_order_is_alphabetical() {
    // The perform site indexes an op tuple by `EffectOpRef.op_index`, which is
    // the op's position in `build_effect_ops_table` — and that table always
    // sorts ops alphabetically. The hand-maintained `NATIVE_EFFECTS` table must
    // match that order or native ops dispatch to the wrong BIF at runtime with
    // no error. Guard the hand-maintained order here so a mis-ordered table
    // fails at test time instead of as a silent wrong-dispatch.
    for tag in super::bootstrap::native_effect_tags() {
        let ops = super::bootstrap::ops_for_effect(tag).unwrap();
        let mut sorted = ops.clone();
        sorted.sort();
        assert_eq!(
            ops, sorted,
            "NATIVE_EFFECTS ops for '{tag}' must be alphabetical to match op_index; got {ops:?}"
        );
    }
}

#[test]
fn bootstrap_identity_op_closure_calls_bif_and_applies_k() {
    // Actor.self has NoArgs shape: fun(Unit, EvidenceAtPerform, K) -> apply K(erlang:self())
    let resolution = ResolutionMap::new();
    let ctors = ConstructorAtoms::new();
    let ctx = CodegenContext::default();
    let handler_info = HandlerAnalysis::default();
    let storage = EffectInfoStorage::empty();
    let effect_info = storage.view();
    let hvm = crate::codegen::monadic::ir::HandlerValueMap::new();
    let mut lowerer = Lowerer::new(&resolution, &ctors, &ctx, &handler_info, &effect_info, &hvm)
        .with_bootstrap_emission(true);
    let cmod = lowerer.lower_module("entry", &vec![]);
    let f = cmod
        .funs
        .iter()
        .find(|f| f.name == "__saga_initial_evidence")
        .unwrap();
    let body = match &f.body {
        CExpr::Fun(_, b) => b.as_ref(),
        _ => unreachable!(),
    };
    // Walk to Actor entry → OpTuple
    let entries = match body {
        CExpr::Tuple(es) => es,
        _ => unreachable!(),
    };
    let actor_entry = entries
        .iter()
        .find(|e| match e {
            CExpr::Tuple(p) => {
                matches!(&p[0], CExpr::Lit(CLit::Atom(a)) if a == "Std.Actor.Actor")
            }
            _ => false,
        })
        .expect("Actor entry");
    let op_tuple = match actor_entry {
        CExpr::Tuple(p) => &p[1],
        _ => unreachable!(),
    };
    let ops = match op_tuple {
        CExpr::Tuple(o) => o,
        _ => unreachable!(),
    };
    let self_closure = &ops[0];
    let (params, closure_body) = match self_closure {
        CExpr::Fun(p, b) => (p.clone(), b.as_ref()),
        other => panic!("expected Fun, got {other:?}"),
    };
    assert_eq!(params, vec!["_Arg0", "_EvidenceAtPerform", "_K"]);
    match closure_body {
        CExpr::Apply(c, args) => {
            assert!(matches!(c.as_ref(), CExpr::Var(n) if n == "_K"));
            match &args[0] {
                CExpr::Call(m, fname, ca) => {
                    assert_eq!(m, "erlang");
                    assert_eq!(fname, "self");
                    assert!(ca.is_empty());
                }
                other => panic!("expected erlang:self call, got {other:?}"),
            }
        }
        other => panic!("expected Apply body, got {other:?}"),
    }
}

#[test]
fn bootstrap_spawn_thunk_uses_perform_site_evidence() {
    let resolution = ResolutionMap::new();
    let ctors = ConstructorAtoms::new();
    let ctx = CodegenContext::default();
    let handler_info = HandlerAnalysis::default();
    let storage = EffectInfoStorage::empty();
    let effect_info = storage.view();
    let hvm = crate::codegen::monadic::ir::HandlerValueMap::new();
    let mut lowerer = Lowerer::new(&resolution, &ctors, &ctx, &handler_info, &effect_info, &hvm)
        .with_bootstrap_emission(true);
    let cmod = lowerer.lower_module("entry", &vec![]);
    let f = cmod
        .funs
        .iter()
        .find(|f| f.name == "__saga_initial_evidence")
        .unwrap();
    let body = match &f.body {
        CExpr::Fun(_, b) => b.as_ref(),
        _ => unreachable!(),
    };
    let entries = match body {
        CExpr::Tuple(es) => es,
        _ => unreachable!(),
    };
    let process_entry = entries
        .iter()
        .find(|e| match e {
            CExpr::Tuple(p) => {
                matches!(&p[0], CExpr::Lit(CLit::Atom(a)) if a == "Std.Actor.Process")
            }
            _ => false,
        })
        .expect("Process entry");
    let ops = match process_entry {
        CExpr::Tuple(p) => match &p[1] {
            CExpr::Tuple(o) => o,
            _ => unreachable!(),
        },
        _ => unreachable!(),
    };
    let spawn_closure = &ops[2];
    let (params, body) = match spawn_closure {
        CExpr::Fun(p, b) => (p, b.as_ref()),
        other => panic!("expected spawn Fun, got {other:?}"),
    };
    assert_eq!(params, &vec!["_Arg0", "_EvidenceAtPerform", "_K"]);

    let thunk = match body {
        CExpr::Apply(c, args) => {
            assert!(matches!(c.as_ref(), CExpr::Var(n) if n == "_K"));
            match &args[0] {
                CExpr::Call(m, f, call_args) => {
                    assert_eq!(m, "erlang");
                    assert_eq!(f, "spawn");
                    assert_eq!(call_args.len(), 1);
                    &call_args[0]
                }
                other => panic!("expected erlang:spawn call, got {other:?}"),
            }
        }
        other => panic!("expected Apply body, got {other:?}"),
    };

    match thunk {
        CExpr::Fun(params, body) => {
            assert!(params.is_empty());
            match body.as_ref() {
                CExpr::Let(k_name, _, apply) => {
                    assert_eq!(k_name, "_SpawnK");
                    match apply.as_ref() {
                        CExpr::Apply(callback, args) => {
                            assert!(matches!(callback.as_ref(), CExpr::Var(n) if n == "_Arg0"));
                            assert!(matches!(&args[0], CExpr::Lit(CLit::Atom(a)) if a == "unit"));
                            assert!(
                                matches!(&args[1], CExpr::Var(n) if n == "_EvidenceAtPerform"),
                                "spawn callback must receive perform-site evidence"
                            );
                            assert!(matches!(&args[2], CExpr::Var(n) if n == "_SpawnK"));
                        }
                        other => panic!("expected callback apply, got {other:?}"),
                    }
                }
                other => panic!("expected _SpawnK let, got {other:?}"),
            }
        }
        other => panic!("expected spawn thunk Fun, got {other:?}"),
    }
}

#[test]
fn bootstrap_process_exit_calls_erlang_exit() {
    let resolution = ResolutionMap::new();
    let ctors = ConstructorAtoms::new();
    let ctx = CodegenContext::default();
    let handler_info = HandlerAnalysis::default();
    let storage = EffectInfoStorage::empty();
    let effect_info = storage.view();
    let hvm = crate::codegen::monadic::ir::HandlerValueMap::new();
    let mut lowerer = Lowerer::new(&resolution, &ctors, &ctx, &handler_info, &effect_info, &hvm)
        .with_bootstrap_emission(true);
    let cmod = lowerer.lower_module("entry", &vec![]);
    let f = cmod
        .funs
        .iter()
        .find(|f| f.name == "__saga_initial_evidence")
        .unwrap();
    let body = match &f.body {
        CExpr::Fun(_, b) => b.as_ref(),
        _ => unreachable!(),
    };
    let entries = match body {
        CExpr::Tuple(es) => es,
        _ => unreachable!(),
    };
    let process_entry = entries
        .iter()
        .find(|e| match e {
            CExpr::Tuple(p) => {
                matches!(&p[0], CExpr::Lit(CLit::Atom(a)) if a == "Std.Actor.Process")
            }
            _ => false,
        })
        .unwrap();
    let ops = match process_entry {
        CExpr::Tuple(p) => match &p[1] {
            CExpr::Tuple(o) => o,
            _ => unreachable!(),
        },
        _ => unreachable!(),
    };
    let exit_closure = &ops[0];
    let closure_body = match exit_closure {
        CExpr::Fun(_, b) => b.as_ref(),
        _ => unreachable!(),
    };
    // apply _K(erlang:exit(_Arg0, _Arg1))
    match closure_body {
        CExpr::Apply(_, args) => match &args[0] {
            CExpr::Call(m, f, ca) => {
                assert_eq!(m, "erlang");
                assert_eq!(f, "exit");
                assert_eq!(ca.len(), 2);
                assert!(matches!(&ca[0], CExpr::Var(n) if n == "_Arg0"));
                assert!(matches!(&ca[1], CExpr::Var(n) if n == "_Arg1"));
            }
            other => panic!("expected exit call, got {other:?}"),
        },
        other => panic!("expected Apply, got {other:?}"),
    }
}

// --- public flag resolution -------------------------------------------

#[test]
fn fun_binding_not_in_exports_is_not_exported() {
    // When the lowerer is given a ModuleCodegenInfo whose exports list
    // does not contain the FunBinding name, the binding stays unexported.
    use crate::codegen::CompiledModule;
    use crate::typechecker::Scheme;

    let mut compiled = CompiledModule::default();
    // Mark "pubfn" public, leave "privfn" out.
    compiled.codegen_info.exports.push((
        "pubfn".to_string(),
        Scheme {
            forall: vec![],
            constraints: vec![],
            ty: crate::typechecker::Type::int(),
        },
    ));
    let mod_name = "vis_test".to_string();
    let mut ctx = CodegenContext::default();
    ctx.modules.insert(mod_name.clone(), compiled);

    let resolution = ResolutionMap::new();
    let ctors = ConstructorAtoms::new();
    let handler_info = HandlerAnalysis::default();
    let storage = EffectInfoStorage::empty();
    let effect_info = storage.view();
    let hvm = crate::codegen::monadic::ir::HandlerValueMap::new();
    let mut lowerer = Lowerer::new(&resolution, &ctors, &ctx, &handler_info, &effect_info, &hvm);

    let mk_fb = |name: &str| {
        MDecl::FunBinding(MFunBinding {
            id: dummy_node(),
            name: name.to_string(),
            name_span: span(),
            params: vec![pat_var("x")],
            guard: None,
            body: pure_unit(),
            span: span(),
        })
    };
    let program = vec![mk_fb("pubfn"), mk_fb("privfn")];
    let cmod = lowerer.lower_module(&mod_name, &program);
    let exported: Vec<&str> = cmod.exports.iter().map(|(n, _)| n.as_str()).collect();
    assert!(exported.contains(&"pubfn"), "pubfn must be exported");
    assert!(!exported.contains(&"privfn"), "privfn must NOT be exported");
    // both fundefs still emitted
    assert_eq!(cmod.funs.len(), 2);
}

#[test]
fn binop_under_bind_threads_inner_k() {
    // Bind { x = BinOp(+, 1, 2), body = Pure(Var x) }
    // expected: let _K0 = fun(X) -> apply _ReturnK(X) in apply _K0(erlang:'+'(1, 2))
    let expr = MExpr::Bind {
        var: mvar("x"),
        value: Box::new(MExpr::BinOp {
            op: ast::BinOp::Add,
            left: atom_int(1),
            right: atom_int(2),
            source: dummy_node(),
        }),
        body: Box::new(MExpr::Pure(atom_var("x"))),
        mode: BindMode::Sequence,
    };
    let ce = lower_expr_default(&expr);
    let ce = skip_control_result_bubble(&ce);
    let body = match ce {
        CExpr::Let(name, _, b) => {
            assert_eq!(name, "_K0");
            b
        }
        other => panic!("expected Let, got {other:?}"),
    };
    match body.as_ref() {
        CExpr::Apply(callee, args) => {
            assert!(matches!(callee.as_ref(), CExpr::Var(n) if n == "_K0"));
            assert_eq!(args.len(), 1);
            match &args[0] {
                CExpr::Call(m, f, _) => {
                    assert_eq!(m, "erlang");
                    assert_eq!(f, "+");
                }
                other => panic!("expected erlang:'+' call, got {other:?}"),
            }
        }
        other => panic!("expected Apply, got {other:?}"),
    }
}
