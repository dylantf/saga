//! New lowerer (uniform-effect-translation, stage 12).
//!
//! Consumes `MProgram` (post-ANF, monadic-translated, optionally-optimized)
//! and produces a Core Erlang `CModule`. Designed to be invoked alongside the
//! old lowerer via the toggle in `src/codegen/mod.rs` (wired in step 8, not
//! this sub-step).
//!
//! ## Sub-step 7a scope
//!
//! Function/decl scaffolding only. The MExpr body lowering is **stubbed**
//! (see [`exprs::lower_body_stub`]) — every emitted CFunDef body is
//! `apply _ReturnK('unit')`. Sub-steps 7b–7g fill in the real translation
//! incrementally.
//!
//! ## Calling convention (uniform)
//!
//! Every emitted CFunDef takes `(user_args..., _Evidence, _ReturnK)` —
//! evidence vector and return continuation are appended even when the source
//! function performs no effects. The slow uniform shape is the load-bearing
//! invariant; selective omission belongs to the optimization stage.
//!
//! ## Module layout
//!
//! - `mod.rs`   — `Lowerer` struct + `lower_module` entry + decl dispatch
//! - `decls.rs` — per-`MDecl` CFunDef construction
//! - `exprs.rs` — MExpr → CExpr (STUB in 7a)
//! - `pats.rs`  — pattern lowering (param-only in 7a; full in 7g)
//! - `util.rs`  — local helpers copied from old lowerer (no imports per
//!   agent-guide allowlist)

#![allow(dead_code)] // 7a scaffolding; consumers land in 7b–7g.

mod decls;
mod exprs;
mod pats;
mod util;

use crate::codegen::CodegenContext;
use crate::codegen::cerl::CModule;
use crate::codegen::handler_analysis::HandlerAnalysis;
use crate::codegen::monadic::ir::{EffectInfo, MDecl, MProgram};
use crate::codegen::resolve::{ConstructorAtoms, ResolutionMap};

use decls::{dict_constructor_arity, fun_binding_arity, val_arity};

/// New-path lowerer.
///
/// Holds read-only borrows of every input the lowering needs: the source-
/// `NodeId`-keyed resolution map, the constructor → atom table, the cross-
/// module codegen context, the handler-arm classification, and the narrowed
/// effect-info view. None of these are mutated; ownership stays with the
/// caller for the duration of `lower_module`.
///
/// **Type note (open):** the planning spec names this field's type
/// `ModuleCodegenContext`. No such type exists in the codebase today; the
/// existing `CodegenContext` (in `src/codegen/mod.rs`) is the only candidate
/// that fits the role. We use that here and flag the divergence — a follow-up
/// rename to `ModuleCodegenContext` is straightforward if the spec is the
/// canonical name.
pub struct Lowerer<'ctx> {
    resolution: &'ctx ResolutionMap,
    ctors: &'ctx ConstructorAtoms,
    module_ctx: &'ctx CodegenContext,
    handler_info: &'ctx HandlerAnalysis,
    effect_info: &'ctx EffectInfo<'ctx>,
}

impl<'ctx> Lowerer<'ctx> {
    pub fn new(
        resolution: &'ctx ResolutionMap,
        ctors: &'ctx ConstructorAtoms,
        module_ctx: &'ctx CodegenContext,
        handler_info: &'ctx HandlerAnalysis,
        effect_info: &'ctx EffectInfo<'ctx>,
    ) -> Self {
        Self {
            resolution,
            ctors,
            module_ctx,
            handler_info,
            effect_info,
        }
    }

    /// Lower an entire `MProgram` to a Core Erlang `CModule`.
    ///
    /// Iterates declarations in source order:
    ///   - `MFunBinding`, `MVal`, `MDictConstructor` → one `CFunDef` each
    ///   - `Passthrough(ast::Decl)` — most decl kinds emit no runtime code
    ///     (type/effect/trait/import/module headers). The few exceptions
    ///     (`@external` wrappers on `FunSignature`, etc.) are handled by a
    ///     later sub-step; in 7a they're silently skipped, which keeps the
    ///     scaffolding honest about what's stubbed.
    ///
    /// Export list:
    ///   - `MVal` carries its own `public` flag → exported when true.
    ///   - `MFunBinding` and `MDictConstructor` have no pub field on the IR.
    ///     For 7a, both are exported unconditionally so the emitted module
    ///     compiles standalone. Sub-step 7g (or earlier, if a real test
    ///     exposes the gap) wires this back to the source-decl visibility.
    pub fn lower_module(&mut self, module_name: &str, program: &MProgram) -> CModule {
        let mut exports = Vec::new();
        let mut funs = Vec::new();

        for decl in program {
            match decl {
                MDecl::FunBinding(fb) => {
                    exports.push((fb.name.clone(), fun_binding_arity(&fb.params)));
                    funs.push(self.lower_fun_binding(fb));
                }
                MDecl::Val(v) => {
                    if v.public {
                        exports.push((v.name.clone(), val_arity()));
                    }
                    funs.push(self.lower_val(v));
                }
                MDecl::DictConstructor(dc) => {
                    exports.push((dc.name.clone(), dict_constructor_arity(dc)));
                    funs.push(self.lower_dict_constructor(dc));
                }
                MDecl::Passthrough(_) => {
                    // No runtime emission for type/effect/trait/import/module
                    // headers. `@external` wrappers and other code-emitting
                    // passthroughs are deferred to a later sub-step.
                }
            }
        }

        CModule {
            name: module_name.to_string(),
            exports,
            funs,
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
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
    fn dict_constructor_emits_uniform_signature_and_stub() {
        let dc = MDictConstructor {
            id: dummy_node(),
            name: "__dict_Show_Int".to_string(),
            dict_params: vec!["sub_a".to_string()],
            methods: vec![pure_unit()],
            method_effects: vec![vec![]],
            method_open_rows: vec![false],
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
        let params = match &f.body {
            CExpr::Fun(p, _) => p.clone(),
            other => panic!("expected CExpr::Fun, got {other:?}"),
        };
        assert_eq!(params, vec!["Sub_a", "_Evidence", "_ReturnK"]);
        assert_stub_body(extract_stub_body(&f.body));
        assert_eq!(cmod.exports, vec![("__dict_Show_Int".to_string(), 3)]);
    }

    #[test]
    fn module_shell_name_matches_input() {
        let cmod = lower(&vec![], "my_app_server");
        assert_eq!(cmod.name, "my_app_server");
        assert!(cmod.exports.is_empty());
        assert!(cmod.funs.is_empty());
    }
}
