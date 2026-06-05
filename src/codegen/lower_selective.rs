//! Experimental direct-first lowerer for the selective-uniform spike.
//!
//! This module is intentionally incomplete, but no longer toy-sized. It keeps
//! pure/direct code in ordinary BEAM shape and lowers effectful regions through
//! explicit CPS islands when the selective planner can prove the shape.
//!
//! The submodules split the moving parts:
//! - `planning`: selective plan discovery and HOF specialization
//! - `functions`: top-level function/module entry emission
//! - `direct*`: direct Core Erlang lowering, direct calls, atoms, and patterns
//! - `cps*`: CPS island lowering, handler lowering, and runtime CPS values
//! - `known_*`, `runtime_values`, `type_queries`: scoped compile-time facts
//! - `support`: small shared shape/data helpers

use std::collections::{BTreeMap, HashMap, HashSet};

mod calls;
mod cps;
mod cps_bind;
mod cps_calls;
mod cps_cases;
mod cps_delimiters;
mod cps_finally;
mod cps_handler_arms;
mod cps_handler_values;
mod cps_hof;
mod cps_static_calls;
mod cps_static_yield;
mod cps_subset;
mod cps_values;
mod cps_with;
mod cps_yield;
mod direct;
mod direct_app;
mod direct_atoms;
mod direct_core_refs;
mod direct_expr;
mod direct_pats;
mod direct_subset;
mod functions;
mod imported_facts;
mod known_facts;
mod known_values;
mod occurs;
mod planning;
mod runtime_values;
mod scopes;
mod support;
mod syntax_queries;
mod type_queries;

pub use imported_facts::{
    collect_imported_dict_constructors, collect_imported_private_helper_candidates,
};

use crate::ast::{Lit, NodeId, Pat};
use crate::codegen::CodegenContext;
use crate::codegen::cerl::{BinSegSize, CArm, CBinSeg, CExpr, CFunDef, CLit, CModule, CPat};
use crate::codegen::handler_analysis::{HandlerAnalysis, ResumptionKind};
use crate::codegen::lower::util::{core_var, lower_lit_atom, mangle_ctor_atom};
use crate::codegen::monadic::ir::{
    Atom, EffectInfo, EffectOpRef, HandlerValueInfo, HandlerValueMap, MArm, MDecl,
    MDictConstructor, MExpr, MFunBinding, MHandler, MHandlerArm, MProgram, MVar,
};
use crate::codegen::native_effects::{NativeArgTransform, native_op};
use crate::codegen::resolve::{
    ConstructorAtoms, ResolutionMap, ResolvedCodegenKind, ResolvedSymbol,
};
use crate::codegen::runtime_shape::RuntimeFunctionShape;
use crate::intrinsics::IntrinsicId;
use crate::typechecker::Type;

use support::*;

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct LoweringOptions {
    pub require_all_functions: bool,
}

pub fn lower_module(
    module_name: &str,
    program: &MProgram,
    resolution: &ResolutionMap,
    ctors: &ConstructorAtoms,
    module_ctx: &CodegenContext,
    effect_info: &EffectInfo<'_>,
) -> CModule {
    let handler_info = HandlerAnalysis::default();
    let handler_value_map = HandlerValueMap::new();
    lower_module_with_entry_export_options(
        module_name,
        program,
        resolution,
        ctors,
        module_ctx,
        &handler_info,
        effect_info,
        None,
        &handler_value_map,
        LoweringOptions::default(),
    )
}

#[allow(clippy::too_many_arguments)]
pub fn lower_module_with_options(
    module_name: &str,
    program: &MProgram,
    resolution: &ResolutionMap,
    ctors: &ConstructorAtoms,
    module_ctx: &CodegenContext,
    handler_info: &HandlerAnalysis,
    effect_info: &EffectInfo<'_>,
    options: LoweringOptions,
) -> CModule {
    lower_module_with_entry_export_options(
        module_name,
        program,
        resolution,
        ctors,
        module_ctx,
        handler_info,
        effect_info,
        None,
        &HandlerValueMap::new(),
        options,
    )
}

#[allow(clippy::too_many_arguments)]
pub fn lower_module_with_entry_export(
    module_name: &str,
    program: &MProgram,
    resolution: &ResolutionMap,
    ctors: &ConstructorAtoms,
    module_ctx: &CodegenContext,
    handler_info: &HandlerAnalysis,
    effect_info: &EffectInfo<'_>,
    entry_export: Option<&str>,
) -> CModule {
    lower_module_with_entry_export_options(
        module_name,
        program,
        resolution,
        ctors,
        module_ctx,
        handler_info,
        effect_info,
        entry_export,
        &HandlerValueMap::new(),
        LoweringOptions::default(),
    )
}

#[allow(clippy::too_many_arguments)]
pub fn lower_module_with_entry_export_options(
    module_name: &str,
    program: &MProgram,
    resolution: &ResolutionMap,
    ctors: &ConstructorAtoms,
    module_ctx: &CodegenContext,
    handler_info: &HandlerAnalysis,
    effect_info: &EffectInfo<'_>,
    entry_export: Option<&str>,
    handler_value_map: &HandlerValueMap,
    options: LoweringOptions,
) -> CModule {
    lower_module_with_entry_export_and_imported_dicts(
        module_name,
        program,
        resolution,
        ctors,
        module_ctx,
        handler_info,
        effect_info,
        entry_export,
        handler_value_map,
        HashMap::new(),
        options,
    )
}

#[allow(clippy::too_many_arguments)]
pub fn lower_module_with_entry_export_and_imported_dicts(
    module_name: &str,
    program: &MProgram,
    resolution: &ResolutionMap,
    ctors: &ConstructorAtoms,
    module_ctx: &CodegenContext,
    handler_info: &HandlerAnalysis,
    effect_info: &EffectInfo<'_>,
    entry_export: Option<&str>,
    handler_value_map: &HandlerValueMap,
    imported_dict_constructors: HashMap<String, MDictConstructor>,
    options: LoweringOptions,
) -> CModule {
    let mut lowerer = DirectLowerer::new(
        resolution,
        ctors,
        module_ctx,
        handler_info,
        effect_info,
        handler_value_map,
        imported_dict_constructors,
        options,
    );
    lowerer.lower_module(module_name, program, entry_export)
}

struct DirectLowerer<'a, 'info> {
    resolution: &'a ResolutionMap,
    ctors: &'a ConstructorAtoms,
    module_ctx: &'a CodegenContext,
    handler_info: &'a HandlerAnalysis,
    effect_info: &'a EffectInfo<'info>,
    handler_value_map: &'a HandlerValueMap,
    current_module: String,
    /// Declared callable shape from type/effect metadata.
    ///
    /// This can be CPS even when the implementation body is direct-lowerable.
    callable_type_shapes: HashMap<String, RuntimeFunctionShape>,
    callable_callback_param_arities: HashMap<String, Vec<Option<usize>>>,
    local_fun_bindings: HashMap<String, MFunBinding>,
    direct_values: HashSet<String>,
    /// Per-function lowering decision for the implementation body.
    function_plans: HashMap<String, FunctionLoweringPlan>,
    /// Emitted entries for functions in the module currently being lowered.
    local_function_entries: HashMap<String, FunctionEntryInfo>,
    /// Local dictionary constructors that the selective lowerer can emit as
    /// direct tuple-producing functions.
    local_dict_constructor_arities: HashMap<String, usize>,
    /// Private direct specializations of CPS-typed higher-order functions when
    /// selected callback parameters are statically pure at a call site.
    local_hof_direct_specializations: HashMap<String, HofDirectSpecialization>,
    local_dict_constructors: HashMap<String, MDictConstructor>,
    imported_dict_constructors: HashMap<String, MDictConstructor>,
    local_external_functions: HashMap<String, DirectCallable>,
    /// Emitted entries discovered for already-compiled imported user modules.
    imported_function_entries: HashMap<(String, String), FunctionEntryInfo>,
    /// Direct HOF specializations discovered for already-compiled imported
    /// user modules.
    imported_hof_direct_specializations: HashMap<(String, String), HofDirectSpecialization>,
    /// Function currently being tested as a direct-body candidate.
    ///
    /// During fixed-point classification this permits recursive self-calls
    /// before the function has been added to `function_plans`.
    direct_candidate_function: Option<String>,
    /// Functions currently being tested as a mutually-recursive direct-body
    /// candidate set.
    direct_candidate_functions: HashSet<String>,
    static_handler_inline_stack: Vec<String>,
    direct_handler_stack: Vec<DirectHandlerFrame>,
    result_delimiter_stack: Vec<ResultDelimiterFrame>,
    cps_temp_counter: usize,
    locals: Vec<HashSet<String>>,
    local_shapes: Vec<HashMap<String, LocalValueShape>>,
    local_known_direct_lambdas: Vec<HashMap<String, KnownDirectLambda>>,
    local_known_cps_lambdas: Vec<HashMap<String, KnownCpsLambda>>,
    local_known_dict_values: Vec<HashMap<String, KnownDictValue>>,
    local_known_direct_atoms: Vec<HashMap<String, Atom>>,
    local_known_direct_values: Vec<HashMap<String, KnownDirectValue>>,
    active_known_dict_methods: HashSet<KnownDictMethodKey>,
    imported_clone_source_module: Option<String>,
    options: LoweringOptions,
}

impl<'a, 'info> DirectLowerer<'a, 'info> {
    fn wrap_param_match(&self, pats: &[Pat], params: &[String], body: CExpr) -> CExpr {
        if pats.iter().all(|pat| matches!(pat, Pat::Var { .. })) {
            return body;
        }
        let scrutinee = CExpr::Tuple(params.iter().map(|name| CExpr::Var(name.clone())).collect());
        CExpr::Case(
            Box::new(scrutinee),
            vec![CArm {
                pat: CPat::Tuple(pats.iter().map(|pat| self.lower_pat(pat)).collect()),
                guard: None,
                body,
            }],
        )
    }

    fn case_clause_error(&self) -> CExpr {
        CExpr::Call(
            "erlang".to_string(),
            "error".to_string(),
            vec![CExpr::Lit(CLit::Atom("case_clause".to_string()))],
        )
    }

    fn unsupported(&self, what: &str) -> ! {
        panic!(
            "selective-uniform direct lowerer TODO in {}: {what}",
            self.current_module
        )
    }

    fn unsupported_expr(&self, expr: &MExpr) -> ! {
        panic!(
            "selective-uniform direct lowerer TODO in {}: unsupported MExpr {expr:?}",
            self.current_module
        )
    }

    fn unsupported_atom(&self, atom: &Atom) -> ! {
        panic!(
            "selective-uniform direct lowerer TODO in {}: unsupported Atom {:?}",
            self.current_module,
            std::mem::discriminant(atom)
        )
    }
}

#[derive(Clone)]
struct ResultDelimiterFrame {
    effects: Vec<String>,
    abort_marker: String,
}

#[derive(Clone, Debug)]
enum DirectHandlerFrame {
    Static {
        arms: Vec<MHandlerArm>,
    },
    Native {
        effects: Vec<String>,
        kind: DirectHandlerKind,
    },
}

#[derive(Clone, Copy, Debug)]
enum RefDirectBackend {
    ProcessDictionary,
    Ets,
}

struct ImportedStaticHandlerCall {
    source_module_name: String,
    erlang_module: String,
    function_name: String,
    program: MProgram,
}

enum CpsCallDecision {
    HofDirect {
        module: Option<String>,
        specialization: HofDirectSpecialization,
    },
    StaticHandlerLocal {
        function_name: String,
    },
    StaticHandlerImported(ImportedStaticHandlerCall),
    KnownLocalLambda {
        name: String,
    },
    Lambda,
    Normal(CallShape),
    Direct,
    Unsupported,
}

impl ResultDelimiterFrame {
    fn handles_effect(&self, effect: &str) -> bool {
        self.effects
            .iter()
            .any(|handled| effect_names_match(handled, effect))
    }
}

impl DirectHandlerFrame {
    fn handles_effect(&self, effect: &str) -> bool {
        match self {
            DirectHandlerFrame::Static { arms } => arms
                .iter()
                .any(|arm| effect_names_match(&arm.op.effect, effect)),
            DirectHandlerFrame::Native { effects, .. } => effects
                .iter()
                .any(|handled| effect_names_match(handled, effect)),
        }
    }
}

fn effect_names_match(left: &str, right: &str) -> bool {
    if left == right {
        return true;
    }
    let left_qualified = left.contains('.');
    let right_qualified = right.contains('.');
    if left_qualified && right_qualified {
        return false;
    }
    left.rsplit('.').next() == right.rsplit('.').next()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::token::Span;

    fn test_span() -> Span {
        Span { start: 0, end: 0 }
    }

    fn test_node() -> NodeId {
        NodeId::fresh()
    }

    #[derive(Default)]
    struct TestEffectInfo {
        effect_calls: HashMap<NodeId, crate::typechecker::ResolvedEffectOp>,
        handler_arms: HashMap<NodeId, crate::typechecker::ResolvedEffectOp>,
        constructors: HashMap<NodeId, String>,
        fun_effects: HashMap<String, HashSet<String>>,
        let_effect_bindings: HashMap<String, Vec<String>>,
        type_at_node: HashMap<NodeId, Type>,
        records: HashMap<String, crate::typechecker::RecordInfo>,
        traits: HashMap<String, crate::typechecker::TraitInfo>,
        effect_ops: HashMap<String, Vec<String>>,
        handler_effects: HashMap<String, Vec<String>>,
        handler_refs: HashMap<NodeId, crate::typechecker::ResolvedValue>,
        let_handler_effects: HashMap<NodeId, Vec<String>>,
    }

    impl TestEffectInfo {
        fn as_effect_info(&self) -> EffectInfo<'_> {
            EffectInfo {
                effect_calls: &self.effect_calls,
                handler_arms: &self.handler_arms,
                constructors: &self.constructors,
                fun_effects: &self.fun_effects,
                let_effect_bindings: &self.let_effect_bindings,
                type_at_node: &self.type_at_node,
                records: &self.records,
                traits: &self.traits,
                effect_ops: &self.effect_ops,
                handler_effects: &self.handler_effects,
                handler_refs: &self.handler_refs,
                let_handler_effects: &self.let_handler_effects,
            }
        }
    }

    fn dict_app(name: &str) -> MExpr {
        MExpr::App {
            head: Atom::DictRef {
                name: name.to_string(),
                source: test_node(),
            },
            args: vec![],
            source: test_node(),
        }
    }

    fn test_lowerer<'a>(
        resolution: &'a ResolutionMap,
        ctors: &'a ConstructorAtoms,
        module_ctx: &'a CodegenContext,
        handler_info: &'a HandlerAnalysis,
        effect_info: &'a EffectInfo<'a>,
        handler_value_map: &'a HandlerValueMap,
    ) -> DirectLowerer<'a, 'a> {
        DirectLowerer::new(
            resolution,
            ctors,
            module_ctx,
            handler_info,
            effect_info,
            handler_value_map,
            HashMap::new(),
            LoweringOptions::default(),
        )
    }

    #[test]
    fn known_dict_values_compose_through_identical_if_branches() {
        let effect_info_fixture = TestEffectInfo::default();
        let effect_info = effect_info_fixture.as_effect_info();
        let resolution = ResolutionMap::new();
        let ctors = ConstructorAtoms::new();
        let module_ctx = CodegenContext::default();
        let handler_info = HandlerAnalysis::default();
        let handler_value_map = HandlerValueMap::new();
        let mut lowerer = DirectLowerer::new(
            &resolution,
            &ctors,
            &module_ctx,
            &handler_info,
            &effect_info,
            &handler_value_map,
            HashMap::new(),
            LoweringOptions::default(),
        );

        let dict_name = "__dict_Readable_Std_Int_Int";
        let program = vec![MDecl::DictConstructor(MDictConstructor {
            id: test_node(),
            name: dict_name.to_string(),
            dict_params: vec![],
            methods: vec![MExpr::Pure(Atom::Lambda {
                params: vec![Pat::Wildcard {
                    id: test_node(),
                    span: test_span(),
                }],
                body: Box::new(MExpr::Pure(Atom::Lit {
                    value: Lit::Int("41".to_string(), 41),
                    source: test_node(),
                })),
                source: test_node(),
            })],
            method_effects: vec![vec![]],
            method_open_rows: vec![false],
            impl_effects: vec![],
            span: test_span(),
        })];
        lowerer.classify_program(&program);

        let expr = MExpr::If {
            cond: Atom::Lit {
                value: Lit::Bool(true),
                source: test_node(),
            },
            then_branch: Box::new(dict_app(dict_name)),
            else_branch: Box::new(dict_app(dict_name)),
            source: test_node(),
        };

        let known = lowerer
            .known_dict_value_for_expr(&expr)
            .expect("identical dict branches should preserve the known dict fact");
        assert_eq!(known.dict_params, Vec::<String>::new());
        assert_eq!(known.dict_args, Vec::<Atom>::new());
        assert_eq!(known.methods.len(), 1);
    }

    #[test]
    fn native_variant_frame_collection_walks_lambda_bodies() {
        let effect_info_fixture = TestEffectInfo::default();
        let effect_info = effect_info_fixture.as_effect_info();
        let resolution = ResolutionMap::new();
        let ctors = ConstructorAtoms::new();
        let module_ctx = CodegenContext::default();
        let handler_info = HandlerAnalysis::default();
        let handler_value_map = HandlerValueMap::new();
        let lowerer = test_lowerer(
            &resolution,
            &ctors,
            &module_ctx,
            &handler_info,
            &effect_info,
            &handler_value_map,
        );

        let program = vec![MDecl::FunBinding(MFunBinding {
            id: test_node(),
            public: true,
            name: "stores_thunk".to_string(),
            name_span: test_span(),
            params: vec![Pat::Wildcard {
                id: test_node(),
                span: test_span(),
            }],
            guard: None,
            body: MExpr::Pure(Atom::Lambda {
                params: vec![Pat::Wildcard {
                    id: test_node(),
                    span: test_span(),
                }],
                body: Box::new(MExpr::With {
                    handler: MHandler::Native {
                        effects: vec!["Std.Actor.Actor".to_string()],
                        handler: "beam_actor".to_string(),
                        source: test_node(),
                    },
                    body: Box::new(MExpr::Pure(Atom::Lit {
                        value: Lit::Unit,
                        source: test_node(),
                    })),
                    source: test_node(),
                }),
                source: test_node(),
            }),
            span: test_span(),
        })];

        let frames = lowerer.native_variant_frames_in_program(&program);
        assert!(
            matches!(
                frames.as_slice(),
                [DirectHandlerFrame::Native {
                    kind: DirectHandlerKind::BeamActor,
                    effects
                }] if effects == &vec!["Std.Actor.Actor".to_string()]
            ),
            "{frames:?}"
        );
    }
}
