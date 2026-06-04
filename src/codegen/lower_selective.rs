//! Experimental direct-first lowerer for the selective-uniform spike.
//!
//! This module is intentionally incomplete, but no longer toy-sized. It keeps
//! pure/direct code in ordinary BEAM shape and lowers effectful regions through
//! explicit CPS islands when the selective planner can prove the shape.
//!
//! The submodules split the moving parts:
//! - `planning`: selective plan discovery, imported metadata, HOF specialization
//! - `direct`: direct Core Erlang lowering
//! - `cps`: CPS island and runtime CPS callable lowering
//! - `support`: small shared shape/data helpers

use std::collections::{BTreeMap, HashMap, HashSet};

mod cps;
mod direct;
mod occurs;
mod planning;
mod support;

use crate::ast::{Lit, NodeId, Pat};
use crate::codegen::CodegenContext;
use crate::codegen::cerl::{CArm, CBinSeg, CExpr, CFunDef, CLit, CModule, CPat};
use crate::codegen::handler_analysis::{HandlerAnalysis, ResumptionKind};
use crate::codegen::lower::util::{core_var, lower_lit_atom, mangle_ctor_atom};
use crate::codegen::monadic::ir::{
    Atom, EffectInfo, EffectOpRef, HandlerValueInfo, HandlerValueMap, MArm, MDecl,
    MDictConstructor, MExpr, MFunBinding, MHandler, MHandlerArm, MProgram, MVar,
};
use crate::codegen::native_effects::{NativeArgTransform, native_op};
use crate::codegen::resolve::{ConstructorAtoms, ResolutionMap, ResolvedCodegenKind};
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
    options: LoweringOptions,
}

impl<'a, 'info> DirectLowerer<'a, 'info> {
    #[allow(clippy::too_many_arguments)]
    fn new(
        resolution: &'a ResolutionMap,
        ctors: &'a ConstructorAtoms,
        module_ctx: &'a CodegenContext,
        handler_info: &'a HandlerAnalysis,
        effect_info: &'a EffectInfo<'info>,
        handler_value_map: &'a HandlerValueMap,
        imported_dict_constructors: HashMap<String, MDictConstructor>,
        options: LoweringOptions,
    ) -> Self {
        Self {
            resolution,
            ctors,
            module_ctx,
            handler_info,
            effect_info,
            handler_value_map,
            current_module: String::new(),
            callable_type_shapes: HashMap::new(),
            callable_callback_param_arities: HashMap::new(),
            local_fun_bindings: HashMap::new(),
            direct_values: HashSet::new(),
            function_plans: HashMap::new(),
            local_function_entries: HashMap::new(),
            local_dict_constructor_arities: HashMap::new(),
            local_hof_direct_specializations: HashMap::new(),
            local_dict_constructors: HashMap::new(),
            imported_dict_constructors,
            local_external_functions: HashMap::new(),
            imported_function_entries: HashMap::new(),
            imported_hof_direct_specializations: HashMap::new(),
            direct_candidate_function: None,
            direct_candidate_functions: HashSet::new(),
            static_handler_inline_stack: Vec::new(),
            direct_handler_stack: Vec::new(),
            result_delimiter_stack: Vec::new(),
            cps_temp_counter: 0,
            locals: vec![HashSet::new()],
            local_shapes: vec![HashMap::new()],
            local_known_direct_lambdas: vec![HashMap::new()],
            local_known_cps_lambdas: vec![HashMap::new()],
            local_known_dict_values: vec![HashMap::new()],
            options,
        }
    }

    fn lower_module(
        &mut self,
        module_name: &str,
        program: &MProgram,
        entry_export: Option<&str>,
    ) -> CModule {
        self.current_module = module_name.to_string();
        self.classify_program(program);
        self.compute_imported_function_entries();
        self.compute_function_lowering_plans(program);
        self.compute_local_function_entries(program);

        let pub_names: Option<HashSet<String>> =
            self.module_ctx.modules.get(module_name).map(|m| {
                m.codegen_info
                    .exports
                    .iter()
                    .map(|(n, _)| n.clone())
                    .collect()
            });
        let is_public =
            |name: &str| -> bool { pub_names.as_ref().is_none_or(|s| s.contains(name)) };
        let is_entry = |name: &str| -> bool { entry_export.is_some_and(|entry| entry == name) };
        let exported_dict_names: HashSet<String> = self
            .module_ctx
            .modules
            .get(module_name)
            .map(|m| {
                m.codegen_info
                    .trait_impl_dicts
                    .iter()
                    .map(|dict| dict.dict_name.clone())
                    .collect()
            })
            .unwrap_or_default();
        let is_exported_dict = |name: &str| -> bool {
            exported_dict_names.is_empty() || exported_dict_names.contains(name)
        };

        if self.options.require_all_functions {
            self.assert_no_unlowered_direct_body_functions(program);
            self.assert_no_unlowered_public_cps_functions(program, &is_public, &is_entry);
            self.assert_all_declarations_have_selective_plans(program);
        }

        let mut exports = Vec::new();
        let mut funs = Vec::new();
        let mut index = 0;
        while index < program.len() {
            match &program[index] {
                MDecl::FunBinding(fb) => {
                    let mut group = vec![fb];
                    let mut next_index = index + 1;
                    while next_index < program.len() {
                        let MDecl::FunBinding(next) = &program[next_index] else {
                            break;
                        };
                        if next.name != fb.name {
                            break;
                        }
                        group.push(next);
                        next_index += 1;
                    }

                    let Some(plan) = self.function_plans.get(&fb.name).copied() else {
                        index = next_index;
                        continue;
                    };
                    if fb.public || is_public(&fb.name) || is_entry(&fb.name) {
                        exports.extend(self.export_entries(&fb.name));
                    }
                    match plan {
                        FunctionLoweringPlan::DirectBody => {
                            funs.push(self.lower_direct_fun_binding_group(&group));
                            if self.needs_cps_adapter(&fb.name) {
                                funs.push(self.lower_cps_adapter_for(fb));
                            }
                        }
                        FunctionLoweringPlan::DirectBodyWithCpsIsland => {
                            funs.push(self.lower_direct_cps_island_fun_binding_group(&group));
                        }
                        FunctionLoweringPlan::CpsBody => {
                            funs.push(self.lower_cps_fun_binding_group(&group));
                        }
                    }
                    if group.len() == 1
                        && let Some(specialization) =
                            self.local_hof_direct_specializations.get(&fb.name).cloned()
                    {
                        if fb.public || is_public(&fb.name) || is_entry(&fb.name) {
                            exports.push((
                                specialization.entry_name.clone(),
                                specialization.source_arity,
                            ));
                        }
                        funs.push(
                            self.lower_hof_direct_specialized_fun_binding(fb, &specialization),
                        );
                    }
                    index = next_index;
                }
                MDecl::Val(v) => {
                    if !self.direct_values.contains(&v.name) {
                        index += 1;
                        continue;
                    }
                    if v.public {
                        exports.push((v.name.clone(), 0));
                    }
                    let body = self.lower_expr(&v.value);
                    funs.push(CFunDef {
                        name: v.name.clone(),
                        arity: 0,
                        body: CExpr::Fun(vec![], Box::new(body)),
                    });
                    index += 1;
                }
                MDecl::DictConstructor(dc) => {
                    if self.local_dict_constructor_arities.contains_key(&dc.name) {
                        if is_exported_dict(&dc.name) {
                            exports.push((dc.name.clone(), dc.dict_params.len()));
                        }
                        funs.push(self.lower_dict_constructor(dc));
                    }
                    index += 1;
                }
                MDecl::Passthrough(_) => {
                    index += 1;
                }
            }
        }

        CModule {
            name: module_name.to_string(),
            exports,
            funs,
        }
    }

    fn lower_fun_binding(&mut self, fb: &MFunBinding) -> CFunDef {
        let params = lower_param_names(&fb.params);
        let pushed_native_frame = self.push_native_variant_frame_for_name(&fb.name);
        self.push_scope();
        self.bind_fun_param_locals(fb);
        let lowered_body = self.lower_expr(&fb.body);
        let body = self.wrap_param_match(&fb.params, &params, lowered_body);
        self.pop_scope();
        if pushed_native_frame {
            self.direct_handler_stack.pop();
        }
        CFunDef {
            name: self.direct_entry_name(&fb.name),
            arity: params.len(),
            body: CExpr::Fun(params, Box::new(body)),
        }
    }

    fn lower_direct_fun_binding_group(&mut self, group: &[&MFunBinding]) -> CFunDef {
        assert!(
            !group.is_empty(),
            "lower_direct_fun_binding_group: empty group is impossible"
        );
        if group.len() == 1 && group[0].guard.is_none() {
            return self.lower_fun_binding(group[0]);
        }

        let name = &group[0].name;
        let source_arity = group[0].params.len();
        for fb in group {
            assert_eq!(
                fb.params.len(),
                source_arity,
                "lower_direct_fun_binding_group: clause arity mismatch for '{}'",
                name
            );
        }

        let params: Vec<String> = (0..source_arity)
            .map(|arg_index| format!("_Arg{arg_index}"))
            .collect();
        let scrutinee = CExpr::Tuple(params.iter().cloned().map(CExpr::Var).collect());
        let scrut_var = self.fresh_cps_temp("_FunScrut");
        let mut rest = self.case_clause_error();

        let pushed_native_frame = self.push_native_variant_frame_for_name(name);
        for fb in group.iter().rev() {
            let rest_var = self.fresh_cps_temp("_FunRest");
            let rest_ref = || CExpr::Apply(Box::new(CExpr::Var(rest_var.clone())), vec![]);
            self.push_scope();
            self.bind_fun_param_locals(fb);
            let body = self.lower_expr(&fb.body);
            let body = match fb.guard.as_ref() {
                Some(guard) => CExpr::Case(
                    Box::new(self.lower_expr(guard)),
                    vec![
                        CArm {
                            pat: CPat::Lit(CLit::Atom("true".to_string())),
                            guard: None,
                            body,
                        },
                        CArm {
                            pat: CPat::Wildcard,
                            guard: None,
                            body: rest_ref(),
                        },
                    ],
                ),
                None => body,
            };
            let pat = CPat::Tuple(fb.params.iter().map(|pat| self.lower_pat(pat)).collect());
            self.pop_scope();
            let current = CExpr::Case(
                Box::new(CExpr::Var(scrut_var.clone())),
                vec![
                    CArm {
                        pat,
                        guard: None,
                        body,
                    },
                    CArm {
                        pat: CPat::Wildcard,
                        guard: None,
                        body: rest_ref(),
                    },
                ],
            );
            rest = CExpr::Let(
                rest_var,
                Box::new(CExpr::Fun(vec![], Box::new(rest))),
                Box::new(current),
            );
        }
        if pushed_native_frame {
            self.direct_handler_stack.pop();
        }

        let body = CExpr::Let(scrut_var, Box::new(scrutinee), Box::new(rest));
        CFunDef {
            name: self.direct_entry_name(name),
            arity: params.len(),
            body: CExpr::Fun(params, Box::new(body)),
        }
    }

    fn lower_hof_direct_specialized_fun_binding(
        &mut self,
        fb: &MFunBinding,
        specialization: &HofDirectSpecialization,
    ) -> CFunDef {
        let params = lower_param_names(&fb.params);
        let (param_shapes, _callback_params) = self
            .hof_direct_specialized_param_shapes(fb)
            .unwrap_or_else(|| (vec![None; fb.params.len()], Vec::new()));
        self.push_scope();
        for (index, pat) in fb.params.iter().enumerate() {
            self.bind_pat_locals_with_shape(pat, param_shapes.get(index).cloned().flatten());
        }
        let lowered_body = self.lower_expr(&fb.body);
        let body = self.wrap_param_match(&fb.params, &params, lowered_body);
        self.pop_scope();
        CFunDef {
            name: specialization.entry_name.clone(),
            arity: params.len(),
            body: CExpr::Fun(params, Box::new(body)),
        }
    }

    fn lower_cps_adapter_for(&self, fb: &MFunBinding) -> CFunDef {
        let direct_params = lower_param_names(&fb.params);
        let mut params = direct_params.clone();
        params.push("_Evidence".to_string());
        params.push("_ReturnK".to_string());
        let direct_call_args = self.cps_adapter_direct_call_args(fb, &direct_params);
        let direct_call = CExpr::Apply(
            Box::new(CExpr::FunRef(
                self.direct_entry_name(&fb.name),
                direct_params.len(),
            )),
            direct_call_args,
        );
        let body = CExpr::Apply(
            Box::new(CExpr::Var("_ReturnK".to_string())),
            vec![direct_call],
        );
        CFunDef {
            name: fb.name.clone(),
            arity: params.len(),
            body: CExpr::Fun(params, Box::new(body)),
        }
    }

    fn cps_adapter_direct_call_args(
        &self,
        fb: &MFunBinding,
        direct_params: &[String],
    ) -> Vec<CExpr> {
        let param_shapes = self.param_shapes_for_fun(fb);
        direct_params
            .iter()
            .enumerate()
            .map(
                |(index, name)| match param_shapes.get(index).and_then(|shape| shape.as_ref()) {
                    Some(LocalValueShape::PureCallableFromUseType) => {
                        let arity = self
                            .pure_callable_param_arity(fb, index)
                            .expect("pure callable param shape must have an arity");
                        self.cps_param_to_direct_closure(name, arity, index)
                    }
                    Some(LocalValueShape::PureCallable { arity }) => {
                        self.cps_param_to_direct_closure(name, *arity, index)
                    }
                    _ => CExpr::Var(name.clone()),
                },
            )
            .collect()
    }

    fn pure_callable_param_arity(&self, fb: &MFunBinding, index: usize) -> Option<usize> {
        let mut current = self.effect_info.type_at_node.get(&fb.id)?;
        for current_index in 0..=index {
            let Type::Fun(param, ret, _) = current else {
                return None;
            };
            if current_index == index {
                return self.pure_function_arity_from_type(param);
            }
            current = ret;
        }
        None
    }

    fn cps_param_to_direct_closure(&self, param_name: &str, arity: usize, index: usize) -> CExpr {
        let arg_names: Vec<String> = (0..arity)
            .map(|arg_index| format!("_CpsAdapterArg{index}_{arg_index}"))
            .collect();
        let k_name = format!("_CpsAdapterK{index}");
        let k_arg = format!("_CpsAdapterV{index}");
        let mut cps_args: Vec<CExpr> = arg_names.iter().cloned().map(CExpr::Var).collect();
        cps_args.push(CExpr::Var("_Evidence".to_string()));
        cps_args.push(CExpr::Var(k_name.clone()));
        let apply_cps = CExpr::Apply(Box::new(CExpr::Var(param_name.to_string())), cps_args);
        let identity_k = CExpr::Fun(vec![k_arg.clone()], Box::new(CExpr::Var(k_arg)));
        CExpr::Fun(
            arg_names,
            Box::new(CExpr::Let(
                k_name,
                Box::new(identity_k),
                Box::new(apply_cps),
            )),
        )
    }

    fn lower_direct_cps_island_fun_binding(&mut self, fb: &MFunBinding) -> CFunDef {
        let params = lower_param_names(&fb.params);

        let prev_direct_candidate = self.direct_candidate_function.replace(fb.name.clone());
        let pushed_native_frame = self.push_native_variant_frame_for_name(&fb.name);
        self.push_scope();
        self.bind_fun_param_locals(fb);
        let return_k = self.identity_cps_continuation();
        let lowered_body = self.lower_cps_expr(&fb.body, CExpr::Tuple(vec![]), return_k);
        let body = self.wrap_param_match(&fb.params, &params, lowered_body);
        self.pop_scope();
        if pushed_native_frame {
            self.direct_handler_stack.pop();
        }
        self.direct_candidate_function = prev_direct_candidate;

        CFunDef {
            name: self.direct_entry_name(&fb.name),
            arity: params.len(),
            body: CExpr::Fun(params, Box::new(body)),
        }
    }

    fn lower_direct_cps_island_fun_binding_group(&mut self, group: &[&MFunBinding]) -> CFunDef {
        assert!(
            !group.is_empty(),
            "lower_direct_cps_island_fun_binding_group: empty group is impossible"
        );
        if group.len() == 1 && group[0].guard.is_none() {
            return self.lower_direct_cps_island_fun_binding(group[0]);
        }

        let name = &group[0].name;
        let source_arity = group[0].params.len();
        for fb in group {
            assert_eq!(
                fb.params.len(),
                source_arity,
                "lower_direct_cps_island_fun_binding_group: clause arity mismatch for '{}'",
                name
            );
        }

        let params: Vec<String> = (0..source_arity)
            .map(|arg_index| format!("_Arg{arg_index}"))
            .collect();
        let scrutinee = CExpr::Tuple(params.iter().cloned().map(CExpr::Var).collect());
        let scrut_var = self.fresh_cps_temp("_FunScrut");
        let mut rest = self.case_clause_error();

        let prev_direct_candidate = self.direct_candidate_function.replace(name.clone());
        let pushed_native_frame = self.push_native_variant_frame_for_name(name);
        for fb in group.iter().rev() {
            let rest_var = self.fresh_cps_temp("_FunRest");
            let rest_ref = || CExpr::Apply(Box::new(CExpr::Var(rest_var.clone())), vec![]);
            self.push_scope();
            self.bind_fun_param_locals(fb);
            let return_k = self.identity_cps_continuation();
            let body = self.lower_cps_expr(&fb.body, CExpr::Tuple(vec![]), return_k);
            let body = match fb.guard.as_ref() {
                Some(guard) => CExpr::Case(
                    Box::new(self.lower_expr(guard)),
                    vec![
                        CArm {
                            pat: CPat::Lit(CLit::Atom("true".to_string())),
                            guard: None,
                            body,
                        },
                        CArm {
                            pat: CPat::Wildcard,
                            guard: None,
                            body: rest_ref(),
                        },
                    ],
                ),
                None => body,
            };
            let pat = CPat::Tuple(fb.params.iter().map(|pat| self.lower_pat(pat)).collect());
            self.pop_scope();
            let current = CExpr::Case(
                Box::new(CExpr::Var(scrut_var.clone())),
                vec![
                    CArm {
                        pat,
                        guard: None,
                        body,
                    },
                    CArm {
                        pat: CPat::Wildcard,
                        guard: None,
                        body: rest_ref(),
                    },
                ],
            );
            rest = CExpr::Let(
                rest_var,
                Box::new(CExpr::Fun(vec![], Box::new(rest))),
                Box::new(current),
            );
        }
        if pushed_native_frame {
            self.direct_handler_stack.pop();
        }
        self.direct_candidate_function = prev_direct_candidate;

        let body = CExpr::Let(scrut_var, Box::new(scrutinee), Box::new(rest));
        CFunDef {
            name: self.direct_entry_name(name),
            arity: params.len(),
            body: CExpr::Fun(params, Box::new(body)),
        }
    }

    fn identity_cps_continuation(&mut self) -> CExpr {
        let result = self.fresh_cps_temp("_CpsResult");
        CExpr::Fun(vec![result.clone()], Box::new(CExpr::Var(result)))
    }

    fn lower_cps_fun_binding(&mut self, fb: &MFunBinding) -> CFunDef {
        let direct_params = lower_param_names(&fb.params);
        let mut params = direct_params.clone();
        params.push("_Evidence".to_string());
        params.push("_ReturnK".to_string());

        let pushed_native_frame = self.push_native_variant_frame_for_name(&fb.name);
        self.push_scope();
        self.bind_cps_entry_param_locals(fb);
        let lowered_body = self.lower_cps_expr(
            &fb.body,
            CExpr::Var("_Evidence".to_string()),
            CExpr::Var("_ReturnK".to_string()),
        );
        let body = self.wrap_param_match(&fb.params, &direct_params, lowered_body);
        self.pop_scope();
        if pushed_native_frame {
            self.direct_handler_stack.pop();
        }

        CFunDef {
            name: fb.name.clone(),
            arity: params.len(),
            body: CExpr::Fun(params, Box::new(body)),
        }
    }

    fn lower_cps_fun_binding_group(&mut self, group: &[&MFunBinding]) -> CFunDef {
        assert!(
            !group.is_empty(),
            "lower_cps_fun_binding_group: empty group is impossible"
        );
        if group.len() == 1 && group[0].guard.is_none() {
            return self.lower_cps_fun_binding(group[0]);
        }

        let name = &group[0].name;
        let source_arity = group[0].params.len();
        for fb in group {
            assert_eq!(
                fb.params.len(),
                source_arity,
                "lower_cps_fun_binding_group: clause arity mismatch for '{}'",
                name
            );
        }

        let direct_params: Vec<String> = (0..source_arity)
            .map(|arg_index| format!("_Arg{arg_index}"))
            .collect();
        let mut params = direct_params.clone();
        params.push("_Evidence".to_string());
        params.push("_ReturnK".to_string());

        let scrutinee = CExpr::Tuple(direct_params.iter().cloned().map(CExpr::Var).collect());
        let scrut_var = self.fresh_cps_temp("_FunScrut");
        let mut rest = self.case_clause_error();

        let prev_direct_candidate = self.direct_candidate_function.replace(name.clone());
        let pushed_native_frame = self.push_native_variant_frame_for_name(name);
        for fb in group.iter().rev() {
            let rest_var = self.fresh_cps_temp("_FunRest");
            let rest_ref = || CExpr::Apply(Box::new(CExpr::Var(rest_var.clone())), vec![]);
            self.push_scope();
            self.bind_cps_entry_param_locals(fb);
            let body = self.lower_cps_expr(
                &fb.body,
                CExpr::Var("_Evidence".to_string()),
                CExpr::Var("_ReturnK".to_string()),
            );
            let body = match fb.guard.as_ref() {
                Some(guard) => CExpr::Case(
                    Box::new(self.lower_expr(guard)),
                    vec![
                        CArm {
                            pat: CPat::Lit(CLit::Atom("true".to_string())),
                            guard: None,
                            body,
                        },
                        CArm {
                            pat: CPat::Wildcard,
                            guard: None,
                            body: rest_ref(),
                        },
                    ],
                ),
                None => body,
            };
            let pat = CPat::Tuple(fb.params.iter().map(|pat| self.lower_pat(pat)).collect());
            self.pop_scope();
            let current = CExpr::Case(
                Box::new(CExpr::Var(scrut_var.clone())),
                vec![
                    CArm {
                        pat,
                        guard: None,
                        body,
                    },
                    CArm {
                        pat: CPat::Wildcard,
                        guard: None,
                        body: rest_ref(),
                    },
                ],
            );
            rest = CExpr::Let(
                rest_var,
                Box::new(CExpr::Fun(vec![], Box::new(rest))),
                Box::new(current),
            );
        }
        if pushed_native_frame {
            self.direct_handler_stack.pop();
        }
        self.direct_candidate_function = prev_direct_candidate;

        let body = CExpr::Let(scrut_var, Box::new(scrutinee), Box::new(rest));
        CFunDef {
            name: name.clone(),
            arity: params.len(),
            body: CExpr::Fun(params, Box::new(body)),
        }
    }

    fn export_entries(&self, name: &str) -> Vec<(String, usize)> {
        let Some(entries) = self.local_function_entries.get(name) else {
            return vec![(name.to_string(), 0)];
        };
        let mut exports = Vec::new();
        if let Some(direct_entry_arity) = entries.direct_entry_arity {
            exports.push((
                self.direct_entry_name_for(name, entries),
                direct_entry_arity,
            ));
        }
        if let Some(cps_adapter_entry_arity) = entries.cps_adapter_entry_arity {
            exports.push((name.to_string(), cps_adapter_entry_arity));
        }
        if exports.is_empty() {
            exports.push((name.to_string(), entries.source_arity));
        }
        exports
    }

    fn needs_cps_adapter(&self, name: &str) -> bool {
        self.local_function_entries
            .get(name)
            .is_some_and(|entries| {
                entries.direct_entry_arity.is_some() && entries.cps_adapter_entry_arity.is_some()
            })
    }

    fn direct_entry_name(&self, name: &str) -> String {
        self.local_function_entries
            .get(name)
            .map(|entries| self.direct_entry_name_for(name, entries))
            .unwrap_or_else(|| name.to_string())
    }

    fn direct_entry_name_for(&self, name: &str, entries: &FunctionEntryInfo) -> String {
        direct_entry_name_for(name, entries)
    }

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

    fn call_shape(&self, head: &Atom) -> Option<CallShape> {
        if let Some(intrinsic) = self.direct_intrinsic(head) {
            return Some(CallShape::Intrinsic(intrinsic));
        }
        if let Some(callable) = self.direct_dict_constructor(head) {
            return Some(CallShape::Direct(callable));
        }
        if let Some(callable) = self.direct_function_callable(head) {
            return Some(CallShape::Direct(callable));
        }
        if let Some(cps) = self.local_cps_function_shape_by_name(head) {
            return Some(cps);
        }
        if let Some(cps) = self.cps_function_shape(head) {
            return Some(cps);
        }
        if let Some(local) = self.local_top_level_function_shape(head) {
            return Some(local);
        }
        if let Atom::Var { name, .. } = head
            && let Some(LocalValueShape::CpsCallable {
                module,
                name: adapter_name,
                source_arity,
                adapter_arity,
                effects,
                ..
            }) = self.local_shape(&name.name)
        {
            return Some(CallShape::Cps {
                module,
                name: adapter_name,
                source_arity,
                adapter_arity,
                effects,
            });
        }
        if let Atom::Var { name, .. } = head
            && let Some(LocalValueShape::RuntimeCpsCallable {
                source_arity,
                adapter_arity,
                effects,
            }) = self.local_shape(&name.name)
        {
            return Some(CallShape::LocalCpsCallable {
                name: name.name.clone(),
                source_arity,
                adapter_arity,
                effects,
            });
        }
        if let Atom::Var { name, source } = head
            && matches!(
                self.local_shape(&name.name),
                Some(LocalValueShape::PureCallableFromUseType)
            )
            && let Some((source_arity, adapter_arity, effects)) =
                self.cps_function_arity_at(*source)
        {
            return Some(CallShape::LocalCpsCallable {
                name: name.name.clone(),
                source_arity,
                adapter_arity,
                effects,
            });
        }
        if let Atom::Var { name, .. } = head
            && let Some(arity) = self.local_callable_arity_for_head(head)
        {
            return Some(CallShape::LocalCallable {
                name: name.name.clone(),
                arity,
            });
        }
        None
    }

    fn local_cps_function_shape_by_name(&self, head: &Atom) -> Option<CallShape> {
        let Atom::Var { name, .. } = head else {
            return None;
        };
        if self.is_local(&name.name) {
            return None;
        }
        let RuntimeFunctionShape::Cps(shape) = self.callable_type_shapes.get(&name.name)? else {
            return None;
        };
        if let Some(entries) = self.local_function_entries.get(&name.name) {
            let adapter_arity = entries.cps_adapter_entry_arity?;
            return Some(CallShape::Cps {
                module: None,
                name: name.name.clone(),
                source_arity: entries.source_arity,
                adapter_arity,
                effects: shape.static_effects.clone(),
            });
        }
        let recursive_self = self
            .direct_candidate_function
            .as_ref()
            .is_some_and(|current| current == &name.name)
            || self.direct_candidate_functions.contains(&name.name);
        let has_cps_plan = self
            .function_plans
            .get(&name.name)
            .copied()
            .is_some_and(FunctionLoweringPlan::has_cps_body);
        if !recursive_self && !has_cps_plan {
            return None;
        }
        let binding = self.local_fun_bindings.get(&name.name)?;
        let source_arity = binding.params.len();
        Some(CallShape::Cps {
            module: None,
            name: name.name.clone(),
            source_arity,
            adapter_arity: source_arity + 2,
            effects: shape.static_effects.clone(),
        })
    }

    fn local_top_level_function_shape(&self, head: &Atom) -> Option<CallShape> {
        let Atom::Var { name, .. } = head else {
            return None;
        };
        if self.is_local(&name.name) {
            return None;
        }
        let entries = self.local_function_entries.get(&name.name)?;
        match self.callable_type_shapes.get(&name.name)? {
            RuntimeFunctionShape::Pure => {
                let arity = entries.direct_entry_arity?;
                Some(CallShape::Direct(DirectCallable {
                    module: None,
                    name: self.direct_entry_name_for(&name.name, entries),
                    arity,
                }))
            }
            RuntimeFunctionShape::Cps(shape) => {
                let adapter_arity = entries.cps_adapter_entry_arity?;
                Some(CallShape::Cps {
                    module: None,
                    name: name.name.clone(),
                    source_arity: entries.source_arity,
                    adapter_arity,
                    effects: shape.static_effects.clone(),
                })
            }
            RuntimeFunctionShape::Intrinsic => None,
        }
    }

    fn is_panic_or_todo_call(&self, head: &Atom, args: &[Atom]) -> bool {
        let Atom::Var { name, source } = head else {
            return false;
        };
        args.len() == 1
            && self.resolution.get(source).is_none()
            && matches!(name.name.as_str(), "panic" | "todo")
    }

    fn cps_function_shape(&self, head: &Atom) -> Option<CallShape> {
        let source = match head {
            Atom::Var { source, .. } | Atom::QualifiedRef { source, .. } => *source,
            _ => return None,
        };
        let resolved = self.resolution.get(&source)?;
        let ResolvedCodegenKind::BeamFunction {
            erlang_mod,
            name,
            arity,
            effects,
        } = &resolved.kind
        else {
            return None;
        };
        let module = resolved_erlang_module_for_call(erlang_mod, &self.current_module);
        let metadata = module
            .as_ref()
            .and_then(|module| {
                self.imported_function_entries
                    .get(&(module.clone(), name.clone()))
            })
            .or_else(|| {
                module
                    .is_none()
                    .then(|| self.local_function_entries.get(name))
                    .flatten()
            });
        if let Some(entries) = metadata
            && let Some(adapter_arity) = entries.cps_adapter_entry_arity
        {
            return Some(CallShape::Cps {
                module,
                name: name.clone(),
                source_arity: entries.source_arity,
                adapter_arity,
                effects: match &entries.callable_type_shape {
                    RuntimeFunctionShape::Cps(shape) => shape.static_effects.clone(),
                    _ => effects.clone(),
                },
            });
        }
        if module.is_none()
            && let Some(RuntimeFunctionShape::Cps(shape)) = self.callable_type_shapes.get(name)
        {
            let (source_arity, adapter_arity, effects) =
                self.cps_function_arity_at(source).unwrap_or_else(|| {
                    let source_arity = source_arity_for_cps_resolved(*arity);
                    (source_arity, source_arity + 2, shape.static_effects.clone())
                });
            return Some(CallShape::Cps {
                module,
                name: name.clone(),
                source_arity,
                adapter_arity,
                effects,
            });
        }
        if effects.is_empty() {
            return None;
        }
        Some(CallShape::Cps {
            module,
            name: name.clone(),
            source_arity: source_arity_for_cps_resolved(*arity),
            adapter_arity: *arity,
            effects: effects.clone(),
        })
    }

    fn direct_intrinsic(&self, head: &Atom) -> Option<IntrinsicId> {
        let source = match head {
            Atom::Var { source, .. } | Atom::QualifiedRef { source, .. } => *source,
            _ => return None,
        };
        let resolved = self.resolution.get(&source)?;
        let ResolvedCodegenKind::Intrinsic { id, .. } = resolved.kind else {
            return None;
        };
        Some(id)
    }

    fn direct_dict_constructor(&self, head: &Atom) -> Option<DirectCallable> {
        let (name, source) = match head {
            Atom::DictRef { name, source } => (name, *source),
            _ => return None,
        };
        if let Some(arity) = self.local_dict_constructor_arities.get(name) {
            return Some(DirectCallable {
                module: None,
                name: name.clone(),
                arity: *arity,
            });
        }
        let resolved = self.resolution.get(&source)?;
        let ResolvedCodegenKind::BeamFunction {
            erlang_mod,
            name,
            arity,
            effects,
        } = &resolved.kind
        else {
            return None;
        };
        if !effects.is_empty() {
            return None;
        }
        Some(DirectCallable {
            module: erlang_mod.clone(),
            name: name.clone(),
            arity: *arity,
        })
    }

    fn direct_function_callable(&self, head: &Atom) -> Option<DirectCallable> {
        if let Some(callable) = self.local_direct_function_callable_by_name(head) {
            return Some(callable);
        }
        if let Some(callable) = self.local_external_callable_by_name(head) {
            return Some(callable);
        }

        let source = match head {
            Atom::Var { source, .. } | Atom::QualifiedRef { source, .. } => *source,
            _ => return None,
        };
        let resolved = self.resolution.get(&source)?;
        if let ResolvedCodegenKind::ExternalFunction {
            target_erlang_mod,
            target_name,
            arity,
            effects,
            ..
        } = &resolved.kind
        {
            if !effects.is_empty() {
                return None;
            }
            return Some(DirectCallable {
                module: Some(target_erlang_mod.clone()),
                name: target_name.clone(),
                arity: *arity,
            });
        }
        let ResolvedCodegenKind::BeamFunction {
            erlang_mod,
            name,
            arity,
            effects,
        } = &resolved.kind
        else {
            return None;
        };
        let is_remote = erlang_mod
            .as_ref()
            .is_some_and(|module| module != &self.current_module);
        if is_remote
            && erlang_mod
                .as_ref()
                .and_then(|module| {
                    self.imported_function_entries
                        .get(&(module.clone(), name.clone()))
                })
                .is_some_and(FunctionEntryInfo::is_cps_typed)
        {
            return None;
        }
        if !effects.is_empty() && is_remote {
            let module = erlang_mod.as_ref()?;
            let entries = self
                .imported_function_entries
                .get(&(module.clone(), name.clone()))?;
            let direct_entry_arity = direct_entry_arity_matching_resolved(*arity, entries)?;
            return Some(DirectCallable {
                module: erlang_mod.clone(),
                name: direct_entry_name_for(name, entries),
                arity: direct_entry_arity,
            });
        }
        if is_remote {
            return Some(DirectCallable {
                module: erlang_mod.clone(),
                name: name.clone(),
                arity: *arity,
            });
        }
        if matches!(
            self.callable_type_shapes.get(name),
            Some(RuntimeFunctionShape::Cps(_))
        ) {
            return None;
        }

        let recursive_self = self
            .direct_candidate_function
            .as_ref()
            .is_some_and(|current| current == name)
            || self.direct_candidate_functions.contains(name);
        let has_direct_entry = self
            .function_plans
            .get(name)
            .copied()
            .is_some_and(FunctionLoweringPlan::has_direct_entry);
        if !recursive_self && !has_direct_entry {
            return None;
        }
        let direct_name = self
            .local_function_entries
            .get(name)
            .map(|entries| self.direct_entry_name_for(name, entries))
            .unwrap_or_else(|| name.clone());
        Some(DirectCallable {
            module: None,
            name: direct_name,
            arity: *arity,
        })
    }

    fn local_direct_function_callable_by_name(&self, head: &Atom) -> Option<DirectCallable> {
        let Atom::Var { name, .. } = head else {
            return None;
        };
        if self.is_local(&name.name) {
            return None;
        }
        if let Some(entries) = self.local_function_entries.get(&name.name) {
            let arity = entries.direct_entry_arity?;
            return Some(DirectCallable {
                module: None,
                name: self.direct_entry_name_for(&name.name, entries),
                arity,
            });
        }
        let recursive_self = self
            .direct_candidate_function
            .as_ref()
            .is_some_and(|current| current == &name.name)
            || self.direct_candidate_functions.contains(&name.name);
        let has_direct_plan = self
            .function_plans
            .get(&name.name)
            .copied()
            .is_some_and(FunctionLoweringPlan::has_direct_entry);
        if recursive_self
            && !has_direct_plan
            && !matches!(
                self.callable_type_shapes.get(&name.name),
                Some(RuntimeFunctionShape::Pure)
            )
        {
            return None;
        }
        if !recursive_self && !has_direct_plan {
            return None;
        }
        let binding = self.local_fun_bindings.get(&name.name)?;
        Some(DirectCallable {
            module: None,
            name: name.name.clone(),
            arity: binding.params.len(),
        })
    }

    fn direct_function_value_ref(&self, head: &Atom) -> Option<CExpr> {
        let source = match head {
            Atom::Var { source, .. } | Atom::QualifiedRef { source, .. } => *source,
            _ => return None,
        };
        let resolved = self.resolution.get(&source)?;
        if let ResolvedCodegenKind::ExternalFunction {
            target_erlang_mod,
            target_name,
            arity,
            effects,
            ..
        } = &resolved.kind
        {
            if !effects.is_empty() {
                return None;
            }
            return Some(remote_fun_value(
                target_erlang_mod.clone(),
                target_name.clone(),
                *arity,
            ));
        }
        let ResolvedCodegenKind::BeamFunction {
            erlang_mod,
            name,
            arity,
            effects,
        } = &resolved.kind
        else {
            return None;
        };
        if !effects.is_empty() {
            return None;
        }
        let is_remote = erlang_mod
            .as_ref()
            .is_some_and(|module| module != &self.current_module);
        if is_remote {
            return erlang_mod
                .as_ref()
                .map(|module| remote_fun_value(module.clone(), name.clone(), *arity));
        }
        let shape = self.callable_type_shapes.get(name)?;
        if !matches!(shape, RuntimeFunctionShape::Pure) || shape.expanded_arity(*arity) != *arity {
            return None;
        }
        Some(if *arity == 0 {
            CExpr::Apply(Box::new(CExpr::FunRef(name.clone(), 0)), vec![])
        } else {
            CExpr::FunRef(name.clone(), *arity)
        })
    }

    fn local_external_callable_by_name(&self, head: &Atom) -> Option<DirectCallable> {
        let Atom::Var { name, .. } = head else {
            return None;
        };
        self.local_external_functions.get(&name.name).cloned()
    }

    fn supported_direct_call(&self, head: &Atom) -> Option<DirectCallable> {
        self.direct_function_callable(head)
    }

    fn is_local(&self, name: &str) -> bool {
        self.locals.iter().rev().any(|scope| scope.contains(name))
    }

    fn local_shape(&self, name: &str) -> Option<LocalValueShape> {
        self.local_shapes
            .iter()
            .rev()
            .find_map(|scope| scope.get(name).cloned())
    }

    fn local_callable_arity_for_head(&self, head: &Atom) -> Option<usize> {
        let Atom::Var { name, source } = head else {
            return None;
        };
        match self.local_shape(&name.name)? {
            LocalValueShape::PureCallable { arity } => Some(arity),
            LocalValueShape::PureCallableFromUseType => self.pure_function_arity_at(*source),
            LocalValueShape::CpsCallable { .. } | LocalValueShape::RuntimeCpsCallable { .. } => {
                None
            }
        }
    }

    fn push_scope(&mut self) {
        self.locals.push(HashSet::new());
        self.local_shapes.push(HashMap::new());
        self.local_known_direct_lambdas.push(HashMap::new());
        self.local_known_cps_lambdas.push(HashMap::new());
        self.local_known_dict_values.push(HashMap::new());
    }

    fn pop_scope(&mut self) {
        self.locals.pop();
        self.local_shapes.pop();
        self.local_known_direct_lambdas.pop();
        self.local_known_cps_lambdas.pop();
        self.local_known_dict_values.pop();
    }

    fn current_scope_mut(&mut self) -> &mut HashSet<String> {
        self.locals.last_mut().expect("direct lowerer has a scope")
    }

    fn current_shape_scope_mut(&mut self) -> &mut HashMap<String, LocalValueShape> {
        self.local_shapes
            .last_mut()
            .expect("direct lowerer has a local-shape scope")
    }

    fn current_known_cps_lambda_scope_mut(&mut self) -> &mut HashMap<String, KnownCpsLambda> {
        self.local_known_cps_lambdas
            .last_mut()
            .expect("direct lowerer has a known-CPS-lambda scope")
    }

    fn current_known_direct_lambda_scope_mut(&mut self) -> &mut HashMap<String, KnownDirectLambda> {
        self.local_known_direct_lambdas
            .last_mut()
            .expect("direct lowerer has a known-direct-lambda scope")
    }

    fn current_known_dict_value_scope_mut(&mut self) -> &mut HashMap<String, KnownDictValue> {
        self.local_known_dict_values
            .last_mut()
            .expect("direct lowerer has a known-dict-value scope")
    }

    fn known_direct_lambda(&self, name: &str) -> Option<KnownDirectLambda> {
        self.local_known_direct_lambdas
            .iter()
            .rev()
            .find_map(|scope| scope.get(name).cloned())
    }

    fn known_cps_lambda(&self, name: &str) -> Option<KnownCpsLambda> {
        self.local_known_cps_lambdas
            .iter()
            .rev()
            .find_map(|scope| scope.get(name).cloned())
    }

    fn known_dict_value(&self, name: &str) -> Option<KnownDictValue> {
        self.local_known_dict_values
            .iter()
            .rev()
            .find_map(|scope| scope.get(name).cloned())
    }

    fn bind_fun_param_locals(&mut self, fb: &MFunBinding) {
        let param_shapes = self.param_shapes_for_fun(fb);
        for (index, pat) in fb.params.iter().enumerate() {
            self.bind_pat_locals_with_shape(pat, param_shapes.get(index).cloned().flatten());
        }
    }

    fn bind_cps_entry_param_locals(&mut self, fb: &MFunBinding) {
        let param_shapes = self.param_shapes_for_cps_entry(fb);
        let callback_params: HashMap<usize, usize> = self
            .cps_callback_params_called_in_body(fb)
            .into_iter()
            .map(|callback| (callback.index, callback.source_arity))
            .collect();
        for (index, pat) in fb.params.iter().enumerate() {
            let shape = param_shapes
                .get(index)
                .cloned()
                .flatten()
                .or_else(|| self.local_shape_for_cps_entry_pat(pat))
                .or_else(|| {
                    callback_params.get(&index).copied().map(|source_arity| {
                        LocalValueShape::RuntimeCpsCallable {
                            source_arity,
                            adapter_arity: source_arity + 2,
                            effects: Vec::new(),
                        }
                    })
                });
            self.bind_pat_locals_with_shape(pat, shape);
        }
    }

    pub(super) fn bind_fun_param_locals_with_arg_shapes(
        &mut self,
        fb: &MFunBinding,
        args: &[Atom],
    ) {
        let param_shapes = self.param_shapes_for_fun(fb);
        for (index, pat) in fb.params.iter().enumerate() {
            let shape = args
                .get(index)
                .and_then(|arg| self.specialized_param_shape_for_arg(arg))
                .or_else(|| param_shapes.get(index).cloned().flatten());
            self.bind_pat_locals_with_shape(pat, shape);
        }
    }

    fn specialized_param_shape_for_arg(&mut self, arg: &Atom) -> Option<LocalValueShape> {
        self.pure_value_atom_shape(arg)
            .or_else(|| self.cps_value_atom_shape(arg))
    }

    fn function_type_for_binding(&self, fb: &MFunBinding) -> Option<&Type> {
        self.effect_info
            .type_at_node
            .get(&fb.id)
            .or_else(|| self.exported_function_type(&fb.name))
    }

    fn exported_function_type(&self, name: &str) -> Option<&Type> {
        self.module_ctx
            .modules
            .get(&self.current_module)?
            .codegen_info
            .exports
            .iter()
            .find_map(|(export_name, scheme)| (export_name == name).then_some(&scheme.ty))
    }

    fn param_shapes_for_fun(&self, fb: &MFunBinding) -> Vec<Option<LocalValueShape>> {
        let Some(mut current) = self.function_type_for_binding(fb) else {
            return vec![None; fb.params.len()];
        };
        let mut shapes = Vec::with_capacity(fb.params.len());
        while let Type::Fun(param, ret, _) = current {
            shapes.push(self.local_shape_for_param_type(param));
            current = ret;
        }
        shapes.resize(fb.params.len(), None);
        shapes
    }

    fn local_shape_for_param_type(&self, ty: &Type) -> Option<LocalValueShape> {
        if self.pure_function_arity_from_type(ty).is_some() {
            Some(LocalValueShape::PureCallableFromUseType)
        } else if let Some((source_arity, adapter_arity, effects)) =
            self.cps_function_arity_from_type(ty)
        {
            Some(LocalValueShape::RuntimeCpsCallable {
                source_arity,
                adapter_arity,
                effects,
            })
        } else {
            None
        }
    }

    fn param_shapes_for_cps_entry(&self, fb: &MFunBinding) -> Vec<Option<LocalValueShape>> {
        let Some(mut current) = self.function_type_for_binding(fb) else {
            return vec![None; fb.params.len()];
        };
        let mut shapes = Vec::with_capacity(fb.params.len());
        while let Type::Fun(param, ret, _) = current {
            shapes.push(self.local_shape_for_cps_entry_param_type(param));
            current = ret;
        }
        shapes.resize(fb.params.len(), None);
        shapes
    }

    fn local_shape_for_cps_entry_param_type(&self, ty: &Type) -> Option<LocalValueShape> {
        if let Some(source_arity) = self.pure_function_arity_from_type(ty) {
            Some(LocalValueShape::RuntimeCpsCallable {
                source_arity,
                adapter_arity: source_arity + 2,
                effects: Vec::new(),
            })
        } else if let Some((source_arity, adapter_arity, effects)) =
            self.cps_function_arity_from_type(ty)
        {
            Some(LocalValueShape::RuntimeCpsCallable {
                source_arity,
                adapter_arity,
                effects,
            })
        } else {
            None
        }
    }

    fn local_shape_for_cps_entry_pat(&self, pat: &Pat) -> Option<LocalValueShape> {
        let Pat::Var { id, .. } = pat else {
            return None;
        };
        if let Some(source_arity) = self.pure_function_arity_at(*id) {
            Some(LocalValueShape::RuntimeCpsCallable {
                source_arity,
                adapter_arity: source_arity + 2,
                effects: Vec::new(),
            })
        } else if let Some((source_arity, adapter_arity, effects)) = self.cps_function_arity_at(*id)
        {
            Some(LocalValueShape::RuntimeCpsCallable {
                source_arity,
                adapter_arity,
                effects,
            })
        } else {
            None
        }
    }

    fn bind_pat_locals(&mut self, pat: &Pat) {
        self.bind_pat_locals_with_shape(pat, None);
    }

    fn bind_cps_handler_arm_param_locals(&mut self, arm: &MHandlerArm) {
        for pat in &arm.params {
            let shape = self
                .local_shape_for_cps_entry_pat(pat)
                .or_else(|| self.runtime_cps_shape_for_handler_param_use(pat, arm));
            self.bind_pat_locals_with_shape(pat, shape);
        }
    }

    fn runtime_cps_shape_for_handler_param_use(
        &self,
        pat: &Pat,
        arm: &MHandlerArm,
    ) -> Option<LocalValueShape> {
        let Pat::Var { name, .. } = pat else {
            return None;
        };
        let mut arity = None;
        if !Self::collect_direct_call_arity_for_local_in_expr(name, &arm.body, &mut arity) {
            return None;
        }
        if let Some(finally_block) = &arm.finally_block
            && !Self::collect_direct_call_arity_for_local_in_expr(name, finally_block, &mut arity)
        {
            return None;
        }
        arity.map(|source_arity| LocalValueShape::RuntimeCpsCallable {
            source_arity,
            adapter_arity: source_arity + 2,
            effects: Vec::new(),
        })
    }

    fn bind_pat_locals_with_shape(&mut self, pat: &Pat, explicit_shape: Option<LocalValueShape>) {
        match pat {
            Pat::Var { id, name, .. } => {
                self.current_scope_mut().insert(name.clone());
                let shape = explicit_shape.unwrap_or_else(|| {
                    if self.pure_function_arity_at(*id).is_some() {
                        LocalValueShape::PureCallableFromUseType
                    } else if let Some((source_arity, adapter_arity, effects)) =
                        self.cps_function_arity_at(*id)
                    {
                        LocalValueShape::RuntimeCpsCallable {
                            source_arity,
                            adapter_arity,
                            effects,
                        }
                    } else {
                        LocalValueShape::PureCallableFromUseType
                    }
                });
                self.current_shape_scope_mut().insert(name.clone(), shape);
            }
            Pat::Tuple { elements, .. } => {
                for pat in elements {
                    self.bind_pat_locals_with_shape(pat, None);
                }
            }
            Pat::Constructor { args, .. } => {
                for pat in args {
                    self.bind_pat_locals_with_shape(pat, None);
                }
            }
            Pat::Record {
                fields, as_name, ..
            } => {
                if let Some(name) = as_name {
                    self.current_scope_mut().insert(name.clone());
                    self.current_shape_scope_mut()
                        .insert(name.clone(), LocalValueShape::PureCallableFromUseType);
                }
                for (field_name, pat) in fields {
                    match pat {
                        Some(pat) => self.bind_pat_locals_with_shape(pat, None),
                        None => {
                            self.current_scope_mut().insert(field_name.clone());
                            self.current_shape_scope_mut().insert(
                                field_name.clone(),
                                LocalValueShape::PureCallableFromUseType,
                            );
                        }
                    }
                }
            }
            Pat::AnonRecord { fields, .. } => {
                for (field_name, pat) in fields {
                    match pat {
                        Some(pat) => self.bind_pat_locals_with_shape(pat, None),
                        None => {
                            self.current_scope_mut().insert(field_name.clone());
                            self.current_shape_scope_mut().insert(
                                field_name.clone(),
                                LocalValueShape::PureCallableFromUseType,
                            );
                        }
                    }
                }
            }
            Pat::StringPrefix { rest, .. } => {
                self.bind_pat_locals_with_shape(rest, None);
            }
            Pat::BitStringPat { segments, .. } => {
                for segment in segments {
                    self.bind_pat_locals_with_shape(&segment.value, None);
                }
            }
            _ => {}
        }
    }

    fn expr_is_direct_subset(&mut self, expr: &MExpr) -> bool {
        match expr {
            MExpr::Pure(atom) => self.atom_is_direct_subset(atom),
            MExpr::Yield { op, args, .. } => self.native_direct_yield_is_direct_subset(op, args),
            MExpr::Let { var, value, body }
            | MExpr::Bind {
                var, value, body, ..
            } => {
                let local_shape = self.direct_local_shape_for_expr(value).or_else(|| {
                    if matches!(&**value, MExpr::Resume { .. }) {
                        self.direct_call_shape_for_local_use_in_expr(&var.name, body)
                            .or(Some(LocalValueShape::PureCallableFromUseType))
                    } else {
                        None
                    }
                });
                if !self.expr_is_direct_subset(value) {
                    return false;
                }
                self.push_scope();
                self.current_scope_mut().insert(var.name.clone());
                if let Some(shape) = local_shape {
                    self.current_shape_scope_mut()
                        .insert(var.name.clone(), shape);
                }
                let supported = self.expr_is_direct_subset(body);
                self.pop_scope();
                supported
            }
            MExpr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                self.atom_is_direct_subset(cond)
                    && self.expr_is_direct_subset(then_branch)
                    && self.expr_is_direct_subset(else_branch)
            }
            MExpr::Case {
                scrutinee, arms, ..
            } => {
                if !self.atom_is_direct_subset(scrutinee) {
                    return false;
                }
                arms.iter().all(|arm| {
                    if !direct_pat_supported(&arm.pattern) {
                        return false;
                    }
                    self.push_scope();
                    self.bind_pat_locals(&arm.pattern);
                    let supported = arm
                        .guard
                        .as_ref()
                        .is_none_or(|guard| self.expr_is_direct_subset(guard))
                        && self.expr_is_direct_subset(&arm.body);
                    self.pop_scope();
                    supported
                })
            }
            MExpr::App { head, args, .. } => {
                if self.is_panic_or_todo_call(head, args) {
                    return self.atom_is_direct_subset(&args[0]);
                }
                match self.call_shape(head) {
                    Some(CallShape::Intrinsic(intrinsic)) => {
                        direct_intrinsic_arity(intrinsic).is_some_and(|arity| arity == args.len())
                            && self.direct_intrinsic_args_are_supported(intrinsic, args)
                    }
                    Some(CallShape::Direct(callable)) => {
                        args.len() <= callable.arity
                            && self.direct_call_args_are_supported(head, args)
                    }
                    Some(CallShape::LocalCallable { arity, .. }) => {
                        args.len() <= arity && self.direct_call_args_are_supported(head, args)
                    }
                    Some(CallShape::Cps {
                        source_arity,
                        adapter_arity,
                        effects,
                        ..
                    }) => {
                        effects.is_empty()
                            && source_arity == args.len()
                            && adapter_arity == args.len() + 2
                            && self.direct_cps_call_args_are_supported(head, args)
                    }
                    Some(CallShape::LocalCpsCallable { .. }) | None => false,
                }
            }
            MExpr::BinOp { left, right, .. } => {
                self.atom_is_direct_subset(left) && self.atom_is_direct_subset(right)
            }
            MExpr::UnaryMinus { value, .. } => self.atom_is_direct_subset(value),
            MExpr::FieldAccess { record, .. } => self.atom_is_direct_subset(record),
            MExpr::RecordUpdate { record, fields, .. } => {
                self.atom_is_direct_subset(record)
                    && fields
                        .iter()
                        .all(|(_, atom)| self.atom_is_direct_subset(atom))
            }
            MExpr::ForeignCall { args, .. } => {
                args.iter().all(|arg| self.atom_is_direct_subset(arg))
            }
            MExpr::Receive { arms, after, .. } => {
                let arms_supported = arms.iter().all(|arm| {
                    if !direct_pat_supported(&arm.pattern) {
                        return false;
                    }
                    self.push_scope();
                    self.bind_pat_locals(&arm.pattern);
                    let supported = arm
                        .guard
                        .as_ref()
                        .is_none_or(|guard| self.expr_is_direct_subset(guard))
                        && self.expr_is_direct_subset(&arm.body);
                    self.pop_scope();
                    supported
                });
                arms_supported
                    && after.as_ref().is_none_or(|(timeout, body)| {
                        self.atom_is_direct_subset(timeout) && self.expr_is_direct_subset(body)
                    })
            }
            MExpr::With { handler, body, .. } => {
                (self.static_handler_is_direct_return_only(handler)
                    || self.direct_handler_kind(handler).is_some())
                    && self.expr_is_direct_subset(body)
            }
            MExpr::BitString { .. }
            | MExpr::Resume { .. }
            | MExpr::Ensure { .. }
            | MExpr::LetFun { .. }
            | MExpr::HandlerValue { .. } => false,
            MExpr::DictMethodAccess { dict, .. } => self.atom_is_direct_subset(dict),
        }
    }

    fn static_handler_is_direct_return_only(&mut self, handler: &MHandler) -> bool {
        let MHandler::Static {
            effects,
            arms,
            return_clause,
            ..
        } = handler
        else {
            return false;
        };
        if !effects.is_empty() || !arms.is_empty() {
            return false;
        }
        let Some(arm) = return_clause else {
            return true;
        };
        if arm.finally_block.is_some()
            || arm.params.len() > 1
            || arm
                .params
                .iter()
                .any(|param| !direct_param_supported(param))
        {
            return false;
        }
        self.push_scope();
        for param in &arm.params {
            self.bind_pat_locals(param);
        }
        let supported = self.expr_is_direct_subset(&arm.body);
        self.pop_scope();
        supported
    }

    fn direct_handler_kind(&self, handler: &MHandler) -> Option<DirectHandlerKind> {
        let MHandler::Native { handler, .. } = handler else {
            return None;
        };
        DirectHandlerKind::from_handler_name(handler)
    }

    fn push_native_variant_frame_for_name(&mut self, name: &str) -> bool {
        let Some(frame) = Self::native_variant_frame_for_name(name) else {
            return false;
        };
        self.direct_handler_stack.push(frame);
        true
    }

    fn native_variant_frame_for_name(name: &str) -> Option<DirectHandlerFrame> {
        let (_, suffix) = name.split_once("__native__")?;
        let (handler, effects) = suffix.split_once("__")?;
        let kind = DirectHandlerKind::from_handler_name(handler)?;
        let effects = effects
            .split("__")
            .filter(|effect| !effect.is_empty())
            .map(|effect| effect.replace('_', "."))
            .collect::<Vec<_>>();
        if effects.is_empty() {
            return None;
        }
        Some(DirectHandlerFrame::Native { effects, kind })
    }

    fn native_direct_yield_is_direct_subset(&mut self, op: &EffectOpRef, args: &[Atom]) -> bool {
        let Some(kind) = self.native_direct_handler_kind_for_yield(op) else {
            return false;
        };
        match kind {
            DirectHandlerKind::BeamActor | DirectHandlerKind::BeamSignal => {
                let Some(spec) = native_op(&op.effect, &op.op) else {
                    return false;
                };
                !spec.erl_module.is_empty()
                    && args.len() == spec.param_count
                    && args.iter().all(|arg| self.atom_is_direct_subset(arg))
            }
            DirectHandlerKind::BeamRef | DirectHandlerKind::EtsRef => {
                op.effect == "Std.Ref.Ref"
                    && match op.op.as_str() {
                        "get" => args.len() == 1 && self.atom_is_direct_subset(&args[0]),
                        "set" => {
                            args.len() == 2
                                && self.atom_is_direct_subset(&args[0])
                                && self.atom_is_direct_subset(&args[1])
                        }
                        "new" => args.len() == 1 && self.atom_is_direct_subset(&args[0]),
                        "modify" => {
                            args.len() == 2
                                && self.atom_is_direct_subset(&args[0])
                                && self.effect_protocol_arg_atom_is_cps_island_subset(&args[1])
                        }
                        _ => false,
                    }
            }
            DirectHandlerKind::BeamVec => false,
        }
    }

    fn direct_cps_call_args_are_supported(&mut self, head: &Atom, args: &[Atom]) -> bool {
        let expected_arg_shapes = self.direct_call_effectful_callback_param_shapes(head);
        if !expected_arg_shapes.iter().any(Option::is_some) {
            return false;
        }
        args.iter().enumerate().all(|(index, arg)| {
            match expected_arg_shapes.get(index).copied().flatten() {
                Some((source_arity, _adapter_arity)) => {
                    self.cps_runtime_arg_atom_is_supported(arg, source_arity)
                }
                None => self.atom_is_direct_subset(arg),
            }
        })
    }

    fn cps_runtime_arg_atom_is_supported(&mut self, atom: &Atom, source_arity: usize) -> bool {
        match atom {
            Atom::Lambda { params, body, .. } => {
                params.len() == source_arity
                    && (self.lambda_is_direct_subset(params, body)
                        || self.lambda_is_cps_subset(atom)
                        || self.lambda_is_direct_cps_island_subset(params, body))
            }
            _ => {
                self.atom_is_direct_subset(atom)
                    || self
                        .cps_value_atom_shape(atom)
                        .is_some_and(|shape| match shape {
                            LocalValueShape::RuntimeCpsCallable {
                                source_arity: actual,
                                ..
                            }
                            | LocalValueShape::CpsCallable {
                                source_arity: actual,
                                ..
                            }
                            | LocalValueShape::PureCallable { arity: actual } => {
                                actual == source_arity
                            }
                            LocalValueShape::PureCallableFromUseType => true,
                        })
            }
        }
    }

    fn expr_is_cps_island_subset(&mut self, expr: &MExpr) -> bool {
        match expr {
            MExpr::Yield { op, args, .. } => self.yield_args_are_cps_island_subset(op, args),
            MExpr::Let { var, value, body }
            | MExpr::Bind {
                var, value, body, ..
            } => {
                let value_supported = self.expr_is_direct_subset(value)
                    || self.expr_is_cps_island_subset(value)
                    || self.cps_bind_value_expr_is_supported(value);
                if !value_supported {
                    return false;
                }

                let local_shape = self
                    .direct_local_shape_for_expr(value)
                    .or_else(|| self.cps_bind_shape_for_expr(value))
                    .or_else(|| self.direct_call_shape_for_local_use_in_expr(&var.name, body));
                self.push_scope();
                self.current_scope_mut().insert(var.name.clone());
                if let Some(shape) = local_shape {
                    self.current_shape_scope_mut()
                        .insert(var.name.clone(), shape);
                }
                let supported =
                    self.expr_is_cps_island_subset(body) || self.expr_is_direct_subset(body);
                self.pop_scope();
                supported
            }
            MExpr::App { head, args, .. } => {
                if self.expr_is_direct_subset(expr) {
                    return true;
                }

                if let Some((source_arity, adapter_arity, _effects)) =
                    self.cps_lambda_arity_for_atom(head)
                    && self.lambda_is_cps_subset(head)
                {
                    return source_arity == args.len()
                        && adapter_arity == args.len() + 2
                        && args.iter().all(|arg| self.atom_is_cps_value_subset(arg));
                }

                let call_supported = match self.call_shape(head) {
                    Some(CallShape::Cps {
                        source_arity,
                        adapter_arity,
                        ..
                    })
                    | Some(CallShape::LocalCpsCallable {
                        source_arity,
                        adapter_arity,
                        ..
                    }) => source_arity == args.len() && adapter_arity == args.len() + 2,
                    _ => false,
                };
                if !call_supported {
                    return false;
                }
                self.cps_call_args_are_supported(head, args)
            }
            MExpr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                self.atom_is_direct_subset(cond)
                    && self.expr_is_cps_island_subset(then_branch)
                    && self.expr_is_cps_island_subset(else_branch)
            }
            MExpr::Case {
                scrutinee, arms, ..
            } => {
                if !self.atom_is_direct_subset(scrutinee) {
                    return false;
                }
                arms.iter().all(|arm| {
                    if !direct_pat_supported(&arm.pattern) {
                        return false;
                    }
                    self.push_scope();
                    self.bind_pat_locals(&arm.pattern);
                    let supported = arm
                        .guard
                        .as_ref()
                        .is_none_or(|guard| self.expr_is_direct_subset(guard))
                        && self.expr_is_cps_island_subset(&arm.body);
                    self.pop_scope();
                    supported
                })
            }
            MExpr::Receive { arms, after, .. } => {
                arms.iter().all(|arm| {
                    if !direct_pat_supported(&arm.pattern) {
                        return false;
                    }
                    self.push_scope();
                    self.bind_pat_locals(&arm.pattern);
                    let supported = arm
                        .guard
                        .as_ref()
                        .is_none_or(|guard| self.expr_is_direct_subset(guard))
                        && self.expr_is_cps_island_subset(&arm.body);
                    self.pop_scope();
                    supported
                }) && after.as_ref().is_none_or(|(timeout, body)| {
                    self.atom_is_direct_subset(timeout) && self.expr_is_cps_island_subset(body)
                })
            }
            MExpr::With { handler, body, .. } => {
                self.handler_is_cps_island_subset(handler) && self.expr_is_cps_island_subset(body)
            }
            MExpr::BitString { segments, .. } => segments.iter().all(|segment| {
                self.atom_is_direct_subset(&segment.value)
                    && segment
                        .size
                        .as_ref()
                        .is_none_or(|size| self.atom_is_direct_subset(size))
            }),
            MExpr::HandlerValue {
                arms,
                return_clause,
                ..
            } => self.handler_value_is_cps_island_subset(arms, return_clause.as_deref()),
            _ => self.expr_is_direct_subset(expr),
        }
    }

    fn yield_args_are_cps_island_subset(&mut self, _op: &EffectOpRef, args: &[Atom]) -> bool {
        args.iter()
            .all(|arg| self.effect_protocol_arg_atom_is_cps_island_subset(arg))
    }

    fn effect_protocol_arg_atom_is_cps_island_subset(&mut self, arg: &Atom) -> bool {
        self.atom_is_direct_subset(arg) || self.atom_is_cps_value_subset(arg)
    }

    fn handler_is_cps_island_subset(&mut self, handler: &MHandler) -> bool {
        let (arms, return_clause) = match handler {
            MHandler::Static {
                arms,
                return_clause,
                ..
            } => (arms, return_clause.as_ref()),
            MHandler::Dynamic {
                op_tuple,
                return_lambda,
                ..
            } => {
                return self.atom_is_direct_subset(op_tuple)
                    && return_lambda
                        .as_ref()
                        .is_none_or(|lambda| self.atom_is_cps_value_subset(lambda));
            }
            MHandler::Native { .. } => return self.direct_handler_kind(handler).is_some(),
            _ => return false,
        };
        if !return_clause.is_none_or(|arm| self.return_clause_is_cps_island_subset(arm)) {
            return false;
        }
        arms.iter()
            .all(|arm| self.handler_arm_is_cps_island_subset(arm))
    }

    fn return_clause_is_cps_island_subset(&mut self, arm: &MHandlerArm) -> bool {
        if arm.finally_block.is_some()
            || arm.params.len() > 1
            || arm.params.iter().any(|p| !direct_param_supported(p))
        {
            return false;
        }
        self.push_scope();
        for pat in &arm.params {
            self.bind_pat_locals(pat);
        }
        let supported =
            self.expr_is_direct_subset(&arm.body) || self.expr_is_cps_island_subset(&arm.body);
        self.pop_scope();
        supported
    }

    fn handler_arm_is_cps_island_subset(&mut self, arm: &MHandlerArm) -> bool {
        if arm.params.iter().any(|p| !direct_param_supported(p)) {
            return false;
        }
        if arm.finally_block.is_some() && Self::handler_arm_expr_contains_yield(&arm.body) {
            return false;
        }
        self.push_scope();
        self.bind_cps_handler_arm_param_locals(arm);
        let supported = match arm.finally_block.as_ref() {
            Some(finally_block) => {
                self.handler_arm_expr_is_cps_island_subset_with_finally(&arm.body, finally_block)
            }
            None => self.handler_arm_expr_is_cps_island_subset(&arm.body),
        };
        self.pop_scope();
        supported
    }

    fn handler_arm_expr_is_cps_island_subset_with_finally(
        &mut self,
        expr: &MExpr,
        finally_block: &MExpr,
    ) -> bool {
        match expr {
            MExpr::Pure(atom) => {
                self.handler_arm_atom_is_cps_island_subset(atom)
                    && self.handler_finally_expr_is_supported(finally_block)
            }
            MExpr::Resume { value, .. } => {
                self.atom_is_direct_subset(value)
                    && self.handler_finally_expr_is_supported(finally_block)
            }
            MExpr::Bind {
                var, value, body, ..
            }
            | MExpr::Let { var, value, body } => {
                let value_supported = if let MExpr::Resume {
                    value: resume_value,
                    ..
                } = &**value
                {
                    self.atom_is_direct_subset(resume_value)
                        && self.handler_finally_expr_is_supported(finally_block)
                } else {
                    self.handler_arm_expr_is_cps_island_subset(value)
                        || self.handler_arm_expr_is_cps_callback_call_subset(value)
                };
                if !value_supported {
                    return false;
                }
                let local_shape = self.direct_local_shape_for_expr(value).or_else(|| {
                    matches!(&**value, MExpr::Resume { .. })
                        .then(|| self.direct_call_shape_for_local_use_in_expr(&var.name, body))
                        .flatten()
                });
                self.push_scope();
                self.current_scope_mut().insert(var.name.clone());
                if let Some(shape) = local_shape {
                    self.current_shape_scope_mut()
                        .insert(var.name.clone(), shape);
                }
                let supported =
                    self.handler_arm_expr_is_cps_island_subset_with_finally(body, finally_block);
                self.pop_scope();
                supported
            }
            MExpr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                self.atom_is_direct_subset(cond)
                    && self.handler_arm_expr_is_cps_island_subset_with_finally(
                        then_branch,
                        finally_block,
                    )
                    && self.handler_arm_expr_is_cps_island_subset_with_finally(
                        else_branch,
                        finally_block,
                    )
            }
            MExpr::Case {
                scrutinee, arms, ..
            } => {
                if !self.atom_is_direct_subset(scrutinee) {
                    return false;
                }
                arms.iter().all(|arm| {
                    if !direct_pat_supported(&arm.pattern) {
                        return false;
                    }
                    self.push_scope();
                    self.bind_pat_locals(&arm.pattern);
                    let supported = arm
                        .guard
                        .as_ref()
                        .is_none_or(|guard| self.expr_is_direct_subset(guard))
                        && self.handler_arm_expr_is_cps_island_subset_with_finally(
                            &arm.body,
                            finally_block,
                        );
                    self.pop_scope();
                    supported
                })
            }
            MExpr::BitString { segments, .. } => {
                segments.iter().all(|segment| {
                    self.handler_arm_atom_is_cps_island_subset(&segment.value)
                        && segment
                            .size
                            .as_ref()
                            .is_none_or(|size| self.handler_arm_atom_is_cps_island_subset(size))
                }) && self.handler_finally_expr_is_supported(finally_block)
            }
            MExpr::Yield { .. } => false,
            MExpr::App { head, args, .. } if self.is_flat_map_identity_resume_app(head, args) => {
                self.handler_finally_expr_is_supported(finally_block)
            }
            _ => {
                (self.expr_is_direct_subset(expr)
                    || self.handler_arm_expr_is_cps_island_subset(expr))
                    && self.handler_finally_expr_is_supported(finally_block)
            }
        }
    }

    fn handler_finally_expr_is_supported(&mut self, expr: &MExpr) -> bool {
        self.expr_is_direct_subset(expr) || self.handler_arm_expr_is_cps_callback_call_subset(expr)
    }

    fn handler_arm_expr_is_cps_callback_call_subset(&mut self, expr: &MExpr) -> bool {
        let MExpr::App { head, args, .. } = expr else {
            return false;
        };
        matches!(
            self.call_shape(head),
            Some(CallShape::Cps { .. } | CallShape::LocalCpsCallable { .. })
        ) && args
            .iter()
            .all(|arg| self.atom_is_direct_subset(arg) || self.atom_is_cps_value_subset(arg))
    }

    fn handler_arm_expr_is_cps_island_subset(&mut self, expr: &MExpr) -> bool {
        if let MExpr::Pure(atom) = expr {
            return self.handler_arm_atom_is_cps_island_subset(atom);
        }
        if self.expr_is_direct_subset(expr) {
            return true;
        }
        match expr {
            MExpr::Yield { op, args, .. } => self.yield_args_are_cps_island_subset(op, args),
            MExpr::Resume { value, .. } => self.atom_is_direct_subset(value),
            MExpr::App { head, args, .. } => {
                self.handler_arm_expr_is_cps_callback_call_subset(expr)
                    || self.is_flat_map_identity_resume_app(head, args)
            }
            MExpr::Bind {
                var, value, body, ..
            }
            | MExpr::Let { var, value, body } => {
                let value_supported = self.handler_arm_expr_is_cps_island_subset(value)
                    || matches!(&**value, MExpr::Resume { value, .. } if self.atom_is_direct_subset(value));
                if !value_supported {
                    return false;
                }
                let local_shape = self.direct_local_shape_for_expr(value).or_else(|| {
                    matches!(&**value, MExpr::Resume { .. })
                        .then(|| self.direct_call_shape_for_local_use_in_expr(&var.name, body))
                        .flatten()
                });
                self.push_scope();
                self.current_scope_mut().insert(var.name.clone());
                if let Some(shape) = local_shape {
                    self.current_shape_scope_mut()
                        .insert(var.name.clone(), shape);
                }
                let supported = self.handler_arm_expr_is_cps_island_subset(body);
                self.pop_scope();
                supported
            }
            MExpr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                self.atom_is_direct_subset(cond)
                    && self.handler_arm_expr_is_cps_island_subset(then_branch)
                    && self.handler_arm_expr_is_cps_island_subset(else_branch)
            }
            MExpr::Case {
                scrutinee, arms, ..
            } => {
                if !self.atom_is_direct_subset(scrutinee) {
                    return false;
                }
                arms.iter().all(|arm| {
                    if !direct_pat_supported(&arm.pattern) {
                        return false;
                    }
                    self.push_scope();
                    self.bind_pat_locals(&arm.pattern);
                    let supported = arm
                        .guard
                        .as_ref()
                        .is_none_or(|guard| self.expr_is_direct_subset(guard))
                        && self.handler_arm_expr_is_cps_island_subset(&arm.body);
                    self.pop_scope();
                    supported
                })
            }
            MExpr::BitString { segments, .. } => segments.iter().all(|segment| {
                self.handler_arm_atom_is_cps_island_subset(&segment.value)
                    && segment
                        .size
                        .as_ref()
                        .is_none_or(|size| self.handler_arm_atom_is_cps_island_subset(size))
            }),
            _ => false,
        }
    }

    fn handler_arm_expr_contains_yield(expr: &MExpr) -> bool {
        match expr {
            MExpr::Yield { .. } => true,
            MExpr::Let { value, body, .. } | MExpr::Bind { value, body, .. } => {
                Self::handler_arm_expr_contains_yield(value)
                    || Self::handler_arm_expr_contains_yield(body)
            }
            MExpr::If {
                then_branch,
                else_branch,
                ..
            } => {
                Self::handler_arm_expr_contains_yield(then_branch)
                    || Self::handler_arm_expr_contains_yield(else_branch)
            }
            MExpr::Case { arms, .. } => arms
                .iter()
                .any(|arm| Self::handler_arm_expr_contains_yield(&arm.body)),
            _ => false,
        }
    }

    fn handler_arm_atom_is_cps_island_subset(&mut self, atom: &Atom) -> bool {
        match atom {
            Atom::Lambda { params, body, .. } => {
                self.handler_arm_lambda_is_cps_island_subset(params, body)
            }
            Atom::Ctor { args, .. } => args
                .iter()
                .all(|arg| self.handler_arm_atom_is_cps_island_subset(arg)),
            Atom::Tuple { elements, .. } => elements
                .iter()
                .all(|arg| self.handler_arm_atom_is_cps_island_subset(arg)),
            Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. } => fields
                .iter()
                .all(|(_, arg)| self.handler_arm_atom_is_cps_island_subset(arg)),
            Atom::BackendSpawnThunk { callback, .. } => {
                self.handler_arm_atom_is_cps_island_subset(callback)
            }
            Atom::Var { .. }
            | Atom::Lit { .. }
            | Atom::Symbol { .. }
            | Atom::QualifiedRef { .. }
            | Atom::DictRef { .. } => self.atom_is_direct_subset(atom),
            Atom::BackendAtom { .. } => true,
        }
    }

    fn handler_arm_lambda_is_cps_island_subset(&mut self, params: &[Pat], body: &MExpr) -> bool {
        if params.iter().any(|p| !direct_param_supported(p)) {
            return false;
        }
        self.push_scope();
        for pat in params {
            self.bind_pat_locals(pat);
        }
        let supported = self.handler_arm_expr_is_cps_island_subset(body);
        self.pop_scope();
        supported
    }

    fn is_flat_map_identity_resume_app(&mut self, head: &Atom, args: &[Atom]) -> bool {
        if args.len() != 2 {
            return false;
        }
        let Some(CallShape::Direct(callable)) = self.call_shape(head) else {
            return false;
        };
        if callable.arity != 2 || callable.name != "flat_map" {
            return false;
        }
        if !self.atom_is_direct_subset(&args[1]) {
            return false;
        }
        let Atom::Lambda { params, body, .. } = &args[0] else {
            return false;
        };
        self.lambda_is_identity_resume(params, body)
    }

    fn lambda_is_identity_resume(&self, params: &[Pat], body: &MExpr) -> bool {
        let [Pat::Var { name, .. }] = params else {
            return false;
        };
        matches!(
            body,
            MExpr::Resume {
                value: Atom::Var { name: var, .. },
                ..
            } if var.name == *name
        )
    }

    fn direct_intrinsic_args_are_supported(
        &mut self,
        intrinsic: IntrinsicId,
        args: &[Atom],
    ) -> bool {
        match intrinsic {
            IntrinsicId::CatchPanic => {
                matches!(
                    args,
                    [Atom::Lambda { params, body, .. }]
                        if self.lambda_is_direct_subset(params, body)
                            || self.lambda_is_pure_direct_cps_island_subset(&args[0], params, body)
                ) || args.iter().all(|arg| self.atom_is_direct_subset(arg))
            }
            IntrinsicId::PrintStdout | IntrinsicId::PrintStderr | IntrinsicId::Dbg => {
                args.iter().all(|arg| self.atom_is_direct_subset(arg))
            }
        }
    }

    fn fresh_cps_temp(&mut self, prefix: &str) -> String {
        let id = self.cps_temp_counter;
        self.cps_temp_counter += 1;
        format!("{prefix}{id}")
    }

    fn fresh_abort_marker(&mut self) -> String {
        let id = self.cps_temp_counter;
        self.cps_temp_counter += 1;
        format!("__saga_abort_{}_{}", self.current_module, id)
    }

    fn handler_arm_semantically_aborts(&self, arm: &MHandlerArm) -> bool {
        !self.expr_contains_resume(&arm.body)
            && self.handler_info.resumption.get(&arm.id) != Some(&ResumptionKind::TailResumptive)
    }

    fn handler_arm_is_optimized_tail_resume(&self, arm: &MHandlerArm) -> bool {
        !self.expr_contains_resume(&arm.body)
            && self.handler_info.resumption.get(&arm.id) == Some(&ResumptionKind::TailResumptive)
    }

    fn atom_is_direct_subset(&mut self, atom: &Atom) -> bool {
        match atom {
            Atom::Var { name, .. } => {
                let cps_callable_local = matches!(
                    self.local_shape(&name.name),
                    Some(
                        LocalValueShape::CpsCallable { .. }
                            | LocalValueShape::RuntimeCpsCallable { .. }
                    )
                );
                (self.is_local(&name.name) && !cps_callable_local)
                    || self.direct_values.contains(&name.name)
                    || self.supported_direct_call(atom).is_some()
                    || self.direct_function_value_ref(atom).is_some()
            }
            Atom::Lit { .. } | Atom::Symbol { .. } => true,
            Atom::Ctor { args, .. } => args.iter().all(|arg| self.atom_is_direct_subset(arg)),
            Atom::Tuple { elements, .. } => {
                elements.iter().all(|arg| self.atom_is_direct_subset(arg))
            }
            Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. } => fields
                .iter()
                .all(|(_, arg)| self.atom_is_direct_subset(arg)),
            Atom::Lambda { params, body, .. } => {
                self.lambda_is_direct_subset(params, body)
                    || self.lambda_is_pure_direct_cps_island_subset(atom, params, body)
            }
            Atom::QualifiedRef { .. } => self.direct_function_value_ref(atom).is_some(),
            Atom::BackendAtom { .. } => true,
            Atom::BackendSpawnThunk { callback, .. } => {
                self.effect_protocol_arg_atom_is_cps_island_subset(callback)
            }
            Atom::DictRef { .. } => self.direct_dict_constructor(atom).is_some(),
        }
    }

    fn atom_is_cps_value_subset(&mut self, atom: &Atom) -> bool {
        if matches!(atom, Atom::Lambda { .. }) {
            return self.lambda_is_cps_subset(atom) || self.atom_is_direct_subset(atom);
        }
        self.cps_value_atom_shape(atom).is_some() || self.atom_is_direct_subset(atom)
    }

    fn cps_call_args_are_supported(&mut self, head: &Atom, args: &[Atom]) -> bool {
        let expected_arg_shapes = self.cps_callback_param_shapes(head);
        let expected_arg_types = self.direct_call_param_types(head);
        args.iter().enumerate().all(|(index, arg)| {
            match expected_arg_shapes.get(index).copied().flatten() {
                Some((_source_arity, _adapter_arity)) => self.cps_callback_arg_is_supported(arg),
                None => {
                    expected_arg_types
                        .get(index)
                        .and_then(Option::as_ref)
                        .cloned()
                        .is_some_and(|ty| self.atom_is_supported_for_expected_type(arg, &ty))
                        || self.atom_is_cps_value_subset(arg)
                }
            }
        })
    }

    fn cps_callback_arg_is_supported(&mut self, atom: &Atom) -> bool {
        if let Atom::Lambda { params, body, .. } = atom {
            self.lambda_is_cps_subset(atom) || self.lambda_is_direct_subset(params, body)
        } else {
            self.cps_value_atom_shape(atom).is_some()
                || self.pure_value_atom_shape(atom).is_some()
                || self.atom_is_direct_subset(atom)
        }
    }

    fn direct_call_args_are_supported(&mut self, head: &Atom, args: &[Atom]) -> bool {
        let expected_arg_shapes = self.direct_call_effectful_callback_param_shapes(head);
        let expected_arg_types = self.direct_call_param_types(head);
        args.iter().enumerate().all(|(index, arg)| {
            match expected_arg_shapes.get(index).copied().flatten() {
                Some((_source_arity, _adapter_arity)) => self.cps_callback_arg_is_supported(arg),
                None => {
                    expected_arg_types
                        .get(index)
                        .and_then(Option::as_ref)
                        .cloned()
                        .is_some_and(|ty| self.atom_is_supported_for_expected_type(arg, &ty))
                        || self.atom_is_direct_subset(arg)
                }
            }
        })
    }

    fn direct_call_param_types(&self, head: &Atom) -> Vec<Option<Type>> {
        let source = match head {
            Atom::Var { source, .. }
            | Atom::QualifiedRef { source, .. }
            | Atom::Lambda { source, .. } => *source,
            _ => return Vec::new(),
        };
        let Some(mut current) = self.effect_info.type_at_node.get(&source) else {
            return Vec::new();
        };
        let mut params = Vec::new();
        while let Type::Fun(param, ret, _) = current {
            params.push(Some((**param).clone()));
            current = ret;
        }
        params
    }

    fn atom_is_supported_for_expected_type(&mut self, atom: &Atom, expected: &Type) -> bool {
        if self.atom_is_direct_subset(atom) {
            return true;
        }

        if self.cps_function_arity_from_type(expected).is_some() {
            return self.cps_callback_arg_is_supported(atom);
        }

        match (atom, expected) {
            (Atom::Ctor { name, args, .. }, Type::Con(type_name, type_args))
                if type_name == crate::typechecker::canonicalize_type_name("List")
                    && type_args.len() == 1 =>
            {
                match (name.as_str(), args.as_slice()) {
                    ("Nil", []) => true,
                    ("Cons", [head, tail]) => {
                        self.atom_is_supported_for_expected_type(head, &type_args[0])
                            && self.atom_is_supported_for_expected_type(tail, expected)
                    }
                    _ => false,
                }
            }
            (Atom::Tuple { elements, .. }, Type::Con(type_name, type_args))
                if type_name == crate::typechecker::canonicalize_type_name("Tuple")
                    && elements.len() == type_args.len() =>
            {
                elements.iter().zip(type_args).all(|(element, expected)| {
                    self.atom_is_supported_for_expected_type(element, expected)
                })
            }
            _ => false,
        }
    }

    fn direct_call_effectful_callback_param_shapes(
        &self,
        head: &Atom,
    ) -> Vec<Option<(usize, usize)>> {
        let source = match head {
            Atom::Var { source, .. }
            | Atom::QualifiedRef { source, .. }
            | Atom::Lambda { source, .. } => *source,
            _ => return Vec::new(),
        };
        let Some(mut current) = self.effect_info.type_at_node.get(&source) else {
            return Vec::new();
        };
        let mut shapes = Vec::new();
        while let Type::Fun(param, ret, _) = current {
            shapes.push(
                self.cps_function_arity_from_type(param)
                    .map(|(source_arity, adapter_arity, _effects)| (source_arity, adapter_arity)),
            );
            current = ret;
        }
        shapes
    }

    fn lambda_is_direct_subset(&mut self, params: &[Pat], body: &MExpr) -> bool {
        if params.iter().any(|p| !direct_param_supported(p)) {
            return false;
        }
        self.push_scope();
        for pat in params {
            self.bind_pat_locals(pat);
        }
        let supported = self.expr_is_direct_subset(body);
        self.pop_scope();
        supported
    }

    fn lambda_is_direct_cps_island_subset(&mut self, params: &[Pat], body: &MExpr) -> bool {
        if params.iter().any(|p| !direct_param_supported(p)) {
            return false;
        }
        self.push_scope();
        for pat in params {
            self.bind_pat_locals(pat);
        }
        let supported = self.expr_is_cps_island_subset(body);
        self.pop_scope();
        supported
    }

    fn lambda_is_pure_direct_cps_island_subset(
        &mut self,
        atom: &Atom,
        params: &[Pat],
        body: &MExpr,
    ) -> bool {
        self.pure_callback_arity_for_atom(atom) == Some(params.len())
            && self.lambda_is_direct_cps_island_subset(params, body)
    }

    fn lambda_is_cps_subset(&mut self, atom: &Atom) -> bool {
        let Atom::Lambda { params, body, .. } = atom else {
            return false;
        };
        if self.cps_lambda_arity_for_atom(atom).is_none()
            || params.iter().any(|p| !direct_param_supported(p))
        {
            return false;
        }
        self.push_scope();
        for pat in params {
            self.bind_pat_locals(pat);
        }
        let direct = self.expr_is_direct_subset(body);
        let supported = !direct && self.expr_is_cps_island_subset(body);
        self.pop_scope();
        supported
    }

    fn direct_local_shape_for_expr(&mut self, expr: &MExpr) -> Option<LocalValueShape> {
        match expr {
            MExpr::Pure(Atom::Lambda { params, body, .. })
                if self.lambda_is_direct_subset(params, body) =>
            {
                Some(LocalValueShape::PureCallable {
                    arity: params.len(),
                })
            }
            MExpr::DictMethodAccess {
                source,
                trait_name,
                method_index,
                ..
            } => self
                .pure_function_arity_at(*source)
                .or_else(|| self.pure_trait_method_arity(trait_name, *method_index))
                .map(|arity| LocalValueShape::PureCallable { arity }),
            MExpr::App { source, .. } => self.local_shape_for_expr_result_type(*source),
            MExpr::Resume { source, .. } | MExpr::With { source, .. } => {
                self.local_shape_for_expr_result_type(*source)
            }
            _ => None,
        }
    }

    fn local_shape_for_expr_result_type(&self, source: NodeId) -> Option<LocalValueShape> {
        let ty = self.effect_info.type_at_node.get(&source)?;
        self.local_shape_for_param_type(ty)
    }

    fn direct_call_shape_for_local_use_in_expr(
        &self,
        local: &str,
        expr: &MExpr,
    ) -> Option<LocalValueShape> {
        let mut arity = None;
        Self::collect_direct_call_arity_for_local_in_expr(local, expr, &mut arity);
        arity.map(|arity| LocalValueShape::PureCallable { arity })
    }

    fn collect_direct_call_arity_for_local_in_expr(
        local: &str,
        expr: &MExpr,
        arity: &mut Option<usize>,
    ) -> bool {
        match expr {
            MExpr::Pure(atom) => {
                Self::collect_direct_call_arity_for_local_in_atom(local, atom, arity)
            }
            MExpr::Yield { args, .. } | MExpr::ForeignCall { args, .. } => args
                .iter()
                .all(|arg| Self::collect_direct_call_arity_for_local_in_atom(local, arg, arity)),
            MExpr::Bind {
                var, value, body, ..
            }
            | MExpr::Let { var, value, body } => {
                Self::collect_direct_call_arity_for_local_in_expr(local, value, arity)
                    && (var.name == local
                        || Self::collect_direct_call_arity_for_local_in_expr(local, body, arity))
            }
            MExpr::Ensure { body, cleanup } => {
                Self::collect_direct_call_arity_for_local_in_expr(local, body, arity)
                    && Self::collect_direct_call_arity_for_local_in_expr(local, cleanup, arity)
            }
            MExpr::Case {
                scrutinee, arms, ..
            } => {
                Self::collect_direct_call_arity_for_local_in_atom(local, scrutinee, arity)
                    && arms.iter().all(|arm| {
                        arm.guard.as_ref().is_none_or(|guard| {
                            Self::collect_direct_call_arity_for_local_in_expr(local, guard, arity)
                        }) && (pat_binds_name(&arm.pattern, local)
                            || Self::collect_direct_call_arity_for_local_in_expr(
                                local, &arm.body, arity,
                            ))
                    })
            }
            MExpr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                Self::collect_direct_call_arity_for_local_in_atom(local, cond, arity)
                    && Self::collect_direct_call_arity_for_local_in_expr(local, then_branch, arity)
                    && Self::collect_direct_call_arity_for_local_in_expr(local, else_branch, arity)
            }
            MExpr::App { head, args, .. } => {
                if let Atom::Var { name, .. } = head
                    && name.name == local
                    && !Self::record_local_call_arity(arity, args.len())
                {
                    return false;
                }
                Self::collect_direct_call_arity_for_local_in_atom(local, head, arity)
                    && args.iter().all(|arg| {
                        Self::collect_direct_call_arity_for_local_in_atom(local, arg, arity)
                    })
            }
            MExpr::With { handler, body, .. } => {
                Self::collect_direct_call_arity_for_local_in_handler(local, handler, arity)
                    && Self::collect_direct_call_arity_for_local_in_expr(local, body, arity)
            }
            MExpr::Resume { value, .. }
            | MExpr::FieldAccess { record: value, .. }
            | MExpr::UnaryMinus { value, .. } => {
                Self::collect_direct_call_arity_for_local_in_atom(local, value, arity)
            }
            MExpr::RecordUpdate { record, fields, .. } => {
                Self::collect_direct_call_arity_for_local_in_atom(local, record, arity)
                    && fields.iter().all(|(_, atom)| {
                        Self::collect_direct_call_arity_for_local_in_atom(local, atom, arity)
                    })
            }
            MExpr::DictMethodAccess { dict, .. } => {
                Self::collect_direct_call_arity_for_local_in_atom(local, dict, arity)
            }
            MExpr::BinOp { left, right, .. } => {
                Self::collect_direct_call_arity_for_local_in_atom(local, left, arity)
                    && Self::collect_direct_call_arity_for_local_in_atom(local, right, arity)
            }
            MExpr::BitString { segments, .. } => segments.iter().all(|segment| {
                Self::collect_direct_call_arity_for_local_in_atom(local, &segment.value, arity)
            }),
            MExpr::Receive { arms, after, .. } => {
                arms.iter().all(|arm| {
                    arm.guard.as_ref().is_none_or(|guard| {
                        Self::collect_direct_call_arity_for_local_in_expr(local, guard, arity)
                    }) && (pat_binds_name(&arm.pattern, local)
                        || Self::collect_direct_call_arity_for_local_in_expr(
                            local, &arm.body, arity,
                        ))
                }) && after.as_ref().is_none_or(|(timeout, body)| {
                    Self::collect_direct_call_arity_for_local_in_atom(local, timeout, arity)
                        && Self::collect_direct_call_arity_for_local_in_expr(local, body, arity)
                })
            }
            MExpr::LetFun {
                name, body, rest, ..
            } => {
                let body_ok = name == local
                    || Self::collect_direct_call_arity_for_local_in_expr(local, body, arity);
                body_ok && Self::collect_direct_call_arity_for_local_in_expr(local, rest, arity)
            }
            MExpr::HandlerValue {
                arms,
                return_clause,
                ..
            } => {
                arms.iter().all(|arm| {
                    Self::collect_direct_call_arity_for_local_in_handler_arm(local, arm, arity)
                }) && return_clause.as_ref().is_none_or(|arm| {
                    Self::collect_direct_call_arity_for_local_in_handler_arm(local, arm, arity)
                })
            }
        }
    }

    fn collect_direct_call_arity_for_local_in_atom(
        local: &str,
        atom: &Atom,
        arity: &mut Option<usize>,
    ) -> bool {
        match atom {
            Atom::Var { .. }
            | Atom::Lit { .. }
            | Atom::DictRef { .. }
            | Atom::QualifiedRef { .. }
            | Atom::Symbol { .. }
            | Atom::BackendAtom { .. } => true,
            Atom::Ctor { args, .. } => args
                .iter()
                .all(|arg| Self::collect_direct_call_arity_for_local_in_atom(local, arg, arity)),
            Atom::Tuple { elements, .. } => elements
                .iter()
                .all(|arg| Self::collect_direct_call_arity_for_local_in_atom(local, arg, arity)),
            Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. } => {
                fields.iter().all(|(_, atom)| {
                    Self::collect_direct_call_arity_for_local_in_atom(local, atom, arity)
                })
            }
            Atom::Lambda { params, body, .. } => {
                params.iter().any(|param| pat_binds_name(param, local))
                    || Self::collect_direct_call_arity_for_local_in_expr(local, body, arity)
            }
            Atom::BackendSpawnThunk { callback, .. } => {
                Self::collect_direct_call_arity_for_local_in_atom(local, callback, arity)
            }
        }
    }

    fn collect_direct_call_arity_for_local_in_handler(
        local: &str,
        handler: &MHandler,
        arity: &mut Option<usize>,
    ) -> bool {
        match handler {
            MHandler::Static {
                arms,
                return_clause,
                ..
            } => {
                arms.iter().all(|arm| {
                    Self::collect_direct_call_arity_for_local_in_handler_arm(local, arm, arity)
                }) && return_clause.as_ref().is_none_or(|arm| {
                    Self::collect_direct_call_arity_for_local_in_handler_arm(local, arm, arity)
                })
            }
            MHandler::Composite { handlers, .. } => handlers.iter().all(|handler| {
                Self::collect_direct_call_arity_for_local_in_handler(local, handler, arity)
            }),
            MHandler::Dynamic {
                op_tuple,
                return_lambda,
                ..
            } => {
                Self::collect_direct_call_arity_for_local_in_atom(local, op_tuple, arity)
                    && return_lambda.as_ref().is_none_or(|return_lambda| {
                        Self::collect_direct_call_arity_for_local_in_atom(
                            local,
                            return_lambda,
                            arity,
                        )
                    })
            }
            MHandler::Native { .. } => true,
        }
    }

    fn collect_direct_call_arity_for_local_in_handler_arm(
        local: &str,
        arm: &MHandlerArm,
        arity: &mut Option<usize>,
    ) -> bool {
        arm.params.iter().any(|param| pat_binds_name(param, local))
            || (Self::collect_direct_call_arity_for_local_in_expr(local, &arm.body, arity)
                && arm.finally_block.as_ref().is_none_or(|finally_block| {
                    Self::collect_direct_call_arity_for_local_in_expr(local, finally_block, arity)
                }))
    }

    fn record_local_call_arity(arity: &mut Option<usize>, next: usize) -> bool {
        match *arity {
            Some(existing) => existing == next,
            None => {
                *arity = Some(next);
                true
            }
        }
    }

    fn cps_dict_method_shape_for_expr(&self, expr: &MExpr) -> Option<LocalValueShape> {
        let MExpr::DictMethodAccess {
            source,
            trait_name,
            method_index,
            ..
        } = expr
        else {
            return None;
        };
        let (source_arity, adapter_arity, effects) = self
            .cps_function_arity_at(*source)
            .or_else(|| self.cps_trait_method_arity(trait_name, *method_index))?;
        Some(LocalValueShape::RuntimeCpsCallable {
            source_arity,
            adapter_arity,
            effects,
        })
    }

    fn cps_local_shape_for_expr(&self, expr: &MExpr) -> Option<LocalValueShape> {
        let MExpr::Pure(atom) = expr else {
            return None;
        };
        match self.cps_function_shape(atom)? {
            CallShape::Cps {
                module,
                name,
                source_arity,
                adapter_arity,
                effects,
            } => Some(LocalValueShape::CpsCallable {
                module,
                name,
                source_arity,
                adapter_arity,
                effects,
                hof_direct_specialization: self
                    .hof_direct_specialization_for_head(atom)
                    .map(|(_, specialization)| specialization),
            }),
            _ => None,
        }
    }

    fn cps_bind_shape_for_expr(&self, expr: &MExpr) -> Option<LocalValueShape> {
        match expr {
            MExpr::Pure(atom) => {
                if self.lambda_is_cps_atom(atom) {
                    let (source_arity, adapter_arity, effects) =
                        self.cps_lambda_arity_for_atom(atom)?;
                    return Some(LocalValueShape::RuntimeCpsCallable {
                        source_arity,
                        adapter_arity,
                        effects,
                    });
                }
                if let Atom::Var { name, source } = atom {
                    match self.local_shape(&name.name) {
                        Some(
                            shape @ (LocalValueShape::CpsCallable { .. }
                            | LocalValueShape::RuntimeCpsCallable { .. }),
                        ) => return Some(shape),
                        Some(LocalValueShape::PureCallableFromUseType) => {
                            let (source_arity, adapter_arity, effects) =
                                self.cps_function_arity_at(*source)?;
                            return Some(LocalValueShape::RuntimeCpsCallable {
                                source_arity,
                                adapter_arity,
                                effects,
                            });
                        }
                        _ => {}
                    }
                }
                self.cps_local_shape_for_expr(expr)
                    .or_else(|| self.pure_value_atom_shape(atom))
            }
            MExpr::DictMethodAccess { .. } => self.cps_dict_method_shape_for_expr(expr),
            MExpr::If {
                then_branch,
                else_branch,
                ..
            } => {
                let then_shape = self.cps_bind_shape_for_expr(then_branch)?;
                let else_shape = self.cps_bind_shape_for_expr(else_branch)?;
                self.compatible_runtime_cps_shape(&then_shape, &else_shape)
            }
            MExpr::Case { arms, .. } => self.compatible_case_runtime_cps_shape(arms),
            _ => None,
        }
    }

    fn known_dict_value_for_expr(&mut self, expr: &MExpr) -> Option<KnownDictValue> {
        match expr {
            MExpr::App { head, args, .. } => {
                let Atom::DictRef { name, .. } = head else {
                    return None;
                };
                let constructor = self
                    .local_dict_constructors
                    .get(name)
                    .or_else(|| self.imported_dict_constructors.get(name))?
                    .clone();
                if constructor.dict_params.len() != args.len()
                    || args.iter().any(|arg| !self.atom_is_direct_subset(arg))
                {
                    return None;
                }

                let mut methods = Vec::with_capacity(constructor.methods.len());
                for method in &constructor.methods {
                    let MExpr::Pure(atom @ Atom::Lambda { .. }) = method else {
                        return None;
                    };
                    methods.push(atom.clone());
                }
                Some(KnownDictValue {
                    dict_params: constructor.dict_params.clone(),
                    dict_args: args.to_vec(),
                    methods,
                })
            }
            MExpr::If {
                then_branch,
                else_branch,
                ..
            } => {
                let then_dict = self.known_dict_value_for_expr(then_branch)?;
                let else_dict = self.known_dict_value_for_expr(else_branch)?;
                (then_dict == else_dict).then_some(then_dict)
            }
            _ => None,
        }
    }

    fn known_cps_lambda_for_expr(&self, expr: &MExpr) -> Option<KnownCpsLambda> {
        let MExpr::DictMethodAccess {
            dict, method_index, ..
        } = expr
        else {
            return None;
        };
        let Atom::Var { name, .. } = dict else {
            return None;
        };
        let known_dict = self.known_dict_value(&name.name)?;
        let method = known_dict.methods.get(*method_index)?.clone();
        let Atom::Lambda { params, body, .. } = method else {
            return None;
        };
        if params.iter().any(|param| !direct_param_supported(param)) {
            return None;
        }
        let dict_bindings = known_dict
            .dict_params
            .into_iter()
            .zip(known_dict.dict_args)
            .collect();
        Some(KnownCpsLambda {
            dict_bindings,
            params,
            body,
        })
    }

    fn known_direct_lambda_for_expr(&self, expr: &MExpr) -> Option<KnownDirectLambda> {
        let MExpr::DictMethodAccess {
            dict, method_index, ..
        } = expr
        else {
            return None;
        };
        let Atom::Var { name, .. } = dict else {
            return None;
        };
        let known_dict = self.known_dict_value(&name.name)?;
        let method = known_dict.methods.get(*method_index)?.clone();
        let Atom::Lambda { params, body, .. } = method else {
            return None;
        };
        if params.iter().any(|param| !direct_param_supported(param)) {
            return None;
        }
        let dict_bindings = known_dict
            .dict_params
            .into_iter()
            .zip(known_dict.dict_args)
            .collect();
        Some(KnownDirectLambda {
            dict_bindings,
            params,
            body,
        })
    }

    fn cps_bind_value_expr_is_supported(&mut self, expr: &MExpr) -> bool {
        if self.handler_value_expr_is_cps_island_subset(expr) {
            return true;
        }
        match expr {
            MExpr::Pure(atom @ Atom::Lambda { .. }) => self.lambda_is_cps_subset(atom),
            MExpr::Pure(_) => self.cps_bind_shape_for_expr(expr).is_some(),
            MExpr::DictMethodAccess { dict, .. } => {
                self.atom_is_direct_subset(dict)
                    && self.cps_dict_method_shape_for_expr(expr).is_some()
            }
            MExpr::HandlerValue {
                arms,
                return_clause,
                ..
            } => self.handler_value_is_cps_island_subset(arms, return_clause.as_deref()),
            MExpr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                self.atom_is_direct_subset(cond)
                    && self.cps_bind_value_expr_is_supported(then_branch)
                    && self.cps_bind_value_expr_is_supported(else_branch)
                    && self.cps_bind_shape_for_expr(expr).is_some()
            }
            MExpr::Case {
                scrutinee, arms, ..
            } => {
                self.atom_is_direct_subset(scrutinee)
                    && arms.iter().all(|arm| {
                        if !direct_pat_supported(&arm.pattern) {
                            return false;
                        }
                        self.push_scope();
                        self.bind_pat_locals(&arm.pattern);
                        let supported = arm
                            .guard
                            .as_ref()
                            .is_none_or(|guard| self.expr_is_direct_subset(guard))
                            && self.cps_bind_value_expr_is_supported(&arm.body);
                        self.pop_scope();
                        supported
                    })
                    && self.cps_bind_shape_for_expr(expr).is_some()
            }
            _ => false,
        }
    }

    fn handler_value_expr_is_cps_island_subset(&mut self, expr: &MExpr) -> bool {
        match expr {
            MExpr::Pure(atom) => self.handler_value_info_for_atom(atom).is_some(),
            MExpr::HandlerValue {
                arms,
                return_clause,
                ..
            } => self.handler_value_is_cps_island_subset(arms, return_clause.as_deref()),
            MExpr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                self.atom_is_direct_subset(cond)
                    && self.handler_value_expr_is_cps_island_subset(then_branch)
                    && self.handler_value_expr_is_cps_island_subset(else_branch)
            }
            _ => false,
        }
    }

    fn handler_value_info_for_atom(&self, atom: &Atom) -> Option<&HandlerValueInfo> {
        let Atom::Var { name, .. } = atom else {
            return None;
        };
        if self.is_local(&name.name) {
            return None;
        }
        self.handler_value_map.get(&name.name)
    }

    fn handler_value_is_cps_island_subset(
        &mut self,
        arms: &[MHandlerArm],
        return_clause: Option<&MHandlerArm>,
    ) -> bool {
        arms.iter()
            .all(|arm| self.handler_arm_is_cps_island_subset(arm))
            && return_clause.is_none_or(|arm| self.return_clause_is_cps_island_subset(arm))
    }

    fn compatible_case_runtime_cps_shape(&self, arms: &[MArm]) -> Option<LocalValueShape> {
        let mut shapes = arms
            .iter()
            .map(|arm| self.cps_bind_shape_for_expr(&arm.body));
        let first = shapes.next()??;
        shapes.try_fold(first, |acc, shape| {
            self.compatible_runtime_cps_shape(&acc, &shape?)
        })
    }

    fn compatible_runtime_cps_shape(
        &self,
        left: &LocalValueShape,
        right: &LocalValueShape,
    ) -> Option<LocalValueShape> {
        if let (LocalValueShape::CpsCallable { .. }, LocalValueShape::CpsCallable { .. }) =
            (left, right)
            && left == right
        {
            return Some(left.clone());
        }

        match (
            self.runtime_cps_shape_parts(left),
            self.runtime_cps_shape_parts(right),
            self.pure_callable_shape_arity(left),
            self.pure_callable_shape_arity(right),
        ) {
            (
                Some((left_source, left_adapter, left_effects)),
                Some((right_source, right_adapter, right_effects)),
                _,
                _,
            ) if left_source == right_source && left_adapter == right_adapter => {
                Some(LocalValueShape::RuntimeCpsCallable {
                    source_arity: left_source,
                    adapter_arity: left_adapter,
                    effects: merge_effect_rows(left_effects, right_effects),
                })
            }
            (Some((source_arity, adapter_arity, effects)), None, _, Some(pure_arity))
                if source_arity == pure_arity =>
            {
                Some(LocalValueShape::RuntimeCpsCallable {
                    source_arity,
                    adapter_arity,
                    effects,
                })
            }
            (None, Some((source_arity, adapter_arity, effects)), Some(pure_arity), _)
                if source_arity == pure_arity =>
            {
                Some(LocalValueShape::RuntimeCpsCallable {
                    source_arity,
                    adapter_arity,
                    effects,
                })
            }
            _ => None,
        }
    }

    fn runtime_cps_shape_parts(
        &self,
        shape: &LocalValueShape,
    ) -> Option<(usize, usize, Vec<String>)> {
        match shape {
            LocalValueShape::CpsCallable {
                source_arity,
                adapter_arity,
                effects,
                ..
            }
            | LocalValueShape::RuntimeCpsCallable {
                source_arity,
                adapter_arity,
                effects,
            } => Some((*source_arity, *adapter_arity, effects.clone())),
            LocalValueShape::PureCallable { .. } | LocalValueShape::PureCallableFromUseType => None,
        }
    }

    fn pure_callable_shape_arity(&self, shape: &LocalValueShape) -> Option<usize> {
        match shape {
            LocalValueShape::PureCallable { arity } => Some(*arity),
            LocalValueShape::PureCallableFromUseType => None,
            LocalValueShape::CpsCallable { .. } | LocalValueShape::RuntimeCpsCallable { .. } => {
                None
            }
        }
    }

    fn cps_value_atom_shape(&self, atom: &Atom) -> Option<LocalValueShape> {
        if self.lambda_is_cps_atom(atom) {
            let (source_arity, adapter_arity, effects) = self.cps_lambda_arity_for_atom(atom)?;
            return Some(LocalValueShape::RuntimeCpsCallable {
                source_arity,
                adapter_arity,
                effects,
            });
        }
        if let Atom::Var { name, source } = atom {
            match self.local_shape(&name.name) {
                Some(shape @ LocalValueShape::CpsCallable { .. }) => return Some(shape),
                Some(shape @ LocalValueShape::RuntimeCpsCallable { .. }) => return Some(shape),
                Some(LocalValueShape::PureCallableFromUseType) => {
                    let (source_arity, adapter_arity, effects) =
                        self.cps_function_arity_at(*source)?;
                    return Some(LocalValueShape::RuntimeCpsCallable {
                        source_arity,
                        adapter_arity,
                        effects,
                    });
                }
                _ => {}
            }
        }
        self.cps_local_shape_for_expr(&MExpr::Pure(atom.clone()))
    }

    fn lambda_is_cps_atom(&self, atom: &Atom) -> bool {
        matches!(atom, Atom::Lambda { .. }) && self.cps_lambda_type_arity_for_atom(atom).is_some()
    }

    fn cps_lambda_arity_for_atom(&self, atom: &Atom) -> Option<(usize, usize, Vec<String>)> {
        self.cps_lambda_type_arity_for_atom(atom)
            .or_else(|| match atom {
                Atom::Lambda { params, .. } => Some((params.len(), params.len() + 2, Vec::new())),
                _ => None,
            })
    }

    fn cps_lambda_type_arity_for_atom(&self, atom: &Atom) -> Option<(usize, usize, Vec<String>)> {
        let Atom::Lambda { source, .. } = atom else {
            return None;
        };
        self.cps_function_arity_at(*source)
    }

    fn pure_value_atom_shape(&self, atom: &Atom) -> Option<LocalValueShape> {
        if let Atom::Var { name, source } = atom {
            match self.local_shape(&name.name) {
                Some(shape @ LocalValueShape::PureCallable { .. }) => return Some(shape),
                Some(LocalValueShape::PureCallableFromUseType) => {
                    return self
                        .pure_function_arity_at(*source)
                        .map(|arity| LocalValueShape::PureCallable { arity });
                }
                _ => {}
            }
        }
        self.pure_callback_arity_for_atom(atom)
            .map(|arity| LocalValueShape::PureCallable { arity })
    }

    fn pure_callback_arity_for_atom(&self, atom: &Atom) -> Option<usize> {
        let source = match atom {
            Atom::Var { source, .. }
            | Atom::QualifiedRef { source, .. }
            | Atom::Lambda { source, .. } => *source,
            _ => return None,
        };
        self.pure_function_arity_at(source)
    }

    fn cps_callback_param_shapes(&self, head: &Atom) -> Vec<Option<(usize, usize)>> {
        let source = match head {
            Atom::Var { source, .. }
            | Atom::QualifiedRef { source, .. }
            | Atom::Lambda { source, .. } => *source,
            _ => return Vec::new(),
        };
        let Some(mut current) = self.effect_info.type_at_node.get(&source) else {
            return Vec::new();
        };
        let mut shapes = Vec::new();
        while let Type::Fun(param, ret, _) = current {
            let shape = if let Some(source_arity) = self.pure_function_arity_from_type(param) {
                Some((source_arity, source_arity + 2))
            } else {
                self.cps_function_arity_from_type(param)
                    .map(|(source_arity, adapter_arity, _effects)| (source_arity, adapter_arity))
            };
            shapes.push(shape);
            current = ret;
        }
        shapes
    }

    fn pure_trait_method_arity(&self, trait_name: &str, method_index: usize) -> Option<usize> {
        let trait_info = self.trait_info(trait_name)?;
        let method = trait_info.methods.get(method_index)?;
        method.effect_sig.effects.is_empty().then_some(())?;
        (!method.effect_sig.is_open_row).then_some(())?;
        Some(method.effect_sig.user_arity)
    }

    fn cps_trait_method_arity(
        &self,
        trait_name: &str,
        method_index: usize,
    ) -> Option<(usize, usize, Vec<String>)> {
        let trait_info = self.trait_info(trait_name)?;
        let method = trait_info.methods.get(method_index)?;
        if method.effect_sig.effects.is_empty() && !method.effect_sig.is_open_row {
            return None;
        }
        let source_arity = method.effect_sig.user_arity;
        Some((
            source_arity,
            source_arity + 2,
            method.effect_sig.effects.clone(),
        ))
    }

    fn trait_info(&self, trait_name: &str) -> Option<&crate::typechecker::TraitInfo> {
        self.effect_info
            .traits
            .get(trait_name)
            .or_else(|| {
                let bare = trait_name.rsplit('.').next().unwrap_or(trait_name);
                self.effect_info.traits.get(bare)
            })
            .or_else(|| {
                let bare = trait_name.rsplit('.').next().unwrap_or(trait_name);
                let canonical = format!("{}.{}", self.current_module, bare);
                self.effect_info.traits.get(&canonical)
            })
    }

    fn pure_function_arity_at(&self, source: NodeId) -> Option<usize> {
        self.pure_function_arity_from_type(self.effect_info.type_at_node.get(&source)?)
    }

    fn pure_function_arity_from_type(&self, ty: &Type) -> Option<usize> {
        let mut current = ty;
        let mut arity = 0;
        while let Type::Fun(_, ret, row) = current {
            if !row.effects.is_empty() || row.tail.is_some() {
                return None;
            }
            arity += 1;
            current = ret;
        }
        (arity > 0).then_some(arity)
    }

    fn cps_function_arity_at(&self, source: NodeId) -> Option<(usize, usize, Vec<String>)> {
        self.cps_function_arity_from_type(self.effect_info.type_at_node.get(&source)?)
    }

    fn cps_function_arity_from_type(&self, ty: &Type) -> Option<(usize, usize, Vec<String>)> {
        let mut current = ty;
        let mut arity = 0;
        let mut effects = Vec::new();
        let mut is_cps = false;
        while let Type::Fun(_, ret, row) = current {
            if !row.effects.is_empty() || row.tail.is_some() {
                is_cps = true;
                for effect in &row.effects {
                    if !effects.contains(&effect.name) {
                        effects.push(effect.name.clone());
                    }
                }
            }
            arity += 1;
            current = ret;
        }
        (is_cps && arity > 0).then_some((arity, arity + 2, effects))
    }

    fn callback_param_arities_from_type(&self, ty: &Type) -> Vec<Option<usize>> {
        let mut current = ty;
        let mut arities = Vec::new();
        while let Type::Fun(param, ret, _) = current {
            arities.push(
                self.cps_function_arity_from_type(param)
                    .map(|(source_arity, _, _)| source_arity),
            );
            current = ret;
        }
        arities
    }

    fn expr_contains_yield(&self, expr: &MExpr) -> bool {
        match expr {
            MExpr::Yield { .. } => true,
            MExpr::Pure(atom) | MExpr::Resume { value: atom, .. } => self.atom_contains_yield(atom),
            MExpr::Bind { value, body, .. } | MExpr::Let { value, body, .. } => {
                self.expr_contains_yield(value) || self.expr_contains_yield(body)
            }
            MExpr::Ensure { body, cleanup } => {
                self.expr_contains_yield(body) || self.expr_contains_yield(cleanup)
            }
            MExpr::Case {
                scrutinee, arms, ..
            } => {
                self.atom_contains_yield(scrutinee)
                    || arms.iter().any(|arm| {
                        arm.guard
                            .as_ref()
                            .is_some_and(|guard| self.expr_contains_yield(guard))
                            || self.expr_contains_yield(&arm.body)
                    })
            }
            MExpr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                self.atom_contains_yield(cond)
                    || self.expr_contains_yield(then_branch)
                    || self.expr_contains_yield(else_branch)
            }
            MExpr::App { head, args, .. } => {
                self.atom_contains_yield(head)
                    || args.iter().any(|arg| self.atom_contains_yield(arg))
            }
            MExpr::With { handler, body, .. } => {
                self.handler_contains_yield(handler) || self.expr_contains_yield(body)
            }
            MExpr::FieldAccess { record, .. }
            | MExpr::DictMethodAccess { dict: record, .. }
            | MExpr::RecordUpdate { record, .. } => self.atom_contains_yield(record),
            MExpr::ForeignCall { args, .. } => args.iter().any(|arg| self.atom_contains_yield(arg)),
            MExpr::BitString { segments, .. } => segments
                .iter()
                .any(|segment| self.atom_contains_yield(&segment.value)),
            MExpr::BinOp { left, right, .. } => {
                self.atom_contains_yield(left) || self.atom_contains_yield(right)
            }
            MExpr::UnaryMinus { value, .. } => self.atom_contains_yield(value),
            MExpr::Receive { .. } | MExpr::LetFun { .. } | MExpr::HandlerValue { .. } => true,
        }
    }

    fn handler_contains_yield(&self, handler: &MHandler) -> bool {
        match handler {
            MHandler::Static {
                arms,
                return_clause,
                ..
            } => {
                arms.iter().any(|arm| {
                    self.expr_contains_yield(&arm.body)
                        || arm
                            .finally_block
                            .as_ref()
                            .is_some_and(|cleanup| self.expr_contains_yield(cleanup))
                }) || return_clause
                    .as_ref()
                    .is_some_and(|arm| self.expr_contains_yield(&arm.body))
            }
            MHandler::Composite { handlers, .. } => handlers
                .iter()
                .any(|handler| self.handler_contains_yield(handler)),
            MHandler::Dynamic {
                op_tuple,
                return_lambda,
                ..
            } => {
                self.atom_contains_yield(op_tuple)
                    || return_lambda
                        .as_ref()
                        .is_some_and(|atom| self.atom_contains_yield(atom))
            }
            MHandler::Native { .. } => false,
        }
    }

    fn atom_contains_yield(&self, atom: &Atom) -> bool {
        match atom {
            Atom::Lambda { body, .. } => self.expr_contains_yield(body),
            Atom::Ctor { args, .. } | Atom::Tuple { elements: args, .. } => {
                args.iter().any(|atom| self.atom_contains_yield(atom))
            }
            Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. } => fields
                .iter()
                .any(|(_, atom)| self.atom_contains_yield(atom)),
            Atom::BackendSpawnThunk { callback, .. } => self.atom_contains_yield(callback),
            Atom::Var { .. }
            | Atom::Lit { .. }
            | Atom::Symbol { .. }
            | Atom::QualifiedRef { .. }
            | Atom::DictRef { .. }
            | Atom::BackendAtom { .. } => false,
        }
    }

    pub(super) fn atom_contains_resume(&self, atom: &Atom) -> bool {
        match atom {
            Atom::Lambda { body, .. } => self.expr_contains_resume(body),
            Atom::Ctor { args, .. } | Atom::Tuple { elements: args, .. } => {
                args.iter().any(|atom| self.atom_contains_resume(atom))
            }
            Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. } => fields
                .iter()
                .any(|(_, atom)| self.atom_contains_resume(atom)),
            Atom::BackendSpawnThunk { callback, .. } => self.atom_contains_resume(callback),
            Atom::Var { .. }
            | Atom::Lit { .. }
            | Atom::Symbol { .. }
            | Atom::QualifiedRef { .. }
            | Atom::DictRef { .. }
            | Atom::BackendAtom { .. } => false,
        }
    }

    fn expr_contains_resume(&self, expr: &MExpr) -> bool {
        match expr {
            MExpr::Resume { .. } => true,
            MExpr::Pure(atom) => self.atom_contains_resume(atom),
            MExpr::Yield { args, .. } => args.iter().any(|arg| self.atom_contains_resume(arg)),
            MExpr::Bind { value, body, .. } | MExpr::Let { value, body, .. } => {
                self.expr_contains_resume(value) || self.expr_contains_resume(body)
            }
            MExpr::Ensure { body, cleanup } => {
                self.expr_contains_resume(body) || self.expr_contains_resume(cleanup)
            }
            MExpr::Case {
                scrutinee, arms, ..
            } => {
                self.atom_contains_resume(scrutinee)
                    || arms.iter().any(|arm| {
                        arm.guard
                            .as_ref()
                            .is_some_and(|guard| self.expr_contains_resume(guard))
                            || self.expr_contains_resume(&arm.body)
                    })
            }
            MExpr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                self.atom_contains_resume(cond)
                    || self.expr_contains_resume(then_branch)
                    || self.expr_contains_resume(else_branch)
            }
            MExpr::App { head, args, .. } => {
                self.atom_contains_resume(head)
                    || args.iter().any(|arg| self.atom_contains_resume(arg))
            }
            MExpr::With { handler, body, .. } => {
                self.handler_contains_resume(handler) || self.expr_contains_resume(body)
            }
            MExpr::FieldAccess { record, .. }
            | MExpr::DictMethodAccess { dict: record, .. }
            | MExpr::RecordUpdate { record, .. } => self.atom_contains_resume(record),
            MExpr::ForeignCall { args, .. } => {
                args.iter().any(|arg| self.atom_contains_resume(arg))
            }
            MExpr::BitString { segments, .. } => segments
                .iter()
                .any(|segment| self.atom_contains_resume(&segment.value)),
            MExpr::BinOp { left, right, .. } => {
                self.atom_contains_resume(left) || self.atom_contains_resume(right)
            }
            MExpr::UnaryMinus { value, .. } => self.atom_contains_resume(value),
            MExpr::Receive { .. } | MExpr::LetFun { .. } | MExpr::HandlerValue { .. } => true,
        }
    }

    fn handler_contains_resume(&self, handler: &MHandler) -> bool {
        match handler {
            MHandler::Static {
                arms,
                return_clause,
                ..
            } => {
                arms.iter().any(|arm| {
                    self.expr_contains_resume(&arm.body)
                        || arm
                            .finally_block
                            .as_ref()
                            .is_some_and(|cleanup| self.expr_contains_resume(cleanup))
                }) || return_clause
                    .as_ref()
                    .is_some_and(|arm| self.expr_contains_resume(&arm.body))
            }
            MHandler::Composite { handlers, .. } => handlers
                .iter()
                .any(|handler| self.handler_contains_resume(handler)),
            MHandler::Dynamic {
                op_tuple,
                return_lambda,
                ..
            } => {
                self.atom_contains_resume(op_tuple)
                    || return_lambda
                        .as_ref()
                        .is_some_and(|atom| self.atom_contains_resume(atom))
            }
            MHandler::Native { .. } => false,
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
}
