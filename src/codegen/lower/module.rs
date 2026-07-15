use std::collections::HashMap;
use std::time::Instant;

use crate::ast::{self, Decl, Expr, ExprKind, Pat};
use crate::codegen::call_effects;
use crate::codegen::cerl::{CArm, CExpr, CFunDef, CLit, CModule, CPat};
use crate::codegen::runtime_shape::{CallableAbi, EvidenceAbi};

use super::init::{PendingAnnotation, extract_external};
use super::pats::lower_params;
use super::util::{self, core_var};
use super::{EvidenceFrame, FunInfo, GeneratedHelperVariant, HoistedDictMethod, Lowerer};

type Clause<'a> = (&'a [Pat], &'a Option<Box<Expr>>, &'a Expr);

fn lower_trace_enabled() -> bool {
    std::env::var_os("SAGA_BUILD_TRACE").is_some()
}

fn trace_lower_phase(module: &str, phase: &str, duration: std::time::Duration) {
    if lower_trace_enabled() {
        eprintln!(
            "[saga-lower] module={} phase={} elapsed={:.1}ms",
            module,
            phase,
            duration.as_secs_f64() * 1000.0
        );
    }
}

fn timed_lower_phase<T>(module: &str, phase: &str, f: impl FnOnce() -> T) -> T {
    if !lower_trace_enabled() {
        return f();
    }
    let start = Instant::now();
    let out = f();
    trace_lower_phase(module, phase, start.elapsed());
    out
}

/// Borrowed metadata for one `DictConstructor` decl, in the field order the
/// dict-lowering and hoist planner consume: name, dict params, superclass dicts,
/// method bodies, per-method effects, per-method open-row flags, impl-level effects.
type DictCtorMeta<'a> = (
    &'a str,
    &'a [String],
    &'a [Expr],
    &'a [Expr],
    &'a [Vec<String>],
    &'a [bool],
    &'a [String],
);

fn count_lambda_params(body: &Expr) -> usize {
    match &body.kind {
        ExprKind::Lambda { params, body, .. } => params.len() + count_lambda_params(body),
        _ => 0,
    }
}

pub(super) fn lower_head_debug_label(head: &Expr) -> String {
    match &head.kind {
        ExprKind::Var { name } => format!("var({name})"),
        ExprKind::QualifiedName { module, name, .. } => format!("qualified({module}.{name})"),
        ExprKind::DictMethodAccess {
            trait_name,
            method_index,
            ..
        } => format!("dict-method({trait_name}#{method_index})"),
        ExprKind::DictSuperAccess {
            trait_name,
            supertrait_index,
            ..
        } => format!("dict-super({trait_name}#{supertrait_index})"),
        ExprKind::Lambda { params, .. } => format!("lambda/{}", params.len()),
        ExprKind::Constructor { name } => format!("ctor({name})"),
        ExprKind::DictRef { name } => format!("dict-ref({name})"),
        ExprKind::ForeignCall { module, func, args } => {
            format!("foreign({module}.{func}/{})", args.len())
        }
        ExprKind::EffectCall {
            qualifier,
            name,
            args,
        } => format!(
            "effect-call({}{name}!/{})",
            qualifier
                .as_ref()
                .map(|qualifier| format!("{qualifier}."))
                .unwrap_or_default(),
            args.len()
        ),
        ExprKind::Lit { value } => format!("lit({value:?})"),
        ExprKind::Tuple { elements } => format!("tuple/{}", elements.len()),
        ExprKind::RecordCreate { name, fields, .. } => format!("record({name}/{})", fields.len()),
        ExprKind::AnonRecordCreate { fields } => format!("anon-record/{}", fields.len()),
        ExprKind::RecordBuild { fields, .. } => format!("record-build/{}", fields.len()),
        ExprKind::HandlerExpr { .. } => "handler-expr".to_string(),
        ExprKind::App { .. } => "app-head".to_string(),
        ExprKind::BinOp { .. } => "binop".to_string(),
        ExprKind::UnaryMinus { .. } => "unary-minus".to_string(),
        ExprKind::If { .. } => "if".to_string(),
        ExprKind::Case { .. } => "case".to_string(),
        ExprKind::Block { .. } => "block".to_string(),
        ExprKind::FieldAccess { field, .. } => format!("field-access(.{field})"),
        ExprKind::RecordUpdate { .. } => "record-update".to_string(),
        ExprKind::With { .. } => "with".to_string(),
        ExprKind::Resume { .. } => "resume".to_string(),
        ExprKind::Do { .. } => "do".to_string(),
        ExprKind::Receive { .. } => "receive".to_string(),
        ExprKind::BitString { segments } => format!("bitstring/{}", segments.len()),
        ExprKind::Ascription { .. } => "ascription".to_string(),
        ExprKind::Pipe { segments, .. } => format!("pipe/{}", segments.len()),
        ExprKind::BinOpChain { segments, .. } => format!("binop-chain/{}", segments.len()),
        ExprKind::PipeBack { segments } => format!("pipe-back/{}", segments.len()),
        ExprKind::ComposeForward { segments } => format!("compose-forward/{}", segments.len()),
        ExprKind::Cons { .. } => "cons".to_string(),
        ExprKind::ListLit { elements, .. } => format!("list/{}", elements.len()),
        ExprKind::StringInterp { parts, .. } => format!("string-interp/{}", parts.len()),
        ExprKind::ListComprehension { qualifiers, .. } => {
            format!("list-comprehension/{}", qualifiers.len())
        }
    }
}

fn is_unit_type_expr(ty: &ast::TypeExpr) -> bool {
    match ty {
        ast::TypeExpr::Named { name, .. } => {
            crate::typechecker::canonicalize_type_name(name)
                == crate::typechecker::canonicalize_type_name("Unit")
        }
        ast::TypeExpr::Labeled { inner, .. } => is_unit_type_expr(inner),
        _ => false,
    }
}

impl<'a> Lowerer<'a> {
    pub(super) fn precompute_call_effects(
        &mut self,
        module_name: &str,
        program: &ast::Program,
    ) -> call_effects::EffectAbiPlan {
        self.current_module = module_name.to_string();
        self.current_source_module = program
            .iter()
            .find_map(|decl| {
                if let Decl::ModuleDecl { path, .. } = decl {
                    Some(path.join("."))
                } else {
                    None
                }
            })
            .unwrap_or_else(|| module_name.to_string());
        self.effect_op_trace.clear();
        self.generated_helper_variants.clear();
        self.generated_hof_variants.clear();
        self.trait_spec_stats.clear();

        let mut pending_annotations = timed_lower_phase(module_name, "init_module", || {
            self.init_module(module_name, program)
        });
        let dict_constructors = timed_lower_phase(module_name, "scan_decls", || {
            self.register_call_effect_decl_metadata(program, &mut pending_annotations)
        });
        timed_lower_phase(module_name, "collect_impl_effects", || {
            self.collect_impl_effect_metadata(&dict_constructors);
        });
        let plan = timed_lower_phase(module_name, "populate_call_effects_active", || {
            self.populate_call_effects_with_check(program, self.check_result)
                .plan
        });
        self.effect_abi_plan = plan;
        timed_lower_phase(module_name, "plan_contextual_effect_abis", || {
            self.plan_contextual_function_value_abis(program)
        });
        std::mem::take(&mut self.effect_abi_plan)
    }

    fn register_call_effect_decl_metadata<'p>(
        &mut self,
        program: &'p ast::Program,
        pending_annotations: &mut HashMap<String, PendingAnnotation>,
    ) -> Vec<DictCtorMeta<'p>> {
        let mut dict_constructors: Vec<DictCtorMeta<'p>> = Vec::new();

        for decl in program {
            match decl {
                Decl::FunBinding {
                    name, params, body, ..
                } => {
                    let PendingAnnotation {
                        mut effects,
                        mut param_absorbed_effects,
                    } = pending_annotations
                        .remove(name.as_str())
                        .unwrap_or(PendingAnnotation {
                            effects: Vec::new(),
                            param_absorbed_effects: HashMap::new(),
                        });
                    let mut param_types = Vec::new();
                    if effects.is_empty()
                        && let Some(scheme) = self.check_result.env.get(name)
                    {
                        let resolved_ty = self.check_result.sub.apply(&scheme.ty);
                        effects = self.canonicalize_effects(
                            util::arity_and_effects_from_type(&resolved_ty).1,
                        );
                        param_absorbed_effects =
                            util::param_absorbed_effects_from_type(&resolved_ty)
                                .into_iter()
                                .map(|(idx, effs)| (idx, self.canonicalize_effects(effs)))
                                .collect();
                        param_types = util::param_types_from_type(&resolved_ty);
                    } else if let Some(scheme) = self.check_result.env.get(name) {
                        param_types =
                            util::param_types_from_type(&self.check_result.sub.apply(&scheme.ty));
                    }
                    let mut base_arity = lower_params(params).len() + count_lambda_params(body);
                    if let Some(scheme) = self.check_result.env.get(name) {
                        let declared_arity = util::arity_and_effects_from_type(
                            &self.check_result.sub.apply(&scheme.ty),
                        )
                        .0;
                        if declared_arity > base_arity {
                            base_arity = declared_arity;
                        }
                    }
                    let mut callable_abi = self
                        .check_result
                        .env
                        .get(name)
                        .map(|scheme| {
                            let ty = self.check_result.sub.apply(&scheme.ty);
                            CallableAbi::from_type(&ty, |effects| {
                                self.canonicalize_effects(effects)
                            })
                        })
                        .unwrap_or_else(|| {
                            if effects.is_empty() {
                                CallableAbi::pure(base_arity)
                            } else {
                                CallableAbi::cps(base_arity, EvidenceAbi::closed(effects.clone()))
                            }
                        });
                    callable_abi.user_arity = callable_abi.user_arity.max(base_arity);
                    if callable_abi.evidence.is_none() && !effects.is_empty() {
                        callable_abi.evidence = Some(EvidenceAbi::closed(effects.clone()));
                    }
                    let registered_abi = callable_abi.clone();
                    self.fun_info.entry(name.clone()).or_insert_with(|| {
                        FunInfo::from_abi(
                            registered_abi,
                            param_absorbed_effects,
                            param_types,
                            self.check_result
                                .env
                                .get(name)
                                .map(|scheme| util::dict_param_count(&scheme.constraints))
                                .unwrap_or(0),
                        )
                    });
                }
                Decl::DictConstructor {
                    name,
                    dict_params,
                    super_dicts,
                    methods,
                    method_effects,
                    method_open_rows,
                    impl_effects,
                    ..
                } => {
                    self.fun_info.insert(
                        name.clone(),
                        FunInfo::from_abi(
                            CallableAbi::pure(dict_params.len()),
                            HashMap::new(),
                            Vec::new(),
                            0,
                        ),
                    );
                    dict_constructors.push((
                        name,
                        dict_params,
                        super_dicts,
                        methods,
                        method_effects,
                        method_open_rows,
                        impl_effects,
                    ));
                }
                _ => {}
            }
        }

        dict_constructors
    }

    fn collect_impl_effect_metadata(&mut self, dict_constructors: &[DictCtorMeta<'_>]) {
        self.impl_effects_by_dict.clear();
        self.impl_method_effects_by_dict.clear();
        for (name, _, _, methods, method_effects, _, impl_effects) in dict_constructors {
            let impl_effects = self.canonicalize_effects(impl_effects.to_vec());
            self.impl_effects_by_dict
                .insert((*name).to_string(), impl_effects.clone());
            for (idx, method) in methods.iter().enumerate() {
                let mut effects =
                    self.canonicalize_effects(method_effects.get(idx).cloned().unwrap_or_default());
                if Self::contains_direct_effect_call(method) {
                    effects.extend(impl_effects.iter().cloned());
                }
                effects.sort();
                effects.dedup();
                self.impl_method_effects_by_dict
                    .insert(((*name).to_string(), idx), effects);
            }
        }
        for m in self.ctx.modules.values() {
            for d in &m.codegen_info.trait_impl_dicts {
                self.impl_effects_by_dict
                    .entry(d.dict_name.clone())
                    .or_insert_with(|| d.impl_effects.clone());
                for (idx, effects) in d.method_effects.iter().enumerate() {
                    self.impl_method_effects_by_dict
                        .entry((d.dict_name.clone(), idx))
                        .or_insert_with(|| effects.clone());
                }
            }
        }
    }

    pub fn lower_module(&mut self, module_name: &str, program: &ast::Program) -> CModule {
        self.current_module = module_name.to_string();
        self.current_source_module = program
            .iter()
            .find_map(|decl| {
                if let Decl::ModuleDecl { path, .. } = decl {
                    Some(path.join("."))
                } else {
                    None
                }
            })
            .unwrap_or_else(|| module_name.to_string());
        self.effect_op_trace.clear();
        self.generated_helper_variants.clear();
        self.generated_hof_variants.clear();
        self.trait_spec_stats.clear();
        let mut pending_annotations = timed_lower_phase(module_name, "init_module", || {
            self.init_module(module_name, program)
        });

        // Group FunBindings by name, preserving declaration order, and simultaneously
        // populate top_level_funs. Handler params are added to the arity for effectful funs.
        let mut clause_groups: Vec<(String, usize, Vec<Clause>, crate::token::Span)> = Vec::new();
        let mut dict_constructors: Vec<DictCtorMeta<'_>> = Vec::new();

        timed_lower_phase(module_name, "scan_decls", || {
            for decl in program {
                match decl {
                    Decl::FunBinding {
                        name,
                        params,
                        guard,
                        body,
                        span,
                        ..
                    } => {
                        let PendingAnnotation {
                            mut effects,
                            mut param_absorbed_effects,
                        } = pending_annotations.remove(name.as_str()).unwrap_or(
                            PendingAnnotation {
                                effects: Vec::new(),
                                param_absorbed_effects: HashMap::new(),
                            },
                        );
                        let mut param_types = Vec::new();
                        if effects.is_empty()
                            && let Some(scheme) = self.check_result.env.get(name)
                        {
                            let resolved_ty = self.check_result.sub.apply(&scheme.ty);
                            effects = self.canonicalize_effects(
                                util::arity_and_effects_from_type(&resolved_ty).1,
                            );
                            param_absorbed_effects =
                                util::param_absorbed_effects_from_type(&resolved_ty)
                                    .into_iter()
                                    .map(|(idx, effs)| (idx, self.canonicalize_effects(effs)))
                                    .collect();
                            param_types = util::param_types_from_type(&resolved_ty);
                        } else if let Some(scheme) = self.check_result.env.get(name) {
                            param_types = util::param_types_from_type(
                                &self.check_result.sub.apply(&scheme.ty),
                            );
                        }
                        let mut base_arity = lower_params(params).len() + count_lambda_params(body);
                        // For eta-reduced functions (e.g. `pg_text = coerce_value`),
                        // the binding has 0 params but the type annotation declares a
                        // higher arity. Use the annotation's arity so cross-module
                        // callers (who derive arity from the type) find the right /N.
                        if let Some(scheme) = self.check_result.env.get(name) {
                            let declared_arity = util::arity_and_effects_from_type(
                                &self.check_result.sub.apply(&scheme.ty),
                            )
                            .0;
                            if declared_arity > base_arity {
                                base_arity = declared_arity;
                            }
                        }
                        let mut callable_abi = self
                            .check_result
                            .env
                            .get(name)
                            .map(|scheme| {
                                let ty = self.check_result.sub.apply(&scheme.ty);
                                CallableAbi::from_type(&ty, |effects| {
                                    self.canonicalize_effects(effects)
                                })
                            })
                            .unwrap_or_else(|| {
                                if effects.is_empty() {
                                    CallableAbi::pure(base_arity)
                                } else {
                                    CallableAbi::cps(
                                        base_arity,
                                        EvidenceAbi::closed(effects.clone()),
                                    )
                                }
                            });
                        callable_abi.user_arity = callable_abi.user_arity.max(base_arity);
                        if callable_abi.evidence.is_none() && !effects.is_empty() {
                            callable_abi.evidence = Some(EvidenceAbi::closed(effects.clone()));
                        }
                        let arity = callable_abi.expanded_arity();
                        if let Some(group) = clause_groups.iter_mut().find(|(n, _, _, _)| n == name)
                        {
                            // Additional clause: just add to existing group
                            group.2.push((params, guard, body));
                        } else {
                            // First clause: register fun_info for arity/effects lookup.
                            self.fun_info.insert(
                                name.clone(),
                                FunInfo::from_abi(
                                    callable_abi,
                                    param_absorbed_effects,
                                    param_types,
                                    self.check_result
                                        .env
                                        .get(name)
                                        .map(|scheme| util::dict_param_count(&scheme.constraints))
                                        .unwrap_or(0),
                                ),
                            );
                            clause_groups.push((
                                name.clone(),
                                arity,
                                vec![(params, guard, body)],
                                *span,
                            ));
                        }
                    }
                    Decl::DictConstructor {
                        name,
                        dict_params,
                        super_dicts,
                        methods,
                        method_effects,
                        method_open_rows,
                        impl_effects,
                        ..
                    } => {
                        self.fun_info.insert(
                            name.clone(),
                            FunInfo::from_abi(
                                CallableAbi::pure(dict_params.len()),
                                HashMap::new(),
                                Vec::new(),
                                0,
                            ),
                        );
                        dict_constructors.push((
                            name,
                            dict_params,
                            super_dicts,
                            methods,
                            method_effects,
                            method_open_rows,
                            impl_effects,
                        ));
                    }
                    _ => {}
                }
            }
        });

        // Phase 2 trait specialization: plan which local nullary dict methods
        // to hoist into top-level functions for direct dispatch. Done before
        // body lowering so call sites can reference the hoisted names; the
        // functions themselves are emitted during dict-constructor lowering.
        timed_lower_phase(module_name, "plan_dict_method_hoists", || {
            self.plan_dict_method_hoists(&dict_constructors);
        });

        // Build dict_name -> impl_effects from the active module's
        // `DictConstructor` nodes (which carry the field directly post-
        // elaboration, since the active module may not appear in
        // `check_result.codegen_info()`) and imported modules' TraitImplDicts.
        // The per-method map keeps pure sibling methods direct even when the
        // impl has an effectful method.
        timed_lower_phase(module_name, "collect_impl_effects", || {
            self.collect_impl_effect_metadata(&dict_constructors);
        });

        // Call-effects pre-pass: tag every `App` node in the elaborated
        // program with `CallEffectInfo` so the lowerer can consume it via
        // lookup. Runs after `init_module` + per-decl `fun_info` registration
        // so all callees have arity/effect entries by the time we classify
        // their call sites.
        let call_effects = timed_lower_phase(module_name, "populate_call_effects_active", || {
            self.populate_call_effects_with_check(program, self.check_result)
        });
        if call_effects::call_effect_trace_enabled_for(&self.current_source_module) {
            eprintln!(
                "{}",
                call_effects::format_call_effect_trace(
                    &self.current_source_module,
                    &call_effects.trace
                )
            );
        }
        self.effect_abi_plan = call_effects.plan;
        timed_lower_phase(module_name, "plan_contextual_effect_abis", || {
            self.plan_contextual_function_value_abis(program)
        });
        // Cross-module inlined handler bodies live in the elaborated programs
        // of compiled modules and are lowered through the active Lowerer.
        // Tag their `App` nodes too so the parallel-check can see them.
        timed_lower_phase(module_name, "populate_call_effects_cross_modules", || {
            for (name, compiled) in self.ctx.modules.iter() {
                if compiled.effect_abi_plan_ready {
                    for (id, abi) in &compiled.effect_abi_plan.declarations {
                        self.effect_abi_plan
                            .declarations
                            .entry(*id)
                            .or_insert_with(|| abi.clone());
                    }
                    for (id, info) in &compiled.effect_abi_plan.calls {
                        self.effect_abi_plan
                            .calls
                            .entry(*id)
                            .or_insert_with(|| info.clone());
                    }
                    for (id, info) in &compiled.effect_abi_plan.function_values {
                        self.effect_abi_plan
                            .function_values
                            .entry(*id)
                            .or_insert_with(|| info.clone());
                    }
                    continue;
                }
                // Use the source module's CheckResult so type_at_span lookups in
                // the populator (e.g. for handler arm parameters) hit. The active
                // module's check_result only carries spans from its own source.
                let module_check = self
                    .check_result
                    .module_check_results()
                    .get(name)
                    .map(|result| result.as_ref())
                    .unwrap_or(self.check_result);
                let cross_call_effects =
                    self.populate_call_effects_with_check(&compiled.elaborated, module_check);
                for (id, abi) in cross_call_effects.plan.declarations {
                    self.effect_abi_plan.declarations.entry(id).or_insert(abi);
                }
                for (id, info) in cross_call_effects.plan.calls {
                    self.effect_abi_plan.calls.entry(id).or_insert(info);
                }
                for (id, info) in cross_call_effects.plan.function_values {
                    self.effect_abi_plan
                        .function_values
                        .entry(id)
                        .or_insert(info);
                }
            }
        });
        timed_lower_phase(module_name, "plan_registered_handler_effect_abis", || {
            self.plan_registered_handler_function_value_abis()
        });

        let mut exports = Vec::new();
        let mut fun_defs = Vec::new();

        // Generate wrapper functions for external declarations so cross-module
        // imports can call them by the local name.
        for decl in program {
            if let Decl::FunSignature {
                public,
                name,
                params,
                annotations,
                ..
            } = decl
            {
                let Some((erl_module, erl_func)) = extract_external(annotations) else {
                    continue;
                };
                let arity = params.len();
                let arg_vars: Vec<String> = (0..arity).map(|i| format!("_Ext{}", i)).collect();
                let call_args: Vec<CExpr> = arg_vars
                    .iter()
                    .zip(params.iter())
                    .filter(|(_, (_, ty))| !is_unit_type_expr(ty))
                    .map(|(v, _)| CExpr::Var(v.clone()))
                    .collect();
                let call = CExpr::Call(erl_module.clone(), erl_func.clone(), call_args);
                fun_defs.push(CFunDef {
                    name: name.clone(),
                    arity,
                    body: CExpr::Fun(arg_vars, Box::new(call)),
                });
                let _ = public; // privacy enforced upstream; export-all in Core
                exports.push((name.clone(), arity));
            }
        }

        for (name, arity, clauses, fun_span) in clause_groups {
            self.current_function = name.clone();
            // Export every function in the emitted Core, not just `pub` ones.
            // Privacy is a front-end concern (the typechecker/resolver already
            // rejected illegal cross-module references in source); at the Core
            // level we export everything so codegen optimizations — notably the
            // cross-module generic fold, which inlines a producer impl body whose
            // own private helpers then lower to `call 'producer':'helper'` — can
            // reach any function without a per-callee export-set computation.
            let export_fun = true;
            exports.push((name.clone(), arity));

            let callable_abi = self
                .fun_info
                .get(&name)
                .map(|info| info.abi.clone())
                .unwrap_or_else(|| crate::codegen::runtime_shape::CallableAbi::pure(arity));
            debug_assert_eq!(callable_abi.expanded_arity(), arity);
            let saved_direct_ops = std::mem::take(&mut self.direct_ops);

            let has_effects = callable_abi.evidence.is_some();
            let base_arity = callable_abi.user_arity;
            let effect_return_k = has_effects.then(|| CExpr::Var("_ReturnK".to_string()));

            // Install the evidence context for the function body. Op-call
            // emission inside the body reads handler closures out of
            // `current_evidence`.
            let saved_evidence = self.current_evidence.clone();
            if let Some(evidence_abi) = callable_abi.evidence.clone() {
                self.current_evidence = Some(EvidenceFrame::new("_Evidence", evidence_abi));
            }

            // For effectful functions, _ReturnK is threaded explicitly into
            // terminal body lowering so handler aborts bypass normal return.
            let all_simple_params = clauses.len() == 1
                && clauses[0].0.iter().all(|p| {
                    matches!(
                        p,
                        Pat::Var { .. }
                            | Pat::Wildcard { .. }
                            | Pat::Lit {
                                value: ast::Lit::Unit,
                                ..
                            }
                    )
                });
            let fun_body = if clauses.len() == 1 && clauses[0].1.is_none() && all_simple_params {
                // Single clause, no guard: emit directly without a case wrapper.
                let (params, _, body) = clauses[0];
                let mut params_ce = lower_params(params);
                let mut saved_handler_vars = Vec::new();
                for param in params {
                    saved_handler_vars.extend(self.register_dynamic_handler_pattern_vars(param));
                }
                // Absorb nested lambda params into the function's param list.
                // e.g. `f dict = fun x -> body` becomes `f(dict, x) = body`
                let mut body = body;
                while let ExprKind::Lambda {
                    params: lam_params,
                    body: lam_body,
                    ..
                } = &body.kind
                {
                    params_ce.extend(lower_params(lam_params));
                    for param in lam_params {
                        saved_handler_vars
                            .extend(self.register_dynamic_handler_pattern_vars(param));
                    }
                    body = lam_body;
                }
                // Eta-expand if the binding has fewer params than the type
                // declares (e.g. `pg_text = coerce_value` with type String -> Value).
                // Without this, the function is emitted as /0 but cross-module
                // callers derive arity from the type and call /1.
                let body_expected_ty = self.function_tail_type_after_params(&name, params_ce.len());
                let eta_count = base_arity.saturating_sub(params_ce.len());
                let eta_params: Vec<String> =
                    (0..eta_count).map(|i| format!("_Eta{}", i)).collect();
                params_ce.extend(eta_params.clone());
                if has_effects {
                    params_ce.push("_Evidence".to_string());
                    params_ce.push("_ReturnK".to_string());
                }
                let body_ce = if !eta_params.is_empty() {
                    let eta_args: Vec<CExpr> =
                        eta_params.iter().map(|p| CExpr::Var(p.clone())).collect();
                    if let Some(body_ty) = body_expected_ty {
                        let body_fun =
                            self.lower_expr_value_with_expected_type(body, Some(&body_ty));
                        let body_is_cps = self.cps_function_shape_from_type(&body_ty).is_some();
                        let mut call_args = eta_args;
                        if body_is_cps {
                            call_args.push(CExpr::Var("_Evidence".to_string()));
                            call_args.push(CExpr::Var("_ReturnK".to_string()));
                            CExpr::Apply(Box::new(body_fun), call_args)
                        } else {
                            let call = CExpr::Apply(Box::new(body_fun), call_args);
                            if has_effects {
                                CExpr::Apply(
                                    Box::new(CExpr::Var("_ReturnK".to_string())),
                                    vec![call],
                                )
                            } else {
                                call
                            }
                        }
                    } else {
                        // For non-block bodies, lower_block didn't run, so apply return_k.
                        // Special case: if the body is a terminal effect call, pass _ReturnK
                        // directly as K so abort-style handlers skip the rest (proper CPS).
                        let body_ce = if has_effects && !matches!(body.kind, ExprKind::Block { .. })
                        {
                            self.lower_terminal_effectful_expr_with_return_k(
                                body,
                                effect_return_k.clone(),
                            )
                        } else {
                            self.lower_expr_with_installed_return_k(body, effect_return_k.clone())
                        };
                        CExpr::Apply(Box::new(body_ce), eta_args)
                    }
                } else if has_effects && !matches!(body.kind, ExprKind::Block { .. }) {
                    self.lower_terminal_effectful_expr_with_return_k(body, effect_return_k.clone())
                } else {
                    self.lower_expr_with_installed_return_k(body, effect_return_k.clone())
                };
                self.restore_dynamic_handler_pattern_vars(saved_handler_vars);
                CExpr::Fun(params_ce, Box::new(body_ce))
            } else {
                // Multi-clause or single clause with a guard: generate fresh arg vars
                // and case-match on them using proper Core Erlang values syntax.
                let mut arg_vars: Vec<String> =
                    (0..base_arity).map(|i| format!("_Arg{}", i)).collect();
                if has_effects {
                    arg_vars.push("_Evidence".to_string());
                    arg_vars.push("_ReturnK".to_string());
                }

                let arms: Vec<CArm> = clauses
                    .iter()
                    .map(|(params, guard, body)| {
                        let mut saved_handler_vars = Vec::new();
                        for param in *params {
                            saved_handler_vars
                                .extend(self.register_dynamic_handler_pattern_vars(param));
                        }
                        // Pattern only matches user params, not handler params
                        let pat = if base_arity == 1 {
                            self.lower_pat(
                                &params[0],
                                &self.constructor_atoms,
                                self.handler_origin_module(),
                            )
                        } else if base_arity == 0 {
                            // No user params to match on -- use wildcard
                            CPat::Wildcard
                        } else {
                            CPat::Values(
                                params
                                    .iter()
                                    .map(|p| {
                                        self.lower_pat(
                                            p,
                                            &self.constructor_atoms,
                                            self.handler_origin_module(),
                                        )
                                    })
                                    .collect(),
                            )
                        };
                        let guard_ce = guard.as_deref().map(|g| self.lower_expr(g));
                        let body_ce = if has_effects && !matches!(body.kind, ExprKind::Block { .. })
                        {
                            self.lower_terminal_effectful_expr_with_return_k(
                                body,
                                effect_return_k.clone(),
                            )
                        } else {
                            self.lower_expr_with_installed_return_k(body, effect_return_k.clone())
                        };
                        self.restore_dynamic_handler_pattern_vars(saved_handler_vars);
                        CArm {
                            pat,
                            guard: guard_ce,
                            body: body_ce,
                        }
                    })
                    .collect();

                // Scrutinee: bare variable for base_arity==1, Values expression otherwise.
                // For effectful arity-0 functions, case on a dummy atom.
                let scrut_ce = if base_arity == 0 {
                    CExpr::Lit(CLit::Atom("unit".to_string()))
                } else if base_arity == 1 {
                    CExpr::Var(arg_vars[0].clone())
                } else {
                    CExpr::Values(
                        arg_vars[..base_arity]
                            .iter()
                            .map(|v| CExpr::Var(v.clone()))
                            .collect(),
                    )
                };
                let case_ce = CExpr::Case(Box::new(scrut_ce), arms);
                CExpr::Fun(arg_vars, Box::new(case_ce))
            };

            self.direct_ops = saved_direct_ops;
            self.current_evidence = saved_evidence;

            // fun_span is available for future use (e.g. function-level metadata)
            let _ = fun_span;
            fun_defs.push(CFunDef {
                name: name.clone(),
                arity,
                body: fun_body,
            });
            self.maybe_emit_hof_direct_variant(&name, base_arity, &clauses, export_fun);
        }

        // Emit dictionary constructor functions
        for (
            name,
            dict_params,
            super_dicts,
            methods,
            _method_effects,
            _method_open_rows,
            _impl_effects,
        ) in dict_constructors
        {
            let arity = dict_params.len();
            let params: Vec<String> = dict_params.iter().map(|p| core_var(p)).collect();
            // Each dictionary slot must match the trait method's declared
            // effect row. The impl-level `needs` clause describes what the
            // impl may use overall, but call sites dispatch by method
            // signature; leaking impl effects into pure sibling methods makes
            // those closures CPS-shaped while callers apply them directly.
            let mut method_exprs: Vec<CExpr> =
                Vec::with_capacity(super_dicts.len() + methods.len());
            for super_dict in super_dicts {
                method_exprs.push(self.lower_expr_value(super_dict));
            }
            for (idx, m) in methods.iter().enumerate() {
                let ce = self.lower_expr(m);
                // Phase 2: if this method is a planned specialization target,
                // hoist the lowered closure into a top-level function and put a
                // reference to it in the dict tuple (so dynamic dispatch still
                // works via `element/2`). Direct call sites call the hoisted
                // function instead, skipping the tuple build and extraction.
                let slot = if let Some(hoist) = self
                    .dict_method_hoists
                    .get(&(name.to_string(), idx))
                    .cloned()
                {
                    let hoisted_arity = hoist.user_arity + if hoist.is_cps { 2 } else { 0 };
                    debug_assert!(
                        matches!(&ce, CExpr::Fun(ps, _) if ps.len() == hoisted_arity),
                        "hoisted dict method {name}#{idx}: lowered arity != planned {hoisted_arity}"
                    );
                    self.generated_helper_variants.push(GeneratedHelperVariant {
                        name: hoist.fn_name.clone(),
                        arity: hoisted_arity,
                        body: ce,
                    });
                    // Export the hoisted method so importing modules can call it
                    // directly cross-module (Phase 3).
                    exports.push((hoist.fn_name.clone(), hoisted_arity));
                    CExpr::FunRef(hoist.fn_name, hoisted_arity)
                } else {
                    ce
                };
                method_exprs.push(slot);
            }
            let body = CExpr::Tuple(method_exprs);
            exports.push((name.to_string(), arity));
            fun_defs.push(CFunDef {
                name: name.to_string(),
                arity,
                body: CExpr::Fun(params, Box::new(body)),
            });
        }

        let needs_ets_ref_table = self.check_result.needs_ets_ref_table
            || self
                .check_result
                .module_check_results()
                .values()
                .any(|result| result.needs_ets_ref_table);
        let needs_vec_table = self.check_result.needs_vec_table
            || self
                .check_result
                .module_check_results()
                .values()
                .any(|result| result.needs_vec_table);

        // If this program or one of its dependencies uses ets_ref, prepend ETS
        // table creation to the entry function.
        if needs_ets_ref_table
            && let Some(entry_def) = fun_defs
                .iter_mut()
                .find(|f| f.name == "main" || f.name == "tests")
        {
            entry_def.body = Self::wrap_with_ets_init(entry_def.body.clone());
        }

        // If this program or one of its dependencies uses beam_vec, prepend ETS
        // table creation for saga_vec_store.
        if needs_vec_table
            && let Some(entry_def) = fun_defs
                .iter_mut()
                .find(|f| f.name == "main" || f.name == "tests")
        {
            entry_def.body = Self::wrap_with_vec_init(entry_def.body.clone());
        }

        fun_defs.extend(
            self.generated_helper_variants
                .drain(..)
                .map(|variant| CFunDef {
                    name: variant.name,
                    arity: variant.arity,
                    body: variant.body,
                }),
        );
        let (hof_exports, hof_funs) = self.generated_hof_fun_defs();
        exports.extend(hof_exports);
        fun_defs.extend(hof_funs);

        if call_effects::effect_op_trace_enabled_for(&self.current_source_module) {
            eprintln!(
                "{}",
                call_effects::format_effect_op_trace(
                    &self.current_source_module,
                    &self.effect_op_trace
                )
            );
        }

        if super::trait_spec_stats::stats_enabled_for(&self.current_source_module) {
            eprintln!(
                "{}",
                self.trait_spec_stats.report(&self.current_source_module)
            );
        }

        CModule {
            name: module_name.to_string(),
            exports,
            funs: fun_defs,
        }
    }

    /// Wraps a function body with idempotent ETS table initialization for `saga_ref_store`.
    fn wrap_with_ets_init(body: CExpr) -> CExpr {
        Self::wrap_with_named_ets_init(body, "saga_ref_store", "_EtsRefInit")
    }

    /// Wraps a function body with idempotent ETS table initialization for `saga_vec_store`.
    fn wrap_with_vec_init(body: CExpr) -> CExpr {
        Self::wrap_with_named_ets_init(body, "saga_vec_store", "_EtsVecInit")
    }

    /// Emits:
    /// `case ets:whereis(Table) of undefined -> ets:new(Table, [set, public, named_table]); _ -> Table end`
    fn named_ets_init(table_name: &str) -> CExpr {
        let table = CExpr::Lit(CLit::Atom(table_name.into()));
        let table_options = CExpr::Cons(
            Box::new(CExpr::Lit(CLit::Atom("set".into()))),
            Box::new(CExpr::Cons(
                Box::new(CExpr::Lit(CLit::Atom("public".into()))),
                Box::new(CExpr::Cons(
                    Box::new(CExpr::Lit(CLit::Atom("named_table".into()))),
                    Box::new(CExpr::Nil),
                )),
            )),
        );

        CExpr::Case(
            Box::new(CExpr::Call(
                "ets".to_string(),
                "whereis".to_string(),
                vec![table.clone()],
            )),
            vec![
                CArm {
                    pat: CPat::Lit(CLit::Atom("undefined".into())),
                    guard: None,
                    body: CExpr::Call(
                        "ets".to_string(),
                        "new".to_string(),
                        vec![table.clone(), table_options],
                    ),
                },
                CArm {
                    pat: CPat::Wildcard,
                    guard: None,
                    body: table,
                },
            ],
        )
    }

    fn wrap_with_named_ets_init(body: CExpr, table_name: &str, binding_name: &str) -> CExpr {
        match body {
            CExpr::Fun(params, inner_body) => CExpr::Fun(
                params,
                Box::new(CExpr::Let(
                    binding_name.to_string(),
                    Box::new(Self::named_ets_init(table_name)),
                    inner_body,
                )),
            ),
            other => other,
        }
    }

    /// Compute a dict method's runtime CPS shape: whether it takes
    /// `_Evidence`/`_ReturnK` (`is_cps`), plus the canonicalized static effect
    /// set and open-row flag used to build its `EvidenceAbi`. Centralizes the
    /// per-method effect logic so the hoist planner and the dict-constructor
    /// emitter agree on shape (and thus arity).
    pub(super) fn method_cps_shape(
        &self,
        m: &Expr,
        method_effects: &[Vec<String>],
        method_open_rows: &[bool],
        impl_effects: &[String],
        idx: usize,
    ) -> (bool, Vec<String>, bool) {
        let mut static_effects =
            self.canonicalize_effects(method_effects.get(idx).cloned().unwrap_or_default());
        if Self::contains_direct_effect_call(m) {
            static_effects.extend(self.canonicalize_effects(impl_effects.to_vec()));
        }
        static_effects.sort();
        static_effects.dedup();
        let is_open_row = method_open_rows.get(idx).copied().unwrap_or(false);
        let is_cps = !static_effects.is_empty() || is_open_row;
        (is_cps, static_effects, is_open_row)
    }

    /// Plan trait specialization: hoist every nullary (non-parameterized) dict
    /// method into a top-level function for direct dispatch.
    ///
    /// Hoisting is **supply-driven**: we hoist all local nullary dict methods,
    /// not just the ones with a local statically-known call site. The extra
    /// hoisted functions are exported (see dict-constructor lowering) so that
    /// *importing* modules can call them directly cross-module — the producer
    /// can't know which of its dicts an importer will specialize, and separate
    /// compilation means we can't go back and add them later. The body stays in
    /// its defining module (called remotely), so this needs no body cloning or
    /// private-helper policy. Only nullary dicts qualify: their methods capture
    /// no dict params, so hoisting to a top-level function is capture-free.
    /// Parameterized dicts stay on the `element/2` path until a later phase.
    fn plan_dict_method_hoists(&mut self, dict_constructors: &[DictCtorMeta<'_>]) {
        self.dict_method_hoists.clear();
        let mut hoists = HashMap::new();
        for &(name, dict_params, _, methods, method_effects, method_open_rows, impl_effects) in
            dict_constructors
        {
            if !dict_params.is_empty() {
                continue; // parameterized dict: method captures sub-dicts (later phase)
            }
            for (idx, m) in methods.iter().enumerate() {
                let ExprKind::Lambda { params, .. } = &m.kind else {
                    continue;
                };
                let (is_cps, _, _) =
                    self.method_cps_shape(m, method_effects, method_open_rows, impl_effects, idx);
                // Keep the full dict name in the hoisted name (so it appears as
                // a clean substring — useful for debugging and dispatch-coherence
                // checks). Dict names are unique, so this is unique per method.
                hoists.insert(
                    (name.to_string(), idx),
                    HoistedDictMethod {
                        fn_name: format!("__saga_dictmethod_{name}_{idx}"),
                        user_arity: params.len(),
                        is_cps,
                    },
                );
            }
        }
        self.dict_method_hoists = hoists;
    }
}
