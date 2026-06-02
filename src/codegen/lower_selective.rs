//! Experimental direct-first lowerer for the selective-uniform spike.
//!
//! This module is intentionally incomplete. It lowers the closed,
//! operationally-direct subset needed to inspect direct `/N` function shape,
//! plus the first tiny CPS island shape: a CPS-typed function body made of one
//! effect operation `Yield`.
//!
//! Handlers, binds, resumes, lambdas, general dictionaries, and partial
//! application should fail loudly here until they are deliberately
//! reintroduced.

use std::collections::{BTreeMap, HashMap, HashSet};

mod cps;
mod direct;
mod support;

use crate::ast::{Lit, NodeId, Pat};
use crate::codegen::CodegenContext;
use crate::codegen::cerl::{CArm, CExpr, CFunDef, CLit, CModule, CPat};
use crate::codegen::lower::util::{core_var, lower_lit_atom, mangle_ctor_atom};
use crate::codegen::monadic::ir::{
    Atom, EffectInfo, EffectOpRef, MArm, MDecl, MExpr, MFunBinding, MHandler, MHandlerArm,
    MProgram, MVar,
};
use crate::codegen::resolve::{ConstructorAtoms, ResolutionMap, ResolvedCodegenKind};
use crate::codegen::runtime_shape::RuntimeFunctionShape;
use crate::intrinsics::IntrinsicId;
use crate::typechecker::Type;

use support::*;

pub fn lower_module(
    module_name: &str,
    program: &MProgram,
    resolution: &ResolutionMap,
    ctors: &ConstructorAtoms,
    module_ctx: &CodegenContext,
    effect_info: &EffectInfo<'_>,
) -> CModule {
    lower_module_with_entry_export(
        module_name,
        program,
        resolution,
        ctors,
        module_ctx,
        effect_info,
        None,
    )
}

pub fn lower_module_with_entry_export(
    module_name: &str,
    program: &MProgram,
    resolution: &ResolutionMap,
    ctors: &ConstructorAtoms,
    module_ctx: &CodegenContext,
    effect_info: &EffectInfo<'_>,
    entry_export: Option<&str>,
) -> CModule {
    let mut lowerer = DirectLowerer::new(resolution, ctors, module_ctx, effect_info);
    lowerer.lower_module(module_name, program, entry_export)
}

struct DirectLowerer<'a, 'info> {
    resolution: &'a ResolutionMap,
    ctors: &'a ConstructorAtoms,
    module_ctx: &'a CodegenContext,
    effect_info: &'a EffectInfo<'info>,
    current_module: String,
    /// Declared callable shape from type/effect metadata.
    ///
    /// This can be CPS even when the implementation body is direct-lowerable.
    callable_type_shapes: HashMap<String, RuntimeFunctionShape>,
    direct_values: HashSet<String>,
    /// Per-function lowering decision for the implementation body.
    function_plans: HashMap<String, FunctionLoweringPlan>,
    /// Emitted entries for functions in the module currently being lowered.
    local_function_entries: HashMap<String, FunctionEntryInfo>,
    /// Emitted entries discovered for already-compiled imported user modules.
    imported_function_entries: HashMap<(String, String), FunctionEntryInfo>,
    /// Function currently being tested as a direct-body candidate.
    ///
    /// During fixed-point classification this permits recursive self-calls
    /// before the function has been added to `function_plans`.
    direct_candidate_function: Option<String>,
    cps_temp_counter: usize,
    locals: Vec<HashSet<String>>,
    local_shapes: Vec<HashMap<String, LocalValueShape>>,
}

impl<'a, 'info> DirectLowerer<'a, 'info> {
    fn new(
        resolution: &'a ResolutionMap,
        ctors: &'a ConstructorAtoms,
        module_ctx: &'a CodegenContext,
        effect_info: &'a EffectInfo<'info>,
    ) -> Self {
        Self {
            resolution,
            ctors,
            module_ctx,
            effect_info,
            current_module: String::new(),
            callable_type_shapes: HashMap::new(),
            direct_values: HashSet::new(),
            function_plans: HashMap::new(),
            local_function_entries: HashMap::new(),
            imported_function_entries: HashMap::new(),
            direct_candidate_function: None,
            cps_temp_counter: 0,
            locals: vec![HashSet::new()],
            local_shapes: vec![HashMap::new()],
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

        self.assert_no_unlowered_direct_body_functions(program);
        self.assert_no_unlowered_public_cps_functions(program, &is_public, &is_entry);

        let mut exports = Vec::new();
        let mut funs = Vec::new();
        for decl in program {
            match decl {
                MDecl::FunBinding(fb) => {
                    let Some(plan) = self.function_plans.get(&fb.name).copied() else {
                        continue;
                    };
                    if fb.public || is_public(&fb.name) || is_entry(&fb.name) {
                        exports.extend(self.export_entries(&fb.name));
                    }
                    match plan {
                        FunctionLoweringPlan::DirectBody => {
                            funs.push(self.lower_fun_binding(fb));
                            if self.needs_cps_adapter(&fb.name) {
                                funs.push(self.lower_cps_adapter(fb));
                            }
                        }
                        FunctionLoweringPlan::DirectBodyWithCpsIsland => {
                            funs.push(self.lower_direct_cps_island_fun_binding(fb));
                        }
                        FunctionLoweringPlan::CpsBody => {
                            funs.push(self.lower_cps_fun_binding(fb));
                        }
                    }
                }
                MDecl::Val(v) => {
                    if !self.direct_values.contains(&v.name) {
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
                }
                MDecl::DictConstructor(_) => self.unsupported("dict constructors"),
                MDecl::Passthrough(_) => {}
            }
        }

        CModule {
            name: module_name.to_string(),
            exports,
            funs,
        }
    }

    fn classify_program(&mut self, program: &MProgram) {
        self.callable_type_shapes.clear();
        self.direct_values.clear();
        self.function_plans.clear();
        for decl in program {
            match decl {
                MDecl::FunBinding(fb) => {
                    let shape = match self.effect_info.fun_effects.get(&fb.name) {
                        Some(effects) if effects.is_empty() => RuntimeFunctionShape::Pure,
                        Some(effects) => {
                            RuntimeFunctionShape::Cps(crate::codegen::runtime_shape::CpsShape {
                                static_effects: effects.iter().cloned().collect(),
                                is_open_row: false,
                            })
                        }
                        None => {
                            RuntimeFunctionShape::Cps(crate::codegen::runtime_shape::CpsShape {
                                static_effects: vec![],
                                is_open_row: true,
                            })
                        }
                    };
                    self.callable_type_shapes.insert(fb.name.clone(), shape);
                }
                MDecl::Val(v) => {
                    if self.expr_is_direct_subset(&v.value) {
                        self.direct_values.insert(v.name.clone());
                    }
                }
                MDecl::DictConstructor(_) | MDecl::Passthrough(_) => {}
            }
        }
    }

    fn compute_function_lowering_plans(&mut self, program: &MProgram) {
        self.compute_direct_body_plans(program);
        self.compute_direct_cps_island_body_plans(program);
        self.compute_cps_body_plans(program);
    }

    fn compute_direct_body_plans(&mut self, program: &MProgram) {
        let funs: Vec<&MFunBinding> = program
            .iter()
            .filter_map(|decl| match decl {
                MDecl::FunBinding(fb) => Some(fb),
                _ => None,
            })
            .collect();

        let mut changed = true;
        while changed {
            changed = false;
            for fb in &funs {
                if self.function_plans.contains_key(&fb.name) {
                    continue;
                }
                if self.can_lower_fun_binding(fb) {
                    self.function_plans
                        .insert(fb.name.clone(), FunctionLoweringPlan::DirectBody);
                    changed = true;
                }
            }
        }
    }

    fn compute_cps_body_plans(&mut self, program: &MProgram) {
        for decl in program {
            let MDecl::FunBinding(fb) = decl else {
                continue;
            };
            if self.function_plans.contains_key(&fb.name) {
                continue;
            }
            if self.can_lower_cps_fun_binding(fb) {
                self.function_plans
                    .insert(fb.name.clone(), FunctionLoweringPlan::CpsBody);
            }
        }
    }

    fn compute_direct_cps_island_body_plans(&mut self, program: &MProgram) {
        for decl in program {
            let MDecl::FunBinding(fb) = decl else {
                continue;
            };
            if self.function_plans.contains_key(&fb.name) {
                continue;
            }
            if self.can_lower_direct_cps_island_fun_binding(fb) {
                self.function_plans.insert(
                    fb.name.clone(),
                    FunctionLoweringPlan::DirectBodyWithCpsIsland,
                );
            }
        }
    }

    fn compute_local_function_entries(&mut self, program: &MProgram) {
        self.local_function_entries.clear();
        for decl in program {
            let MDecl::FunBinding(fb) = decl else {
                continue;
            };
            let callable_type_shape = self
                .callable_type_shapes
                .get(&fb.name)
                .cloned()
                .unwrap_or_else(|| {
                    RuntimeFunctionShape::Cps(crate::codegen::runtime_shape::CpsShape {
                        static_effects: vec![],
                        is_open_row: true,
                    })
                });
            let entries = FunctionEntryInfo::from_fun_binding(
                fb,
                callable_type_shape,
                self.function_plans.get(&fb.name).copied(),
            );
            self.local_function_entries.insert(fb.name.clone(), entries);
        }
    }

    fn compute_imported_function_entries(&mut self) {
        self.imported_function_entries.clear();
        for (source_module_name, compiled) in &self.module_ctx.modules {
            if source_module_name == &self.current_module
                || source_module_name.starts_with("Std.")
                || compiled.elaborated.is_empty()
            {
                continue;
            }

            let anf_imported = crate::codegen::anf::normalize(
                compiled.elaborated.clone(),
                Some(&compiled.resolution),
            );
            let imported_handler_decls = HashMap::new();
            let (monadic_imported, _) = crate::codegen::monadic::translate::translate_with_imports(
                &anf_imported,
                &compiled.resolution,
                self.effect_info,
                &imported_handler_decls,
            );

            let mut imported = DirectLowerer::new(
                &compiled.resolution,
                self.ctors,
                self.module_ctx,
                self.effect_info,
            );
            imported.current_module = source_module_name.clone();
            imported.classify_program(&monadic_imported);
            imported.compute_function_lowering_plans(&monadic_imported);
            imported.compute_local_function_entries(&monadic_imported);

            let erlang_module = erlang_module_name(source_module_name);
            for (name, entries) in imported.local_function_entries {
                self.imported_function_entries
                    .insert((erlang_module.clone(), name.clone()), entries.clone());
                self.imported_function_entries
                    .insert((source_module_name.clone(), name.clone()), entries);
            }
        }
    }

    fn assert_no_unlowered_direct_body_functions(&self, program: &MProgram) {
        for decl in program {
            let MDecl::FunBinding(fb) = decl else {
                continue;
            };
            if self
                .local_function_entries
                .get(&fb.name)
                .is_some_and(|entries| {
                    matches!(entries.callable_type_shape, RuntimeFunctionShape::Pure)
                        && entries.direct_entry_arity.is_none()
                })
            {
                self.unsupported(&format!(
                    "direct function '{}' is outside the current direct subset",
                    fb.name
                ));
            }
        }
    }

    fn assert_no_unlowered_public_cps_functions(
        &self,
        program: &MProgram,
        is_public: &impl Fn(&str) -> bool,
        is_entry: &impl Fn(&str) -> bool,
    ) {
        for decl in program {
            let MDecl::FunBinding(fb) = decl else {
                continue;
            };
            if (fb.public || is_public(&fb.name) || is_entry(&fb.name))
                && self
                    .local_function_entries
                    .get(&fb.name)
                    .is_some_and(|entries| {
                        entries.is_cps_typed() && entries.cps_adapter_entry_arity.is_none()
                    })
            {
                self.unsupported(&format!(
                    "CPS-shaped function '{}' is not lowered by selective-core yet",
                    fb.name
                ));
            }
        }
    }

    fn can_lower_fun_binding(&mut self, fb: &MFunBinding) -> bool {
        if fb.guard.is_some() || fb.params.iter().any(|p| !direct_param_supported(p)) {
            return false;
        }

        let prev_direct_candidate = self.direct_candidate_function.replace(fb.name.clone());
        self.push_scope();
        self.bind_fun_param_locals(fb);
        let supported = self.expr_is_direct_subset(&fb.body);
        self.pop_scope();
        self.direct_candidate_function = prev_direct_candidate;
        supported
    }

    fn can_lower_cps_fun_binding(&mut self, fb: &MFunBinding) -> bool {
        if fb.guard.is_some() || fb.params.iter().any(|p| !direct_param_supported(p)) {
            return false;
        }
        if !matches!(
            self.callable_type_shapes.get(&fb.name),
            Some(RuntimeFunctionShape::Cps(_))
        ) {
            return false;
        }

        self.push_scope();
        self.bind_fun_param_locals(fb);
        let supported = self.expr_is_cps_island_subset(&fb.body);
        self.pop_scope();
        supported
    }

    fn can_lower_direct_cps_island_fun_binding(&mut self, fb: &MFunBinding) -> bool {
        if fb.guard.is_some() || fb.params.iter().any(|p| !direct_param_supported(p)) {
            return false;
        }
        if !matches!(
            self.callable_type_shapes.get(&fb.name),
            Some(RuntimeFunctionShape::Pure)
        ) {
            return false;
        }

        self.push_scope();
        self.bind_fun_param_locals(fb);
        let supported = self.expr_is_cps_island_subset(&fb.body);
        self.pop_scope();
        supported
    }

    fn lower_fun_binding(&mut self, fb: &MFunBinding) -> CFunDef {
        let params = lower_param_names(&fb.params);
        self.push_scope();
        self.bind_fun_param_locals(fb);
        let lowered_body = self.lower_expr(&fb.body);
        let body = self.wrap_param_match(&fb.params, &params, lowered_body);
        self.pop_scope();
        CFunDef {
            name: self.direct_entry_name(&fb.name),
            arity: params.len(),
            body: CExpr::Fun(params, Box::new(body)),
        }
    }

    fn lower_cps_adapter(&self, fb: &MFunBinding) -> CFunDef {
        let direct_params = lower_param_names(&fb.params);
        let mut params = direct_params.clone();
        params.push("_Evidence".to_string());
        params.push("_ReturnK".to_string());
        let direct_call = CExpr::Apply(
            Box::new(CExpr::FunRef(
                self.direct_entry_name(&fb.name),
                direct_params.len(),
            )),
            direct_params.into_iter().map(CExpr::Var).collect(),
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

    fn lower_direct_cps_island_fun_binding(&mut self, fb: &MFunBinding) -> CFunDef {
        let params = lower_param_names(&fb.params);

        self.push_scope();
        self.bind_fun_param_locals(fb);
        let return_k = self.identity_cps_continuation();
        let lowered_body = self.lower_cps_expr(&fb.body, CExpr::Tuple(vec![]), return_k);
        let body = self.wrap_param_match(&fb.params, &params, lowered_body);
        self.pop_scope();

        CFunDef {
            name: self.direct_entry_name(&fb.name),
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

        self.push_scope();
        self.bind_fun_param_locals(fb);
        let lowered_body = self.lower_cps_expr(
            &fb.body,
            CExpr::Var("_Evidence".to_string()),
            CExpr::Var("_ReturnK".to_string()),
        );
        let body = self.wrap_param_match(&fb.params, &direct_params, lowered_body);
        self.pop_scope();

        CFunDef {
            name: fb.name.clone(),
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
        if let Some(cps) = self.cps_function_shape(head) {
            return Some(cps);
        }
        if let Atom::Var { name, .. } = head
            && let Some(LocalValueShape::CpsCallable {
                module,
                name: adapter_name,
                source_arity,
                adapter_arity,
                effects,
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
            }) = self.local_shape(&name.name)
        {
            return Some(CallShape::LocalCpsCallable {
                name: name.name.clone(),
                source_arity,
                adapter_arity,
            });
        }
        if let Atom::Var { name, source } = head
            && matches!(
                self.local_shape(&name.name),
                Some(LocalValueShape::PureCallableFromUseType)
            )
            && let Some((source_arity, adapter_arity, _effects)) =
                self.cps_function_arity_at(*source)
        {
            return Some(CallShape::LocalCpsCallable {
                name: name.name.clone(),
                source_arity,
                adapter_arity,
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
        if module.is_none()
            && let Some(RuntimeFunctionShape::Cps(shape)) = self.callable_type_shapes.get(name)
        {
            return Some(CallShape::Cps {
                module,
                name: name.clone(),
                source_arity: *arity,
                adapter_arity: *arity + 2,
                effects: shape.static_effects.clone(),
            });
        }
        if effects.is_empty() {
            return None;
        }
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
                effects: effects.clone(),
            });
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
        let source = match head {
            Atom::DictRef { source, .. } => *source,
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
        let is_remote = erlang_mod
            .as_ref()
            .is_some_and(|module| module != &self.current_module);
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

        let recursive_self = self
            .direct_candidate_function
            .as_ref()
            .is_some_and(|current| current == name);
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

    fn direct_function_value_ref(&self, head: &Atom) -> Option<CExpr> {
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
    }

    fn pop_scope(&mut self) {
        self.locals.pop();
        self.local_shapes.pop();
    }

    fn current_scope_mut(&mut self) -> &mut HashSet<String> {
        self.locals.last_mut().expect("direct lowerer has a scope")
    }

    fn current_shape_scope_mut(&mut self) -> &mut HashMap<String, LocalValueShape> {
        self.local_shapes
            .last_mut()
            .expect("direct lowerer has a local-shape scope")
    }

    fn bind_fun_param_locals(&mut self, fb: &MFunBinding) {
        let param_shapes = self.param_shapes_for_fun(fb);
        for (index, pat) in fb.params.iter().enumerate() {
            self.bind_pat_locals_with_shape(pat, param_shapes.get(index).cloned().flatten());
        }
    }

    fn param_shapes_for_fun(&self, fb: &MFunBinding) -> Vec<Option<LocalValueShape>> {
        let Some(mut current) = self.effect_info.type_at_node.get(&fb.id) else {
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
        } else if let Some((source_arity, adapter_arity, _effects)) =
            self.cps_function_arity_from_type(ty)
        {
            Some(LocalValueShape::RuntimeCpsCallable {
                source_arity,
                adapter_arity,
            })
        } else {
            None
        }
    }

    fn bind_pat_locals(&mut self, pat: &Pat) {
        self.bind_pat_locals_with_shape(pat, None);
    }

    fn bind_pat_locals_with_shape(&mut self, pat: &Pat, explicit_shape: Option<LocalValueShape>) {
        match pat {
            Pat::Var { id, name, .. } => {
                self.current_scope_mut().insert(name.clone());
                let shape = explicit_shape.unwrap_or_else(|| {
                    if self.pure_function_arity_at(*id).is_some() {
                        LocalValueShape::PureCallableFromUseType
                    } else if let Some((source_arity, adapter_arity, _effects)) =
                        self.cps_function_arity_at(*id)
                    {
                        LocalValueShape::RuntimeCpsCallable {
                            source_arity,
                            adapter_arity,
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
            _ => {}
        }
    }

    fn expr_is_direct_subset(&mut self, expr: &MExpr) -> bool {
        match expr {
            MExpr::Pure(atom) => self.atom_is_direct_subset(atom),
            MExpr::Let { var, value, body }
            | MExpr::Bind {
                var, value, body, ..
            } => {
                let local_shape = self.direct_local_shape_for_expr(value);
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
                let direct_call_supported = match self.call_shape(head) {
                    Some(CallShape::Intrinsic(intrinsic)) => {
                        direct_intrinsic_arity(intrinsic).is_some_and(|arity| arity == args.len())
                    }
                    Some(CallShape::Direct(callable)) => callable.arity == args.len(),
                    Some(CallShape::LocalCallable { arity, .. }) => arity == args.len(),
                    Some(CallShape::Cps { .. })
                    | Some(CallShape::LocalCpsCallable { .. })
                    | None => false,
                };
                direct_call_supported && args.iter().all(|arg| self.atom_is_direct_subset(arg))
            }
            MExpr::BinOp { left, right, .. } => {
                self.atom_is_direct_subset(left) && self.atom_is_direct_subset(right)
            }
            MExpr::UnaryMinus { value, .. } => self.atom_is_direct_subset(value),
            MExpr::FieldAccess { record, .. } => self.atom_is_direct_subset(record),
            MExpr::RecordUpdate { .. }
            | MExpr::ForeignCall { .. }
            | MExpr::BitString { .. }
            | MExpr::Yield { .. }
            | MExpr::With { .. }
            | MExpr::Resume { .. }
            | MExpr::Ensure { .. }
            | MExpr::Receive { .. }
            | MExpr::LetFun { .. }
            | MExpr::HandlerValue { .. } => false,
            MExpr::DictMethodAccess { dict, .. } => self.atom_is_direct_subset(dict),
        }
    }

    fn expr_is_cps_island_subset(&mut self, expr: &MExpr) -> bool {
        match expr {
            MExpr::Yield { args, .. } => args.iter().all(|arg| self.atom_is_cps_value_subset(arg)),
            MExpr::Bind {
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
                    .or_else(|| self.cps_bind_shape_for_expr(value));
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
                call_supported && args.iter().all(|arg| self.atom_is_cps_value_subset(arg))
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
            MExpr::With { handler, body, .. } => {
                self.handler_is_cps_island_subset(handler) && self.expr_is_cps_island_subset(body)
            }
            _ => self.expr_is_direct_subset(expr),
        }
    }

    fn handler_is_cps_island_subset(&mut self, handler: &MHandler) -> bool {
        let MHandler::Static {
            arms,
            return_clause,
            ..
        } = handler
        else {
            return false;
        };
        let return_supported = return_clause
            .as_ref()
            .is_none_or(|arm| self.return_clause_is_cps_island_subset(arm));
        if !return_supported {
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
        if let Some(finally_block) = &arm.finally_block
            && !self.expr_is_direct_subset(finally_block)
        {
            return false;
        }
        self.push_scope();
        for pat in &arm.params {
            self.bind_pat_locals(pat);
        }
        let supported = self.handler_arm_expr_is_cps_island_subset(&arm.body);
        self.pop_scope();
        supported
    }

    fn handler_arm_expr_is_cps_island_subset(&mut self, expr: &MExpr) -> bool {
        if self.expr_is_direct_subset(expr) {
            return true;
        }
        match expr {
            MExpr::Resume { value, .. } => self.atom_is_direct_subset(value),
            MExpr::Bind {
                var, value, body, ..
            }
            | MExpr::Let { var, value, body } => {
                if !self.expr_is_direct_subset(value) {
                    return false;
                }
                let local_shape = self.direct_local_shape_for_expr(value);
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
            _ => false,
        }
    }

    fn fresh_cps_temp(&mut self, prefix: &str) -> String {
        let id = self.cps_temp_counter;
        self.cps_temp_counter += 1;
        format!("{prefix}{id}")
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
            Atom::Lambda { params, body, .. } => self.lambda_is_direct_subset(params, body),
            Atom::QualifiedRef { .. } => self.direct_function_value_ref(atom).is_some(),
            Atom::BackendAtom { .. } | Atom::BackendSpawnThunk { .. } => false,
            Atom::DictRef { .. } => self.direct_dict_constructor(atom).is_some(),
        }
    }

    fn atom_is_cps_value_subset(&mut self, atom: &Atom) -> bool {
        self.cps_value_atom_shape(atom).is_some() || self.atom_is_direct_subset(atom)
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
            } => Some(
                self.pure_function_arity_at(*source)
                    .or_else(|| self.pure_trait_method_arity(trait_name, *method_index))
                    .map_or(LocalValueShape::PureCallableFromUseType, |arity| {
                        LocalValueShape::PureCallable { arity }
                    }),
            ),
            _ => None,
        }
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
            }),
            _ => None,
        }
    }

    fn cps_bind_shape_for_expr(&self, expr: &MExpr) -> Option<LocalValueShape> {
        match expr {
            MExpr::Pure(atom) => {
                if let Atom::Var { name, source } = atom {
                    match self.local_shape(&name.name) {
                        Some(
                            shape @ (LocalValueShape::CpsCallable { .. }
                            | LocalValueShape::RuntimeCpsCallable { .. }),
                        ) => return Some(shape),
                        Some(LocalValueShape::PureCallableFromUseType) => {
                            let (source_arity, adapter_arity, _effects) =
                                self.cps_function_arity_at(*source)?;
                            return Some(LocalValueShape::RuntimeCpsCallable {
                                source_arity,
                                adapter_arity,
                            });
                        }
                        _ => {}
                    }
                }
                self.cps_local_shape_for_expr(expr)
            }
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

    fn cps_bind_value_expr_is_supported(&mut self, expr: &MExpr) -> bool {
        match expr {
            MExpr::Pure(_) => self.cps_bind_shape_for_expr(expr).is_some(),
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
        let (left_source, left_adapter) = self.runtime_cps_arities(left)?;
        let (right_source, right_adapter) = self.runtime_cps_arities(right)?;
        (left_source == right_source && left_adapter == right_adapter).then_some(
            LocalValueShape::RuntimeCpsCallable {
                source_arity: left_source,
                adapter_arity: left_adapter,
            },
        )
    }

    fn runtime_cps_arities(&self, shape: &LocalValueShape) -> Option<(usize, usize)> {
        match shape {
            LocalValueShape::CpsCallable {
                source_arity,
                adapter_arity,
                ..
            }
            | LocalValueShape::RuntimeCpsCallable {
                source_arity,
                adapter_arity,
            } => Some((*source_arity, *adapter_arity)),
            LocalValueShape::PureCallable { .. } | LocalValueShape::PureCallableFromUseType => None,
        }
    }

    fn cps_value_atom_shape(&self, atom: &Atom) -> Option<LocalValueShape> {
        if let Atom::Var { name, source } = atom {
            match self.local_shape(&name.name) {
                Some(shape @ LocalValueShape::CpsCallable { .. }) => return Some(shape),
                Some(shape @ LocalValueShape::RuntimeCpsCallable { .. }) => return Some(shape),
                Some(LocalValueShape::PureCallableFromUseType) => {
                    let (source_arity, adapter_arity, _effects) =
                        self.cps_function_arity_at(*source)?;
                    return Some(LocalValueShape::RuntimeCpsCallable {
                        source_arity,
                        adapter_arity,
                    });
                }
                _ => {}
            }
        }
        self.cps_local_shape_for_expr(&MExpr::Pure(atom.clone()))
    }

    fn pure_trait_method_arity(&self, trait_name: &str, method_index: usize) -> Option<usize> {
        let trait_info = self.effect_info.traits.get(trait_name).or_else(|| {
            let bare = trait_name.rsplit('.').next().unwrap_or(trait_name);
            self.effect_info.traits.get(bare)
        })?;
        let method = trait_info.methods.get(method_index)?;
        method.effect_sig.effects.is_empty().then_some(())?;
        (!method.effect_sig.is_open_row).then_some(())?;
        Some(method.effect_sig.user_arity)
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

    fn unsupported(&self, what: &str) -> ! {
        panic!("selective-uniform direct lowerer TODO: {what}")
    }

    fn unsupported_expr(&self, expr: &MExpr) -> ! {
        panic!(
            "selective-uniform direct lowerer TODO: unsupported MExpr {:?}",
            std::mem::discriminant(expr)
        )
    }

    fn unsupported_atom(&self, atom: &Atom) -> ! {
        panic!(
            "selective-uniform direct lowerer TODO: unsupported Atom {:?}",
            std::mem::discriminant(atom)
        )
    }
}
