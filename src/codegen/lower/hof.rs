use std::collections::{HashMap, HashSet};

use crate::ast::{self, Expr, ExprKind, Pat};
use crate::codegen::cerl::{CExpr, CFunDef};
use crate::codegen::optimize::{HofCallbackParam, HofDirectSpecialization};

use super::pats;
use super::{DirectHofValueBinding, GeneratedHofVariant, Lowerer};

impl<'a> Lowerer<'a> {
    fn hof_lookup_candidates(&self, lookup_name: &str, head: &Expr) -> Vec<String> {
        let mut candidates = Vec::new();
        if let Some(resolved) = self.resolved.get(&head.id) {
            candidates.push(resolved.canonical_name.clone());
        }
        candidates.push(lookup_name.to_string());
        candidates.dedup();
        candidates
    }

    fn hof_direct_specialization_for_call(
        &self,
        lookup_name: &str,
        head: &Expr,
    ) -> Option<(String, HofDirectSpecialization)> {
        self.hof_lookup_candidates(lookup_name, head)
            .into_iter()
            .find_map(|candidate| {
                self.optimization
                    .hof_direct_specializations
                    .get(&candidate)
                    .cloned()
                    .or_else(|| {
                        self.ctx.modules_semantics().find_map(|(_, semantics)| {
                            semantics
                                .optimization
                                .hof_direct_specializations
                                .get(&candidate)
                                .cloned()
                        })
                    })
                    .map(|specialization| (candidate, specialization))
            })
    }

    pub(super) fn try_hof_direct_specialized_call(
        &mut self,
        lookup_name: &str,
        _emit_name: &str,
        head: &Expr,
        args: &[&Expr],
        return_k: Option<CExpr>,
    ) -> Option<CExpr> {
        let (_key, specialization) = self.hof_direct_specialization_for_call(lookup_name, head)?;
        let info = self.resolved_fun_info(head.id, lookup_name)?;
        if !Self::hof_direct_effects_covered(info, &specialization) {
            return None;
        }
        if specialization.source_arity != args.len()
            || !self.hof_direct_callback_args_supported(&specialization.callback_params, args)
        {
            return None;
        }

        let callback_indexes: HashSet<usize> = specialization
            .callback_params
            .iter()
            .map(|param| param.index)
            .collect();
        let param_types = self
            .resolved_fun_info(head.id, lookup_name)
            .map(|f| f.expected_arg_types(args.len()));

        let mut arg_vars = Vec::with_capacity(args.len());
        let mut bindings = Vec::with_capacity(args.len());
        for (idx, arg) in args.iter().enumerate() {
            let var = self.fresh();
            let ce = if callback_indexes.contains(&idx) {
                self.lower_expr_value(arg)
            } else {
                self.lower_expr_value_with_expected_type(
                    arg,
                    param_types.as_ref().and_then(|tys| tys.get(idx)),
                )
            };
            arg_vars.push(var.clone());
            bindings.push((var, ce));
        }

        let arity = specialization.source_arity;
        let call_args = arg_vars.into_iter().map(CExpr::Var).collect();
        let call = if self.resolved.get(&head.id).is_some_and(|resolved| {
            resolved.source_module.as_deref() != Some(&self.current_source_module)
        }) {
            let module = self
                .resolved
                .get(&head.id)
                .and_then(|resolved| resolved.source_module.as_deref())
                .map(Self::module_name_to_erlang)
                .unwrap_or_else(|| self.current_module.clone());
            CExpr::Call(module, specialization.entry_name.clone(), call_args)
        } else if let Some(module) = self
            .resolved
            .get(&head.id)
            .and_then(|resolved| resolved.source_module.as_deref())
            .filter(|source| *source != self.current_source_module)
        {
            CExpr::Call(
                Self::module_name_to_erlang(module),
                specialization.entry_name.clone(),
                call_args,
            )
        } else {
            CExpr::Apply(
                Box::new(CExpr::FunRef(specialization.entry_name.clone(), arity)),
                call_args,
            )
        };
        let call = self.direct_hof_value_with_return_k(call, return_k);
        Some(self.wrap_let_bindings(bindings, call))
    }

    pub(super) fn try_hof_direct_specialized_value_call(
        &mut self,
        var_name: &str,
        args: &[&Expr],
        return_k: Option<CExpr>,
    ) -> Option<CExpr> {
        let binding = self.direct_hof_value_bindings.get(var_name).cloned()?;
        let specialization = binding.specialization;
        if specialization.source_arity != args.len()
            || !self.hof_direct_callback_args_supported(&specialization.callback_params, args)
        {
            return None;
        }

        let mut arg_vars = Vec::with_capacity(args.len());
        let mut bindings = Vec::with_capacity(args.len());
        for arg in args {
            let var = self.fresh();
            let ce = self.lower_expr_value(arg);
            arg_vars.push(var.clone());
            bindings.push((var, ce));
        }

        let arity = specialization.source_arity;
        let call_args = arg_vars.into_iter().map(CExpr::Var).collect();
        let call = if let Some(source_module) = binding
            .source_module
            .filter(|source| source != &self.current_source_module)
        {
            CExpr::Call(
                Self::module_name_to_erlang(&source_module),
                specialization.entry_name,
                call_args,
            )
        } else {
            CExpr::Apply(
                Box::new(CExpr::FunRef(specialization.entry_name, arity)),
                call_args,
            )
        };
        let call = self.direct_hof_value_with_return_k(call, return_k);
        Some(self.wrap_let_bindings(bindings, call))
    }

    pub(super) fn hof_direct_binding_for_value_expr(
        &self,
        expr: &Expr,
    ) -> Option<DirectHofValueBinding> {
        match &expr.kind {
            ExprKind::Var { name, .. } => self
                .hof_direct_specialization_for_call(name, expr)
                .and_then(|(_, specialization)| {
                    let info = self.resolved_fun_info(expr.id, name)?;
                    Self::hof_direct_effects_covered(info, &specialization).then_some(
                        DirectHofValueBinding {
                            specialization,
                            source_module: self
                                .resolved
                                .get(&expr.id)
                                .and_then(|resolved| resolved.source_module.clone()),
                        },
                    )
                }),
            ExprKind::QualifiedName { module, name, .. } => {
                let qualified = format!("{}.{}", module, name);
                self.hof_direct_specialization_for_call(&qualified, expr)
                    .and_then(|(_, specialization)| {
                        let info = self.resolved_fun_info(expr.id, &qualified)?;
                        Self::hof_direct_effects_covered(info, &specialization).then_some(
                            DirectHofValueBinding {
                                specialization,
                                source_module: self
                                    .resolved
                                    .get(&expr.id)
                                    .and_then(|resolved| resolved.source_module.clone()),
                            },
                        )
                    })
            }
            _ => None,
        }
    }

    fn hof_direct_effects_covered(
        info: &super::FunInfo,
        specialization: &HofDirectSpecialization,
    ) -> bool {
        if info.is_open_row() {
            return false;
        }
        if info.effects().is_empty() {
            return true;
        }
        let covered: HashSet<&str> = specialization
            .callback_params
            .iter()
            .filter_map(|callback| info.param_absorbed_effects.get(&callback.index))
            .flat_map(|effects| effects.iter().map(String::as_str))
            .collect();
        info.effects()
            .iter()
            .all(|effect| covered.contains(effect.as_str()))
    }

    fn hof_direct_callback_args_supported(
        &self,
        callback_params: &[HofCallbackParam],
        args: &[&Expr],
    ) -> bool {
        callback_params.iter().all(|param| {
            args.get(param.index)
                .is_some_and(|arg| self.hof_direct_callback_arg_supported(arg, param.source_arity))
        })
    }

    fn hof_direct_callback_arg_supported(&self, arg: &Expr, expected_arity: usize) -> bool {
        if self.expr_cps_function_shape(arg).is_some() {
            return false;
        }
        if let Some(ty) = self.check_result.resolved_type_for_node(arg.id) {
            let ty = self.check_result.sub.apply(&ty);
            let (arity, effects) = super::util::arity_and_effects_from_type(&ty);
            return arity == expected_arity
                && effects.is_empty()
                && matches!(ty, crate::typechecker::Type::Fun(_, _, _));
        }
        match &arg.kind {
            ExprKind::Var { name, .. } => {
                self.resolved_fun_info(arg.id, name).is_some_and(|info| {
                    info.arity() == expected_arity
                        && info.effects().is_empty()
                        && !info.is_open_row()
                })
            }
            ExprKind::QualifiedName { module, name, .. } => {
                let qualified = format!("{}.{}", module, name);
                self.resolved_fun_info(arg.id, &qualified)
                    .is_some_and(|info| {
                        info.arity() == expected_arity
                            && info.effects().is_empty()
                            && !info.is_open_row()
                    })
            }
            _ => false,
        }
    }

    pub(super) fn direct_hof_callback_arity(&self, name: &str) -> Option<usize> {
        self.direct_hof_callback_params.get(name).copied()
    }

    fn direct_hof_value_with_return_k(&mut self, value: CExpr, return_k: Option<CExpr>) -> CExpr {
        if let Some(k) = return_k {
            match k {
                CExpr::Fun(params, body) if params.len() == 1 => {
                    CExpr::Let(params[0].clone(), Box::new(value), body)
                }
                other => {
                    let result_var = self.fresh();
                    CExpr::Let(
                        result_var.clone(),
                        Box::new(value),
                        Box::new(CExpr::Apply(Box::new(other), vec![CExpr::Var(result_var)])),
                    )
                }
            }
        } else {
            value
        }
    }

    pub(super) fn maybe_emit_hof_direct_variant(
        &mut self,
        name: &str,
        arity: usize,
        clauses: &[super::Clause<'_>],
        export: bool,
    ) {
        let Some(specialization) = self
            .optimization
            .hof_direct_specializations
            .get(name)
            .cloned()
        else {
            return;
        };
        let Some(info) = self.fun_info.get(name) else {
            return;
        };
        debug_assert_eq!(
            info.abi.user_arity, arity,
            "direct-HOF variant must preserve the source CallableAbi user arity"
        );
        if !Self::hof_direct_effects_covered(info, &specialization) {
            return;
        }
        if specialization.source_arity != arity
            || clauses.len() != 1
            || clauses[0].1.is_some()
            || !Self::hof_direct_params_supported(clauses[0].0)
        {
            return;
        }

        let (params, _, body) = clauses[0];
        let variant_params = pats::lower_params(params);
        if variant_params.len() != arity {
            return;
        }
        let callback_param_names =
            Self::hof_direct_callback_param_names(params, &specialization.callback_params);
        if callback_param_names.len() != specialization.callback_params.len() {
            return;
        }

        let saved_callbacks = std::mem::take(&mut self.direct_hof_callback_params);
        self.direct_hof_callback_params = callback_param_names;
        let saved_evidence = self.current_evidence.clone();
        let saved_function = self.current_function.clone();
        self.current_evidence = None;
        self.current_function = specialization.entry_name.clone();
        let body = self.lower_expr_with_installed_return_k(body, None);
        self.current_function = saved_function;
        self.current_evidence = saved_evidence;
        self.direct_hof_callback_params = saved_callbacks;

        self.generated_hof_variants.push(GeneratedHofVariant {
            name: specialization.entry_name,
            arity,
            body: CExpr::Fun(variant_params, Box::new(body)),
            export,
        });
    }

    fn hof_direct_params_supported(params: &[Pat]) -> bool {
        params.iter().all(|param| {
            matches!(
                param,
                Pat::Var { .. }
                    | Pat::Wildcard { .. }
                    | Pat::Lit {
                        value: ast::Lit::Unit,
                        ..
                    }
            )
        })
    }

    fn hof_direct_callback_param_names(
        params: &[Pat],
        callback_params: &[HofCallbackParam],
    ) -> HashMap<String, usize> {
        callback_params
            .iter()
            .filter_map(|callback| match params.get(callback.index) {
                Some(Pat::Var { name, .. }) => {
                    Some((super::util::core_var(name), callback.source_arity))
                }
                _ => None,
            })
            .collect()
    }

    pub(super) fn generated_hof_fun_defs(&mut self) -> (Vec<(String, usize)>, Vec<CFunDef>) {
        let variants = std::mem::take(&mut self.generated_hof_variants);
        let mut exports = Vec::new();
        let mut funs = Vec::new();
        for variant in variants {
            if variant.export {
                exports.push((variant.name.clone(), variant.arity));
            }
            funs.push(CFunDef {
                name: variant.name,
                arity: variant.arity,
                body: variant.body,
            });
        }
        (exports, funs)
    }
}
