use super::*;

impl<'a, 'info> DirectLowerer<'a, 'info> {
    pub(super) fn call_shape(&self, head: &Atom) -> Option<CallShape> {
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

    pub(super) fn local_cps_function_shape_by_name(&self, head: &Atom) -> Option<CallShape> {
        if self.head_resolves_to_imported_clone_source_local_beam(head) {
            return None;
        }
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

    pub(super) fn local_top_level_function_shape(&self, head: &Atom) -> Option<CallShape> {
        if self.head_resolves_to_imported_clone_source_local_beam(head) {
            return None;
        }
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

    pub(super) fn is_panic_or_todo_call(&self, head: &Atom, args: &[Atom]) -> bool {
        let Atom::Var { name, source } = head else {
            return false;
        };
        args.len() == 1
            && self.resolution.get(source).is_none()
            && matches!(name.name.as_str(), "panic" | "todo")
    }

    pub(super) fn cps_function_shape(&self, head: &Atom) -> Option<CallShape> {
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
        let module = self.resolved_erlang_module_for_symbol(resolved, erlang_mod);
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

    pub(super) fn resolved_erlang_module_for_symbol(
        &self,
        resolved: &ResolvedSymbol,
        erlang_mod: &Option<String>,
    ) -> Option<String> {
        resolved_erlang_module_for_call(erlang_mod, &self.current_module).or_else(|| {
            resolved
                .source_module
                .as_ref()
                .filter(|source_module| source_module.as_str() != self.current_module)
                .map(|source_module| erlang_module_name(source_module))
                .filter(|erlang_module| erlang_module != &self.current_module)
        })
    }

    pub(super) fn direct_intrinsic(&self, head: &Atom) -> Option<IntrinsicId> {
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

    pub(super) fn direct_dict_constructor(&self, head: &Atom) -> Option<DirectCallable> {
        if self.head_resolves_to_imported_clone_source_local_beam(head) {
            return None;
        }
        let (name, source) = match head {
            Atom::DictRef { name, source } => (name, *source),
            _ => return None,
        };
        if let Some(arity) = self.local_dict_constructor_arities.get(name) {
            debug_selective_subject("dict-call", name, || {
                format!(
                    "{}: direct local constructor {name}/{arity}",
                    self.current_module
                )
            });
            return Some(DirectCallable {
                module: None,
                name: name.clone(),
                arity: *arity,
            });
        }
        let Some(resolved) = self.resolution.get(&source) else {
            debug_selective_subject("dict-call", name, || {
                format!(
                    "{}: miss {name}: no backend resolution entry",
                    self.current_module
                )
            });
            return None;
        };
        let ResolvedCodegenKind::BeamFunction {
            erlang_mod,
            name,
            arity,
            effects,
        } = &resolved.kind
        else {
            debug_selective_subject("dict-call", name, || {
                format!(
                    "{}: reject {name}: resolved symbol is not a BeamFunction",
                    self.current_module
                )
            });
            return None;
        };
        if !effects.is_empty() {
            debug_selective_subject("dict-call", name, || {
                format!(
                    "{}: reject {name}/{arity}: effectful resolved constructor",
                    self.current_module
                )
            });
            return None;
        }
        let module = self.resolved_erlang_module_for_symbol(resolved, erlang_mod);
        debug_selective_subject("dict-call", name, || {
            let module_label = module.as_deref().unwrap_or("<local>");
            format!(
                "{}: direct resolved constructor {module_label}:{name}/{arity}",
                self.current_module
            )
        });
        Some(DirectCallable {
            module,
            name: name.clone(),
            arity: *arity,
        })
    }

    pub(super) fn direct_function_callable(&self, head: &Atom) -> Option<DirectCallable> {
        if let Some(callable) = self.local_direct_function_callable_by_name(head) {
            return Some(callable);
        }
        if let Some(callable) = self.local_external_callable_by_name(head) {
            return Some(callable);
        }
        if let Some(callable) = self.imported_direct_function_callable_by_unqualified_name(head) {
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
        let module = self.resolved_erlang_module_for_symbol(resolved, erlang_mod);
        let is_remote = module.is_some();
        if is_remote
            && module
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
            let module = module.as_ref()?;
            let entries = self
                .imported_function_entries
                .get(&(module.clone(), name.clone()))?;
            let direct_entry_arity = direct_entry_arity_matching_resolved(*arity, entries)?;
            return Some(DirectCallable {
                module: Some(module.clone()),
                name: direct_entry_name_for(name, entries),
                arity: direct_entry_arity,
            });
        }
        if is_remote {
            return Some(DirectCallable {
                module,
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

    fn imported_direct_function_callable_by_unqualified_name(
        &self,
        head: &Atom,
    ) -> Option<DirectCallable> {
        let Atom::Var { name, .. } = head else {
            return None;
        };
        if self.is_local(&name.name) || self.local_fun_bindings.contains_key(&name.name) {
            return None;
        }

        let mut matches = self
            .imported_function_entries
            .iter()
            .filter_map(|((module, fun_name), entries)| {
                if fun_name != &name.name {
                    return None;
                }
                let arity = entries.direct_entry_arity?;
                let module = if module.contains('.') {
                    erlang_module_name(module)
                } else {
                    module.clone()
                };
                Some(DirectCallable {
                    module: Some(module),
                    name: direct_entry_name_for(fun_name, entries),
                    arity,
                })
            })
            .collect::<Vec<_>>();
        matches.sort_by(|left, right| {
            (&left.module, &left.name, left.arity).cmp(&(&right.module, &right.name, right.arity))
        });
        matches.dedup_by(|left, right| {
            left.module == right.module && left.name == right.name && left.arity == right.arity
        });
        let [callable] = matches.as_slice() else {
            return None;
        };
        Some(callable.clone())
    }

    pub(super) fn local_direct_function_callable_by_name(
        &self,
        head: &Atom,
    ) -> Option<DirectCallable> {
        if self.head_resolves_to_imported_clone_source_local_beam(head) {
            return None;
        }
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

    pub(super) fn direct_function_value_ref(&self, head: &Atom) -> Option<CExpr> {
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
        let module = self.resolved_erlang_module_for_symbol(resolved, erlang_mod);
        if let Some(module) = module {
            if let Some(entries) = self
                .imported_function_entries
                .get(&(module.clone(), name.clone()))
                && !entries.is_cps_typed()
                && let Some(arity) = entries.direct_entry_arity
            {
                return Some(remote_fun_value(
                    module,
                    direct_entry_name_for(name, entries),
                    arity,
                ));
            }
            return Some(remote_fun_value(module, name.clone(), *arity));
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

    pub(super) fn local_external_callable_by_name(&self, head: &Atom) -> Option<DirectCallable> {
        let Atom::Var { name, .. } = head else {
            return None;
        };
        self.local_external_functions.get(&name.name).cloned()
    }

    fn head_resolves_to_imported_clone_source_local_beam(&self, head: &Atom) -> bool {
        let Some(source_module) = self.imported_clone_source_module.as_deref() else {
            return false;
        };
        let source = match head {
            Atom::Var { source, .. }
            | Atom::QualifiedRef { source, .. }
            | Atom::DictRef { source, .. } => *source,
            _ => return false,
        };
        let Some(resolved) = self.resolution.get(&source) else {
            return false;
        };
        let ResolvedCodegenKind::BeamFunction {
            erlang_mod: None, ..
        } = resolved.kind
        else {
            return false;
        };
        resolved
            .source_module
            .as_deref()
            .is_none_or(|module| module == source_module)
    }

    pub(super) fn supported_direct_call(&self, head: &Atom) -> Option<DirectCallable> {
        self.direct_function_callable(head)
    }
}
