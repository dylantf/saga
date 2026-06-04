use super::*;

impl<'a, 'info> DirectLowerer<'a, 'info> {
    pub(super) fn is_local(&self, name: &str) -> bool {
        self.locals.iter().rev().any(|scope| scope.contains(name))
    }

    pub(super) fn local_shape(&self, name: &str) -> Option<LocalValueShape> {
        self.local_shapes
            .iter()
            .rev()
            .find_map(|scope| scope.get(name).cloned())
    }

    pub(super) fn local_callable_arity_for_head(&self, head: &Atom) -> Option<usize> {
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

    pub(super) fn push_scope(&mut self) {
        self.locals.push(HashSet::new());
        self.local_shapes.push(HashMap::new());
        self.local_known_direct_lambdas.push(HashMap::new());
        self.local_known_cps_lambdas.push(HashMap::new());
        self.local_known_dict_values.push(HashMap::new());
        self.local_known_direct_atoms.push(HashMap::new());
    }

    pub(super) fn pop_scope(&mut self) {
        self.locals.pop();
        self.local_shapes.pop();
        self.local_known_direct_lambdas.pop();
        self.local_known_cps_lambdas.pop();
        self.local_known_dict_values.pop();
        self.local_known_direct_atoms.pop();
    }

    pub(super) fn current_scope_mut(&mut self) -> &mut HashSet<String> {
        self.locals.last_mut().expect("direct lowerer has a scope")
    }

    pub(super) fn current_shape_scope_mut(&mut self) -> &mut HashMap<String, LocalValueShape> {
        self.local_shapes
            .last_mut()
            .expect("direct lowerer has a local-shape scope")
    }

    pub(super) fn current_known_cps_lambda_scope_mut(
        &mut self,
    ) -> &mut HashMap<String, KnownCpsLambda> {
        self.local_known_cps_lambdas
            .last_mut()
            .expect("direct lowerer has a known-CPS-lambda scope")
    }

    pub(super) fn current_known_direct_lambda_scope_mut(
        &mut self,
    ) -> &mut HashMap<String, KnownDirectLambda> {
        self.local_known_direct_lambdas
            .last_mut()
            .expect("direct lowerer has a known-direct-lambda scope")
    }

    pub(super) fn current_known_dict_value_scope_mut(
        &mut self,
    ) -> &mut HashMap<String, KnownDictValue> {
        self.local_known_dict_values
            .last_mut()
            .expect("direct lowerer has a known-dict-value scope")
    }

    pub(super) fn current_known_direct_atom_scope_mut(&mut self) -> &mut HashMap<String, Atom> {
        self.local_known_direct_atoms
            .last_mut()
            .expect("direct lowerer has a known-direct-atom scope")
    }

    pub(super) fn known_direct_lambda(&self, name: &str) -> Option<KnownDirectLambda> {
        self.local_known_direct_lambdas
            .iter()
            .rev()
            .find_map(|scope| scope.get(name).cloned())
    }

    pub(super) fn known_cps_lambda(&self, name: &str) -> Option<KnownCpsLambda> {
        self.local_known_cps_lambdas
            .iter()
            .rev()
            .find_map(|scope| scope.get(name).cloned())
    }

    pub(super) fn known_dict_value(&self, name: &str) -> Option<KnownDictValue> {
        self.local_known_dict_values
            .iter()
            .rev()
            .find_map(|scope| scope.get(name).cloned())
    }

    pub(super) fn bind_fun_param_locals(&mut self, fb: &MFunBinding) {
        let param_shapes = self.param_shapes_for_fun(fb);
        for (index, pat) in fb.params.iter().enumerate() {
            self.bind_pat_locals_with_shape(pat, param_shapes.get(index).cloned().flatten());
        }
    }

    pub(super) fn bind_cps_entry_param_locals(&mut self, fb: &MFunBinding) {
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

    pub(super) fn specialized_param_shape_for_arg(
        &mut self,
        arg: &Atom,
    ) -> Option<LocalValueShape> {
        self.pure_value_atom_shape(arg)
            .or_else(|| self.cps_value_atom_shape(arg))
    }

    pub(super) fn function_type_for_binding(&self, fb: &MFunBinding) -> Option<&Type> {
        self.effect_info
            .type_at_node
            .get(&fb.id)
            .or_else(|| self.exported_function_type(&fb.name))
    }

    pub(super) fn exported_function_type(&self, name: &str) -> Option<&Type> {
        self.module_ctx
            .modules
            .get(&self.current_module)?
            .codegen_info
            .exports
            .iter()
            .find_map(|(export_name, scheme)| (export_name == name).then_some(&scheme.ty))
    }

    pub(super) fn param_shapes_for_fun(&self, fb: &MFunBinding) -> Vec<Option<LocalValueShape>> {
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

    pub(super) fn local_shape_for_param_type(&self, ty: &Type) -> Option<LocalValueShape> {
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

    pub(super) fn param_shapes_for_cps_entry(
        &self,
        fb: &MFunBinding,
    ) -> Vec<Option<LocalValueShape>> {
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

    pub(super) fn local_shape_for_cps_entry_param_type(
        &self,
        ty: &Type,
    ) -> Option<LocalValueShape> {
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

    pub(super) fn local_shape_for_cps_entry_pat(&self, pat: &Pat) -> Option<LocalValueShape> {
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

    pub(super) fn bind_pat_locals(&mut self, pat: &Pat) {
        self.bind_pat_locals_with_shape(pat, None);
    }

    pub(super) fn bind_cps_handler_arm_param_locals(&mut self, arm: &MHandlerArm) {
        for pat in &arm.params {
            let shape = self
                .local_shape_for_cps_entry_pat(pat)
                .or_else(|| self.runtime_cps_shape_for_handler_param_use(pat, arm));
            self.bind_pat_locals_with_shape(pat, shape);
        }
    }

    pub(super) fn runtime_cps_shape_for_handler_param_use(
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

    pub(super) fn bind_pat_locals_with_shape(
        &mut self,
        pat: &Pat,
        explicit_shape: Option<LocalValueShape>,
    ) {
        match pat {
            Pat::Var { id, name, .. } => {
                self.current_scope_mut().insert(name.clone());
                self.shadow_known_direct_atom_with_local(name.clone(), *id);
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
}
