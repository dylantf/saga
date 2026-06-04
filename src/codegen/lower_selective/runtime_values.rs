use super::*;

impl<'a, 'info> DirectLowerer<'a, 'info> {
    pub(super) fn cps_bind_value_expr_is_supported(&mut self, expr: &MExpr) -> bool {
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

    pub(super) fn handler_value_expr_is_cps_island_subset(&mut self, expr: &MExpr) -> bool {
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

    pub(super) fn handler_value_info_for_atom(&self, atom: &Atom) -> Option<&HandlerValueInfo> {
        let Atom::Var { name, .. } = atom else {
            return None;
        };
        if self.is_local(&name.name) {
            return None;
        }
        self.handler_value_map.get(&name.name)
    }

    pub(super) fn handler_value_is_cps_island_subset(
        &mut self,
        arms: &[MHandlerArm],
        return_clause: Option<&MHandlerArm>,
    ) -> bool {
        arms.iter()
            .all(|arm| self.handler_arm_is_cps_island_subset(arm))
            && return_clause.is_none_or(|arm| self.return_clause_is_cps_island_subset(arm))
    }

    pub(super) fn compatible_case_runtime_cps_shape(
        &self,
        arms: &[MArm],
    ) -> Option<LocalValueShape> {
        let mut shapes = arms
            .iter()
            .map(|arm| self.cps_bind_shape_for_expr(&arm.body));
        let first = shapes.next()??;
        shapes.try_fold(first, |acc, shape| {
            self.compatible_runtime_cps_shape(&acc, &shape?)
        })
    }

    pub(super) fn compatible_runtime_cps_shape(
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

    pub(super) fn runtime_cps_shape_parts(
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

    pub(super) fn pure_callable_shape_arity(&self, shape: &LocalValueShape) -> Option<usize> {
        match shape {
            LocalValueShape::PureCallable { arity } => Some(*arity),
            LocalValueShape::PureCallableFromUseType => None,
            LocalValueShape::CpsCallable { .. } | LocalValueShape::RuntimeCpsCallable { .. } => {
                None
            }
        }
    }

    pub(super) fn cps_value_atom_shape(&self, atom: &Atom) -> Option<LocalValueShape> {
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

    pub(super) fn lambda_is_cps_atom(&self, atom: &Atom) -> bool {
        matches!(atom, Atom::Lambda { .. }) && self.cps_lambda_type_arity_for_atom(atom).is_some()
    }

    pub(super) fn cps_lambda_arity_for_atom(
        &self,
        atom: &Atom,
    ) -> Option<(usize, usize, Vec<String>)> {
        self.cps_lambda_type_arity_for_atom(atom)
            .or_else(|| match atom {
                Atom::Lambda { params, .. } => Some((params.len(), params.len() + 2, Vec::new())),
                _ => None,
            })
    }

    pub(super) fn cps_lambda_type_arity_for_atom(
        &self,
        atom: &Atom,
    ) -> Option<(usize, usize, Vec<String>)> {
        let Atom::Lambda { source, .. } = atom else {
            return None;
        };
        self.cps_function_arity_at(*source)
    }

    pub(super) fn pure_value_atom_shape(&self, atom: &Atom) -> Option<LocalValueShape> {
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

    pub(super) fn pure_callback_arity_for_atom(&self, atom: &Atom) -> Option<usize> {
        let source = match atom {
            Atom::Var { source, .. }
            | Atom::QualifiedRef { source, .. }
            | Atom::Lambda { source, .. } => *source,
            _ => return None,
        };
        self.pure_function_arity_at(source)
    }

    pub(super) fn cps_callback_param_shapes(&self, head: &Atom) -> Vec<Option<(usize, usize)>> {
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

    pub(super) fn pure_trait_method_arity(
        &self,
        trait_name: &str,
        method_index: usize,
    ) -> Option<usize> {
        let trait_info = self.trait_info(trait_name)?;
        let method = trait_info.methods.get(method_index)?;
        method.effect_sig.effects.is_empty().then_some(())?;
        (!method.effect_sig.is_open_row).then_some(())?;
        Some(method.effect_sig.user_arity)
    }

    pub(super) fn cps_trait_method_arity(
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
}
