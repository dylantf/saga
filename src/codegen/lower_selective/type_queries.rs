use super::*;

impl<'a, 'info> DirectLowerer<'a, 'info> {
    pub(super) fn trait_info(&self, trait_name: &str) -> Option<&crate::typechecker::TraitInfo> {
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

    pub(super) fn pure_function_arity_at(&self, source: NodeId) -> Option<usize> {
        self.pure_function_arity_from_type(self.effect_info.type_at_node.get(&source)?)
    }

    pub(super) fn pure_function_arity_from_type(&self, ty: &Type) -> Option<usize> {
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

    pub(super) fn cps_function_arity_at(
        &self,
        source: NodeId,
    ) -> Option<(usize, usize, Vec<String>)> {
        self.cps_function_arity_from_type(self.effect_info.type_at_node.get(&source)?)
    }

    pub(super) fn cps_function_arity_from_type(
        &self,
        ty: &Type,
    ) -> Option<(usize, usize, Vec<String>)> {
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

    pub(super) fn callback_param_arities_from_type(&self, ty: &Type) -> Vec<Option<usize>> {
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
}
