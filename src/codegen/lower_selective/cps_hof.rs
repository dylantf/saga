use super::*;

impl<'a, 'info> DirectLowerer<'a, 'info> {
    pub(super) fn hof_direct_specialization_for_cps_call(
        &mut self,
        head: &Atom,
        args: &[Atom],
    ) -> Option<(Option<String>, HofDirectSpecialization)> {
        let (module, specialization) = self.hof_direct_specialization_for_head(head)?;
        if specialization.source_arity != args.len() {
            return None;
        }

        let callback_indices: std::collections::HashSet<usize> = specialization
            .callback_params
            .iter()
            .map(|param| param.index)
            .collect();
        for callback in &specialization.callback_params {
            let arg = args.get(callback.index)?;
            if self.pure_hof_callback_arg_arity(arg)? != callback.source_arity {
                return None;
            }
        }
        for (index, arg) in args.iter().enumerate() {
            if callback_indices.contains(&index) {
                continue;
            }
            if !self.atom_is_direct_subset(arg) {
                return None;
            }
        }
        Some((module, specialization))
    }

    pub(super) fn hof_direct_specialization_for_head(
        &self,
        head: &Atom,
    ) -> Option<(Option<String>, HofDirectSpecialization)> {
        let (local_name, source) = match head {
            Atom::Var { name, source } => (Some(name.name.as_str()), *source),
            Atom::QualifiedRef { source, .. } => (None, *source),
            _ => return None,
        };
        if let Some(local_name) = local_name
            && let Some(LocalValueShape::CpsCallable {
                module,
                hof_direct_specialization: Some(specialization),
                ..
            }) = self.local_shape(local_name)
        {
            return Some((module, specialization));
        }
        if let Some(local_name) = local_name
            && let Some(specialization) = self.local_hof_direct_specializations.get(local_name)
        {
            return Some((None, specialization.clone()));
        }
        let resolved = self.resolution.get(&source)?;
        let ResolvedCodegenKind::BeamFunction {
            erlang_mod, name, ..
        } = &resolved.kind
        else {
            return None;
        };
        let module = resolved_erlang_module_for_call(erlang_mod, &self.current_module)?;
        let specialization = self
            .imported_hof_direct_specializations
            .get(&(module.clone(), name.clone()))?
            .clone();
        Some((Some(module), specialization))
    }

    pub(super) fn pure_hof_callback_arg_arity(&mut self, atom: &Atom) -> Option<usize> {
        if let Atom::Lambda { params, body, .. } = atom {
            if self.lambda_is_direct_subset(params, body) {
                return Some(params.len());
            }
            if self.pure_callback_arity_for_atom(atom) == Some(params.len())
                && self.lambda_is_direct_cps_island_subset(params, body)
            {
                return Some(params.len());
            }
            return None;
        }
        match self.pure_value_atom_shape(atom)? {
            LocalValueShape::PureCallable { arity } => Some(arity),
            LocalValueShape::PureCallableFromUseType
            | LocalValueShape::CpsCallable { .. }
            | LocalValueShape::RuntimeCpsCallable { .. } => None,
        }
    }

    pub(super) fn lower_hof_direct_specialized_call(
        &mut self,
        module: Option<String>,
        specialization: &HofDirectSpecialization,
        args: &[Atom],
    ) -> CExpr {
        let callback_indices: std::collections::HashSet<usize> = specialization
            .callback_params
            .iter()
            .map(|param| param.index)
            .collect();
        let lowered_args = args
            .iter()
            .enumerate()
            .map(|(index, arg)| {
                self.lower_hof_direct_specialized_arg(arg, callback_indices.contains(&index))
            })
            .collect();
        match module {
            Some(module) => CExpr::Call(module, specialization.entry_name.clone(), lowered_args),
            None => CExpr::Apply(
                Box::new(CExpr::FunRef(
                    specialization.entry_name.clone(),
                    specialization.source_arity,
                )),
                lowered_args,
            ),
        }
    }

    pub(super) fn lower_hof_direct_specialized_arg(
        &mut self,
        atom: &Atom,
        callback_arg: bool,
    ) -> CExpr {
        if callback_arg
            && let Atom::Lambda { params, body, .. } = atom
            && !self.lambda_is_direct_subset(params, body)
            && self.lambda_is_direct_cps_island_subset(params, body)
        {
            return self.lower_direct_cps_island_lambda_atom(params, body);
        }
        self.lower_atom(atom)
    }
}
