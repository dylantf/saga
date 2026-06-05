use super::*;

impl<'a, 'info> DirectLowerer<'a, 'info> {
    pub(super) fn bind_known_direct_atom(&mut self, name: impl Into<String>, atom: Atom) {
        let name = name.into();
        self.current_known_direct_atom_scope_mut()
            .insert(name.clone(), atom.clone());
        self.bind_known_direct_value(name, KnownDirectValue::Atom(atom));
    }

    pub(super) fn shadow_known_direct_atom_with_local(
        &mut self,
        name: impl Into<String>,
        id: NodeId,
    ) {
        let name = name.into();
        self.bind_known_direct_atom(
            name.clone(),
            Atom::Var {
                name: MVar {
                    name: name.clone(),
                    id: id.0,
                },
                source: id,
            },
        );
    }

    pub(super) fn bind_known_direct_lambda(
        &mut self,
        name: impl Into<String>,
        lambda: KnownDirectLambda,
    ) {
        self.current_known_direct_lambda_scope_mut()
            .insert(name.into(), lambda);
    }

    pub(super) fn bind_known_cps_lambda(
        &mut self,
        name: impl Into<String>,
        lambda: KnownCpsLambda,
    ) {
        self.current_known_cps_lambda_scope_mut()
            .insert(name.into(), lambda);
    }

    pub(super) fn bind_known_dict_value(&mut self, name: impl Into<String>, dict: KnownDictValue) {
        self.current_known_dict_value_scope_mut()
            .insert(name.into(), dict);
    }

    pub(super) fn bind_known_dict_values(
        &mut self,
        bindings: impl IntoIterator<Item = (String, KnownDictValue)>,
    ) {
        for (name, dict) in bindings {
            self.bind_known_dict_value(name, dict);
        }
    }

    pub(super) fn bind_known_direct_atom_pattern_values(
        &mut self,
        bindings: impl IntoIterator<Item = (String, Atom)>,
    ) {
        for (name, atom) in bindings {
            if matches!(&atom, Atom::Var { name: atom_name, .. } if atom_name.name == name) {
                continue;
            }
            self.bind_known_direct_atom(name, atom);
        }
    }

    pub(super) fn bind_known_direct_value(
        &mut self,
        name: impl Into<String>,
        value: KnownDirectValue,
    ) {
        self.current_known_direct_value_scope_mut()
            .insert(name.into(), value);
    }

    pub(super) fn bind_known_direct_values(
        &mut self,
        bindings: impl IntoIterator<Item = (String, KnownDirectValue)>,
    ) {
        for (name, value) in bindings {
            if matches!(&value, KnownDirectValue::Atom(Atom::Var { name: atom_name, .. }) if atom_name.name == name)
            {
                continue;
            }
            self.bind_known_direct_value(name, value);
        }
    }

    pub(super) fn bind_known_direct_value_pattern_values(
        &mut self,
        bindings: impl IntoIterator<Item = (String, KnownDirectValue)>,
    ) {
        self.bind_known_direct_values(bindings);
    }

    pub(super) fn known_direct_atom(&self, name: &str) -> Option<Atom> {
        self.known_direct_atom_guarded(name, &mut HashSet::new())
    }

    fn known_direct_atom_guarded(&self, name: &str, seen: &mut HashSet<String>) -> Option<Atom> {
        if !seen.insert(name.to_string()) {
            return None;
        }
        let atom = self
            .local_known_direct_atoms
            .iter()
            .rev()
            .find_map(|scope| scope.get(name).cloned())?;
        let source = match &atom {
            Atom::Var { source, .. }
            | Atom::Lit { source, .. }
            | Atom::Ctor { source, .. }
            | Atom::Tuple { source, .. }
            | Atom::AnonRecord { source, .. }
            | Atom::Record { source, .. }
            | Atom::Lambda { source, .. }
            | Atom::DictRef { source, .. }
            | Atom::QualifiedRef { source, .. }
            | Atom::Symbol { source, .. }
            | Atom::BackendAtom { source, .. }
            | Atom::BackendSpawnThunk { source, .. } => *source,
        };
        match atom {
            Atom::Var {
                name: alias_name, ..
            } => self
                .known_direct_atom_guarded(&alias_name.name, seen)
                .or_else(|| {
                    (alias_name.name != name).then_some(Atom::Var {
                        name: alias_name,
                        source,
                    })
                }),
            other => Some(other),
        }
    }

    pub(super) fn known_direct_value(&self, name: &str) -> Option<KnownDirectValue> {
        self.known_direct_value_guarded(name, &mut HashSet::new())
    }

    fn known_direct_value_guarded(
        &self,
        name: &str,
        seen: &mut HashSet<String>,
    ) -> Option<KnownDirectValue> {
        if !seen.insert(name.to_string()) {
            return None;
        }
        let value = self
            .local_known_direct_values
            .iter()
            .rev()
            .find_map(|scope| scope.get(name).cloned())?;
        match value {
            KnownDirectValue::Atom(Atom::Var {
                name: alias_name,
                source,
            }) => self
                .known_direct_value_guarded(&alias_name.name, seen)
                .or_else(|| {
                    (alias_name.name != name).then_some(KnownDirectValue::Atom(Atom::Var {
                        name: alias_name,
                        source,
                    }))
                }),
            other => Some(other),
        }
    }

    pub(super) fn known_direct_atom_for_expr(&mut self, expr: &MExpr) -> Option<Atom> {
        match expr {
            MExpr::Pure(atom) => self.known_direct_atom_for_atom(atom),
            MExpr::Let { var, value, body }
            | MExpr::Bind {
                var, value, body, ..
            } => {
                let value = self.known_direct_atom_for_expr(value)?;
                self.push_scope();
                self.current_scope_mut().insert(var.name.clone());
                self.bind_known_direct_atom(var.name.clone(), value);
                let body = self.known_direct_atom_for_expr(body);
                self.pop_scope();
                body
            }
            MExpr::FieldAccess {
                record,
                field,
                record_name,
                anon_fields,
                ..
            } => self.known_direct_field_value(record, field, record_name.as_deref(), anon_fields),
            MExpr::App { head, args, .. } => self.known_direct_atom_for_lambda_app(head, args),
            _ => None,
        }
    }

    pub(super) fn known_direct_value_for_expr(&mut self, expr: &MExpr) -> Option<KnownDirectValue> {
        match expr {
            MExpr::Pure(atom) => self.known_direct_value_for_atom(atom),
            MExpr::Let { var, value, body }
            | MExpr::Bind {
                var, value, body, ..
            } => {
                let value = self.known_direct_value_for_expr(value)?;
                self.push_scope();
                self.current_scope_mut().insert(var.name.clone());
                self.bind_known_direct_value(var.name.clone(), value);
                let body = self.known_direct_value_for_expr(body);
                self.pop_scope();
                body
            }
            MExpr::FieldAccess {
                record,
                field,
                record_name,
                anon_fields,
                ..
            } => self
                .known_direct_field_direct_value(record, field, record_name.as_deref(), anon_fields)
                .or_else(|| {
                    (self.atom_is_direct_subset(record))
                        .then(|| {
                            self.lower_known_field_access_expr(
                                record,
                                field,
                                record_name.as_deref(),
                                anon_fields.as_deref(),
                            )
                        })
                        .flatten()
                        .map(KnownDirectValue::Core)
                }),
            MExpr::App { head, args, .. } => self.known_direct_value_for_lambda_app(head, args),
            MExpr::Case {
                scrutinee, arms, ..
            } => self.known_direct_value_for_case(scrutinee, arms),
            _ => None,
        }
    }

    fn known_direct_value_for_case(
        &mut self,
        scrutinee: &Atom,
        arms: &[MArm],
    ) -> Option<KnownDirectValue> {
        let scrutinee = self.known_direct_value_for_atom(scrutinee)?;
        for arm in arms {
            if arm.guard.is_some() {
                break;
            }
            let Some(bindings) = self.match_known_direct_value_pattern(&scrutinee, &arm.pattern)
            else {
                continue;
            };
            self.push_scope();
            self.bind_pat_locals(&arm.pattern);
            self.bind_known_direct_value_pattern_values(bindings);
            let body = self.known_direct_value_for_expr(&arm.body);
            self.pop_scope();
            return body;
        }
        None
    }

    fn known_direct_atom_for_lambda_app(&mut self, head: &Atom, args: &[Atom]) -> Option<Atom> {
        let lambda = self.known_direct_lambda_for_atom(head)?;
        if lambda.params.len() != args.len()
            || lambda
                .params
                .iter()
                .any(|param| !direct_param_supported(param))
        {
            return None;
        }

        let mut dict_aliases = lambda.known_dict_aliases.clone();
        dict_aliases.extend(self.known_dict_aliases_for_bindings(&lambda.dict_bindings));
        let mut atom_bindings = Vec::new();
        for (param, arg) in lambda.params.iter().zip(args) {
            let arg = self.known_direct_atom_for_atom(arg)?;
            atom_bindings.extend(self.match_known_direct_atom_pattern(&arg, param)?);
        }

        self.push_scope();
        for (name, _) in &lambda.dict_bindings {
            self.current_scope_mut().insert(name.clone());
        }
        self.bind_known_dict_values(dict_aliases);
        for pat in &lambda.params {
            self.bind_pat_locals(pat);
        }
        self.bind_known_direct_atom_pattern_values(atom_bindings);
        let body = self.known_direct_atom_for_expr(&lambda.body);
        self.pop_scope();
        body
    }

    fn known_direct_value_for_lambda_app(
        &mut self,
        head: &Atom,
        args: &[Atom],
    ) -> Option<KnownDirectValue> {
        let lambda = self.known_direct_lambda_for_atom(head)?;
        if lambda.params.len() != args.len()
            || lambda
                .params
                .iter()
                .any(|param| !direct_param_supported(param))
        {
            return None;
        }

        let mut dict_aliases = lambda.known_dict_aliases.clone();
        dict_aliases.extend(self.known_dict_aliases_for_bindings(&lambda.dict_bindings));
        let mut value_bindings = Vec::new();
        for (param, arg) in lambda.params.iter().zip(args) {
            let arg = self.known_direct_value_for_atom(arg)?;
            value_bindings.extend(self.match_known_direct_value_pattern(&arg, param)?);
        }

        self.push_scope();
        for (name, _) in &lambda.dict_bindings {
            self.current_scope_mut().insert(name.clone());
        }
        self.bind_known_dict_values(dict_aliases);
        for pat in &lambda.params {
            self.bind_pat_locals(pat);
        }
        self.bind_known_direct_value_pattern_values(value_bindings);
        let body = self.known_direct_value_for_expr(&lambda.body);
        self.pop_scope();
        body
    }

    pub(super) fn known_direct_atom_for_case_scrutinee(&self, atom: &Atom) -> Option<Atom> {
        match atom {
            Atom::Var { name, .. } => self.known_direct_atom(&name.name),
            _ => self.known_direct_atom_for_atom(atom),
        }
    }

    pub(super) fn known_direct_atom_for_atom(&self, atom: &Atom) -> Option<Atom> {
        match atom {
            Atom::Lit { .. } => Some(atom.clone()),
            Atom::Ctor { name, args, source } => Some(Atom::Ctor {
                name: name.clone(),
                args: args
                    .iter()
                    .map(|arg| {
                        self.known_direct_atom_for_atom(arg)
                            .unwrap_or_else(|| arg.clone())
                    })
                    .collect(),
                source: *source,
            }),
            Atom::Tuple { elements, source } => Some(Atom::Tuple {
                elements: elements
                    .iter()
                    .map(|arg| {
                        self.known_direct_atom_for_atom(arg)
                            .unwrap_or_else(|| arg.clone())
                    })
                    .collect(),
                source: *source,
            }),
            Atom::AnonRecord { fields, source } => Some(Atom::AnonRecord {
                fields: self.known_direct_atom_fields(fields),
                source: *source,
            }),
            Atom::Record {
                name,
                fields,
                source,
            } => Some(Atom::Record {
                name: name.clone(),
                fields: self.known_direct_atom_fields(fields),
                source: *source,
            }),
            Atom::Var { name, .. } => self.known_direct_atom(&name.name),
            _ => None,
        }
    }

    pub(super) fn known_direct_value_for_atom(&self, atom: &Atom) -> Option<KnownDirectValue> {
        match atom {
            Atom::Lit { .. }
            | Atom::Symbol { .. }
            | Atom::BackendAtom { .. }
            | Atom::DictRef { .. }
            | Atom::Lambda { .. }
            | Atom::BackendSpawnThunk { .. } => Some(KnownDirectValue::Atom(atom.clone())),
            Atom::QualifiedRef { module, name, .. } => self
                .imported_direct_values
                .get(&(module.clone(), name.clone()))
                .map(|atom| {
                    self.known_direct_value_for_atom(atom)
                        .unwrap_or_else(|| KnownDirectValue::Atom(atom.clone()))
                })
                .or_else(|| Some(KnownDirectValue::Atom(atom.clone()))),
            Atom::Ctor { name, args, .. } => Some(KnownDirectValue::Ctor {
                name: name.clone(),
                args: args
                    .iter()
                    .map(|arg| {
                        self.known_direct_value_for_atom(arg)
                            .unwrap_or_else(|| KnownDirectValue::Atom(arg.clone()))
                    })
                    .collect(),
            }),
            Atom::Tuple { elements, .. } => Some(KnownDirectValue::Tuple(
                elements
                    .iter()
                    .map(|arg| {
                        self.known_direct_value_for_atom(arg)
                            .unwrap_or_else(|| KnownDirectValue::Atom(arg.clone()))
                    })
                    .collect(),
            )),
            Atom::AnonRecord { fields, .. } => Some(KnownDirectValue::AnonRecord(
                fields
                    .iter()
                    .map(|(name, atom)| {
                        (
                            name.clone(),
                            self.known_direct_value_for_atom(atom)
                                .unwrap_or_else(|| KnownDirectValue::Atom(atom.clone())),
                        )
                    })
                    .collect(),
            )),
            Atom::Record { name, fields, .. } => Some(KnownDirectValue::Record {
                name: name.clone(),
                fields: fields
                    .iter()
                    .map(|(name, atom)| {
                        (
                            name.clone(),
                            self.known_direct_value_for_atom(atom)
                                .unwrap_or_else(|| KnownDirectValue::Atom(atom.clone())),
                        )
                    })
                    .collect(),
            }),
            Atom::Var { name, .. } => self
                .known_direct_value(&name.name)
                .or_else(|| Some(KnownDirectValue::Atom(atom.clone()))),
        }
    }

    pub(super) fn known_direct_bool_for_atom(&self, atom: &Atom) -> Option<bool> {
        match self.known_direct_value_for_atom(atom)? {
            KnownDirectValue::Atom(Atom::Lit {
                value: Lit::Bool(value),
                ..
            }) => Some(value),
            _ => None,
        }
    }

    fn known_direct_atom_fields(&self, fields: &[(String, Atom)]) -> Vec<(String, Atom)> {
        fields
            .iter()
            .map(|(name, atom)| {
                (
                    name.clone(),
                    self.known_direct_atom_for_atom(atom)
                        .unwrap_or_else(|| atom.clone()),
                )
            })
            .collect()
    }

    pub(super) fn known_direct_field_value(
        &self,
        record: &Atom,
        field: &str,
        record_name: Option<&str>,
        anon_fields: &Option<Vec<String>>,
    ) -> Option<Atom> {
        match self.known_direct_atom_for_case_scrutinee(record)? {
            Atom::Record { name, fields, .. } => {
                if let Some(expected_name) = record_name
                    && mangle_ctor_atom(&name, self.ctors)
                        != mangle_ctor_atom(expected_name, self.ctors)
                {
                    return None;
                }
                fields
                    .into_iter()
                    .find_map(|(name, atom)| (name == field).then_some(atom))
            }
            Atom::AnonRecord { fields, .. } => {
                if let Some(expected_fields) = anon_fields
                    && !same_field_set(
                        &fields
                            .iter()
                            .map(|(name, _)| name.clone())
                            .collect::<Vec<_>>(),
                        expected_fields,
                    )
                {
                    return None;
                }
                fields
                    .into_iter()
                    .find_map(|(name, atom)| (name == field).then_some(atom))
            }
            _ => None,
        }
    }

    pub(super) fn known_direct_field_direct_value(
        &self,
        record: &Atom,
        field: &str,
        record_name: Option<&str>,
        anon_fields: &Option<Vec<String>>,
    ) -> Option<KnownDirectValue> {
        match self.known_direct_value_for_atom(record)? {
            KnownDirectValue::Record { name, fields, .. } => {
                if let Some(expected_name) = record_name
                    && mangle_ctor_atom(&name, self.ctors)
                        != mangle_ctor_atom(expected_name, self.ctors)
                {
                    return None;
                }
                fields
                    .into_iter()
                    .find_map(|(name, value)| (name == field).then_some(value))
            }
            KnownDirectValue::AnonRecord(fields) => {
                if let Some(expected_fields) = anon_fields
                    && !same_field_set(
                        &fields
                            .iter()
                            .map(|(name, _)| name.clone())
                            .collect::<Vec<_>>(),
                        expected_fields,
                    )
                {
                    return None;
                }
                fields
                    .into_iter()
                    .find_map(|(name, value)| (name == field).then_some(value))
            }
            KnownDirectValue::Atom(atom) => self
                .known_direct_field_value(&atom, field, record_name, anon_fields)
                .map(KnownDirectValue::Atom),
            _ => None,
        }
    }

    pub(super) fn known_direct_atom_pattern_bindings_for_params(
        &self,
        params: &[Pat],
        args: &[Atom],
    ) -> Vec<(String, Atom)> {
        let mut bindings = Vec::new();
        for (param, arg) in params.iter().zip(args) {
            let Some(arg) = self.known_direct_atom_for_atom(arg) else {
                continue;
            };
            let Some(param_bindings) = self.match_known_direct_atom_pattern(&arg, param) else {
                continue;
            };
            bindings.extend(param_bindings);
        }
        bindings
    }

    pub(super) fn known_direct_value_pattern_bindings_for_params(
        &self,
        params: &[Pat],
        args: &[Atom],
    ) -> Vec<(String, KnownDirectValue)> {
        let mut bindings = Vec::new();
        for (param, arg) in params.iter().zip(args) {
            let Some(arg) = self.known_direct_value_for_atom(arg) else {
                continue;
            };
            let Some(param_bindings) = self.match_known_direct_value_pattern(&arg, param) else {
                continue;
            };
            bindings.extend(param_bindings);
        }
        bindings
    }

    pub(super) fn known_direct_atom_bindings_for_all_params(
        &self,
        params: &[Pat],
        args: &[Atom],
    ) -> Option<Vec<(String, Atom)>> {
        if params.len() != args.len() {
            return None;
        }

        let mut bindings = Vec::new();
        for (param, arg) in params.iter().zip(args) {
            let arg = self.known_direct_atom_for_atom(arg)?;
            bindings.extend(self.match_known_direct_atom_pattern(&arg, param)?);
        }
        Some(bindings)
    }

    pub(super) fn known_direct_value_bindings_for_all_params(
        &self,
        params: &[Pat],
        args: &[Atom],
    ) -> Option<Vec<(String, KnownDirectValue)>> {
        if params.len() != args.len() {
            return None;
        }

        let mut bindings = Vec::new();
        for (param, arg) in params.iter().zip(args) {
            let arg = self.known_direct_value_for_atom(arg)?;
            bindings.extend(self.match_known_direct_value_pattern(&arg, param)?);
        }
        Some(bindings)
    }

    pub(super) fn match_known_direct_atom_pattern(
        &self,
        atom: &Atom,
        pat: &Pat,
    ) -> Option<Vec<(String, Atom)>> {
        match pat {
            Pat::Wildcard { .. } => Some(Vec::new()),
            Pat::Var { name, .. } => Some(vec![(name.clone(), atom.clone())]),
            Pat::Lit { value, .. } => {
                let Atom::Lit {
                    value: atom_value, ..
                } = atom
                else {
                    return None;
                };
                lit_values_match(atom_value, value).then(Vec::new)
            }
            Pat::Constructor { name, args, .. } => {
                let Atom::Ctor {
                    name: atom_name,
                    args: atom_args,
                    ..
                } = atom
                else {
                    return None;
                };
                if atom_args.len() != args.len()
                    || mangle_ctor_atom(atom_name, self.ctors) != mangle_ctor_atom(name, self.ctors)
                {
                    return None;
                }
                self.match_known_direct_atom_patterns(atom_args, args)
            }
            Pat::Tuple { elements, .. } => {
                let Atom::Tuple {
                    elements: atom_elements,
                    ..
                } = atom
                else {
                    return match elements.as_slice() {
                        [only] => self.match_known_direct_atom_pattern(atom, only),
                        _ => None,
                    };
                };
                if atom_elements.len() != elements.len() {
                    return None;
                }
                self.match_known_direct_atom_patterns(atom_elements, elements)
            }
            Pat::Record {
                name,
                fields,
                as_name,
                ..
            } => {
                let Atom::Record {
                    name: atom_name,
                    fields: atom_fields,
                    ..
                } = atom
                else {
                    return None;
                };
                if mangle_ctor_atom(atom_name, self.ctors) != mangle_ctor_atom(name, self.ctors) {
                    return None;
                }
                let mut bindings = self.match_known_direct_record_fields(atom_fields, fields)?;
                if let Some(as_name) = as_name {
                    bindings.push((as_name.clone(), atom.clone()));
                }
                Some(bindings)
            }
            Pat::AnonRecord { fields, .. } => {
                let Atom::AnonRecord {
                    fields: atom_fields,
                    ..
                } = atom
                else {
                    return None;
                };
                self.match_known_direct_record_fields(atom_fields, fields)
            }
            _ => None,
        }
    }

    pub(super) fn match_known_direct_value_pattern(
        &self,
        value: &KnownDirectValue,
        pat: &Pat,
    ) -> Option<Vec<(String, KnownDirectValue)>> {
        match pat {
            Pat::Wildcard { .. } => Some(Vec::new()),
            Pat::Var { name, .. } => Some(vec![(name.clone(), value.clone())]),
            Pat::Lit { value: lit, .. } => {
                let KnownDirectValue::Atom(Atom::Lit {
                    value: atom_value, ..
                }) = value
                else {
                    return None;
                };
                lit_values_match(atom_value, lit).then(Vec::new)
            }
            Pat::Constructor { name, args, .. } => {
                let KnownDirectValue::Ctor {
                    name: value_name,
                    args: value_args,
                    ..
                } = value
                else {
                    if let KnownDirectValue::Atom(atom) = value {
                        return self
                            .match_known_direct_atom_pattern(atom, pat)
                            .map(|bindings| {
                                bindings
                                    .into_iter()
                                    .map(|(name, atom)| (name, KnownDirectValue::Atom(atom)))
                                    .collect()
                            });
                    }
                    return None;
                };
                if value_args.len() != args.len()
                    || mangle_ctor_atom(value_name, self.ctors)
                        != mangle_ctor_atom(name, self.ctors)
                {
                    return None;
                }
                self.match_known_direct_value_patterns(value_args, args)
            }
            Pat::Tuple { elements, .. } => {
                let KnownDirectValue::Tuple(value_elements) = value else {
                    return match elements.as_slice() {
                        [only] => self.match_known_direct_value_pattern(value, only),
                        _ => {
                            if let KnownDirectValue::Atom(atom) = value {
                                return self.match_known_direct_atom_pattern(atom, pat).map(
                                    |bindings| {
                                        bindings
                                            .into_iter()
                                            .map(|(name, atom)| {
                                                (name, KnownDirectValue::Atom(atom))
                                            })
                                            .collect()
                                    },
                                );
                            }
                            None
                        }
                    };
                };
                if value_elements.len() != elements.len() {
                    return None;
                }
                self.match_known_direct_value_patterns(value_elements, elements)
            }
            Pat::Record {
                name,
                fields,
                as_name,
                ..
            } => {
                let KnownDirectValue::Record {
                    name: value_name,
                    fields: value_fields,
                    ..
                } = value
                else {
                    if let KnownDirectValue::Atom(atom) = value {
                        return self
                            .match_known_direct_atom_pattern(atom, pat)
                            .map(|bindings| {
                                bindings
                                    .into_iter()
                                    .map(|(name, atom)| (name, KnownDirectValue::Atom(atom)))
                                    .collect()
                            });
                    }
                    return None;
                };
                if mangle_ctor_atom(value_name, self.ctors) != mangle_ctor_atom(name, self.ctors) {
                    return None;
                }
                let mut bindings =
                    self.match_known_direct_value_record_fields(value_fields, fields)?;
                if let Some(as_name) = as_name {
                    bindings.push((as_name.clone(), value.clone()));
                }
                Some(bindings)
            }
            Pat::AnonRecord { fields, .. } => {
                let KnownDirectValue::AnonRecord(value_fields) = value else {
                    if let KnownDirectValue::Atom(atom) = value {
                        return self
                            .match_known_direct_atom_pattern(atom, pat)
                            .map(|bindings| {
                                bindings
                                    .into_iter()
                                    .map(|(name, atom)| (name, KnownDirectValue::Atom(atom)))
                                    .collect()
                            });
                    }
                    return None;
                };
                self.match_known_direct_value_record_fields(value_fields, fields)
            }
            _ => None,
        }
    }

    fn match_known_direct_atom_patterns(
        &self,
        atoms: &[Atom],
        pats: &[Pat],
    ) -> Option<Vec<(String, Atom)>> {
        let mut bindings = Vec::new();
        for (atom, pat) in atoms.iter().zip(pats) {
            bindings.extend(self.match_known_direct_atom_pattern(atom, pat)?);
        }
        Some(bindings)
    }

    fn match_known_direct_value_patterns(
        &self,
        values: &[KnownDirectValue],
        pats: &[Pat],
    ) -> Option<Vec<(String, KnownDirectValue)>> {
        let mut bindings = Vec::new();
        for (value, pat) in values.iter().zip(pats) {
            bindings.extend(self.match_known_direct_value_pattern(value, pat)?);
        }
        Some(bindings)
    }

    fn match_known_direct_record_fields(
        &self,
        atom_fields: &[(String, Atom)],
        pat_fields: &[(String, Option<Pat>)],
    ) -> Option<Vec<(String, Atom)>> {
        let atom_field_map: HashMap<&str, &Atom> = atom_fields
            .iter()
            .map(|(name, atom)| (name.as_str(), atom))
            .collect();
        let mut bindings = Vec::new();
        for (field_name, pat) in pat_fields {
            let atom = atom_field_map.get(field_name.as_str())?;
            match pat {
                Some(pat) => bindings.extend(self.match_known_direct_atom_pattern(atom, pat)?),
                None => bindings.push((field_name.clone(), (*atom).clone())),
            }
        }
        Some(bindings)
    }

    fn match_known_direct_value_record_fields(
        &self,
        value_fields: &[(String, KnownDirectValue)],
        pat_fields: &[(String, Option<Pat>)],
    ) -> Option<Vec<(String, KnownDirectValue)>> {
        let value_field_map: HashMap<&str, &KnownDirectValue> = value_fields
            .iter()
            .map(|(name, value)| (name.as_str(), value))
            .collect();
        let mut bindings = Vec::new();
        for (field_name, pat) in pat_fields {
            let value = value_field_map.get(field_name.as_str())?;
            match pat {
                Some(pat) => bindings.extend(self.match_known_direct_value_pattern(value, pat)?),
                None => bindings.push((field_name.clone(), (*value).clone())),
            }
        }
        Some(bindings)
    }

    pub(super) fn lower_known_direct_value(&mut self, value: &KnownDirectValue) -> CExpr {
        match value {
            KnownDirectValue::Atom(atom) => self.lower_atom(atom),
            KnownDirectValue::Core(expr) => expr.clone(),
            KnownDirectValue::Ctor { name, args, .. } => {
                self.lower_known_direct_ctor_value(name, args)
            }
            KnownDirectValue::Tuple(elements) => {
                let (elements, bindings) = self.lower_known_direct_values_as_core_atoms(elements);
                bindings
                    .into_iter()
                    .rev()
                    .fold(CExpr::Tuple(elements), |body, (name, value)| {
                        CExpr::Let(name, Box::new(value), Box::new(body))
                    })
            }
            KnownDirectValue::AnonRecord(fields) => {
                let names: Vec<&str> = fields.iter().map(|(n, _)| n.as_str()).collect();
                let tag = crate::ast::anon_record_tag(&names);
                let mut sorted: Vec<&(String, KnownDirectValue)> = fields.iter().collect();
                sorted.sort_by(|a, b| a.0.cmp(&b.0));
                let sorted_values: Vec<KnownDirectValue> =
                    sorted.into_iter().map(|(_, value)| value.clone()).collect();
                let (field_values, bindings) =
                    self.lower_known_direct_values_as_core_atoms(&sorted_values);
                let mut elems = vec![CExpr::Lit(CLit::Atom(tag))];
                elems.extend(field_values);
                bindings
                    .into_iter()
                    .rev()
                    .fold(CExpr::Tuple(elems), |body, (name, value)| {
                        CExpr::Let(name, Box::new(value), Box::new(body))
                    })
            }
            KnownDirectValue::Record { name, fields, .. } => {
                let tag = mangle_ctor_atom(name, self.ctors);
                let field_values: Vec<KnownDirectValue> =
                    fields.iter().map(|(_, value)| value.clone()).collect();
                let (field_values, bindings) =
                    self.lower_known_direct_values_as_core_atoms(&field_values);
                let mut elems = vec![CExpr::Lit(CLit::Atom(tag))];
                elems.extend(field_values);
                bindings
                    .into_iter()
                    .rev()
                    .fold(CExpr::Tuple(elems), |body, (name, value)| {
                        CExpr::Let(name, Box::new(value), Box::new(body))
                    })
            }
        }
    }

    fn lower_known_direct_ctor_value(&mut self, name: &str, args: &[KnownDirectValue]) -> CExpr {
        let bare = name.rsplit('.').next().unwrap_or(name);
        match bare {
            "Nil" if args.is_empty() => return CExpr::Nil,
            "True" if args.is_empty() => return CExpr::Lit(CLit::Atom("true".to_string())),
            "False" if args.is_empty() => return CExpr::Lit(CLit::Atom("false".to_string())),
            _ => {}
        }
        if name == "Cons" && args.len() == 2 {
            let (args, bindings) = self.lower_known_direct_values_as_core_atoms(args);
            let body = CExpr::Cons(Box::new(args[0].clone()), Box::new(args[1].clone()));
            return bindings
                .into_iter()
                .rev()
                .fold(body, |body, (name, value)| {
                    CExpr::Let(name, Box::new(value), Box::new(body))
                });
        }
        let tag = mangle_ctor_atom(name, self.ctors);
        let (args, bindings) = self.lower_known_direct_values_as_core_atoms(args);
        let mut elems = vec![CExpr::Lit(CLit::Atom(tag))];
        elems.extend(args);
        bindings
            .into_iter()
            .rev()
            .fold(CExpr::Tuple(elems), |body, (name, value)| {
                CExpr::Let(name, Box::new(value), Box::new(body))
            })
    }

    fn lower_known_direct_values_as_core_atoms(
        &mut self,
        values: &[KnownDirectValue],
    ) -> (Vec<CExpr>, Vec<(String, CExpr)>) {
        let mut lowered = Vec::with_capacity(values.len());
        let mut bindings = Vec::new();
        for value in values {
            let expr = self.lower_known_direct_value(value);
            if core_expr_is_simple_value(&expr) {
                lowered.push(expr);
            } else {
                let temp = self.fresh_cps_temp("_KnownValue");
                lowered.push(CExpr::Var(temp.clone()));
                bindings.push((temp, expr));
            }
        }
        (lowered, bindings)
    }
}

fn lit_values_match(left: &Lit, right: &Lit) -> bool {
    match (left, right) {
        (Lit::Int(_, left), Lit::Int(_, right)) => left == right,
        (Lit::Float(_, left), Lit::Float(_, right)) => left.to_bits() == right.to_bits(),
        (Lit::String(left, left_kind), Lit::String(right, right_kind)) => {
            left == right && left_kind == right_kind
        }
        (Lit::Bool(left), Lit::Bool(right)) => left == right,
        (Lit::Unit, Lit::Unit) => true,
        _ => false,
    }
}

fn same_field_set(left: &[String], right: &[String]) -> bool {
    if left.len() != right.len() {
        return false;
    }
    let left: HashSet<&str> = left.iter().map(String::as_str).collect();
    right.iter().all(|field| left.contains(field.as_str()))
}
