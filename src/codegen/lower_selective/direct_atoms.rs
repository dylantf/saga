use super::*;

impl<'a, 'info> DirectLowerer<'a, 'info> {
    pub(super) fn lower_atom(&mut self, atom: &Atom) -> CExpr {
        match atom {
            Atom::Var { name, .. } => {
                if let Some(value) = self.known_direct_value(&name.name) {
                    return self.lower_known_direct_value(&value);
                }
                if let Some(atom) = self.known_direct_atom(&name.name) {
                    return self.lower_atom(&atom);
                }
                if self.is_local(&name.name) {
                    if matches!(
                        self.local_shape(&name.name),
                        Some(
                            LocalValueShape::CpsCallable { .. }
                                | LocalValueShape::RuntimeCpsCallable { .. }
                        )
                    ) {
                        return self.lower_cps_value_atom(atom);
                    }
                    CExpr::Var(core_var(&name.name))
                } else if self.cps_value_atom_shape(atom).is_some() {
                    self.lower_cps_value_atom(atom)
                } else if let Some(value_ref) = self.direct_function_value_ref(atom) {
                    value_ref
                } else if let Some(value_ref) = self.imported_zero_arity_value_ref(&name.name) {
                    value_ref
                } else if self.direct_values.contains(&name.name) {
                    CExpr::Apply(Box::new(CExpr::FunRef(name.name.clone(), 0)), vec![])
                } else {
                    self.unsupported(&format!("non-local atom '{}'", name.name))
                }
            }
            Atom::Lit { value, .. } => lower_lit_atom(value),
            Atom::Ctor { name, args, .. } => self.lower_ctor_atom(name, args),
            Atom::Tuple { elements, .. } => {
                let (elements, bindings) = self.lower_atoms_as_core_values(elements);
                bindings
                    .into_iter()
                    .rev()
                    .fold(CExpr::Tuple(elements), |body, (name, value)| {
                        CExpr::Let(name, Box::new(value), Box::new(body))
                    })
            }
            Atom::AnonRecord { fields, .. } => self.lower_anon_record_atom(fields),
            Atom::Record { name, fields, .. } => self.lower_record_atom(name, fields),
            Atom::Lambda { params, body, .. } => {
                if self.lambda_is_direct_subset(params, body) {
                    self.lower_lambda_atom(params, body)
                } else if self.cps_value_atom_shape(atom).is_some() {
                    self.lower_cps_value_atom(atom)
                } else if self.lambda_is_direct_cps_island_subset(params, body) {
                    self.lower_direct_cps_island_lambda_atom(params, body)
                } else {
                    self.lower_lambda_atom(params, body)
                }
            }
            Atom::Symbol { symbol, .. } => {
                crate::codegen::lower::util::lower_string_to_binary(symbol)
            }
            Atom::QualifiedRef { .. } => {
                if let Some(value) = self.known_direct_value_for_atom(atom)
                    && !matches!(value, KnownDirectValue::Atom(Atom::QualifiedRef { .. }))
                {
                    self.lower_known_direct_value(&value)
                } else if self.cps_value_atom_shape(atom).is_some() {
                    self.lower_cps_value_atom(atom)
                } else {
                    self.direct_function_value_ref(atom)
                        .unwrap_or_else(|| self.unsupported_atom(atom))
                }
            }
            Atom::BackendAtom { atom, .. } => CExpr::Lit(CLit::Atom(atom.clone())),
            Atom::BackendSpawnThunk { callback, source } => {
                self.lower_backend_spawn_thunk(callback, *source)
            }
            Atom::DictRef { .. } => self.unsupported_atom(atom),
        }
    }

    pub(super) fn imported_zero_arity_value_ref(&self, name: &str) -> Option<CExpr> {
        let mut candidates = self
            .module_ctx
            .modules
            .iter()
            .filter_map(|(module_name, module)| {
                let (_, scheme) = module
                    .codegen_info
                    .exports
                    .iter()
                    .find(|(export_name, _)| export_name == name)?;
                let (arity, effects) =
                    crate::codegen::type_shape::arity_and_effects_from_type(&scheme.ty);
                (arity == 0 && effects.is_empty())
                    .then(|| CExpr::Call(erlang_module_name(module_name), name.to_string(), vec![]))
            });
        let candidate = candidates.next()?;
        candidates.next().is_none().then_some(candidate)
    }

    pub(super) fn lower_backend_spawn_thunk(&mut self, callback: &Atom, source: NodeId) -> CExpr {
        let callback_expr = self.lower_effect_protocol_arg_atom(callback);
        let k_var = format!("_SpawnK{}", source.0);
        let v_var = format!("_SpawnV{}", source.0);
        let identity_k = CExpr::Fun(vec![v_var.clone()], Box::new(CExpr::Var(v_var)));
        let apply_callback = CExpr::Apply(
            Box::new(callback_expr),
            vec![
                CExpr::Lit(CLit::Atom("unit".to_string())),
                CExpr::Tuple(vec![]),
                CExpr::Var(k_var.clone()),
            ],
        );
        CExpr::Fun(
            vec![],
            Box::new(CExpr::Let(
                k_var,
                Box::new(identity_k),
                Box::new(apply_callback),
            )),
        )
    }

    pub(super) fn lower_lambda_atom(&mut self, params: &[Pat], body: &MExpr) -> CExpr {
        if params.iter().any(|p| !direct_param_supported(p)) {
            self.unsupported("direct lambda with unsupported parameter pattern");
        }
        let param_names = lower_param_names(params);
        self.push_scope();
        for pat in params {
            self.bind_pat_locals(pat);
        }
        let lowered_body = self.lower_expr(body);
        let lowered_body = self.wrap_param_match(params, &param_names, lowered_body);
        self.pop_scope();
        CExpr::Fun(param_names, Box::new(lowered_body))
    }

    pub(super) fn lower_direct_cps_island_lambda_atom(
        &mut self,
        params: &[Pat],
        body: &MExpr,
    ) -> CExpr {
        if params.iter().any(|p| !direct_param_supported(p)) {
            self.unsupported("direct CPS-island lambda with unsupported parameter pattern");
        }
        let param_names = lower_param_names(params);
        self.push_scope();
        for pat in params {
            self.bind_pat_locals(pat);
        }
        let return_k = self.identity_cps_continuation();
        let lowered_body = self.lower_cps_expr(body, CExpr::Tuple(vec![]), return_k);
        let lowered_body = self.wrap_param_match(params, &param_names, lowered_body);
        self.pop_scope();
        CExpr::Fun(param_names, Box::new(lowered_body))
    }

    pub(super) fn lower_dict_constructor(&mut self, dc: &MDictConstructor) -> CFunDef {
        let mut methods = Vec::with_capacity(dc.methods.len());
        self.push_scope();
        for dict_param in &dc.dict_params {
            self.current_scope_mut().insert(dict_param.clone());
        }
        for (index, method) in dc.methods.iter().enumerate() {
            let effectful = dc
                .method_effects
                .get(index)
                .is_some_and(|effects| !effects.is_empty())
                || dc.method_open_rows.get(index).copied().unwrap_or(false);

            let key = KnownDictMethodKey {
                constructor_name: dc.name.clone(),
                method_index: index,
                dict_arg_keys: Vec::new(),
            };
            let inserted = self.active_known_dict_methods.insert(key.clone());
            let lowered = match method {
                MExpr::Pure(Atom::Lambda { params, body, .. }) if effectful => {
                    self.lower_cps_lambda_atom(params, body)
                }
                MExpr::Pure(Atom::Lambda { params, body, .. }) => {
                    self.lower_lambda_atom(params, body)
                }
                _ if !effectful => self.lower_expr(method),
                _ => self.unsupported(&format!(
                    "dict constructor '{}' method {} is not a lowerable method value",
                    dc.name, index
                )),
            };
            if inserted {
                self.active_known_dict_methods.remove(&key);
            }
            methods.push(lowered);
        }
        self.pop_scope();

        CFunDef {
            name: dc.name.clone(),
            arity: dc.dict_params.len(),
            body: CExpr::Fun(
                dc.dict_params.iter().map(|param| core_var(param)).collect(),
                Box::new(CExpr::Tuple(methods)),
            ),
        }
    }

    pub(super) fn lower_ctor_atom(&mut self, name: &str, args: &[Atom]) -> CExpr {
        let bare = name.rsplit('.').next().unwrap_or(name);
        match bare {
            "Nil" if args.is_empty() => return CExpr::Nil,
            "True" if args.is_empty() => return CExpr::Lit(CLit::Atom("true".to_string())),
            "False" if args.is_empty() => return CExpr::Lit(CLit::Atom("false".to_string())),
            _ => {}
        }
        if name == "Cons" && args.len() == 2 {
            let (args, bindings) = self.lower_atoms_as_core_values(args);
            let body = CExpr::Cons(Box::new(args[0].clone()), Box::new(args[1].clone()));
            return bindings
                .into_iter()
                .rev()
                .fold(body, |body, (name, value)| {
                    CExpr::Let(name, Box::new(value), Box::new(body))
                });
        }
        let tag = mangle_ctor_atom(name, self.ctors);
        let (args, bindings) = self.lower_atoms_as_core_values(args);
        let mut elems = vec![CExpr::Lit(CLit::Atom(tag))];
        elems.extend(args);
        bindings
            .into_iter()
            .rev()
            .fold(CExpr::Tuple(elems), |body, (name, value)| {
                CExpr::Let(name, Box::new(value), Box::new(body))
            })
    }

    pub(super) fn lower_anon_record_atom(&mut self, fields: &[(String, Atom)]) -> CExpr {
        let names: Vec<&str> = fields.iter().map(|(n, _)| n.as_str()).collect();
        let tag = crate::ast::anon_record_tag(&names);
        let mut sorted: Vec<&(String, Atom)> = fields.iter().collect();
        sorted.sort_by(|a, b| a.0.cmp(&b.0));
        let sorted_atoms: Vec<Atom> = sorted.into_iter().map(|(_, atom)| atom.clone()).collect();
        let (fields, bindings) = self.lower_atoms_as_core_values(&sorted_atoms);
        let mut elems = vec![CExpr::Lit(CLit::Atom(tag))];
        elems.extend(fields);
        bindings
            .into_iter()
            .rev()
            .fold(CExpr::Tuple(elems), |body, (name, value)| {
                CExpr::Let(name, Box::new(value), Box::new(body))
            })
    }

    pub(super) fn lower_record_atom(&mut self, name: &str, fields: &[(String, Atom)]) -> CExpr {
        let tag = mangle_ctor_atom(name, self.ctors);
        let field_atoms: Vec<Atom> = fields.iter().map(|(_, atom)| atom.clone()).collect();
        let (fields, bindings) = self.lower_atoms_as_core_values(&field_atoms);
        let mut elems = vec![CExpr::Lit(CLit::Atom(tag))];
        elems.extend(fields);
        bindings
            .into_iter()
            .rev()
            .fold(CExpr::Tuple(elems), |body, (name, value)| {
                CExpr::Let(name, Box::new(value), Box::new(body))
            })
    }

    pub(super) fn lower_atoms_as_core_values(
        &mut self,
        atoms: &[Atom],
    ) -> (Vec<CExpr>, Vec<(String, CExpr)>) {
        let mut lowered = Vec::with_capacity(atoms.len());
        let mut bindings = Vec::new();
        for atom in atoms {
            let (expr, binding) = self.lower_atom_as_core_value(atom, "_AtomValue");
            lowered.push(expr);
            bindings.extend(binding);
        }
        (lowered, bindings)
    }

    pub(super) fn lower_atom_as_core_value(
        &mut self,
        atom: &Atom,
        temp_prefix: &str,
    ) -> (CExpr, Option<(String, CExpr)>) {
        let expr = self.lower_atom(atom);
        if core_expr_is_simple_value(&expr) {
            (expr, None)
        } else {
            let temp = self.fresh_cps_temp(temp_prefix);
            (CExpr::Var(temp.clone()), Some((temp, expr)))
        }
    }

    pub(super) fn wrap_core_value_bindings(
        &self,
        body: CExpr,
        bindings: Vec<(String, CExpr)>,
    ) -> CExpr {
        bindings
            .into_iter()
            .rev()
            .fold(body, |body, (name, value)| {
                CExpr::Let(name, Box::new(value), Box::new(body))
            })
    }

    pub(super) fn lower_bitstring_value(
        &mut self,
        segments: &[crate::codegen::monadic::ir::MBitSegment],
    ) -> CExpr {
        let mut lowered_segments: Vec<CBinSeg<CExpr>> = Vec::with_capacity(segments.len());
        for segment in segments {
            if let Atom::Lit {
                value: Lit::String(s, kind),
                ..
            } = &segment.value
            {
                let resolved = if kind.is_multiline() {
                    process_string_escapes(s)
                } else {
                    s.clone()
                };
                lowered_segments.extend(resolved.as_bytes().iter().copied().map(CBinSeg::Byte));
                continue;
            }

            let is_binary = segment.specs.contains(&crate::ast::BitSegSpec::Binary);
            let value = self.lower_atom(&segment.value);
            if is_binary && segment.size.is_none() {
                lowered_segments.push(CBinSeg::BinaryAll(value));
                continue;
            }

            let (type_name, default_size, unit) = resolve_bit_segment_meta(&segment.specs);
            let flags = resolve_bit_segment_flags(&segment.specs);
            let size = segment.size.as_ref().map(|size| self.lower_atom(size));
            let size = resolve_bit_segment_size(size, &type_name, default_size);
            lowered_segments.push(CBinSeg::Segment {
                value,
                size,
                unit,
                type_name,
                flags,
            });
        }
        CExpr::Binary(lowered_segments)
    }
}
