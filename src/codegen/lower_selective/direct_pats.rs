use super::*;

impl<'a, 'info> DirectLowerer<'a, 'info> {
    pub(super) fn lower_pat(&self, pat: &Pat) -> CPat {
        match pat {
            Pat::Wildcard { .. } => CPat::Wildcard,
            Pat::Var { name, .. } => CPat::Var(core_var(name)),
            Pat::Lit { value, .. } => match value {
                Lit::String(s, _) => CPat::Binary(
                    s.as_bytes()
                        .iter()
                        .map(|&byte| CBinSeg::Byte(byte))
                        .collect(),
                ),
                _ => CPat::Lit(lower_lit_pat(value)),
            },
            Pat::Tuple { elements, .. } => {
                CPat::Tuple(elements.iter().map(|p| self.lower_pat(p)).collect())
            }
            Pat::Constructor { name, args, .. } => self.lower_ctor_pat(name, args),
            Pat::Record {
                name,
                fields,
                as_name,
                ..
            } => self.lower_record_pat(name, fields, as_name.as_deref()),
            Pat::AnonRecord { fields, .. } => self.lower_anon_record_pat(fields),
            Pat::StringPrefix { prefix, rest, .. } => {
                let mut segs: Vec<CBinSeg<CPat>> = prefix
                    .as_bytes()
                    .iter()
                    .map(|&b| CBinSeg::Byte(b))
                    .collect();
                segs.push(CBinSeg::BinaryAll(self.lower_pat(rest)));
                CPat::Binary(segs)
            }
            Pat::BitStringPat { segments, .. } => {
                let mut segs = Vec::with_capacity(segments.len());
                for segment in segments {
                    if let Pat::Lit {
                        value: Lit::String(s, kind),
                        ..
                    } = &segment.value
                    {
                        let resolved = if kind.is_multiline() {
                            process_string_escapes(s)
                        } else {
                            s.clone()
                        };
                        segs.extend(resolved.as_bytes().iter().copied().map(CBinSeg::Byte));
                        continue;
                    }
                    segs.push(self.lower_bit_segment_pat(segment));
                }
                CPat::Binary(segs)
            }
            Pat::ListPat { .. } | Pat::ConsPat { .. } | Pat::Or { .. } => {
                unreachable!("surface syntax should be desugared before codegen")
            }
        }
    }

    pub(super) fn lower_bit_segment_pat(
        &self,
        segment: &crate::ast::BitSegment<Pat>,
    ) -> CBinSeg<CPat> {
        let is_binary = segment.specs.contains(&crate::ast::BitSegSpec::Binary);
        let pat = self.lower_pat(&segment.value);

        if is_binary && segment.size.is_none() {
            return CBinSeg::BinaryAll(pat);
        }

        let (type_name, default_size, unit) = resolve_bit_segment_meta(&segment.specs);
        let flags = resolve_bit_segment_flags(&segment.specs);
        let size = segment.size.as_deref().map(lower_pat_size_expr);
        let size = resolve_bit_segment_size(size, &type_name, default_size);

        CBinSeg::Segment {
            value: pat,
            size,
            unit,
            type_name,
            flags,
        }
    }

    pub(super) fn lower_record_pat(
        &self,
        name: &str,
        fields: &[(String, Option<Pat>)],
        as_name: Option<&str>,
    ) -> CPat {
        let tag = mangle_ctor_atom(name, self.ctors);
        let mut elems = vec![CPat::Lit(CLit::Atom(tag))];
        let field_map: HashMap<&str, Option<&Pat>> = fields
            .iter()
            .map(|(field_name, pat)| (field_name.as_str(), pat.as_ref()))
            .collect();

        match self.record_pat_field_order(name) {
            Some(order) => {
                for field_name in order {
                    match field_map.get(field_name.as_str()) {
                        Some(Some(pat)) => elems.push(self.lower_pat(pat)),
                        Some(None) => elems.push(CPat::Var(core_var(&field_name))),
                        None => elems.push(CPat::Wildcard),
                    }
                }
            }
            None => {
                for (field_name, pat) in fields {
                    match pat {
                        Some(pat) => elems.push(self.lower_pat(pat)),
                        None => elems.push(CPat::Var(core_var(field_name))),
                    }
                }
            }
        }

        let tuple_pat = CPat::Tuple(elems);
        match as_name {
            Some(var) => CPat::Alias(core_var(var), Box::new(tuple_pat)),
            None => tuple_pat,
        }
    }

    pub(super) fn record_pat_field_order(&self, name: &str) -> Option<Vec<String>> {
        self.effect_info
            .records
            .get(name)
            .or_else(|| {
                let bare = name.rsplit('.').next().unwrap_or(name);
                self.effect_info.records.get(bare)
            })
            .or_else(|| {
                let bare = name.rsplit('.').next().unwrap_or(name);
                self.effect_info
                    .records
                    .iter()
                    .find(|(candidate, _)| {
                        candidate
                            .rsplit('.')
                            .next()
                            .is_some_and(|last| last == bare)
                    })
                    .map(|(_, info)| info)
            })
            .map(|info| info.fields.iter().map(|(field, _)| field.clone()).collect())
    }

    pub(super) fn lower_anon_record_pat(&self, fields: &[(String, Option<Pat>)]) -> CPat {
        let field_names: Vec<&str> = fields.iter().map(|(name, _)| name.as_str()).collect();
        let tag = crate::ast::anon_record_tag(&field_names);
        let mut sorted_names = field_names;
        sorted_names.sort();
        let field_map: HashMap<&str, Option<&Pat>> = fields
            .iter()
            .map(|(field_name, pat)| (field_name.as_str(), pat.as_ref()))
            .collect();

        let mut elems = vec![CPat::Lit(CLit::Atom(tag))];
        for field_name in sorted_names {
            match field_map.get(field_name) {
                Some(Some(pat)) => elems.push(self.lower_pat(pat)),
                Some(None) => elems.push(CPat::Var(core_var(field_name))),
                None => elems.push(CPat::Wildcard),
            }
        }
        CPat::Tuple(elems)
    }

    pub(super) fn lower_ctor_pat(&self, name: &str, args: &[Pat]) -> CPat {
        let bare = name.rsplit('.').next().unwrap_or(name);
        match bare {
            "Nil" if args.is_empty() => return CPat::Nil,
            "True" if args.is_empty() => return CPat::Lit(CLit::Atom("true".to_string())),
            "False" if args.is_empty() => return CPat::Lit(CLit::Atom("false".to_string())),
            "Normal" | "Shutdown" | "Killed" | "Noproc" if args.is_empty() => {
                return CPat::Lit(CLit::Atom(mangle_ctor_atom(bare, self.ctors)));
            }
            _ => {}
        }
        if bare == "Cons" && args.len() == 2 {
            return CPat::Cons(
                Box::new(self.lower_pat(&args[0])),
                Box::new(self.lower_pat(&args[1])),
            );
        }
        let tag = mangle_ctor_atom(name, self.ctors);
        let mut elems = vec![CPat::Lit(CLit::Atom(tag))];
        elems.extend(args.iter().map(|pat| self.lower_pat(pat)));
        CPat::Tuple(elems)
    }
}
