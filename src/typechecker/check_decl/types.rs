use super::*;

impl Checker {
    pub(crate) fn register_type_def(
        &mut self,
        name: &str,
        type_params: &[TypeParam],
        variants: &[&ast::TypeConstructor],
    ) -> Result<(), Diagnostic> {
        // Create fresh type variables for the type parameters, honoring
        // declared kinds (e.g. `(n : Symbol)`).
        let mut param_vars: Vec<(String, u32)> = type_params
            .iter()
            .map(|p| {
                let var = self.fresh_var();
                let id = match var {
                    Type::Var(id) => id,
                    _ => unreachable!(),
                };
                (p.name.clone(), id)
            })
            .collect();

        // Canonical type name: "Module.TypeName" for module types, bare for non-module.
        // Don't apply builtin canonicalization here — a locally-defined "Maybe" is NOT
        // the stdlib Std.Maybe.Maybe.
        let canonical_name = match &self.current_module {
            Some(module) => format!("{}.{}", module, name),
            None => name.to_string(),
        };

        let result_type = Type::Con(
            canonical_name.clone(),
            param_vars.iter().map(|(_, id)| Type::Var(*id)).collect(),
        );

        let forall: Vec<u32> = param_vars.iter().map(|(_, id)| *id).collect();

        for variant in variants {
            let canonical_ctor = match &self.current_module {
                Some(module) => format!("{}.{}", module, variant.name),
                None => variant.name.clone(),
            };
            let ctor_ty = if variant.fields.is_empty() {
                result_type.clone()
            } else {
                // Build: field1 -> field2 -> ... -> ResultType
                let mut ty = result_type.clone();
                for (_, field) in variant.fields.iter().rev() {
                    let field_ty = self.convert_user_type_expr(field, &mut param_vars);
                    ty = Type::arrow(field_ty, ty);
                }
                ty
            };

            let scheme = Scheme {
                forall: forall.clone(),
                constraints: vec![],
                ty: ctor_ty,
            };
            self.constructors
                .insert(canonical_ctor.clone(), scheme.clone());
            // Keep the source-bare entry for module export collection and
            // pre-resolve local metadata; use-site lookup resolves to canonical.
            self.constructors.insert(variant.name.clone(), scheme);
            self.lsp
                .constructor_def_ids
                .insert(canonical_ctor.clone(), variant.id);
            self.lsp
                .constructor_def_ids
                .insert(variant.name.clone(), variant.id);
            self.lsp.node_spans.insert(variant.id, variant.span);
        }

        self.adt_variants.insert(
            canonical_name.clone(),
            variants
                .iter()
                .map(|v| {
                    let canonical_ctor = match &self.current_module {
                        Some(module) => format!("{}.{}", module, v.name),
                        None => v.name.clone(),
                    };
                    (canonical_ctor, v.fields.len())
                })
                .collect(),
        );

        self.type_arity.insert(canonical_name, type_params.len());

        Ok(())
    }

    pub(crate) fn register_type_alias(
        &mut self,
        name: &str,
        type_params: &[TypeParam],
        body: &ast::TypeExpr,
        span: Span,
    ) -> Result<(), Diagnostic> {
        let mut param_vars: Vec<(String, u32)> = type_params
            .iter()
            .map(|p| {
                let var = self.fresh_var();
                let id = match var {
                    Type::Var(id) => id,
                    _ => unreachable!(),
                };
                (p.name.clone(), id)
            })
            .collect();

        let canonical_name = match &self.current_module {
            Some(module) => format!("{}.{}", module, name),
            None => name.to_string(),
        };

        // Convert the body; further nested aliases unfold via try_unfold_alias.
        // Any new entries added to `param_vars` beyond the declared params
        // are free type variables in the alias body — reject them, since
        // Saga doesn't implicitly quantify type alias bodies.
        let declared_count = param_vars.len();
        let body_ty = self.convert_type_expr_inner(body, &mut param_vars);
        // The inner entry point bypasses convert_type_expr's wrapper, so
        // run the partial-alias check explicitly so invalid alias bodies
        // (`type alias Bad = Bag` where `Bag` has arity 1) fail at the
        // declaration, not at a downstream use site.
        self.check_no_partial_alias(&body_ty, body.span());
        if param_vars.len() > declared_count {
            let extras: Vec<String> = param_vars[declared_count..]
                .iter()
                .map(|(n, _)| format!("`{}`", n))
                .collect();
            return Err(Diagnostic::error_at(
                body.span(),
                format!(
                    "type alias `{}` body references undeclared type variable{}: {}. \
                     Add {} to the alias's parameter list.",
                    name,
                    if extras.len() == 1 { "" } else { "s" },
                    extras.join(", "),
                    if extras.len() == 1 { "it" } else { "them" },
                ),
            ));
        }

        let info = crate::typechecker::TypeAliasInfo {
            param_vars: param_vars.iter().map(|(_, id)| *id).collect(),
            body: body_ty,
            span,
        };
        self.type_aliases.insert(canonical_name, info);
        Ok(())
    }

    /// Detect cycles among type aliases declared in this module. A cycle is
    /// any alias whose body transitively references itself. Cross-module
    /// alias chains can't cycle because they're acyclic at module level
    /// (modules don't have mutual imports).
    pub(crate) fn detect_alias_cycles(
        &self,
        aliases: &[&Decl],
    ) -> std::result::Result<(), Vec<Diagnostic>> {
        use std::collections::HashSet;
        // Collect alias names declared in this module (bare + canonical).
        let mut local_aliases: HashMap<String, String> = HashMap::new();
        for decl in aliases {
            if let Decl::TypeAlias { name, .. } = decl {
                let canonical = match &self.current_module {
                    Some(module) => format!("{}.{}", module, name),
                    None => name.clone(),
                };
                local_aliases.insert(name.clone(), canonical);
            }
        }

        fn collect_alias_refs(
            texpr: &ast::TypeExpr,
            local: &HashMap<String, String>,
            scope: &crate::typechecker::ScopeMap,
            out: &mut HashSet<String>,
        ) {
            match texpr {
                ast::TypeExpr::Named { name, .. } => {
                    if let Some(canonical) = local.get(name) {
                        out.insert(canonical.clone());
                    } else if let Some(canonical) = scope.resolve_type(name)
                        && local.values().any(|v| v == canonical)
                    {
                        out.insert(canonical.to_string());
                    }
                }
                ast::TypeExpr::Var { .. } => {}
                ast::TypeExpr::App { func, arg, .. } => {
                    collect_alias_refs(func, local, scope, out);
                    collect_alias_refs(arg, local, scope, out);
                }
                ast::TypeExpr::Arrow { from, to, .. } => {
                    collect_alias_refs(from, local, scope, out);
                    collect_alias_refs(to, local, scope, out);
                }
                ast::TypeExpr::Record { fields, .. } => {
                    for (_, t) in fields {
                        collect_alias_refs(t, local, scope, out);
                    }
                }
                ast::TypeExpr::Labeled { inner, .. } => {
                    collect_alias_refs(inner, local, scope, out);
                }
            }
        }

        let mut graph: HashMap<String, HashSet<String>> = HashMap::new();
        let mut spans: HashMap<String, Span> = HashMap::new();
        for decl in aliases {
            if let Decl::TypeAlias {
                name, body, span, ..
            } = decl
            {
                let canonical = local_aliases[name].clone();
                let mut refs = HashSet::new();
                collect_alias_refs(body, &local_aliases, &self.scope_map, &mut refs);
                graph.insert(canonical.clone(), refs);
                spans.insert(canonical, *span);
            }
        }

        // DFS for cycles.
        #[derive(PartialEq, Eq, Clone, Copy)]
        enum Color {
            White,
            Gray,
            Black,
        }
        let mut color: HashMap<String, Color> =
            graph.keys().map(|k| (k.clone(), Color::White)).collect();
        let mut cycle: Option<Vec<String>> = None;

        fn visit(
            node: &str,
            graph: &HashMap<String, HashSet<String>>,
            color: &mut HashMap<String, Color>,
            stack: &mut Vec<String>,
            cycle: &mut Option<Vec<String>>,
        ) {
            if cycle.is_some() {
                return;
            }
            color.insert(node.to_string(), Color::Gray);
            stack.push(node.to_string());
            if let Some(edges) = graph.get(node) {
                for dep in edges {
                    match color.get(dep).copied().unwrap_or(Color::Black) {
                        Color::White => visit(dep, graph, color, stack, cycle),
                        Color::Gray => {
                            // Found a cycle: from `dep` in stack to current.
                            let start = stack.iter().position(|n| n == dep).unwrap_or(0);
                            let mut path: Vec<String> = stack[start..].to_vec();
                            path.push(dep.clone());
                            *cycle = Some(path);
                            return;
                        }
                        Color::Black => {}
                    }
                    if cycle.is_some() {
                        return;
                    }
                }
            }
            stack.pop();
            color.insert(node.to_string(), Color::Black);
        }

        let nodes: Vec<String> = graph.keys().cloned().collect();
        for node in nodes {
            if color.get(&node).copied().unwrap_or(Color::Black) == Color::White {
                let mut stack = Vec::new();
                visit(&node, &graph, &mut color, &mut stack, &mut cycle);
                if cycle.is_some() {
                    break;
                }
            }
        }

        if let Some(path) = cycle {
            let display: Vec<String> = path
                .iter()
                .map(|c| crate::typechecker::bare_type_name(c).to_string())
                .collect();
            let head = display.first().cloned().unwrap_or_default();
            let span = spans
                .get(&path[0])
                .copied()
                .unwrap_or(Span { start: 0, end: 0 });
            return Err(vec![Diagnostic::error_at(
                span,
                format!(
                    "type alias `{}` is recursive: {}",
                    head,
                    display.join(" -> "),
                ),
            )]);
        }
        Ok(())
    }

    pub(crate) fn register_record_def(
        &mut self,
        name: &str,
        type_params: &[TypeParam],
        fields: &[&(String, ast::TypeExpr)],
        def_id: crate::ast::NodeId,
    ) -> Result<(), Diagnostic> {
        // Create fresh type variables for declared type parameters (same as register_type_def)
        let mut param_vars: Vec<(String, u32)> = type_params
            .iter()
            .map(|p| {
                let var = self.fresh_var();
                let id = match var {
                    Type::Var(id) => id,
                    _ => unreachable!(),
                };
                (p.name.clone(), id)
            })
            .collect();

        let field_types: Vec<(String, Type)> = fields
            .iter()
            .map(|(fname, texpr)| {
                (
                    fname.clone(),
                    self.convert_user_type_expr(texpr, &mut param_vars),
                )
            })
            .collect();

        let forall: Vec<u32> = param_vars.iter().map(|(_, id)| *id).collect();

        // Canonical type name: "Module.TypeName" for module types, bare for non-module.
        let canonical_name = match &self.current_module {
            Some(module) => format!("{}.{}", module, name),
            None => name.to_string(),
        };

        // Build result type: e.g. Box a -> Con("MyMod.Box", [Var(a_id)])
        let result_type = Type::Con(
            canonical_name.clone(),
            forall.iter().map(|&id| Type::Var(id)).collect(),
        );

        // Register record constructor scheme: e.g. Box : forall a. a -> Box a
        // Constructor takes fields in order, returns the record type.
        let mut ctor_ty = result_type;
        for (_, field_ty) in field_types.iter().rev() {
            ctor_ty = Type::arrow(field_ty.clone(), ctor_ty);
        }
        let scheme = Scheme {
            forall: forall.clone(),
            constraints: vec![],
            ty: ctor_ty,
        };
        self.constructors
            .insert(canonical_name.clone(), scheme.clone());
        self.constructors.insert(name.into(), scheme);
        self.lsp
            .constructor_def_ids
            .insert(canonical_name.clone(), def_id);
        self.lsp.constructor_def_ids.insert(name.into(), def_id);

        let num_fields = field_types.len();
        self.records.insert(
            canonical_name.clone(),
            RecordInfo {
                type_params: forall,
                fields: field_types,
            },
        );
        // Register as a single-constructor ADT for exhaustiveness checking
        self.adt_variants.insert(
            canonical_name.clone(),
            vec![(canonical_name.clone(), num_fields)],
        );
        self.type_arity
            .insert(canonical_name, type_params.len());
        Ok(())
    }
}
