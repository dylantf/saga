use super::*;

pub(super) fn add_decl_type_symbols(
    index: &mut SemanticIndex,
    uri: &Url,
    line_index: &LineIndex,
    source: &str,
    decl: &ast::Decl,
    check: &typechecker::CheckResult,
    module_name: Option<&str>,
) {
    match decl {
        ast::Decl::FunSignature {
            id,
            doc,
            params,
            return_type,
            effects,
            where_clause,
            ..
        } => {
            add_value_docs(index, *id, doc);
            for (_, type_expr) in params {
                add_type_expr_symbols(index, uri, line_index, source, type_expr, check);
            }
            add_type_expr_symbols(index, uri, line_index, source, return_type, check);
            for effect_ref in effects {
                add_effect_ref_symbol(index, uri, line_index, source, effect_ref, check);
            }
            add_where_clause_type_symbols(index, uri, line_index, source, where_clause, check);
        }
        ast::Decl::FunBinding {
            params,
            guard,
            body,
            ..
        } => {
            for param in params {
                add_pat_type_symbols(index, uri, line_index, source, param, check);
            }
            if let Some(guard) = guard {
                add_expr_type_symbols(index, uri, line_index, source, guard, check);
            }
            add_expr_type_symbols(index, uri, line_index, source, body, check);
        }
        ast::Decl::Let {
            annotation, value, ..
        } => {
            if let Some(annotation) = annotation {
                add_type_expr_symbols(index, uri, line_index, source, annotation, check);
            }
            add_expr_type_symbols(index, uri, line_index, source, value, check);
        }
        ast::Decl::TypeDef {
            name,
            name_span,
            doc,
            variants,
            ..
        } => {
            add_type_definition_symbol(
                index,
                uri,
                line_index,
                source,
                module_name,
                name,
                *name_span,
            );
            add_type_definition_docs(index, module_name, name, doc);
            for variant in variants {
                for (_, type_expr) in &variant.node.fields {
                    add_type_expr_symbols(index, uri, line_index, source, type_expr, check);
                }
            }
        }
        ast::Decl::TypeAlias {
            name,
            name_span,
            doc,
            body,
            ..
        } => {
            add_type_definition_symbol(
                index,
                uri,
                line_index,
                source,
                module_name,
                name,
                *name_span,
            );
            add_type_definition_docs(index, module_name, name, doc);
            add_type_expr_symbols(index, uri, line_index, source, body, check);
        }
        ast::Decl::RecordDef {
            name,
            name_span,
            doc,
            fields,
            ..
        } => {
            add_type_definition_symbol(
                index,
                uri,
                line_index,
                source,
                module_name,
                name,
                *name_span,
            );
            add_type_definition_docs(index, module_name, name, doc);
            for field in fields {
                add_type_expr_symbols(index, uri, line_index, source, &field.node.1, check);
            }
        }
        ast::Decl::RecordBuilderDef {
            id,
            context,
            context_span,
            ..
        } => {
            if let Some(resolved) = check.resolved_type_name_for_node(*id) {
                add_type_reference_symbol(
                    index,
                    uri,
                    resolved.to_string(),
                    name_range(context_span.start, context, line_index, source),
                );
            }
        }
        ast::Decl::EffectDef {
            name,
            name_span,
            doc,
            operations,
            ..
        } => {
            let effect_name = type_definition_name(module_name, name);
            add_semantic_symbol_definition(
                index,
                uri,
                line_index,
                source,
                SemanticSymbolKind::Effect,
                effect_name.clone(),
                *name_span,
            );
            add_semantic_symbol_docs(index, SemanticSymbolKind::Effect, effect_name.clone(), doc);
            for op in operations {
                add_effect_operation_definition_symbol(
                    index,
                    uri,
                    line_index,
                    source,
                    &effect_name,
                    &op.node,
                );
                for (_, type_expr) in &op.node.params {
                    add_type_expr_symbols(index, uri, line_index, source, type_expr, check);
                }
                add_type_expr_symbols(index, uri, line_index, source, &op.node.return_type, check);
                for effect_ref in &op.node.effects {
                    add_effect_ref_symbol(index, uri, line_index, source, effect_ref, check);
                }
                add_where_clause_type_symbols(
                    index,
                    uri,
                    line_index,
                    source,
                    &op.node.where_clause,
                    check,
                );
            }
        }
        ast::Decl::HandlerDef {
            name,
            name_span,
            doc,
            body,
            ..
        } => {
            let handler_name = type_definition_name(module_name, name);
            add_semantic_symbol_definition(
                index,
                uri,
                line_index,
                source,
                SemanticSymbolKind::Handler,
                handler_name.clone(),
                *name_span,
            );
            add_semantic_symbol_docs(index, SemanticSymbolKind::Handler, handler_name, doc);
            add_handler_body_type_symbols(index, uri, line_index, source, body, check);
        }
        ast::Decl::TraitDef {
            name,
            name_span,
            doc,
            supertraits,
            methods,
            ..
        } => {
            let trait_name = type_definition_name(module_name, name);
            add_semantic_symbol_definition(
                index,
                uri,
                line_index,
                source,
                SemanticSymbolKind::Trait,
                trait_name.clone(),
                *name_span,
            );
            add_semantic_symbol_docs(index, SemanticSymbolKind::Trait, trait_name.clone(), doc);
            for trait_ref in supertraits {
                add_trait_ref_symbol(index, uri, line_index, source, trait_ref, check);
            }
            for method in methods {
                add_trait_method_definition_symbol(
                    index,
                    uri,
                    line_index,
                    source,
                    &trait_name,
                    &method.node,
                );
                for (_, type_expr) in &method.node.params {
                    add_type_expr_symbols(index, uri, line_index, source, type_expr, check);
                }
                add_type_expr_symbols(
                    index,
                    uri,
                    line_index,
                    source,
                    &method.node.return_type,
                    check,
                );
                for effect_ref in &method.node.effects {
                    add_effect_ref_symbol(index, uri, line_index, source, effect_ref, check);
                }
            }
        }
        ast::Decl::ImplDef {
            id,
            target_type,
            target_type_span,
            target_type_expr,
            trait_name,
            trait_name_span,
            trait_type_args,
            where_clause,
            where_apps,
            needs,
            methods,
            ..
        } => {
            let resolved_trait = check.resolved_trait_name_for_node(*id);
            if let Some(resolved) = resolved_trait {
                add_semantic_symbol_reference(
                    index,
                    uri,
                    SemanticSymbolKind::Trait,
                    resolved.to_string(),
                    span_to_range(trait_name_span, line_index, source),
                );
            } else {
                let _ = trait_name;
            }
            if let Some(name) = check.resolved_type_name_for_node(*id) {
                add_type_reference_symbol(
                    index,
                    uri,
                    name.to_string(),
                    span_to_range(target_type_span, line_index, source),
                );
            } else {
                let _ = target_type;
            }
            if let Some(target_type_expr) = target_type_expr {
                add_type_expr_symbols(index, uri, line_index, source, target_type_expr, check);
            }
            for type_expr in trait_type_args {
                add_type_expr_symbols(index, uri, line_index, source, type_expr, check);
            }
            add_where_clause_type_symbols(index, uri, line_index, source, where_clause, check);
            for app in where_apps {
                add_trait_app_symbol(index, uri, line_index, source, app, check);
            }
            for effect_ref in needs {
                add_effect_ref_symbol(index, uri, line_index, source, effect_ref, check);
            }
            for method in methods {
                if let Some(resolved_trait) = resolved_trait {
                    add_trait_method_reference_symbol(
                        index,
                        uri,
                        resolved_trait,
                        &method.node.name,
                        span_to_range(&method.node.name_span, line_index, source),
                    );
                }
                for param in &method.node.params {
                    add_pat_type_symbols(index, uri, line_index, source, param, check);
                }
                add_expr_type_symbols(index, uri, line_index, source, &method.node.body, check);
            }
        }
        ast::Decl::DictConstructor { methods, .. } => {
            for method in methods {
                add_expr_type_symbols(index, uri, line_index, source, method, check);
            }
        }
        ast::Decl::Import {
            module_path, span, ..
        } => {
            let module_name = module_path.join(".");
            index.add_module_reference(
                module_name,
                Location {
                    uri: uri.clone(),
                    range: path_name_range(*span, module_path, line_index, source),
                },
            );
        }
        ast::Decl::ModuleDecl {
            path, span, doc, ..
        } => {
            let module_name = path.join(".");
            let location = Location {
                uri: uri.clone(),
                range: path_name_range(*span, path, line_index, source),
            };
            index.add_module_definition(module_name.clone(), location);
            add_semantic_symbol_docs(index, SemanticSymbolKind::Module, module_name, doc);
        }
    }
}
