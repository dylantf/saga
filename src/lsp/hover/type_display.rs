use saga::ast::NodeId;
use saga::ast::{Decl, TypeExpr};
use saga::token::Span;
use saga::typechecker::CheckResult;

/// Look up the type of a name in the checker's environment.
/// At usage sites (node_id present), prefer the resolved/instantiated type.
/// At definition sites (no node_id), prefer the annotation (includes labels).
pub fn type_at_name(
    result: &CheckResult,
    name: &str,
    span: Option<&Span>,
    node_id: Option<&NodeId>,
    program: &[Decl],
) -> Option<String> {
    // Check node-based type map first (Expr nodes at usage sites get resolved types)
    if let Some(id) = node_id
        && let Some(ty_str) = result.type_at_node(id)
    {
        // Graft labels onto the resolved type if available
        if let Some(labels) =
            annotation_labels(program, name).or_else(|| constructor_labels(program, name))
        {
            return Some(labeled_type(&labels, &ty_str));
        }
        return Some(ty_str);
    }

    // Check span-based type map (Pat bindings)
    if let Some(span) = span
        && let Some(ty_str) = result.type_at_span(span)
    {
        return Some(ty_str);
    }

    // Check for a FunAnnotation (has labeled params, good for definitions)
    if let Some(sig) = find_annotation(program, name) {
        return Some(sig);
    }

    // Check env (functions, variables)
    if let Some(scheme) = result.env.get(name) {
        return Some(scheme.display_with_constraints(&result.sub));
    }

    // Check constructors
    if let Some(scheme) = result.constructors.get(name) {
        let type_str = scheme.display_with_constraints(&result.sub);
        if let Some(labels) = constructor_labels(program, name) {
            return Some(labeled_type(&labels, &type_str));
        }
        return Some(type_str);
    }

    None
}

/// Get constructor parameter labels from a TypeDef in the AST.
/// Returns None if the constructor has no labeled fields.
fn constructor_labels(program: &[Decl], constructor_name: &str) -> Option<Vec<String>> {
    for decl in program {
        if let Decl::TypeDef { variants, .. } = decl {
            for variant in variants {
                let variant = &variant.node;
                if variant.name == constructor_name && !variant.fields.is_empty() {
                    let labels: Vec<String> = variant
                        .fields
                        .iter()
                        .map(|(label, _)| label.as_deref().unwrap_or("_").to_string())
                        .collect();
                    if labels.iter().any(|l| l != "_") {
                        return Some(labels);
                    }
                    return None;
                }
            }
        }
    }
    None
}

/// Format doc comment lines as markdown text.
fn format_doc(doc: &[String]) -> Option<String> {
    if doc.is_empty() {
        return None;
    }
    Some(doc.join("\n"))
}

/// Prepend doc comments (as markdown) before a code block.
fn with_doc(doc: &[String], code: &str) -> String {
    match format_doc(doc) {
        Some(doc_text) => format!("{}\n\n---\n\n```\n{}\n```", doc_text, code),
        None => format!("```\n{}\n```", code),
    }
}

/// Format a type/record/effect/trait definition summary for hover.
/// Returns None if the name doesn't match any definition.
pub fn type_definition_summary(
    result: &CheckResult,
    name: &str,
    program: &[Decl],
) -> Option<String> {
    // Check AST declarations for the definition
    for decl in program {
        match decl {
            Decl::TypeDef {
                name: def_name,
                doc,
                type_params,
                variants,
                ..
            } if def_name == name => {
                let mut lines = vec![format!(
                    "type {}{} {{",
                    name,
                    format_type_params(type_params)
                )];
                for variant in variants {
                    let variant = &variant.node;
                    if variant.fields.is_empty() {
                        lines.push(format!("  {}", variant.name));
                    } else {
                        let fields: Vec<String> = variant
                            .fields
                            .iter()
                            .map(|(label, ty)| match label {
                                Some(l) => format!("{}: {}", l, format_type_expr(ty)),
                                None => format_type_expr(ty),
                            })
                            .collect();
                        lines.push(format!("  {}({})", variant.name, fields.join(", ")));
                    }
                }
                lines.push("}".to_string());
                return Some(with_doc(doc, &lines.join("\n")));
            }
            Decl::RecordDef {
                name: def_name,
                doc,
                type_params,
                fields,
                ..
            } if def_name == name => {
                let field_strs: Vec<String> = fields
                    .iter()
                    .map(|f| format!("  {}: {}", f.node.0, format_type_expr(&f.node.1)))
                    .collect();
                let code = format!(
                    "record {}{} {{\n{}\n}}",
                    name,
                    format_type_params(type_params),
                    field_strs.join(",\n")
                );
                return Some(with_doc(doc, &code));
            }
            Decl::EffectDef {
                name: def_name,
                doc,
                type_params,
                operations,
                ..
            } if def_name == name => {
                let ops: Vec<String> = operations
                    .iter()
                    .map(|op| {
                        let op = &op.node;
                        format!(
                            "  {}",
                            format_signature(&op.name, &op.params, &op.return_type)
                        )
                    })
                    .collect();
                let code = format!(
                    "effect {}{} {{\n{}\n}}",
                    name,
                    format_type_params(type_params),
                    ops.join("\n")
                );
                return Some(with_doc(doc, &code));
            }
            Decl::TraitDef {
                name: def_name,
                doc,
                type_params,
                supertraits,
                methods,
                ..
            } if def_name == name => {
                let supers = if supertraits.is_empty() {
                    String::new()
                } else {
                    let names: Vec<&str> = supertraits.iter().map(|(n, _)| n.as_str()).collect();
                    format!(" where {{{}}}", names.join(", "))
                };
                let method_strs: Vec<String> = methods
                    .iter()
                    .map(|m| {
                        let m = &m.node;
                        format!("  {}", format_signature(&m.name, &m.params, &m.return_type))
                    })
                    .collect();
                let code = format!(
                    "trait {} {}{} {{\n{}\n}}",
                    name,
                    type_params.join(" "),
                    supers,
                    method_strs.join("\n")
                );
                return Some(with_doc(doc, &code));
            }
            _ => {}
        }
    }

    // Check imported types: prefer AST from cached module programs (preserves user-written
    // type variable names), fall back to CheckResult data with prettified vars.
    if let Some(source_module) = result.scope_map.origin_of(name) {
        let source_module = &source_module.to_string();
        // Module ASTs use bare names for their own declarations, so strip the module prefix
        let bare_name = name.rsplit('.').next().unwrap_or(name);
        if let Some(module_program) = result.programs().get(source_module)
            && let Some(summary) = type_definition_summary(result, bare_name, module_program)
        {
            return Some(summary);
        }
        // Also check per-module CheckResults for transitive imports
        if let Some(module_result) = result.module_check_results().get(source_module)
            && let Some(module_program) = module_result.programs().get(source_module)
            && let Some(summary) = type_definition_summary(result, bare_name, module_program)
        {
            return Some(summary);
        }
    }

    if let Some(info) = result.records.get(name) {
        let params = if info.type_params.is_empty() {
            String::new()
        } else {
            format!(" ({})", info.type_params.len())
        };
        let prettified = result.prettify_record(info);
        let field_strs: Vec<String> = prettified
            .iter()
            .map(|(fname, ty)| format!("  {}: {}", fname, ty))
            .collect();
        let code = format!(
            "record {}{} {{\n{}\n}}",
            name,
            params,
            field_strs.join(",\n")
        );
        let doc = result
            .imported_docs
            .get(name)
            .map(|d| d.as_slice())
            .unwrap_or(&[]);
        return Some(with_doc(doc, &code));
    }

    if let Some(info) = result.resolve_effect(name) {
        let prettified = result.prettify_effect(info);
        let ops: Vec<String> = prettified
            .iter()
            .map(|(op_name, params, ret)| {
                let param_strs: Vec<String> = params
                    .iter()
                    .map(|(label, ty)| format_labeled_param(label, &format!("{}", ty)))
                    .collect();
                let ret_str = format!("{}", ret);
                format!("  {}", join_signature(op_name, &param_strs, &ret_str))
            })
            .collect();
        let code = format!("effect {} {{\n{}\n}}", name, ops.join("\n"));
        let doc = result
            .imported_docs
            .get(name)
            .map(|d| d.as_slice())
            .unwrap_or(&[]);
        return Some(with_doc(doc, &code));
    }

    None
}

/// Get just the parameter labels from a FunAnnotation.
/// Returns None if no annotation exists or if no params have real labels.
pub(crate) fn annotation_labels(program: &[Decl], name: &str) -> Option<Vec<String>> {
    for decl in program {
        if let Decl::FunSignature {
            name: fn_name,
            params,
            ..
        } = decl
            && fn_name == name
        {
            let labels: Vec<String> = params.iter().map(|(label, _)| label.clone()).collect();
            if labels.iter().any(|l| !l.starts_with('_')) {
                return Some(labels);
            }
            return None;
        }
    }
    None
}

/// Graft parameter labels onto a resolved type string.
/// E.g., labels=["a", "b"], type_str="Int -> Int -> String" => "(a: Int) (b: Int) -> String"
fn labeled_type(labels: &[String], type_str: &str) -> String {
    let parts: Vec<&str> = type_str.splitn(labels.len() + 1, " -> ").collect();
    if parts.len() <= labels.len() {
        return type_str.to_string();
    }
    let labeled: Vec<String> = labels
        .iter()
        .zip(parts.iter())
        .map(|(label, ty)| format_labeled_param(label, ty))
        .collect();
    let rest = parts[labels.len()..].join(" -> ");
    format!("{} -> {}", labeled.join(" -> "), rest)
}

/// Get doc comments for a named declaration.
/// Checks local AST first, then falls back to imported docs from other modules.
pub fn doc_for_name(program: &[Decl], name: &str, result: &CheckResult) -> Option<String> {
    // Check local AST declarations
    for decl in program {
        let doc = match decl {
            Decl::FunSignature { name: n, doc, .. } if n == name => doc,
            Decl::TypeDef { name: n, doc, .. } if n == name => doc,
            Decl::RecordDef { name: n, doc, .. } if n == name => doc,
            Decl::EffectDef { name: n, doc, .. } if n == name => doc,
            Decl::HandlerDef { name: n, doc, .. } if n == name => doc,
            Decl::TraitDef { name: n, doc, .. } if n == name => doc,
            _ => continue,
        };
        if !doc.is_empty() {
            return format_doc(doc);
        }
    }
    // Check imported docs from other modules
    if let Some(doc) = result.imported_docs.get(name) {
        return format_doc(doc);
    }
    None
}

/// Find a FunAnnotation for the given name and format it with labels.
pub(crate) fn find_annotation(program: &[Decl], name: &str) -> Option<String> {
    for decl in program {
        if let Decl::FunSignature {
            name: fn_name,
            params,
            return_type,
            effects,
            ..
        } = decl
            && fn_name == name
        {
            let params_str: Vec<String> = params
                .iter()
                .map(|(label, ty)| format_labeled_param(label, &format_type_expr(ty)))
                .collect();
            let ret = format_type_expr(return_type);
            let mut sig = if params_str.is_empty() {
                ret
            } else {
                format!("{} -> {}", params_str.join(" -> "), ret)
            };
            if !effects.is_empty() {
                let effs: Vec<String> = effects.iter().map(format_effect_ref).collect();
                sig.push_str(&format!(" needs {{{}}}", effs.join(", ")));
            }
            return Some(sig);
        }
    }
    None
}

// --- Shared formatting helpers ---

/// Format a parameter with an optional label: `(label: Type)` or just `Type`.
fn format_labeled_param(label: &str, ty_str: &str) -> String {
    if label.starts_with('_') {
        ty_str.to_string()
    } else {
        format!("({}: {})", label, ty_str)
    }
}

/// Format type parameters: `""` or `" a b"`.
fn format_type_params(params: &[String]) -> String {
    if params.is_empty() {
        String::new()
    } else {
        format!(" {}", params.join(" "))
    }
}

/// Format an operation/method signature from AST types: `name : params -> return`.
pub(crate) fn format_signature(
    name: &str,
    params: &[(String, TypeExpr)],
    return_type: &TypeExpr,
) -> String {
    let param_strs: Vec<String> = params
        .iter()
        .map(|(label, ty)| format_labeled_param(label, &format_type_expr(ty)))
        .collect();
    let ret = format_type_expr(return_type);
    join_signature(name, &param_strs, &ret)
}

/// Join a name, formatted params, and return type into `name : params -> ret`.
fn join_signature(name: &str, params: &[String], ret: &str) -> String {
    if params.is_empty() {
        format!("{} : {}", name, ret)
    } else {
        format!("{} : {} -> {}", name, params.join(" -> "), ret)
    }
}

/// Format an EffectRef for display.
fn format_effect_ref(e: &saga::ast::EffectRef) -> String {
    if e.type_args.is_empty() {
        e.name.clone()
    } else {
        let args: Vec<String> = e.type_args.iter().map(format_type_expr).collect();
        format!("{} {}", e.name, args.join(" "))
    }
}

pub(crate) fn format_type_expr(ty: &TypeExpr) -> String {
    match ty {
        TypeExpr::Named { name, .. } => name.clone(),
        TypeExpr::Var { name, .. } => name.clone(),
        TypeExpr::App { func, arg, .. } => {
            format!("{} {}", format_type_expr(func), format_type_expr(arg))
        }
        TypeExpr::Arrow {
            from, to, effects, ..
        } => {
            let arrow = format!("{} -> {}", format_type_expr(from), format_type_expr(to));
            if effects.is_empty() {
                arrow
            } else {
                let effs: Vec<String> = effects.iter().map(format_effect_ref).collect();
                format!("{} needs {{{}}}", arrow, effs.join(", "))
            }
        }
        TypeExpr::Record { fields, .. } => {
            let field_strs: Vec<String> = fields
                .iter()
                .map(|(name, ty)| format!("{}: {}", name, format_type_expr(ty)))
                .collect();
            format!("{{ {} }}", field_strs.join(", "))
        }
        TypeExpr::Labeled { label, inner, .. } => {
            format!("({}: {})", label, format_type_expr(inner))
        }
    }
}
