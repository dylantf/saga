use saga::{ast, typechecker};
use tower_lsp::lsp_types::*;

use super::semantic::{
    SemanticDocKey, SemanticIndex, SemanticSymbolKey, SemanticSymbolKind, member_symbol_name,
};
use super::text::{LineIndex, span_to_range};

mod decl;

pub(super) fn add_program_type_symbols(
    index: &mut SemanticIndex,
    uri: &Url,
    line_index: &LineIndex,
    source: &str,
    program: &[ast::Decl],
    check: &typechecker::CheckResult,
    module_name: Option<&str>,
) {
    for decl in program {
        decl::add_decl_type_symbols(index, uri, line_index, source, decl, check, module_name);
    }
}

fn type_definition_name(module_name: Option<&str>, name: &str) -> String {
    module_name
        .map(|module| format!("{module}.{name}"))
        .unwrap_or_else(|| name.to_string())
}

fn name_range(start: usize, name: &str, line_index: &LineIndex, source: &str) -> Range {
    span_to_range(
        &saga::token::Span {
            start,
            end: start + name.len(),
        },
        line_index,
        source,
    )
}

fn final_segment_name_range(
    span: saga::token::Span,
    name: &str,
    line_index: &LineIndex,
    source: &str,
) -> Range {
    let haystack = source.get(span.start..span.end).unwrap_or_default();
    if let Some(relative_start) = haystack.rfind(name) {
        name_range(span.start + relative_start, name, line_index, source)
    } else {
        name_range(span.start, name, line_index, source)
    }
}

fn path_name_range(
    span: saga::token::Span,
    path: &[String],
    line_index: &LineIndex,
    source: &str,
) -> Range {
    let name = path.join(".");
    let haystack = source.get(span.start..span.end).unwrap_or_default();
    if let Some(relative_start) = haystack.find(&name) {
        name_range(span.start + relative_start, &name, line_index, source)
    } else {
        span_to_range(&span, line_index, source)
    }
}

fn add_type_definition_symbol(
    index: &mut SemanticIndex,
    uri: &Url,
    line_index: &LineIndex,
    source: &str,
    module_name: Option<&str>,
    name: &str,
    name_span: saga::token::Span,
) {
    index.add_type_definition(
        type_definition_name(module_name, name),
        Location {
            uri: uri.clone(),
            range: span_to_range(&name_span, line_index, source),
        },
    );
}

fn add_type_definition_docs(
    index: &mut SemanticIndex,
    module_name: Option<&str>,
    name: &str,
    doc: &[String],
) {
    index.add_docs(
        SemanticDocKey::Type(type_definition_name(module_name, name)),
        doc,
    );
}

fn add_value_docs(index: &mut SemanticIndex, node_id: ast::NodeId, doc: &[String]) {
    index.add_docs(SemanticDocKey::Value(node_id), doc);
}

fn add_type_reference_symbol(index: &mut SemanticIndex, uri: &Url, name: String, range: Range) {
    index.add_type_reference(
        name,
        Location {
            uri: uri.clone(),
            range,
        },
    );
}

fn add_semantic_symbol_definition(
    index: &mut SemanticIndex,
    uri: &Url,
    line_index: &LineIndex,
    source: &str,
    kind: SemanticSymbolKind,
    name: String,
    name_span: saga::token::Span,
) {
    index.add_symbol_definition(
        kind,
        name.clone(),
        Location {
            uri: uri.clone(),
            range: span_to_range(&name_span, line_index, source),
        },
    );
}

fn add_semantic_symbol_docs(
    index: &mut SemanticIndex,
    kind: SemanticSymbolKind,
    name: String,
    doc: &[String],
) {
    index.add_docs(
        SemanticDocKey::Symbol(SemanticSymbolKey { kind, name }),
        doc,
    );
}

fn add_semantic_symbol_reference(
    index: &mut SemanticIndex,
    uri: &Url,
    kind: SemanticSymbolKind,
    name: String,
    range: Range,
) {
    index.add_symbol_reference(
        kind,
        name,
        Location {
            uri: uri.clone(),
            range,
        },
    );
}

fn add_trait_method_definition_symbol(
    index: &mut SemanticIndex,
    uri: &Url,
    line_index: &LineIndex,
    source: &str,
    trait_name: &str,
    method: &ast::TraitMethod,
) {
    index.add_symbol_definition(
        SemanticSymbolKind::TraitMethod,
        member_symbol_name(trait_name, &method.name),
        Location {
            uri: uri.clone(),
            range: final_segment_name_range(method.span, &method.name, line_index, source),
        },
    );
    add_semantic_symbol_docs(
        index,
        SemanticSymbolKind::TraitMethod,
        member_symbol_name(trait_name, &method.name),
        &method.doc,
    );
}

fn add_effect_operation_definition_symbol(
    index: &mut SemanticIndex,
    uri: &Url,
    line_index: &LineIndex,
    source: &str,
    effect_name: &str,
    op: &ast::EffectOp,
) {
    index.add_symbol_definition(
        SemanticSymbolKind::EffectOperation,
        member_symbol_name(effect_name, &op.name),
        Location {
            uri: uri.clone(),
            range: final_segment_name_range(op.span, &op.name, line_index, source),
        },
    );
    add_semantic_symbol_docs(
        index,
        SemanticSymbolKind::EffectOperation,
        member_symbol_name(effect_name, &op.name),
        &op.doc,
    );
}

fn add_trait_method_reference_symbol(
    index: &mut SemanticIndex,
    uri: &Url,
    trait_name: &str,
    method_name: &str,
    range: Range,
) {
    add_semantic_symbol_reference(
        index,
        uri,
        SemanticSymbolKind::TraitMethod,
        member_symbol_name(trait_name, method_name),
        range,
    );
}

fn add_effect_operation_reference_symbol(
    index: &mut SemanticIndex,
    uri: &Url,
    effect_name: &str,
    op_name: &str,
    range: Range,
) {
    add_semantic_symbol_reference(
        index,
        uri,
        SemanticSymbolKind::EffectOperation,
        member_symbol_name(effect_name, op_name),
        range,
    );
}

fn add_trait_ref_symbol(
    index: &mut SemanticIndex,
    uri: &Url,
    line_index: &LineIndex,
    source: &str,
    trait_ref: &ast::TraitRef,
    check: &typechecker::CheckResult,
) {
    if let Some(resolved) = check.resolved_trait_name_for_node(trait_ref.id) {
        add_semantic_symbol_reference(
            index,
            uri,
            SemanticSymbolKind::Trait,
            resolved.to_string(),
            name_range(trait_ref.span.start, &trait_ref.name, line_index, source),
        );
    }
    for type_expr in &trait_ref.type_args {
        add_type_expr_symbols(index, uri, line_index, source, type_expr, check);
    }
}

fn add_trait_app_symbol(
    index: &mut SemanticIndex,
    uri: &Url,
    line_index: &LineIndex,
    source: &str,
    app: &ast::TraitApp,
    check: &typechecker::CheckResult,
) {
    if let Some(resolved) = check.resolved_trait_name_for_node(app.id) {
        add_semantic_symbol_reference(
            index,
            uri,
            SemanticSymbolKind::Trait,
            resolved.to_string(),
            name_range(app.span.start, &app.trait_name, line_index, source),
        );
    }
    for type_expr in &app.type_args {
        add_type_expr_symbols(index, uri, line_index, source, type_expr, check);
    }
}

fn add_effect_ref_symbol(
    index: &mut SemanticIndex,
    uri: &Url,
    line_index: &LineIndex,
    source: &str,
    effect_ref: &ast::EffectRef,
    check: &typechecker::CheckResult,
) {
    if let Some(resolved) = check.resolved_effect_name_for_node(effect_ref.id) {
        add_semantic_symbol_reference(
            index,
            uri,
            SemanticSymbolKind::Effect,
            resolved.to_string(),
            name_range(effect_ref.span.start, &effect_ref.name, line_index, source),
        );
    }
    for type_expr in &effect_ref.type_args {
        add_type_expr_symbols(index, uri, line_index, source, type_expr, check);
    }
}

fn add_handler_ref_symbol(
    index: &mut SemanticIndex,
    uri: &Url,
    line_index: &LineIndex,
    source: &str,
    handler_ref: &ast::NamedHandlerRef,
    check: &typechecker::CheckResult,
) {
    if let Some(resolved) = check.resolved_handler_name_for_node(handler_ref.id) {
        add_semantic_symbol_reference(
            index,
            uri,
            SemanticSymbolKind::Handler,
            resolved,
            name_range(
                handler_ref.span.start,
                &handler_ref.name,
                line_index,
                source,
            ),
        );
    }
}

fn add_where_clause_type_symbols(
    index: &mut SemanticIndex,
    uri: &Url,
    line_index: &LineIndex,
    source: &str,
    where_clause: &[ast::TraitBound],
    check: &typechecker::CheckResult,
) {
    for bound in where_clause {
        for trait_ref in &bound.traits {
            add_trait_ref_symbol(index, uri, line_index, source, trait_ref, check);
        }
    }
}

fn add_type_expr_symbols(
    index: &mut SemanticIndex,
    uri: &Url,
    line_index: &LineIndex,
    source: &str,
    type_expr: &ast::TypeExpr,
    check: &typechecker::CheckResult,
) {
    match type_expr {
        ast::TypeExpr::Named { id, name, span } => {
            if let Some(resolved) = check.resolved_type_name_for_node(*id) {
                add_type_reference_symbol(
                    index,
                    uri,
                    resolved.to_string(),
                    span_to_range(span, line_index, source),
                );
            } else {
                let _ = name;
            }
        }
        ast::TypeExpr::App { func, arg, .. } => {
            add_type_expr_symbols(index, uri, line_index, source, func, check);
            add_type_expr_symbols(index, uri, line_index, source, arg, check);
        }
        ast::TypeExpr::Arrow {
            from, to, effects, ..
        } => {
            add_type_expr_symbols(index, uri, line_index, source, from, check);
            add_type_expr_symbols(index, uri, line_index, source, to, check);
            for effect in effects {
                add_effect_ref_symbol(index, uri, line_index, source, effect, check);
            }
        }
        ast::TypeExpr::Record { fields, .. } => {
            for (_, type_expr) in fields {
                add_type_expr_symbols(index, uri, line_index, source, type_expr, check);
            }
        }
        ast::TypeExpr::Labeled { inner, .. } => {
            add_type_expr_symbols(index, uri, line_index, source, inner, check);
        }
        ast::TypeExpr::Var { .. } => {}
    }
}

fn add_pat_type_symbols(
    index: &mut SemanticIndex,
    uri: &Url,
    line_index: &LineIndex,
    source: &str,
    pat: &ast::Pat,
    check: &typechecker::CheckResult,
) {
    match pat {
        ast::Pat::Constructor { args, .. } | ast::Pat::Tuple { elements: args, .. } => {
            for arg in args {
                add_pat_type_symbols(index, uri, line_index, source, arg, check);
            }
        }
        ast::Pat::Record {
            id, name, fields, ..
        } => {
            if let Some(resolved) = check.resolved_type_name_for_node(*id) {
                add_type_reference_symbol(
                    index,
                    uri,
                    resolved.to_string(),
                    name_range(pat.span().start, name, line_index, source),
                );
            }
            for (_, field_pat) in fields {
                if let Some(field_pat) = field_pat {
                    add_pat_type_symbols(index, uri, line_index, source, field_pat, check);
                }
            }
        }
        ast::Pat::AnonRecord { fields, .. } => {
            for (_, field_pat) in fields {
                if let Some(field_pat) = field_pat {
                    add_pat_type_symbols(index, uri, line_index, source, field_pat, check);
                }
            }
        }
        ast::Pat::StringPrefix { rest, .. } => {
            add_pat_type_symbols(index, uri, line_index, source, rest, check);
        }
        ast::Pat::BitStringPat { segments, .. } => {
            for segment in segments {
                add_pat_type_symbols(index, uri, line_index, source, &segment.value, check);
                if let Some(size) = &segment.size {
                    add_expr_type_symbols(index, uri, line_index, source, size, check);
                }
            }
        }
        ast::Pat::ListPat { elements, .. }
        | ast::Pat::Or {
            patterns: elements, ..
        } => {
            for element in elements {
                add_pat_type_symbols(index, uri, line_index, source, element, check);
            }
        }
        ast::Pat::ConsPat { head, tail, .. } => {
            add_pat_type_symbols(index, uri, line_index, source, head, check);
            add_pat_type_symbols(index, uri, line_index, source, tail, check);
        }
        ast::Pat::Wildcard { .. } | ast::Pat::Var { .. } | ast::Pat::Lit { .. } => {}
    }
}

fn add_stmt_type_symbols(
    index: &mut SemanticIndex,
    uri: &Url,
    line_index: &LineIndex,
    source: &str,
    stmt: &ast::Stmt,
    check: &typechecker::CheckResult,
) {
    match stmt {
        ast::Stmt::Let {
            pattern,
            annotation,
            value,
            ..
        } => {
            add_pat_type_symbols(index, uri, line_index, source, pattern, check);
            if let Some(annotation) = annotation {
                add_type_expr_symbols(index, uri, line_index, source, annotation, check);
            }
            add_expr_type_symbols(index, uri, line_index, source, value, check);
        }
        ast::Stmt::LetFun {
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
        ast::Stmt::Expr(expr) => add_expr_type_symbols(index, uri, line_index, source, expr, check),
    }
}

fn add_expr_type_symbols(
    index: &mut SemanticIndex,
    uri: &Url,
    line_index: &LineIndex,
    source: &str,
    expr: &ast::Expr,
    check: &typechecker::CheckResult,
) {
    match &expr.kind {
        ast::ExprKind::Lit { .. }
        | ast::ExprKind::Constructor { .. }
        | ast::ExprKind::DictRef { .. } => {}
        ast::ExprKind::Var { name } => {
            if let Some((trait_name, method_name)) = check.resolved_trait_method_for_node(expr.id) {
                add_trait_method_reference_symbol(
                    index,
                    uri,
                    trait_name,
                    method_name,
                    final_segment_name_range(expr.span, name, line_index, source),
                );
            }
        }
        ast::ExprKind::QualifiedName { name, .. } => {
            if let Some((trait_name, method_name)) = check.resolved_trait_method_for_node(expr.id) {
                add_trait_method_reference_symbol(
                    index,
                    uri,
                    trait_name,
                    method_name,
                    final_segment_name_range(expr.span, name, line_index, source),
                );
            }
        }
        ast::ExprKind::App { func, arg } => {
            add_expr_type_symbols(index, uri, line_index, source, func, check);
            add_expr_type_symbols(index, uri, line_index, source, arg, check);
        }
        ast::ExprKind::BinOp { left, right, .. } => {
            add_expr_type_symbols(index, uri, line_index, source, left, check);
            add_expr_type_symbols(index, uri, line_index, source, right, check);
        }
        ast::ExprKind::UnaryMinus { expr } => {
            add_expr_type_symbols(index, uri, line_index, source, expr, check);
        }
        ast::ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            add_expr_type_symbols(index, uri, line_index, source, cond, check);
            add_expr_type_symbols(index, uri, line_index, source, then_branch, check);
            add_expr_type_symbols(index, uri, line_index, source, else_branch, check);
        }
        ast::ExprKind::Case {
            scrutinee, arms, ..
        } => {
            add_expr_type_symbols(index, uri, line_index, source, scrutinee, check);
            for arm in arms {
                add_pat_type_symbols(index, uri, line_index, source, &arm.node.pattern, check);
                if let Some(guard) = &arm.node.guard {
                    add_expr_type_symbols(index, uri, line_index, source, guard, check);
                }
                add_expr_type_symbols(index, uri, line_index, source, &arm.node.body, check);
            }
        }
        ast::ExprKind::Block { stmts, .. } => {
            for stmt in stmts {
                add_stmt_type_symbols(index, uri, line_index, source, &stmt.node, check);
            }
        }
        ast::ExprKind::Lambda { params, body } => {
            for param in params {
                add_pat_type_symbols(index, uri, line_index, source, param, check);
            }
            add_expr_type_symbols(index, uri, line_index, source, body, check);
        }
        ast::ExprKind::FieldAccess { expr, .. } => {
            add_expr_type_symbols(index, uri, line_index, source, expr, check);
        }
        ast::ExprKind::RecordCreate { name, fields, .. } => {
            if let Some(resolved) = check.resolved_type_name_for_node(expr.id) {
                add_type_reference_symbol(
                    index,
                    uri,
                    resolved.to_string(),
                    name_range(expr.span.start, name, line_index, source),
                );
            }
            for (_, _, value) in fields {
                add_expr_type_symbols(index, uri, line_index, source, value, check);
            }
        }
        ast::ExprKind::AnonRecordCreate { fields } => {
            for (_, _, value) in fields {
                add_expr_type_symbols(index, uri, line_index, source, value, check);
            }
        }
        ast::ExprKind::RecordBuild {
            record,
            record_span,
            fields,
            ..
        } => {
            if let (Some(record), Some(record_span)) = (record, record_span)
                && let Some(resolved) = check.resolved_type_name_for_node(expr.id)
            {
                add_type_reference_symbol(
                    index,
                    uri,
                    resolved.to_string(),
                    name_range(record_span.start, record, line_index, source),
                );
            }
            for (_, _, value) in fields {
                add_expr_type_symbols(index, uri, line_index, source, value, check);
            }
        }
        ast::ExprKind::RecordUpdate { record, fields, .. } => {
            add_expr_type_symbols(index, uri, line_index, source, record, check);
            for (_, _, value) in fields {
                add_expr_type_symbols(index, uri, line_index, source, value, check);
            }
        }
        ast::ExprKind::EffectCall {
            name,
            qualifier,
            args,
        } => {
            if let Some((effect_name, op_name)) =
                check.resolved_effect_operation_for_call_node(expr.id)
            {
                add_effect_operation_reference_symbol(
                    index,
                    uri,
                    effect_name,
                    op_name,
                    final_segment_name_range(expr.span, name, line_index, source),
                );
            }
            if let Some(qualifier) = qualifier
                && let Some(resolved) = check.resolved_effect_call_effect_name_for_node(expr.id)
            {
                add_semantic_symbol_reference(
                    index,
                    uri,
                    SemanticSymbolKind::Effect,
                    resolved.to_string(),
                    name_range(expr.span.start, qualifier, line_index, source),
                );
            }
            for arg in args {
                add_expr_type_symbols(index, uri, line_index, source, arg, check);
            }
        }
        ast::ExprKind::With { expr, handler } => {
            add_expr_type_symbols(index, uri, line_index, source, expr, check);
            add_handler_type_symbols(index, uri, line_index, source, handler, check);
        }
        ast::ExprKind::Resume { value } => {
            add_expr_type_symbols(index, uri, line_index, source, value, check);
        }
        ast::ExprKind::Tuple { elements } => {
            for element in elements {
                add_expr_type_symbols(index, uri, line_index, source, element, check);
            }
        }
        ast::ExprKind::ListLit { elements, .. } => {
            for element in elements {
                add_expr_type_symbols(index, uri, line_index, source, &element.node, check);
            }
        }
        ast::ExprKind::Do {
            bindings,
            success,
            else_arms,
            ..
        } => {
            for (pattern, value) in bindings {
                add_pat_type_symbols(index, uri, line_index, source, pattern, check);
                add_expr_type_symbols(index, uri, line_index, source, value, check);
            }
            add_expr_type_symbols(index, uri, line_index, source, success, check);
            for arm in else_arms {
                add_pat_type_symbols(index, uri, line_index, source, &arm.node.pattern, check);
                if let Some(guard) = &arm.node.guard {
                    add_expr_type_symbols(index, uri, line_index, source, guard, check);
                }
                add_expr_type_symbols(index, uri, line_index, source, &arm.node.body, check);
            }
        }
        ast::ExprKind::Receive {
            arms, after_clause, ..
        } => {
            for arm in arms {
                add_pat_type_symbols(index, uri, line_index, source, &arm.node.pattern, check);
                if let Some(guard) = &arm.node.guard {
                    add_expr_type_symbols(index, uri, line_index, source, guard, check);
                }
                add_expr_type_symbols(index, uri, line_index, source, &arm.node.body, check);
            }
            if let Some((timeout, body)) = after_clause {
                add_expr_type_symbols(index, uri, line_index, source, timeout, check);
                add_expr_type_symbols(index, uri, line_index, source, body, check);
            }
        }
        ast::ExprKind::BitString { segments } => {
            for segment in segments {
                add_expr_type_symbols(index, uri, line_index, source, &segment.value, check);
                if let Some(size) = &segment.size {
                    add_expr_type_symbols(index, uri, line_index, source, size, check);
                }
            }
        }
        ast::ExprKind::Ascription { expr, type_expr } => {
            add_expr_type_symbols(index, uri, line_index, source, expr, check);
            add_type_expr_symbols(index, uri, line_index, source, type_expr, check);
        }
        ast::ExprKind::HandlerExpr { body } => {
            add_handler_body_type_symbols(index, uri, line_index, source, body, check);
        }
        ast::ExprKind::Pipe { segments, .. }
        | ast::ExprKind::BinOpChain { segments, .. }
        | ast::ExprKind::PipeBack { segments }
        | ast::ExprKind::ComposeForward { segments } => {
            for segment in segments {
                add_expr_type_symbols(index, uri, line_index, source, &segment.node, check);
            }
        }
        ast::ExprKind::Cons { head, tail } => {
            add_expr_type_symbols(index, uri, line_index, source, head, check);
            add_expr_type_symbols(index, uri, line_index, source, tail, check);
        }
        ast::ExprKind::StringInterp { parts, .. } => {
            for part in parts {
                if let ast::StringPart::Expr(expr) = part {
                    add_expr_type_symbols(index, uri, line_index, source, expr, check);
                }
            }
        }
        ast::ExprKind::ListComprehension { body, qualifiers } => {
            add_expr_type_symbols(index, uri, line_index, source, body, check);
            for qualifier in qualifiers {
                match qualifier {
                    ast::ComprehensionQualifier::Generator(pattern, value)
                    | ast::ComprehensionQualifier::Let(pattern, value) => {
                        add_pat_type_symbols(index, uri, line_index, source, pattern, check);
                        add_expr_type_symbols(index, uri, line_index, source, value, check);
                    }
                    ast::ComprehensionQualifier::Guard(value) => {
                        add_expr_type_symbols(index, uri, line_index, source, value, check);
                    }
                }
            }
        }
        ast::ExprKind::DictMethodAccess { dict, .. }
        | ast::ExprKind::DictSuperAccess { dict, .. } => {
            add_expr_type_symbols(index, uri, line_index, source, dict, check);
        }
        ast::ExprKind::ForeignCall { args, .. } => {
            for arg in args {
                add_expr_type_symbols(index, uri, line_index, source, arg, check);
            }
        }
    }
}

fn add_handler_body_type_symbols(
    index: &mut SemanticIndex,
    uri: &Url,
    line_index: &LineIndex,
    source: &str,
    body: &ast::HandlerBody,
    check: &typechecker::CheckResult,
) {
    for effect_ref in &body.effects {
        add_effect_ref_symbol(index, uri, line_index, source, effect_ref, check);
    }
    for effect_ref in &body.needs {
        add_effect_ref_symbol(index, uri, line_index, source, effect_ref, check);
    }
    add_where_clause_type_symbols(index, uri, line_index, source, &body.where_clause, check);
    for arm in &body.arms {
        add_handler_arm_type_symbols(index, uri, line_index, source, &arm.node, check);
    }
    if let Some(return_clause) = &body.return_clause {
        add_handler_arm_type_symbols(index, uri, line_index, source, return_clause, check);
    }
}

fn add_handler_type_symbols(
    index: &mut SemanticIndex,
    uri: &Url,
    line_index: &LineIndex,
    source: &str,
    handler: &ast::Handler,
    check: &typechecker::CheckResult,
) {
    match handler {
        ast::Handler::Named(named) => {
            add_handler_ref_symbol(index, uri, line_index, source, named, check);
        }
        ast::Handler::Inline { items, .. } => {
            for item in items {
                match &item.node {
                    ast::HandlerItem::Named(named) => {
                        add_handler_ref_symbol(index, uri, line_index, source, named, check);
                    }
                    ast::HandlerItem::Arm(arm) | ast::HandlerItem::Return(arm) => {
                        add_handler_arm_type_symbols(index, uri, line_index, source, arm, check);
                    }
                }
            }
        }
    }
}

fn add_handler_arm_type_symbols(
    index: &mut SemanticIndex,
    uri: &Url,
    line_index: &LineIndex,
    source: &str,
    arm: &ast::HandlerArm,
    check: &typechecker::CheckResult,
) {
    if let Some(qualifier) = &arm.qualifier
        && let Some(resolved) = check.resolved_handler_arm_effect_name_for_node(arm.id)
    {
        add_semantic_symbol_reference(
            index,
            uri,
            SemanticSymbolKind::Effect,
            resolved.to_string(),
            name_range(arm.span.start, qualifier, line_index, source),
        );
    }
    if let Some((effect_name, op_name)) =
        check.resolved_effect_operation_for_handler_arm_node(arm.id)
    {
        add_effect_operation_reference_symbol(
            index,
            uri,
            effect_name,
            op_name,
            final_segment_name_range(arm.span, &arm.op_name, line_index, source),
        );
    }
    for param in &arm.params {
        add_pat_type_symbols(index, uri, line_index, source, param, check);
    }
    add_expr_type_symbols(index, uri, line_index, source, &arm.body, check);
    if let Some(finally_block) = &arm.finally_block {
        add_expr_type_symbols(index, uri, line_index, source, finally_block, check);
    }
}
