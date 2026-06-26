use std::collections::{HashMap, HashSet};

use saga::typechecker;
use tower_lsp::lsp_types::*;

use super::super::text::source_text_at;
use super::push_completion;

pub(super) fn push_record_field_completions(
    items: &mut Vec<CompletionItem>,
    seen: &mut HashSet<String>,
    prefix: &str,
    fields: Vec<(String, typechecker::Type)>,
) {
    for (field_name, field_type) in fields {
        push_completion(
            items,
            seen,
            field_name,
            CompletionItemKind::FIELD,
            Some(format!("{field_type}")),
            prefix,
        );
    }
}

pub(super) fn record_fields_for_chain(
    check: &typechecker::CheckResult,
    chain: &[String],
    source: &str,
) -> Option<Vec<(String, typechecker::Type)>> {
    let mut fields = record_fields_for_receiver(check, chain.first()?, source)?;
    for segment in &chain[1..] {
        let (_, field_ty) = fields.iter().find(|(name, _)| name == segment)?;
        fields = record_fields_for_type(check, &check.sub.apply(field_ty))?;
    }
    Some(fields)
}

fn record_fields_for_receiver(
    check: &typechecker::CheckResult,
    receiver: &str,
    source: &str,
) -> Option<Vec<(String, typechecker::Type)>> {
    for (span, ty) in &check.type_at_span {
        if source_text_at(source, *span) == receiver
            && let Some(fields) = record_fields_for_type(check, &check.sub.apply(ty))
        {
            return Some(fields);
        }
    }
    for (node_id, span) in &check.node_spans {
        if source_text_at(source, *span) == receiver
            && let Some(ty) = check.resolved_type_for_node(*node_id)
            && let Some(fields) = record_fields_for_type(check, &check.sub.apply(&ty))
        {
            return Some(fields);
        }
    }
    None
}

pub(super) fn record_fields_for_name(
    check: &typechecker::CheckResult,
    record_name: &str,
) -> Option<Vec<(String, typechecker::Type)>> {
    let canonical = check
        .scope_map
        .resolve_type(record_name)
        .unwrap_or(record_name);
    check
        .records
        .get(canonical)
        .or_else(|| {
            check
                .records
                .iter()
                .find(|(name, _)| typechecker::bare_type_name(name) == record_name)
                .map(|(_, info)| info)
        })
        .map(|info| info.fields.clone())
}

fn record_fields_for_type(
    check: &typechecker::CheckResult,
    ty: &typechecker::Type,
) -> Option<Vec<(String, typechecker::Type)>> {
    match ty {
        typechecker::Type::Record(fields) => Some(fields.clone()),
        typechecker::Type::Con(name, args) => {
            let info = check.records.get(name)?;
            let replacements: HashMap<u32, typechecker::Type> = info
                .type_params
                .iter()
                .copied()
                .zip(args.iter().cloned())
                .collect();
            Some(
                info.fields
                    .iter()
                    .map(|(field, ty)| (field.clone(), replace_type_vars(ty, &replacements)))
                    .collect(),
            )
        }
        _ => None,
    }
}

fn replace_type_vars(
    ty: &typechecker::Type,
    replacements: &HashMap<u32, typechecker::Type>,
) -> typechecker::Type {
    match ty {
        typechecker::Type::Var(id) => replacements
            .get(id)
            .cloned()
            .unwrap_or(typechecker::Type::Var(*id)),
        typechecker::Type::Fun(a, b, row) => typechecker::Type::Fun(
            Box::new(replace_type_vars(a, replacements)),
            Box::new(replace_type_vars(b, replacements)),
            typechecker::EffectRow {
                effects: row
                    .effects
                    .iter()
                    .map(|effect| typechecker::EffectEntry {
                        name: effect.name.clone(),
                        args: effect
                            .args
                            .iter()
                            .map(|arg| replace_type_vars(arg, replacements))
                            .collect(),
                    })
                    .collect(),
                tails: row
                    .tails
                    .iter()
                    .map(|tail| replace_type_vars(tail, replacements))
                    .collect(),
            },
        ),
        typechecker::Type::Con(name, args) => typechecker::Type::Con(
            name.clone(),
            args.iter()
                .map(|arg| replace_type_vars(arg, replacements))
                .collect(),
        ),
        typechecker::Type::Record(fields) => typechecker::Type::Record(
            fields
                .iter()
                .map(|(field, ty)| (field.clone(), replace_type_vars(ty, replacements)))
                .collect(),
        ),
        typechecker::Type::Symbol(name) => typechecker::Type::Symbol(name.clone()),
        typechecker::Type::Error => typechecker::Type::Error,
    }
}
