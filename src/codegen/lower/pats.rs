use crate::ast::{Lit, Pat};
use crate::codegen::cerl::{CLit, CPat};
use std::collections::HashMap;

use super::util::{core_var, lower_lit};

/// Map a function's parameter patterns to Core Erlang variable names.
/// Unit patterns are dropped (they contribute no variable).
pub(super) fn lower_params(params: &[Pat]) -> Vec<String> {
    params
        .iter()
        .enumerate()
        .filter_map(|(i, pat)| match pat {
            Pat::Lit {
                value: Lit::Unit, ..
            } => None,
            Pat::Var { name, .. } => Some(core_var(name)),
            Pat::Wildcard { .. } => Some(format!("_Arg{}", i)),
            _ => Some(format!("_Arg{}", i)),
        })
        .collect()
}

pub(super) fn lower_pat(pat: &Pat, record_fields: &HashMap<String, Vec<String>>) -> CPat {
    match pat {
        Pat::Wildcard { .. } => CPat::Wildcard,
        Pat::Var { name, .. } => CPat::Var(core_var(name)),
        Pat::Lit { value, .. } => CPat::Lit(lower_lit(value)),
        Pat::Tuple { elements, .. } => {
            CPat::Tuple(elements.iter().map(|p| lower_pat(p, record_fields)).collect())
        }
        Pat::Constructor { name, args, .. } => {
            let mut elems = vec![CPat::Lit(CLit::Atom(name.clone()))];
            elems.extend(args.iter().map(|p| lower_pat(p, record_fields)));
            CPat::Tuple(elems)
        }
        Pat::Record { name, fields, .. } => {
            // Records are tagged tuples in declared field order.
            let mut elems = vec![CPat::Lit(CLit::Atom(name.clone()))];
            if let Some(order) = record_fields.get(name) {
                let field_map: HashMap<&str, Option<&Pat>> = fields
                    .iter()
                    .map(|(n, p)| (n.as_str(), p.as_ref()))
                    .collect();
                for field_name in order {
                    match field_map.get(field_name.as_str()) {
                        Some(Some(p)) => elems.push(lower_pat(p, record_fields)),
                        // Field without alias: bind to a var named after the field
                        Some(None) => elems.push(CPat::Var(core_var(field_name))),
                        None => elems.push(CPat::Wildcard),
                    }
                }
            } else {
                for (_, alias) in fields {
                    match alias {
                        Some(p) => elems.push(lower_pat(p, record_fields)),
                        None => elems.push(CPat::Wildcard),
                    }
                }
            }
            CPat::Tuple(elems)
        }
        Pat::StringPrefix { .. } => CPat::Wildcard, // TODO
    }
}
