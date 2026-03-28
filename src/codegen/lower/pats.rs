use crate::ast::{Lit, Pat};
use crate::codegen::cerl::{CLit, CPat};
use std::collections::HashMap;

use super::util::{core_var, lower_lit, mangle_ctor_atom};

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

pub(super) fn lower_pat(
    pat: &Pat,
    record_fields: &HashMap<String, Vec<String>>,
    constructor_atoms: &HashMap<String, String>,
) -> CPat {
    match pat {
        Pat::Wildcard { .. } => CPat::Wildcard,
        Pat::Var { name, .. } => CPat::Var(core_var(name)),
        Pat::Lit { value, .. } => CPat::Lit(lower_lit(value)),
        Pat::Tuple { elements, .. } => {
            CPat::Tuple(elements.iter().map(|p| lower_pat(p, record_fields, constructor_atoms)).collect())
        }
        Pat::Constructor { name, args, .. } => match name.as_str() {
            "Cons" if args.len() == 2 => CPat::Cons(
                Box::new(lower_pat(&args[0], record_fields, constructor_atoms)),
                Box::new(lower_pat(&args[1], record_fields, constructor_atoms)),
            ),
            "Nil" if args.is_empty() => CPat::Nil,
            // Just(v) -> bare variable pattern (the value itself, no tuple)
            "Just" if args.len() == 1 => {
                lower_pat(&args[0], record_fields, constructor_atoms)
            }
            // Nothing -> match the atom 'undefined'
            "Nothing" if args.is_empty() => {
                CPat::Lit(CLit::Atom("undefined".to_string()))
            }
            // Booleans are bare atoms to match Erlang's native true/false
            "True" if args.is_empty() => CPat::Lit(CLit::Atom("true".to_string())),
            "False" if args.is_empty() => CPat::Lit(CLit::Atom("false".to_string())),
            // ExitReason constructors are bare atoms to match Erlang exit reasons
            "Normal" if args.is_empty() => CPat::Lit(CLit::Atom("normal".to_string())),
            "Shutdown" if args.is_empty() => CPat::Lit(CLit::Atom("shutdown".to_string())),
            "Killed" if args.is_empty() => CPat::Lit(CLit::Atom("killed".to_string())),
            "Noproc" if args.is_empty() => CPat::Lit(CLit::Atom("noproc".to_string())),
            _ => {
                let atom = mangle_ctor_atom(name, constructor_atoms);
                let mut elems = vec![CPat::Lit(CLit::Atom(atom))];
                elems.extend(args.iter().map(|p| lower_pat(p, record_fields, constructor_atoms)));
                CPat::Tuple(elems)
            }
        }
        Pat::Record { name, fields, as_name, .. } => {
            // Records are tagged tuples in declared field order.
            let atom = mangle_ctor_atom(name, constructor_atoms);
            let mut elems = vec![CPat::Lit(CLit::Atom(atom))];
            if let Some(order) = record_fields.get(name) {
                let field_map: HashMap<&str, Option<&Pat>> = fields
                    .iter()
                    .map(|(n, p)| (n.as_str(), p.as_ref()))
                    .collect();
                for field_name in order {
                    match field_map.get(field_name.as_str()) {
                        Some(Some(p)) => elems.push(lower_pat(p, record_fields, constructor_atoms)),
                        // Field without alias: bind to a var named after the field
                        Some(None) => elems.push(CPat::Var(core_var(field_name))),
                        None => elems.push(CPat::Wildcard),
                    }
                }
            } else {
                for (_, alias) in fields {
                    match alias {
                        Some(p) => elems.push(lower_pat(p, record_fields, constructor_atoms)),
                        None => elems.push(CPat::Wildcard),
                    }
                }
            }
            let tuple_pat = CPat::Tuple(elems);
            match as_name {
                Some(var) => CPat::Alias(core_var(var), Box::new(tuple_pat)),
                None => tuple_pat,
            }
        }
        Pat::AnonRecord { fields, .. } => {
            // Anonymous records are tagged tuples with a deterministic tag.
            let mut sorted_fields: Vec<&str> = fields.iter().map(|(n, _)| n.as_str()).collect();
            sorted_fields.sort();
            let tag = format!("__anon_{}", sorted_fields.join("_"));
            let mut elems = vec![CPat::Lit(CLit::Atom(tag))];
            let field_map: HashMap<&str, Option<&Pat>> = fields
                .iter()
                .map(|(n, p)| (n.as_str(), p.as_ref()))
                .collect();
            for field_name in &sorted_fields {
                match field_map.get(field_name) {
                    Some(Some(p)) => elems.push(lower_pat(p, record_fields, constructor_atoms)),
                    Some(None) => elems.push(CPat::Var(core_var(field_name))),
                    None => elems.push(CPat::Wildcard),
                }
            }
            CPat::Tuple(elems)
        }
        Pat::StringPrefix {
            prefix, rest, ..
        } => {
            // "abc" <> rest  =>  [97 | [98 | [99 | Rest]]]
            // Expand the prefix string into a cons chain of character codes,
            // with the rest pattern as the tail.
            let tail = lower_pat(rest, record_fields, constructor_atoms);
            prefix.chars().rev().fold(tail, |acc, ch| {
                CPat::Cons(Box::new(CPat::Lit(CLit::Int(ch as i64))), Box::new(acc))
            })
        }
        Pat::ListPat { .. } | Pat::ConsPat { .. } => {
            unreachable!("surface syntax should be desugared before codegen")
        }
    }
}
