use super::*;

pub(super) fn native_variant_name(name: &str, stack: &[HandlerFrame]) -> String {
    let mut parts = vec![NATIVE_VARIANT_PREFIX.to_string(), sanitize_ident_part(name)];
    for frame in stack {
        match frame {
            HandlerFrame::Native { effects, handler } => {
                parts.push("native".to_string());
                parts.push(sanitize_ident_part(handler));
                for effect in effects {
                    parts.push(sanitize_ident_part(effect));
                }
            }
            HandlerFrame::Blocking { effects } => {
                parts.push("blocking".to_string());
                for effect in effects {
                    parts.push(sanitize_ident_part(effect));
                }
            }
            HandlerFrame::Static { .. } => {}
        }
    }
    parts.join("__")
}

pub(super) fn variant_name_for_imported(
    source_module: &str,
    name: &str,
    stack: &[HandlerFrame],
) -> String {
    native_variant_name(&format!("xmod__{source_module}__{name}"), stack)
}

pub(super) fn variant_name_for_imported_static(
    source_module: &str,
    name: &str,
    stack: &[HandlerFrame],
) -> String {
    static_variant_name(&format!("xmod__{source_module}__{name}"), stack)
}

pub(super) fn imported_private_helper_variant_name(
    source_module: &str,
    name: &str,
    stack: &[HandlerFrame],
) -> String {
    static_variant_name(&format!("xmod_helper__{source_module}__{name}"), stack)
}

pub(super) fn variant_name_with_dict_key(
    base: String,
    dict_replacements: &[DictParamReplacement],
) -> String {
    if dict_replacements.is_empty() {
        return base;
    }

    let mut key = String::new();
    for replacement in dict_replacements {
        key.push_str(&replacement.target.name);
        key.push('=');
        key.push_str(&replacement.key);
        key.push(';');
    }
    format!("{base}__dict_{:016x}", stable_key_hash(&key))
}

pub(super) fn variant_name_with_value_key(
    base: String,
    value_replacements: &[ValueParamReplacement],
) -> String {
    if value_replacements.is_empty() {
        return base;
    }

    let mut key = String::new();
    for replacement in value_replacements {
        key.push_str(&replacement.target.name);
        key.push('=');
        key.push_str(&replacement.key);
        key.push(';');
    }
    format!("{base}__value_{:016x}", stable_key_hash(&key))
}

pub(super) fn variant_name_with_callback_key(
    base: String,
    callback_replacements: &[CallbackParamReplacement],
) -> String {
    if callback_replacements.is_empty() {
        return base;
    }

    let mut key = String::new();
    for replacement in callback_replacements {
        key.push_str(&replacement.target.name);
        key.push('=');
        key.push_str(&replacement.key);
        key.push(';');
    }
    format!("{base}__cb_{:016x}", stable_key_hash(&key))
}

pub(super) fn variant_name_with_capture_key(base: String, captures: &[String]) -> String {
    if captures.is_empty() {
        return base;
    }
    format!("{base}__caps_{:016x}", stable_key_hash(&captures.join(";")))
}

pub(super) fn stable_key_hash(value: &str) -> u64 {
    let mut hash = 0xcbf29ce484222325_u64;
    for byte in value.as_bytes() {
        hash ^= u64::from(*byte);
        hash = hash.wrapping_mul(0x100000001b3);
    }
    hash
}

pub(super) fn captures_collide_with_params(captures: &[String], params: &[Pat]) -> bool {
    let param_names = bound_names_in_pats(params)
        .into_iter()
        .collect::<HashSet<_>>();
    captures.iter().any(|capture| param_names.contains(capture))
}

pub(super) fn append_capture_variant_args(
    mut params: Vec<Pat>,
    mut args: Vec<Atom>,
    captures: &[String],
    source: crate::ast::NodeId,
) -> (Vec<Pat>, Vec<Atom>) {
    for capture in captures {
        params.push(Pat::Var {
            name: capture.clone(),
            id: source,
            span: crate::token::Span { start: 0, end: 0 },
        });
        args.push(Atom::Var {
            name: MVar {
                name: capture.clone(),
                id: source.0,
            },
            source,
        });
    }
    (params, args)
}

pub(super) fn append_capture_args_to_self_calls(
    expr: MExpr,
    variant_name: &str,
    captures: &[String],
    source: crate::ast::NodeId,
) -> MExpr {
    if captures.is_empty() {
        return expr;
    }
    append_args_to_direct_calls(expr, variant_name, captures, source)
}

pub(super) fn lambda_capture_names(lambda: &Atom) -> Vec<String> {
    let mut names = free_atom_names(lambda).into_iter().collect::<Vec<_>>();
    names.sort();
    names
}

pub(super) fn atom_key(atom: &Atom) -> String {
    match atom {
        Atom::Var { name, .. } => format!("var:{}", name.name),
        Atom::Lit { value, .. } => format!("lit:{value:?}"),
        Atom::Ctor { name, args, .. } => {
            let args = args.iter().map(atom_key).collect::<Vec<_>>().join(",");
            format!("ctor:{name}({args})")
        }
        Atom::Tuple { elements, .. } => {
            let elements = elements.iter().map(atom_key).collect::<Vec<_>>().join(",");
            format!("tuple:({elements})")
        }
        Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. } => {
            let fields = fields
                .iter()
                .map(|(name, value)| format!("{name}:{}", atom_key(value)))
                .collect::<Vec<_>>()
                .join(",");
            format!("record:{{{fields}}}")
        }
        Atom::Lambda { source, .. } => format!("lambda:{}", source.0),
        Atom::DictRef { name, .. } => format!("dict:{name}"),
        Atom::QualifiedRef { module, name, .. } => format!("qualified:{module}.{name}"),
        Atom::Symbol { symbol, .. } => format!("symbol:{symbol}"),
        Atom::BackendAtom { atom, .. } => format!("backend_atom:{atom}"),
        Atom::BackendSpawnThunk { source, .. } => format!("spawn_thunk:{}", source.0),
    }
}

pub(super) fn closed_dict_constructor_arg(atom: &Atom) -> Option<Atom> {
    match atom {
        Atom::Var { .. } | Atom::Lambda { .. } | Atom::QualifiedRef { .. } => None,
        Atom::Lit { .. }
        | Atom::Symbol { .. }
        | Atom::BackendAtom { .. }
        | Atom::DictRef { .. }
        | Atom::BackendSpawnThunk { .. } => Some(atom.clone()),
        Atom::Ctor { args, .. }
            if args
                .iter()
                .all(|arg| closed_dict_constructor_arg(arg).is_some()) =>
        {
            Some(atom.clone())
        }
        Atom::Tuple { elements, .. }
            if elements
                .iter()
                .all(|arg| closed_dict_constructor_arg(arg).is_some()) =>
        {
            Some(atom.clone())
        }
        Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. }
            if fields
                .iter()
                .all(|(_, arg)| closed_dict_constructor_arg(arg).is_some()) =>
        {
            Some(atom.clone())
        }
        Atom::Ctor { .. } | Atom::Tuple { .. } | Atom::AnonRecord { .. } | Atom::Record { .. } => {
            None
        }
    }
}

pub(super) fn closed_value_variant_arg(atom: &Atom) -> Option<Atom> {
    match atom {
        Atom::Ctor { args, .. }
            if args
                .iter()
                .all(|arg| closed_value_variant_arg(arg).is_some()) =>
        {
            Some(atom.clone())
        }
        Atom::Tuple { elements, .. }
            if elements
                .iter()
                .all(|arg| closed_value_variant_arg(arg).is_some()) =>
        {
            Some(atom.clone())
        }
        Atom::Lit { .. } | Atom::Symbol { .. } | Atom::BackendAtom { .. } => Some(atom.clone()),
        Atom::Ctor { .. }
        | Atom::Tuple { .. }
        | Atom::Var { .. }
        | Atom::Lambda { .. }
        | Atom::DictRef { .. }
        | Atom::QualifiedRef { .. }
        | Atom::AnonRecord { .. }
        | Atom::Record { .. }
        | Atom::BackendSpawnThunk { .. } => None,
    }
}

pub(super) fn closed_constructor_variant_arg(atom: &Atom) -> Option<Atom> {
    match atom {
        Atom::Ctor { args, .. }
            if args
                .iter()
                .all(|arg| closed_value_variant_arg(arg).is_some()) =>
        {
            Some(atom.clone())
        }
        _ => None,
    }
}

pub(super) fn closed_case_scrutinee(atom: &Atom) -> Option<Atom> {
    match atom {
        Atom::Lit { .. } | Atom::Ctor { .. } | Atom::Tuple { .. } => closed_value_variant_arg(atom),
        _ => None,
    }
}

pub(super) fn match_pat_atom(pat: &Pat, atom: &Atom) -> Option<Vec<(MVar, Atom)>> {
    let mut bindings = Vec::new();
    match_pat_atom_into(pat, atom, &mut bindings).then_some(bindings)
}

pub(super) fn match_pat_atom_into(
    pat: &Pat,
    atom: &Atom,
    bindings: &mut Vec<(MVar, Atom)>,
) -> bool {
    match (pat, atom) {
        (Pat::Wildcard { .. }, _) => true,
        (Pat::Var { name, id, .. }, _) => {
            bindings.push((
                MVar {
                    name: name.clone(),
                    id: id.0,
                },
                atom.clone(),
            ));
            true
        }
        (Pat::Lit { value, .. }, Atom::Lit { value: atom, .. }) => value == atom,
        (
            Pat::Constructor {
                name,
                args: pat_args,
                ..
            },
            Atom::Ctor {
                name: atom_name,
                args,
                ..
            },
        ) if constructor_names_match(name, atom_name) && pat_args.len() == args.len() => pat_args
            .iter()
            .zip(args)
            .all(|(pat, atom)| match_pat_atom_into(pat, atom, bindings)),
        (
            Pat::Tuple { elements, .. },
            Atom::Tuple {
                elements: atoms, ..
            },
        ) if elements.len() == atoms.len() => elements
            .iter()
            .zip(atoms)
            .all(|(pat, atom)| match_pat_atom_into(pat, atom, bindings)),
        _ => false,
    }
}

pub(super) fn constructor_names_match(a: &str, b: &str) -> bool {
    if a == b {
        return true;
    }
    let a_is_qualified = a.contains('.');
    let b_is_qualified = b.contains('.');
    if a_is_qualified && b_is_qualified {
        return false;
    }
    a.rsplit('.').next() == b.rsplit('.').next()
}

pub(super) fn prune_unused_dict_variant_args(
    params: &[Pat],
    args: Vec<Atom>,
    body: &MExpr,
    dict_replacements: &[DictParamReplacement],
) -> (Vec<Pat>, Vec<Atom>) {
    if dict_replacements.is_empty() {
        return (params.to_vec(), args);
    }

    let prunable_targets = dict_replacements
        .iter()
        .map(|replacement| replacement.target.clone())
        .collect::<Vec<_>>();
    let mut params_out = Vec::with_capacity(params.len());
    let mut args_out = Vec::with_capacity(args.len());
    let mut pruned_any = false;

    for (param, arg) in params.iter().cloned().zip(args) {
        let target = match &param {
            Pat::Var { name, id, .. } => Some(MVar {
                name: name.clone(),
                id: id.0,
            }),
            _ => None,
        };
        let should_prune = target.as_ref().is_some_and(|target| {
            prunable_targets
                .iter()
                .any(|replacement_target| var_matches(target, replacement_target))
                && !expr_contains_target(body, target)
        });

        if should_prune {
            pruned_any = true;
        } else {
            params_out.push(param);
            args_out.push(arg);
        }
    }

    if pruned_any {
        (params_out, args_out)
    } else {
        (params.to_vec(), args_out)
    }
}

pub(super) fn static_variant_name(name: &str, stack: &[HandlerFrame]) -> String {
    let mut parts = vec![STATIC_VARIANT_PREFIX.to_string(), sanitize_ident_part(name)];
    for frame in stack {
        match frame {
            HandlerFrame::Static { effects, arms } => {
                parts.push("static".to_string());
                for effect in effects {
                    parts.push(sanitize_ident_part(effect));
                }
                let mut arm_keys: Vec<_> = arms
                    .iter()
                    .map(|arm| {
                        (
                            arm.op.effect.as_str(),
                            arm.op.op.as_str(),
                            arm.id.0,
                            arm.op.op_index,
                            handler_arm_body_hash(arm),
                        )
                    })
                    .collect();
                arm_keys.sort();
                for (effect, op, id, op_index, body_hash) in arm_keys {
                    parts.push(sanitize_ident_part(effect));
                    parts.push(sanitize_ident_part(op));
                    parts.push(id.to_string());
                    parts.push(op_index.to_string());
                    parts.push(format!("{body_hash:016x}"));
                }
            }
            HandlerFrame::Blocking { effects } => {
                parts.push("blocking".to_string());
                for effect in effects {
                    parts.push(sanitize_ident_part(effect));
                }
            }
            HandlerFrame::Native { effects, handler } => {
                parts.push("native".to_string());
                parts.push(sanitize_ident_part(handler));
                for effect in effects {
                    parts.push(sanitize_ident_part(effect));
                }
            }
        }
    }
    parts.join("__")
}

pub(super) fn handler_arm_body_hash(arm: &MHandlerArm) -> u64 {
    stable_key_hash(&format!("{:?}|{:?}", arm.body, arm.finally_block))
}

pub(crate) fn is_generated_variant_name(name: &str) -> bool {
    name.starts_with(NATIVE_VARIANT_PREFIX) || name.starts_with(STATIC_VARIANT_PREFIX)
}

pub(super) fn sanitize_ident_part(value: &str) -> String {
    let mut out = String::new();
    for ch in value.chars() {
        if ch.is_ascii_alphanumeric() || ch == '_' {
            out.push(ch);
        } else {
            out.push('_');
        }
    }
    if out.is_empty() { "_".to_string() } else { out }
}
