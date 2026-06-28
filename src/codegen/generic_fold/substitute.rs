use super::*;

/// Replace every `Var` whose name is a substituted dict param with the
/// corresponding concrete sub-dictionary expression (cloned with fresh ids).
pub(crate) fn substitute_dict_vars(expr: &mut Expr, subst: &HashMap<&str, &Expr>) {
    if let ExprKind::Var { name } = &expr.kind
        && let Some(replacement) = subst.get(name.as_str())
    {
        let mut value = (*replacement).clone();
        freshen_expr_ids(&mut value);
        *expr = value;
        return;
    }
    for child in child_exprs_mut(expr) {
        substitute_dict_vars(child, subst);
    }
}

/// Collect carried side-table ids from `expr` and descendant patterns in a
/// deterministic pre-order. Run before and after `freshen_expr_ids` on the same
/// structurally unchanged tree to build an old->new id mapping by position.
pub(crate) fn collect_carried_ids(expr: &mut Expr, out: &mut Vec<NodeId>) {
    out.push(expr.id);
    match &mut expr.kind {
        ExprKind::Lambda { params, .. } => {
            for pat in params {
                collect_pat_ids(pat, out);
            }
        }
        ExprKind::Case { arms, .. } | ExprKind::Receive { arms, .. } => {
            for arm in arms {
                collect_pat_ids(&mut arm.node.pattern, out);
            }
        }
        ExprKind::Do {
            bindings,
            else_arms,
            ..
        } => {
            for (pat, _) in bindings {
                collect_pat_ids(pat, out);
            }
            for arm in else_arms {
                collect_pat_ids(&mut arm.node.pattern, out);
            }
        }
        _ => {}
    }
    for child in child_exprs_mut(expr) {
        collect_carried_ids(child, out);
    }
}

pub(crate) fn collect_pat_ids(pat: &mut Pat, out: &mut Vec<NodeId>) {
    out.push(pat.id());
    match pat {
        Pat::Constructor { args, .. } => {
            for arg in args {
                collect_pat_ids(arg, out);
            }
        }
        Pat::Record { fields, .. } | Pat::AnonRecord { fields, .. } => {
            for (_, maybe_pat) in fields {
                if let Some(field_pat) = maybe_pat {
                    collect_pat_ids(field_pat, out);
                }
            }
        }
        Pat::Tuple { elements, .. }
        | Pat::ListPat { elements, .. }
        | Pat::Or {
            patterns: elements, ..
        } => {
            for element in elements {
                collect_pat_ids(element, out);
            }
        }
        Pat::StringPrefix { rest, .. } => collect_pat_ids(rest, out),
        Pat::BitStringPat { segments, .. } => {
            for segment in segments {
                collect_pat_ids(&mut segment.value, out);
            }
        }
        Pat::ConsPat { head, tail, .. } => {
            collect_pat_ids(head, out);
            collect_pat_ids(tail, out);
        }
        Pat::Wildcard { .. } | Pat::Var { .. } | Pat::Lit { .. } => {}
    }
}

pub(crate) fn collect_constructor_names(expr: &mut Expr, out: &mut Vec<String>) {
    match &mut expr.kind {
        ExprKind::Constructor { name } => out.push(base_name(name).to_string()),
        ExprKind::RecordCreate { name, .. } => out.push(base_name(name).to_string()),
        ExprKind::Lambda { params, .. } => {
            for pat in params {
                collect_pat_constructor_names(pat, out);
            }
        }
        ExprKind::Case { arms, .. } | ExprKind::Receive { arms, .. } => {
            for arm in arms {
                collect_pat_constructor_names(&mut arm.node.pattern, out);
            }
        }
        ExprKind::Do {
            bindings,
            else_arms,
            ..
        } => {
            for (pat, _) in bindings {
                collect_pat_constructor_names(pat, out);
            }
            for arm in else_arms {
                collect_pat_constructor_names(&mut arm.node.pattern, out);
            }
        }
        _ => {}
    }
    for child in child_exprs_mut(expr) {
        collect_constructor_names(child, out);
    }
}

pub(crate) fn collect_pat_constructor_names(pat: &mut Pat, out: &mut Vec<String>) {
    match pat {
        Pat::Constructor { name, args, .. } => {
            out.push(base_name(name).to_string());
            for arg in args {
                collect_pat_constructor_names(arg, out);
            }
        }
        Pat::Record { name, fields, .. } => {
            out.push(base_name(name).to_string());
            for (_, maybe_pat) in fields {
                if let Some(field_pat) = maybe_pat {
                    collect_pat_constructor_names(field_pat, out);
                }
            }
        }
        Pat::AnonRecord { fields, .. } => {
            for (_, maybe_pat) in fields {
                if let Some(field_pat) = maybe_pat {
                    collect_pat_constructor_names(field_pat, out);
                }
            }
        }
        Pat::Tuple { elements, .. }
        | Pat::ListPat { elements, .. }
        | Pat::Or {
            patterns: elements, ..
        } => {
            for element in elements {
                collect_pat_constructor_names(element, out);
            }
        }
        Pat::StringPrefix { rest, .. } => collect_pat_constructor_names(rest, out),
        Pat::BitStringPat { segments, .. } => {
            for segment in segments {
                collect_pat_constructor_names(&mut segment.value, out);
            }
        }
        Pat::ConsPat { head, tail, .. } => {
            collect_pat_constructor_names(head, out);
            collect_pat_constructor_names(tail, out);
        }
        Pat::Wildcard { .. } | Pat::Var { .. } | Pat::Lit { .. } => {}
    }
}

/// Replace free occurrences of `Var{name}` with `replacement` (cloned with fresh
/// ids per occurrence), **capture-avoiding**: substitution does not descend into
/// a sub-scope that re-binds `name`. This matters because bottom-up folding nests
/// inlined bodies that independently reuse binder names (every building-block
/// codec names its payload `inner`), so the same name is shadowed at several
/// depths; a naive substitution would rewrite the shadowed occurrences too.
pub(crate) fn substitute_var(expr: &mut Expr, name: &str, replacement: &Expr) {
    match &mut expr.kind {
        ExprKind::Var { name: var_name } => {
            if var_name == name {
                let mut value = replacement.clone();
                freshen_expr_ids(&mut value);
                *expr = value;
            }
        }
        ExprKind::Case {
            scrutinee, arms, ..
        } => {
            substitute_var(scrutinee, name, replacement);
            for ann in arms {
                // The arm pattern binds for its guard + body; if it re-binds
                // `name`, those are a shadowed scope — leave them.
                if pat_binds(&ann.node.pattern, name) {
                    continue;
                }
                if let Some(g) = &mut ann.node.guard {
                    substitute_var(g, name, replacement);
                }
                substitute_var(&mut ann.node.body, name, replacement);
            }
        }
        ExprKind::Lambda { params, body } => {
            if !params.iter().any(|p| pat_binds(p, name)) {
                substitute_var(body, name, replacement);
            }
        }
        ExprKind::Block { stmts, .. } => {
            // Sequential scoping: a `let`/`letfun` binding `name` shadows it for
            // every following statement and the block tail.
            let mut shadowed = false;
            for ann in stmts {
                match &mut ann.node {
                    Stmt::Let { pattern, value, .. } => {
                        if !shadowed {
                            substitute_var(value, name, replacement);
                        }
                        if pat_binds(pattern, name) {
                            shadowed = true;
                        }
                    }
                    Stmt::LetFun {
                        name: fn_name,
                        params,
                        guard,
                        body,
                        ..
                    } => {
                        let body_shadowed = shadowed
                            || fn_name == name
                            || params.iter().any(|p| pat_binds(p, name));
                        if !body_shadowed {
                            if let Some(g) = guard {
                                substitute_var(g, name, replacement);
                            }
                            substitute_var(body, name, replacement);
                        }
                        if fn_name == name {
                            shadowed = true;
                        }
                    }
                    Stmt::Expr(e) => {
                        if !shadowed {
                            substitute_var(e, name, replacement);
                        }
                    }
                }
            }
        }
        ExprKind::Do {
            bindings,
            success,
            else_arms,
            ..
        } => {
            let mut shadowed = false;
            for (pat, e) in bindings {
                if !shadowed {
                    substitute_var(e, name, replacement);
                }
                if pat_binds(pat, name) {
                    shadowed = true;
                }
            }
            if !shadowed {
                substitute_var(success, name, replacement);
            }
            // Else arms run in the outer scope (the do-bindings failed), each
            // scoped only by its own pattern.
            for ann in else_arms {
                if pat_binds(&ann.node.pattern, name) {
                    continue;
                }
                if let Some(g) = &mut ann.node.guard {
                    substitute_var(g, name, replacement);
                }
                substitute_var(&mut ann.node.body, name, replacement);
            }
        }
        ExprKind::ListComprehension { body, qualifiers } => {
            let mut shadowed = false;
            for q in qualifiers {
                match q {
                    ComprehensionQualifier::Generator(pat, e)
                    | ComprehensionQualifier::Let(pat, e) => {
                        if !shadowed {
                            substitute_var(e, name, replacement);
                        }
                        if pat_binds(pat, name) {
                            shadowed = true;
                        }
                    }
                    ComprehensionQualifier::Guard(e) => {
                        if !shadowed {
                            substitute_var(e, name, replacement);
                        }
                    }
                }
            }
            if !shadowed {
                substitute_var(body, name, replacement);
            }
        }
        ExprKind::Receive {
            arms, after_clause, ..
        } => {
            for ann in arms {
                if pat_binds(&ann.node.pattern, name) {
                    continue;
                }
                if let Some(g) = &mut ann.node.guard {
                    substitute_var(g, name, replacement);
                }
                substitute_var(&mut ann.node.body, name, replacement);
            }
            if let Some((timeout, body)) = after_clause {
                substitute_var(timeout, name, replacement);
                substitute_var(body, name, replacement);
            }
        }
        ExprKind::With {
            expr: inner,
            handler,
        } => {
            substitute_var(inner, name, replacement);
            substitute_in_handler(handler, name, replacement);
        }
        ExprKind::HandlerExpr { body } => {
            for arm in &mut body.arms {
                substitute_in_handler_arm(&mut arm.node, name, replacement);
            }
        }
        // No other `ExprKind` binds variables, so the generic child recursion is
        // capture-safe for them.
        _ => {
            for child in child_exprs_mut(expr) {
                substitute_var(child, name, replacement);
            }
        }
    }
}

/// Does `pat` bind `name`? (Used to stop capture-avoiding substitution at a
/// shadowing binder.)
pub(crate) fn pat_binds(pat: &Pat, name: &str) -> bool {
    match pat {
        Pat::Wildcard { .. } | Pat::Lit { .. } => false,
        Pat::Var { name: n, .. } => n == name,
        Pat::Constructor { args, .. } => args.iter().any(|p| pat_binds(p, name)),
        Pat::Tuple { elements, .. } | Pat::ListPat { elements, .. } => {
            elements.iter().any(|p| pat_binds(p, name))
        }
        Pat::Or { patterns, .. } => patterns.iter().any(|p| pat_binds(p, name)),
        // A field with no alias binds the field name itself (`{ status }`); an
        // aliased field (`{ code: c }`) binds the alias pattern's vars.
        Pat::Record {
            fields, as_name, ..
        } => as_name.as_deref() == Some(name) || record_fields_bind(fields, name),
        Pat::AnonRecord { fields, .. } => record_fields_bind(fields, name),
        Pat::StringPrefix { rest, .. } => pat_binds(rest, name),
        Pat::ConsPat { head, tail, .. } => pat_binds(head, name) || pat_binds(tail, name),
        Pat::BitStringPat { segments, .. } => segments.iter().any(|s| pat_binds(&s.value, name)),
    }
}

pub(crate) fn record_fields_bind(fields: &[(String, Option<Pat>)], name: &str) -> bool {
    fields.iter().any(|(fname, sub)| match sub {
        Some(p) => pat_binds(p, name),
        None => fname == name,
    })
}

pub(crate) fn substitute_in_handler(handler: &mut Handler, name: &str, replacement: &Expr) {
    match handler {
        Handler::Named(_) => {}
        Handler::Inline { items, .. } => {
            for item in items {
                match &mut item.node {
                    HandlerItem::Named(_) => {}
                    HandlerItem::Arm(arm) | HandlerItem::Return(arm) => {
                        substitute_in_handler_arm(arm, name, replacement);
                    }
                }
            }
        }
    }
}

pub(crate) fn substitute_in_handler_arm(arm: &mut HandlerArm, name: &str, replacement: &Expr) {
    // The arm's operation parameters bind for its body and finally block.
    if arm.params.iter().any(|p| pat_binds(p, name)) {
        return;
    }
    substitute_var(&mut arm.body, name, replacement);
    if let Some(fb) = &mut arm.finally_block {
        substitute_var(fb, name, replacement);
    }
}

/// Names bound by a pattern (appended to `out`). Used by the case-of-case capture
/// guard and is the dual of [`pat_binds`].
pub(crate) fn pat_bound_names(pat: &Pat, out: &mut Vec<String>) {
    match pat {
        Pat::Wildcard { .. } | Pat::Lit { .. } => {}
        Pat::Var { name, .. } => out.push(name.clone()),
        Pat::Constructor { args, .. } => {
            for a in args {
                pat_bound_names(a, out);
            }
        }
        Pat::Tuple { elements, .. } | Pat::ListPat { elements, .. } => {
            for a in elements {
                pat_bound_names(a, out);
            }
        }
        Pat::Or { patterns, .. } => {
            for a in patterns {
                pat_bound_names(a, out);
            }
        }
        Pat::Record {
            fields, as_name, ..
        } => {
            if let Some(n) = as_name {
                out.push(n.clone());
            }
            record_field_bound_names(fields, out);
        }
        Pat::AnonRecord { fields, .. } => record_field_bound_names(fields, out),
        Pat::StringPrefix { rest, .. } => pat_bound_names(rest, out),
        Pat::ConsPat { head, tail, .. } => {
            pat_bound_names(head, out);
            pat_bound_names(tail, out);
        }
        Pat::BitStringPat { segments, .. } => {
            for s in segments {
                pat_bound_names(&s.value, out);
            }
        }
    }
}

pub(crate) fn record_field_bound_names(fields: &[(String, Option<Pat>)], out: &mut Vec<String>) {
    for (fname, sub) in fields {
        match sub {
            Some(p) => pat_bound_names(p, out),
            None => out.push(fname.clone()),
        }
    }
}

/// Free variables across a list of case arms (each arm pattern binds within its
/// guard + body). Binder-aware so a name bound *inside* an arm isn't counted as
/// free — the case-of-case capture guard needs the precise set, not an
/// over-approximation (the decode codec reuses `e` for every `Err` arm).
pub(crate) fn free_vars_arms(arms: &[Annotated<CaseArm>]) -> std::collections::HashSet<String> {
    let mut acc = std::collections::HashSet::new();
    for ann in arms {
        let arm = &ann.node;
        let mut bound = Vec::new();
        pat_bound_names(&arm.pattern, &mut bound);
        if let Some(g) = &arm.guard {
            collect_free_vars(g, &bound, &mut acc);
        }
        collect_free_vars(&arm.body, &bound, &mut acc);
    }
    acc
}

/// Collect free `Var` names of `expr` into `acc`, treating names in `bound` (and
/// any binders encountered along the way) as not free. Mirrors the binder
/// structure of [`substitute_var`].
pub(crate) fn collect_free_vars(
    expr: &Expr,
    bound: &[String],
    acc: &mut std::collections::HashSet<String>,
) {
    match &expr.kind {
        ExprKind::Var { name } => {
            if !bound.contains(name) {
                acc.insert(name.clone());
            }
        }
        ExprKind::Case {
            scrutinee, arms, ..
        } => {
            collect_free_vars(scrutinee, bound, acc);
            for ann in arms {
                let arm = &ann.node;
                let mut inner = bound.to_vec();
                pat_bound_names(&arm.pattern, &mut inner);
                if let Some(g) = &arm.guard {
                    collect_free_vars(g, &inner, acc);
                }
                collect_free_vars(&arm.body, &inner, acc);
            }
        }
        ExprKind::Lambda { params, body } => {
            let mut inner = bound.to_vec();
            for p in params {
                pat_bound_names(p, &mut inner);
            }
            collect_free_vars(body, &inner, acc);
        }
        ExprKind::Block { stmts, .. } => {
            let mut inner = bound.to_vec();
            for ann in stmts {
                match &ann.node {
                    Stmt::Let { pattern, value, .. } => {
                        collect_free_vars(value, &inner, acc);
                        pat_bound_names(pattern, &mut inner);
                    }
                    Stmt::LetFun {
                        name,
                        params,
                        guard,
                        body,
                        ..
                    } => {
                        inner.push(name.clone());
                        let mut body_scope = inner.clone();
                        for p in params {
                            pat_bound_names(p, &mut body_scope);
                        }
                        if let Some(g) = guard {
                            collect_free_vars(g, &body_scope, acc);
                        }
                        collect_free_vars(body, &body_scope, acc);
                    }
                    Stmt::Expr(e) => collect_free_vars(e, &inner, acc),
                }
            }
        }
        ExprKind::Do {
            bindings,
            success,
            else_arms,
            ..
        } => {
            let mut inner = bound.to_vec();
            for (pat, e) in bindings {
                collect_free_vars(e, &inner, acc);
                pat_bound_names(pat, &mut inner);
            }
            collect_free_vars(success, &inner, acc);
            for ann in else_arms {
                let arm = &ann.node;
                let mut arm_scope = bound.to_vec();
                pat_bound_names(&arm.pattern, &mut arm_scope);
                if let Some(g) = &arm.guard {
                    collect_free_vars(g, &arm_scope, acc);
                }
                collect_free_vars(&arm.body, &arm_scope, acc);
            }
        }
        ExprKind::ListComprehension { body, qualifiers } => {
            let mut inner = bound.to_vec();
            for q in qualifiers {
                match q {
                    ComprehensionQualifier::Generator(pat, e)
                    | ComprehensionQualifier::Let(pat, e) => {
                        collect_free_vars(e, &inner, acc);
                        pat_bound_names(pat, &mut inner);
                    }
                    ComprehensionQualifier::Guard(e) => collect_free_vars(e, &inner, acc),
                }
            }
            collect_free_vars(body, &inner, acc);
        }
        // Other binders (Receive, With, HandlerExpr) don't appear in the decode
        // fusion shapes; fall through to the generic child walk, which keeps the
        // outer `bound` set. This can only *over*-count free vars there (treating
        // their binders as free), which makes the capture guard more conservative
        // — never unsound.
        _ => {
            let mut e = expr.clone();
            for child in child_exprs_mut(&mut e) {
                collect_free_vars(child, bound, acc);
            }
        }
    }
}

/// Mutable references to the direct child expressions of `expr`. Descends into
/// `DictMethodAccess.dict` (the dictionary sub-expression). The match is
/// exhaustive so a newly-added `ExprKind` is a compile error here, not a silent
/// gap. Returning a `Vec<&mut Expr>` (rather than taking a visitor closure) lets
/// callers recurse without a `&mut self`-capturing closure, which would not
/// borrow-check.
pub(crate) fn child_exprs_mut(expr: &mut Expr) -> Vec<&mut Expr> {
    let mut out: Vec<&mut Expr> = Vec::new();
    match &mut expr.kind {
        ExprKind::Lit { .. }
        | ExprKind::Var { .. }
        | ExprKind::Constructor { .. }
        | ExprKind::QualifiedName { .. }
        | ExprKind::DictRef { .. }
        | ExprKind::SymbolIntrinsic { .. } => {}

        ExprKind::DictMethodAccess { dict, .. } | ExprKind::DictSuperAccess { dict, .. } => {
            out.push(dict)
        }

        ExprKind::App { func, arg } => {
            out.push(func);
            out.push(arg);
        }
        ExprKind::BinOp { left, right, .. } => {
            out.push(left);
            out.push(right);
        }
        ExprKind::UnaryMinus { expr: inner } => out.push(inner),
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            out.push(cond);
            out.push(then_branch);
            out.push(else_branch);
        }
        ExprKind::Case {
            scrutinee, arms, ..
        } => {
            out.push(scrutinee);
            for ann_arm in arms {
                if let Some(g) = &mut ann_arm.node.guard {
                    out.push(g);
                }
                out.push(&mut ann_arm.node.body);
            }
        }
        ExprKind::Block { stmts, .. } => {
            for ann_stmt in stmts {
                push_stmt_child_exprs(&mut ann_stmt.node, &mut out);
            }
        }
        ExprKind::Lambda { body, .. } => out.push(body),
        ExprKind::FieldAccess { expr: inner, .. } => out.push(inner),
        ExprKind::RecordCreate { fields, .. }
        | ExprKind::ProjectionLiteral { fields, .. }
        | ExprKind::AnonRecordCreate { fields, .. } => {
            for (_, _, val) in fields {
                out.push(val);
            }
        }
        ExprKind::RecordUpdate { record, fields, .. } => {
            out.push(record);
            for (_, _, val) in fields {
                out.push(val);
            }
        }
        ExprKind::EffectCall { args, .. } => {
            for arg in args {
                out.push(arg);
            }
        }
        ExprKind::With {
            expr: inner,
            handler,
        } => {
            out.push(inner);
            push_handler_child_exprs(handler, &mut out);
        }
        ExprKind::Resume { value } => out.push(value),
        ExprKind::HandlerExpr { body } => push_handler_body_child_exprs(body, &mut out),
        ExprKind::Tuple { elements } => {
            for e in elements {
                out.push(e);
            }
        }
        ExprKind::Do {
            bindings,
            success,
            else_arms,
            ..
        } => {
            for (_, e) in bindings {
                out.push(e);
            }
            out.push(success);
            for ann_arm in else_arms {
                if let Some(g) = &mut ann_arm.node.guard {
                    out.push(g);
                }
                out.push(&mut ann_arm.node.body);
            }
        }
        ExprKind::Receive {
            arms, after_clause, ..
        } => {
            for ann_arm in arms {
                if let Some(g) = &mut ann_arm.node.guard {
                    out.push(g);
                }
                out.push(&mut ann_arm.node.body);
            }
            if let Some((timeout, body)) = after_clause {
                out.push(timeout);
                out.push(body);
            }
        }
        ExprKind::Ascription { expr: inner, .. } => out.push(inner),
        ExprKind::BitString { segments } => {
            for seg in segments {
                out.push(&mut seg.value);
                if let Some(size) = &mut seg.size {
                    out.push(size);
                }
            }
        }
        ExprKind::Pipe { segments, .. } | ExprKind::BinOpChain { segments, .. } => {
            for seg in segments {
                out.push(&mut seg.node);
            }
        }
        ExprKind::PipeBack { segments } | ExprKind::ComposeForward { segments } => {
            for seg in segments {
                out.push(&mut seg.node);
            }
        }
        ExprKind::Cons { head, tail } => {
            out.push(head);
            out.push(tail);
        }
        ExprKind::ListLit { elements } => {
            for e in elements {
                out.push(e);
            }
        }
        ExprKind::StringInterp { parts, .. } => {
            for part in parts {
                if let StringPart::Expr(e) = part {
                    out.push(e);
                }
            }
        }
        ExprKind::ListComprehension { body, qualifiers } => {
            out.push(body);
            for q in qualifiers {
                match q {
                    ComprehensionQualifier::Generator(_, e)
                    | ComprehensionQualifier::Let(_, e)
                    | ComprehensionQualifier::Guard(e) => out.push(e),
                }
            }
        }
        ExprKind::ForeignCall { args, .. } => {
            for arg in args {
                out.push(arg);
            }
        }
    }
    out
}

pub(crate) fn push_stmt_child_exprs<'e>(stmt: &'e mut Stmt, out: &mut Vec<&'e mut Expr>) {
    match stmt {
        Stmt::Let { value, .. } => out.push(value),
        Stmt::LetFun { guard, body, .. } => {
            if let Some(g) = guard {
                out.push(g);
            }
            out.push(body);
        }
        Stmt::Expr(e) => out.push(e),
    }
}

pub(crate) fn push_handler_child_exprs<'e>(handler: &'e mut Handler, out: &mut Vec<&'e mut Expr>) {
    match handler {
        Handler::Named(_) => {}
        Handler::Inline { items, .. } => {
            for item in items {
                match &mut item.node {
                    HandlerItem::Named(_) => {}
                    HandlerItem::Arm(arm) | HandlerItem::Return(arm) => {
                        push_handler_arm_child_exprs(arm, out);
                    }
                }
            }
        }
    }
}

pub(crate) fn push_handler_body_child_exprs<'e>(
    body: &'e mut HandlerBody,
    out: &mut Vec<&'e mut Expr>,
) {
    for arm in &mut body.arms {
        push_handler_arm_child_exprs(&mut arm.node, out);
    }
}

pub(crate) fn push_handler_arm_child_exprs<'e>(
    arm: &'e mut HandlerArm,
    out: &mut Vec<&'e mut Expr>,
) {
    out.push(&mut arm.body);
    if let Some(fb) = &mut arm.finally_block {
        out.push(fb);
    }
}
