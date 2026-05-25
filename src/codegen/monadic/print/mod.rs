//! Debug pretty-printer for the monadic IR.
//!
//! Standalone — not wired into any consumer yet. The output is intended for
//! humans reading IR dumps during development and for snapshot tests. It is
//! NOT a parseable surface form: there is no round-trip from output back to
//! `MProgram`.
//!
//! Design constraints (from the planning doc, step 5):
//!   - Stable output for the same input (deterministic ordering everywhere).
//!   - Bind / Let chains print as flat sequences, not nested blocks.
//!   - NodeIds appear as `[#N]` suffixes on structural nodes; omitted on
//!     `Pure` / `Bind` / `Let` (no source NodeId on those).
//!   - Handler classification (Static / Dynamic) is shown explicitly.
//!   - Indent step is two spaces.

#![allow(dead_code)] // Public API used by tests + future debug callers.

use std::fmt::Write;

use crate::ast::{BinOp, Lit, Pat};

use super::ir::{
    Atom, EffectOpRef, MArm, MBitSegment, MDecl, MDictConstructor, MExpr, MFunBinding, MHandler,
    MHandlerArm, MProgram, MVal, MVar,
};

// -------------------------------------------------------------------------
// Public API
// -------------------------------------------------------------------------

pub fn print_program(m: &MProgram) -> String {
    let mut out = String::new();
    for (i, d) in m.iter().enumerate() {
        if i > 0 {
            out.push('\n');
        }
        write_decl(&mut out, d);
    }
    trim_trailing_newlines(&mut out);
    out
}

pub fn print_expr(e: &MExpr) -> String {
    let mut out = String::new();
    write_expr(&mut out, 0, e);
    trim_trailing_newlines(&mut out);
    out
}

pub fn print_atom(a: &Atom) -> String {
    atom_str(a)
}

pub fn print_handler(h: &MHandler) -> String {
    let mut out = String::new();
    write_handler(&mut out, 0, h);
    trim_trailing_newlines(&mut out);
    out
}

// -------------------------------------------------------------------------
// Decls
// -------------------------------------------------------------------------

fn write_decl(out: &mut String, d: &MDecl) {
    match d {
        MDecl::FunBinding(f) => write_fun_binding(out, f),
        MDecl::Val(v) => write_val(out, v),
        MDecl::DictConstructor(dc) => write_dict_ctor(out, dc),
        MDecl::Passthrough(decl) => {
            // Passthrough decls have no monadic body; print a short marker so
            // dumps remain stable and identifiable without leaking the full
            // ast::Decl Debug shape.
            writeln!(out, "passthrough {}", decl_kind_name(decl)).unwrap();
        }
    }
}

fn write_fun_binding(out: &mut String, f: &MFunBinding) {
    let params = params_str(&f.params);
    writeln!(out, "fun {} ({}) [#{}] =", f.name, params, f.id.0).unwrap();
    write_expr(out, 2, &f.body);
}

fn write_val(out: &mut String, v: &MVal) {
    let vis = if v.public { "pub " } else { "" };
    writeln!(out, "{vis}val {} [#{}] =", v.name, v.id.0).unwrap();
    write_expr(out, 2, &v.value);
}

fn write_dict_ctor(out: &mut String, dc: &MDictConstructor) {
    writeln!(
        out,
        "dict-ctor {} ({}) [#{}]",
        dc.name,
        dc.dict_params.join(", "),
        dc.id.0
    )
    .unwrap();
    for (i, m) in dc.methods.iter().enumerate() {
        writeln!(out, "  method[{}]:", i).unwrap();
        write_expr(out, 4, m);
    }
}

fn decl_kind_name(d: &crate::ast::Decl) -> &'static str {
    use crate::ast::Decl::*;
    match d {
        FunSignature { .. } => "FunSignature",
        FunBinding { .. } => "FunBinding",
        Let { .. } => "Let",
        TypeDef { .. } => "TypeDef",
        RecordDef { .. } => "RecordDef",
        EffectDef { .. } => "EffectDef",
        TraitDef { .. } => "TraitDef",
        ImplDef { .. } => "ImplDef",
        Import { .. } => "Import",
        ModuleDecl { .. } => "ModuleDecl",
        TypeAlias { .. } => "TypeAlias",
        Val { .. } => "Val",
        HandlerDef { .. } => "HandlerDef",
        DictConstructor { .. } => "DictConstructor",
    }
}

// -------------------------------------------------------------------------
// Expressions
// -------------------------------------------------------------------------

fn write_expr(out: &mut String, indent: usize, e: &MExpr) {
    // Flatten Bind / Let chains so consecutive binders sit at the same indent.
    let mut cur = e;
    loop {
        match cur {
            MExpr::Bind { var, value, body } => {
                write_bind_line(out, indent, "bind", var, value);
                cur = body;
            }
            MExpr::Let { var, value, body } => {
                write_bind_line(out, indent, "let", var, value);
                cur = body;
            }
            _ => break,
        }
    }
    write_tail(out, indent, cur);
}

fn write_bind_line(out: &mut String, indent: usize, kw: &str, var: &MVar, value: &MExpr) {
    let p = pad(indent);
    let v = mvar_str(var);
    if should_inline_value(value) {
        writeln!(out, "{p}{kw} {v} <- {}", expr_compact(value)).unwrap();
    } else {
        writeln!(out, "{p}{kw} {v} <-").unwrap();
        write_expr(out, indent + 2, value);
    }
}

fn write_tail(out: &mut String, indent: usize, e: &MExpr) {
    let p = pad(indent);
    match e {
        MExpr::Bind { .. } | MExpr::Let { .. } => unreachable!("flattened above"),
        MExpr::Pure(a) => writeln!(out, "{p}Pure({})", atom_str(a)).unwrap(),
        MExpr::Yield { op, args, source } => writeln!(
            out,
            "{p}Yield({}, [{}]) [#{}]",
            op_str(op),
            atoms_str(args),
            source.0
        )
        .unwrap(),
        MExpr::App { head, args, source } => writeln!(
            out,
            "{p}App({}, [{}]) [#{}]",
            atom_str(head),
            atoms_str(args),
            source.0
        )
        .unwrap(),
        MExpr::Case {
            scrutinee,
            arms,
            source,
        } => {
            writeln!(out, "{p}case {} [#{}] of", atom_str(scrutinee), source.0).unwrap();
            for arm in arms {
                write_arm(out, indent + 2, arm);
            }
        }
        MExpr::If {
            cond,
            then_branch,
            else_branch,
            source,
        } => {
            writeln!(out, "{p}if {} [#{}] then", atom_str(cond), source.0).unwrap();
            write_expr(out, indent + 2, then_branch);
            writeln!(out, "{p}else").unwrap();
            write_expr(out, indent + 2, else_branch);
        }
        MExpr::With {
            handler,
            body,
            source: _,
        } => {
            write_handler(out, indent, handler);
            write_expr(out, indent, body);
        }
        MExpr::Resume { value, source } => {
            writeln!(out, "{p}Resume({}) [#{}]", atom_str(value), source.0).unwrap();
        }
        MExpr::FieldAccess {
            record,
            field,
            record_name,
            source,
        } => {
            let rn = record_name
                .as_deref()
                .map(|n| format!("{n}."))
                .unwrap_or_default();
            writeln!(
                out,
                "{p}FieldAccess({}, {}{}) [#{}]",
                atom_str(record),
                rn,
                field,
                source.0
            )
            .unwrap();
        }
        MExpr::RecordUpdate {
            record,
            fields,
            record_name,
            source,
        } => {
            let rn = record_name
                .as_deref()
                .map(|n| format!("{n} "))
                .unwrap_or_default();
            writeln!(
                out,
                "{p}RecordUpdate({}{}, {{{}}}) [#{}]",
                rn,
                atom_str(record),
                fields_str(fields),
                source.0
            )
            .unwrap();
        }
        MExpr::DictMethodAccess {
            dict,
            trait_name,
            method_index,
            source,
        } => {
            writeln!(
                out,
                "{p}DictMethodAccess({}, {}[{}]) [#{}]",
                atom_str(dict),
                trait_name,
                method_index,
                source.0
            )
            .unwrap();
        }
        MExpr::ForeignCall {
            module,
            func,
            args,
            source,
        } => {
            writeln!(
                out,
                "{p}ForeignCall({}:{}, [{}]) [#{}]",
                module,
                func,
                atoms_str(args),
                source.0
            )
            .unwrap();
        }
        MExpr::BinOp {
            op,
            left,
            right,
            source,
        } => writeln!(
            out,
            "{p}BinOp({}, {}, {}) [#{}]",
            binop_sym(op),
            atom_str(left),
            atom_str(right),
            source.0
        )
        .unwrap(),
        MExpr::UnaryMinus { value, source } => {
            writeln!(out, "{p}UnaryMinus({}) [#{}]", atom_str(value), source.0).unwrap()
        }
        MExpr::BitString { segments, source } => writeln!(
            out,
            "{p}BitString([{}]) [#{}]",
            segments.iter().map(seg_str).collect::<Vec<_>>().join(", "),
            source.0
        )
        .unwrap(),
        MExpr::Receive {
            arms,
            after,
            source,
        } => {
            writeln!(out, "{p}receive [#{}] of", source.0).unwrap();
            for arm in arms {
                write_arm(out, indent + 2, arm);
            }
            if let Some((timeout, body)) = after {
                writeln!(out, "{p}after {} ->", atom_str(timeout)).unwrap();
                write_expr(out, indent + 2, body);
            }
        }
    }
}

/// Single-line compact rendering. Used for the right-hand side of a `bind` /
/// `let` line when the value is leaf-shaped, and for Lambda bodies inside
/// atoms. Control-flow variants (`Case` / `If` / `With` / `Receive`) collapse
/// to `<Variant [#id]>` placeholders here — those should be reached via
/// `write_expr` instead, since `should_inline_value` rejects them.
fn expr_compact(e: &MExpr) -> String {
    match e {
        MExpr::Pure(a) => format!("Pure({})", atom_str(a)),
        MExpr::Bind { var, value, body } => format!(
            "bind {} <- {}; {}",
            mvar_str(var),
            expr_compact(value),
            expr_compact(body)
        ),
        MExpr::Let { var, value, body } => format!(
            "let {} <- {}; {}",
            mvar_str(var),
            expr_compact(value),
            expr_compact(body)
        ),
        MExpr::Yield { op, args, source } => format!(
            "Yield({}, [{}]) [#{}]",
            op_str(op),
            atoms_str(args),
            source.0
        ),
        MExpr::App { head, args, source } => format!(
            "App({}, [{}]) [#{}]",
            atom_str(head),
            atoms_str(args),
            source.0
        ),
        MExpr::Case { source, .. } => format!("<Case [#{}]>", source.0),
        MExpr::If { source, .. } => format!("<If [#{}]>", source.0),
        MExpr::With { source, .. } => format!("<With [#{}]>", source.0),
        MExpr::Resume { value, source } => {
            format!("Resume({}) [#{}]", atom_str(value), source.0)
        }
        MExpr::FieldAccess {
            record,
            field,
            record_name,
            source,
        } => {
            let rn = record_name
                .as_deref()
                .map(|n| format!("{n}."))
                .unwrap_or_default();
            format!(
                "FieldAccess({}, {}{}) [#{}]",
                atom_str(record),
                rn,
                field,
                source.0
            )
        }
        MExpr::RecordUpdate {
            record,
            fields,
            record_name,
            source,
        } => {
            let rn = record_name
                .as_deref()
                .map(|n| format!("{n} "))
                .unwrap_or_default();
            format!(
                "RecordUpdate({}{}, {{{}}}) [#{}]",
                rn,
                atom_str(record),
                fields_str(fields),
                source.0
            )
        }
        MExpr::DictMethodAccess {
            dict,
            trait_name,
            method_index,
            source,
        } => format!(
            "DictMethodAccess({}, {}[{}]) [#{}]",
            atom_str(dict),
            trait_name,
            method_index,
            source.0
        ),
        MExpr::ForeignCall {
            module,
            func,
            args,
            source,
        } => format!(
            "ForeignCall({}:{}, [{}]) [#{}]",
            module,
            func,
            atoms_str(args),
            source.0
        ),
        MExpr::BinOp {
            op,
            left,
            right,
            source,
        } => format!(
            "BinOp({}, {}, {}) [#{}]",
            binop_sym(op),
            atom_str(left),
            atom_str(right),
            source.0
        ),
        MExpr::UnaryMinus { value, source } => {
            format!("UnaryMinus({}) [#{}]", atom_str(value), source.0)
        }
        MExpr::BitString { segments, source } => format!(
            "BitString([{}]) [#{}]",
            segments.iter().map(seg_str).collect::<Vec<_>>().join(", "),
            source.0
        ),
        MExpr::Receive { source, .. } => format!("<Receive [#{}]>", source.0),
    }
}

/// Whether an expression should appear on the right-hand side of `bind x <- _`
/// instead of being broken across lines. Control-flow nodes get a multi-line
/// rendering for readability.
fn should_inline_value(e: &MExpr) -> bool {
    matches!(
        e,
        MExpr::Pure(_)
            | MExpr::Yield { .. }
            | MExpr::App { .. }
            | MExpr::ForeignCall { .. }
            | MExpr::BinOp { .. }
            | MExpr::UnaryMinus { .. }
            | MExpr::Resume { .. }
            | MExpr::FieldAccess { .. }
            | MExpr::RecordUpdate { .. }
            | MExpr::DictMethodAccess { .. }
            | MExpr::BitString { .. }
    )
}

// -------------------------------------------------------------------------
// Atoms
// -------------------------------------------------------------------------

fn atom_str(a: &Atom) -> String {
    match a {
        Atom::Var { name, .. } => format!("Var({})", mvar_str(name)),
        Atom::Lit { value, .. } => format!("Lit({})", lit_str(value)),
        Atom::Ctor { name, args, .. } => {
            if args.is_empty() {
                format!("Ctor({})", name)
            } else {
                format!("Ctor({}, [{}])", name, atoms_str(args))
            }
        }
        Atom::Tuple { elements, .. } => format!("Tuple([{}])", atoms_str(elements)),
        Atom::AnonRecord { fields, .. } => {
            format!("AnonRecord({{{}}})", fields_str(fields))
        }
        Atom::Record { name, fields, .. } => {
            format!("Record({}, {{{}}})", name, fields_str(fields))
        }
        Atom::Lambda { params, body, .. } => {
            format!("Lambda([{}], {})", params_str(params), expr_compact(body))
        }
        Atom::DictRef { name, .. } => format!("DictRef({})", name),
        Atom::QualifiedRef { module, name, .. } => {
            format!("QualifiedRef({}.{})", module, name)
        }
        Atom::Symbol { symbol, .. } => format!("Symbol({})", symbol),
    }
}

fn atoms_str(args: &[Atom]) -> String {
    args.iter().map(atom_str).collect::<Vec<_>>().join(", ")
}

fn fields_str(fs: &[(String, Atom)]) -> String {
    fs.iter()
        .map(|(n, a)| format!("{}: {}", n, atom_str(a)))
        .collect::<Vec<_>>()
        .join(", ")
}

// -------------------------------------------------------------------------
// Handlers
// -------------------------------------------------------------------------

fn write_handler(out: &mut String, indent: usize, h: &MHandler) {
    let p = pad(indent);
    match h {
        MHandler::Static {
            effects,
            arms,
            return_clause,
            source,
        } => {
            writeln!(
                out,
                "{p}with handler<Static>(effects=[{}]) [#{}] {{",
                effects.join(", "),
                source.0
            )
            .unwrap();
            for arm in arms {
                write_handler_arm(out, indent + 2, arm, false);
            }
            if let Some(ret) = return_clause {
                write_handler_arm(out, indent + 2, ret, true);
            }
            writeln!(out, "{p}}} in").unwrap();
        }
        MHandler::Dynamic {
            effects,
            op_tuple,
            return_lambda,
            source,
        } => {
            writeln!(
                out,
                "{p}with handler<Dynamic>(effects=[{}], op_tuple={}) [#{}] {{",
                effects.join(", "),
                atom_str(op_tuple),
                source.0
            )
            .unwrap();
            match return_lambda {
                Some(a) => {
                    writeln!(out, "{p}  return = Some({})", atom_str(a)).unwrap();
                }
                None => {
                    writeln!(out, "{p}  return = None").unwrap();
                }
            }
            writeln!(out, "{p}}} in").unwrap();
        }
    }
}

fn write_handler_arm(out: &mut String, indent: usize, arm: &MHandlerArm, is_return: bool) {
    let p = pad(indent);
    let params = params_str(&arm.params);
    let header = if is_return {
        format!("return({}) [#{}]:", params, arm.id.0)
    } else {
        format!(
            "arm {}/{}@{}({}) [#{}]:",
            arm.op.effect, arm.op.op, arm.op.op_index, params, arm.id.0
        )
    };
    writeln!(out, "{p}{header}").unwrap();
    write_expr(out, indent + 2, &arm.body);
    if let Some(fb) = &arm.finally_block {
        writeln!(out, "{p}finally:").unwrap();
        write_expr(out, indent + 2, fb);
    }
}

// -------------------------------------------------------------------------
// Case / Receive arms
// -------------------------------------------------------------------------

fn write_arm(out: &mut String, indent: usize, arm: &MArm) {
    let p = pad(indent);
    let guard = match &arm.guard {
        Some(g) => format!(" when {}", expr_compact(g)),
        None => String::new(),
    };
    writeln!(out, "{p}| {}{} ->", pat_str(&arm.pattern), guard).unwrap();
    write_expr(out, indent + 2, &arm.body);
}

fn seg_str(s: &MBitSegment) -> String {
    let size = s
        .size
        .as_ref()
        .map(|a| format!(":{}", atom_str(a)))
        .unwrap_or_default();
    let specs = if s.specs.is_empty() {
        String::new()
    } else {
        format!(
            "/{}",
            s.specs
                .iter()
                .map(|sp| format!("{:?}", sp))
                .collect::<Vec<_>>()
                .join("-")
        )
    };
    format!("{}{}{}", atom_str(&s.value), size, specs)
}

// -------------------------------------------------------------------------
// Leaf helpers
// -------------------------------------------------------------------------

fn pad(indent: usize) -> String {
    " ".repeat(indent)
}

fn trim_trailing_newlines(s: &mut String) {
    while s.ends_with('\n') {
        s.pop();
    }
}

fn mvar_str(v: &MVar) -> String {
    if v.id == 0 {
        v.name.clone()
    } else {
        format!("{}#{}", v.name, v.id)
    }
}

fn op_str(op: &EffectOpRef) -> String {
    format!("{}/{}@{}", op.effect, op.op, op.op_index)
}

fn lit_str(l: &Lit) -> String {
    match l {
        Lit::Int(s, _) => s.clone(),
        Lit::Float(s, _) => s.clone(),
        Lit::String(s, _) => format!("\"{}\"", s),
        Lit::Bool(b) => b.to_string(),
        Lit::Unit => "()".to_string(),
    }
}

fn binop_sym(b: &BinOp) -> &'static str {
    match b {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::FloatDiv => "/.",
        BinOp::IntDiv => "/",
        BinOp::Mod => "%",
        BinOp::FloatMod => "%.",
        BinOp::Eq => "==",
        BinOp::NotEq => "!=",
        BinOp::Lt => "<",
        BinOp::Gt => ">",
        BinOp::LtEq => "<=",
        BinOp::GtEq => ">=",
        BinOp::And => "&&",
        BinOp::Or => "||",
        BinOp::Concat => "<>",
    }
}

fn params_str(ps: &[Pat]) -> String {
    ps.iter().map(pat_str).collect::<Vec<_>>().join(", ")
}

fn pat_str(p: &Pat) -> String {
    match p {
        Pat::Wildcard { .. } => "_".to_string(),
        Pat::Var { name, .. } => name.clone(),
        Pat::Lit { value, .. } => lit_str(value),
        Pat::Constructor { name, args, .. } => {
            if args.is_empty() {
                name.clone()
            } else {
                format!(
                    "{}({})",
                    name,
                    args.iter().map(pat_str).collect::<Vec<_>>().join(", ")
                )
            }
        }
        Pat::Record {
            name,
            fields,
            as_name,
            rest,
            ..
        } => {
            let mut parts: Vec<String> = fields
                .iter()
                .map(|(n, p)| match p {
                    Some(p) => format!("{}: {}", n, pat_str(p)),
                    None => n.clone(),
                })
                .collect();
            if *rest {
                parts.push("..".to_string());
            }
            let body = format!("{} {{{}}}", name, parts.join(", "));
            match as_name {
                Some(a) => format!("{} as {}", body, a),
                None => body,
            }
        }
        Pat::AnonRecord { fields, rest, .. } => {
            let mut parts: Vec<String> = fields
                .iter()
                .map(|(n, p)| match p {
                    Some(p) => format!("{}: {}", n, pat_str(p)),
                    None => n.clone(),
                })
                .collect();
            if *rest {
                parts.push("..".to_string());
            }
            format!("{{{}}}", parts.join(", "))
        }
        Pat::Tuple { elements, .. } => {
            format!(
                "({})",
                elements.iter().map(pat_str).collect::<Vec<_>>().join(", ")
            )
        }
        Pat::StringPrefix { prefix, rest, .. } => {
            format!("\"{}\" <> {}", prefix, pat_str(rest))
        }
        Pat::BitStringPat { segments, .. } => format!("<<{} segs>>", segments.len()),
        Pat::ListPat { elements, .. } => format!(
            "[{}]",
            elements.iter().map(pat_str).collect::<Vec<_>>().join(", ")
        ),
        Pat::ConsPat { head, tail, .. } => format!("{} :: {}", pat_str(head), pat_str(tail)),
        Pat::Or { patterns, .. } => patterns.iter().map(pat_str).collect::<Vec<_>>().join(" | "),
    }
}

// -------------------------------------------------------------------------
// Tests
// -------------------------------------------------------------------------

#[cfg(test)]
mod tests;
