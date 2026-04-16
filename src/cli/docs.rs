use std::fmt::Write;
use std::fs;
use std::path::Path;

use saga::ast::*;
use saga::lexer::Lexer;
use saga::parser::Parser;
use saga::typechecker::BUILTIN_MODULES;

/// Generate markdown documentation for all stdlib modules.
pub fn generate_docs(output_dir: &Path) {
    fs::create_dir_all(output_dir).unwrap_or_else(|e| {
        eprintln!("Error creating output directory: {}", e);
        std::process::exit(1);
    });

    let mut modules_generated = 0;

    for &(module_name, source) in BUILTIN_MODULES {
        let tokens = match Lexer::new(source).lex() {
            Ok(t) => t,
            Err(e) => {
                eprintln!("Lex error in {}: {:?}", module_name, e);
                continue;
            }
        };

        let program = match Parser::new(tokens).parse_program() {
            Ok(p) => p,
            Err(e) => {
                eprintln!("Parse error in {}: {}", module_name, e.message);
                continue;
            }
        };

        let mdx = render_module(module_name, &program);
        let filename = format!("{}.md", module_name);
        let out_path = output_dir.join(&filename);
        fs::write(&out_path, &mdx).unwrap_or_else(|e| {
            eprintln!("Error writing {}: {}", out_path.display(), e);
            std::process::exit(1);
        });
        modules_generated += 1;
    }

    eprintln!(
        "  {} Generated docs for {} modules in {}",
        super::color::green("Done."),
        modules_generated,
        output_dir.display()
    );
}

fn render_module(module_name: &str, decls: &[Decl]) -> String {
    let mut out = String::new();

    // Frontmatter
    writeln!(out, "---").unwrap();
    writeln!(out, "title: {}", module_name).unwrap();
    writeln!(out, "---").unwrap();
    writeln!(out).unwrap();

    // Module-level doc from the ModuleDecl
    for decl in decls {
        if let Decl::ModuleDecl { doc, .. } = decl {
            if !doc.is_empty() {
                render_doc(&mut out, doc);
            }
            break;
        }
    }

    // Collect all pub declarations grouped by kind
    let mut types = Vec::new();
    let mut functions = Vec::new();
    let mut effects = Vec::new();
    let mut handlers = Vec::new();
    let mut traits = Vec::new();
    let mut vals = Vec::new();

    // Build a map of fun signatures so we can pair them with bindings
    let signatures: std::collections::HashMap<&str, &Decl> = decls
        .iter()
        .filter_map(|d| match d {
            Decl::FunSignature { name, public, .. } if *public => Some((name.as_str(), d)),
            _ => None,
        })
        .collect();

    for decl in decls {
        match decl {
            Decl::TypeDef { public: true, .. } => types.push(decl),
            Decl::RecordDef { public: true, .. } => types.push(decl),
            Decl::FunSignature { public: true, .. } => functions.push(decl),
            Decl::EffectDef { public: true, .. } => effects.push(decl),
            Decl::HandlerDef { public: true, .. } => handlers.push(decl),
            Decl::TraitDef { public: true, .. } => traits.push(decl),
            Decl::Val { public: true, .. } => vals.push(decl),
            // Pub functions without a separate signature (just binding)
            // are uncommon in stdlib, skip for now
            _ => {}
        }
    }

    // Types
    if !types.is_empty() {
        writeln!(out, "## Types\n").unwrap();
        for decl in &types {
            render_type_decl(&mut out, decl);
        }
    }

    // Traits
    if !traits.is_empty() {
        writeln!(out, "## Traits\n").unwrap();
        for decl in &traits {
            render_trait_decl(&mut out, decl);
        }
    }

    // Effects
    if !effects.is_empty() {
        writeln!(out, "## Effects\n").unwrap();
        for decl in &effects {
            render_effect_decl(&mut out, decl);
        }
    }

    // Handlers
    if !handlers.is_empty() {
        writeln!(out, "## Handlers\n").unwrap();
        for decl in &handlers {
            render_handler_decl(&mut out, decl);
        }
    }

    // Values
    if !vals.is_empty() {
        writeln!(out, "## Values\n").unwrap();
        for decl in &vals {
            render_val_decl(&mut out, decl);
        }
    }

    // Functions
    if !functions.is_empty() {
        writeln!(out, "## Functions\n").unwrap();
        for decl in &functions {
            render_fun_signature(&mut out, decl);
        }
    }

    // Suppress unused variable warning
    let _ = signatures;

    out
}

fn render_doc(out: &mut String, doc: &[String]) {
    if doc.is_empty() {
        return;
    }
    for line in doc {
        writeln!(out, "{}", line.trim()).unwrap();
    }
    writeln!(out).unwrap();
}

fn render_fun_signature(out: &mut String, decl: &Decl) {
    let Decl::FunSignature {
        name,
        doc,
        params,
        return_type,
        effects,
        effect_row_var,
        where_clause,
        ..
    } = decl
    else {
        return;
    };

    writeln!(out, "### {}\n", name).unwrap();
    writeln!(out, "```saga").unwrap();
    write!(out, "fun {} : ", name).unwrap();

    // Render parameter types -> return type
    for (label, ty) in params {
        if label.is_empty() || label.starts_with('_') {
            write!(out, "{} -> ", format_type_expr(ty)).unwrap();
        } else {
            write!(out, "({}: {}) -> ", label, format_type_expr(ty)).unwrap();
        }
    }
    write!(out, "{}", format_type_expr(return_type)).unwrap();

    // Effects
    if !effects.is_empty() {
        let effs: Vec<String> = effects.iter().map(format_effect_ref).collect();
        let mut needs = effs.join(", ");
        if let Some((var, _)) = effect_row_var {
            needs.push_str(&format!(", ..{}", var));
        }
        write!(out, " needs {{{}}}", needs).unwrap();
    }

    // Where clause
    if !where_clause.is_empty() {
        let bounds: Vec<String> = where_clause.iter().map(format_trait_bound).collect();
        write!(out, " where {{{}}}", bounds.join(", ")).unwrap();
    }

    writeln!(out).unwrap();
    writeln!(out, "```\n").unwrap();

    render_doc(out, doc);
}

fn render_type_decl(out: &mut String, decl: &Decl) {
    match decl {
        Decl::TypeDef {
            name,
            doc,
            type_params,
            variants,
            opaque,
            ..
        } => {
            writeln!(out, "### {}\n", name).unwrap();
            writeln!(out, "```saga").unwrap();
            if *opaque {
                write!(out, "opaque type {}", name).unwrap();
            } else {
                write!(out, "type {}", name).unwrap();
            }
            for p in type_params {
                write!(out, " {}", p).unwrap();
            }
            if !*opaque && !variants.is_empty() {
                writeln!(out, " =").unwrap();
                for (i, v) in variants.iter().enumerate() {
                    write!(out, "  | {}", v.node.name).unwrap();
                    for (label, ty) in &v.node.fields {
                        if let Some(l) = label {
                            write!(out, " ({}: {})", l, format_type_expr(ty)).unwrap();
                        } else {
                            write!(out, " {}", format_type_expr_atom(ty)).unwrap();
                        }
                    }
                    if i < variants.len() - 1 {
                        writeln!(out).unwrap();
                    }
                }
            }
            writeln!(out).unwrap();
            writeln!(out, "```\n").unwrap();
            render_doc(out, doc);
        }
        Decl::RecordDef {
            name,
            doc,
            type_params,
            fields,
            ..
        } => {
            writeln!(out, "### {}\n", name).unwrap();
            writeln!(out, "```saga").unwrap();
            write!(out, "record {}", name).unwrap();
            for p in type_params {
                write!(out, " {}", p).unwrap();
            }
            writeln!(out, " {{").unwrap();
            for (i, f) in fields.iter().enumerate() {
                let (fname, ftype) = &f.node;
                write!(out, "  {}: {}", fname, format_type_expr(ftype)).unwrap();
                if i < fields.len() - 1 {
                    writeln!(out, ",").unwrap();
                } else {
                    writeln!(out).unwrap();
                }
            }
            writeln!(out, "}}").unwrap();
            writeln!(out, "```\n").unwrap();
            render_doc(out, doc);
        }
        _ => {}
    }
}

fn render_effect_decl(out: &mut String, decl: &Decl) {
    let Decl::EffectDef {
        name,
        doc,
        type_params,
        operations,
        ..
    } = decl
    else {
        return;
    };

    writeln!(out, "### {}\n", name).unwrap();
    writeln!(out, "```saga").unwrap();
    write!(out, "effect {}", name).unwrap();
    for p in type_params {
        write!(out, " {}", p).unwrap();
    }
    writeln!(out, " {{").unwrap();
    for op in operations {
        write!(out, "  fun {} : ", op.node.name).unwrap();
        for (label, ty) in &op.node.params {
            if label.is_empty() || label.starts_with('_') {
                write!(out, "{} -> ", format_type_expr(ty)).unwrap();
            } else {
                write!(out, "({}: {}) -> ", label, format_type_expr(ty)).unwrap();
            }
        }
        write!(out, "{}", format_type_expr(&op.node.return_type)).unwrap();
        if !op.node.effects.is_empty() {
            let effs: Vec<String> = op.node.effects.iter().map(format_effect_ref).collect();
            let mut needs = effs.join(", ");
            if let Some((var, _)) = &op.node.effect_row_var {
                needs.push_str(&format!(", ..{}", var));
            }
            write!(out, " needs {{{}}}", needs).unwrap();
        }
        writeln!(out).unwrap();
    }
    writeln!(out, "}}").unwrap();
    writeln!(out, "```\n").unwrap();
    render_doc(out, doc);

    // Render individual operation docs if they have any
    for op in operations {
        if !op.node.doc.is_empty() {
            writeln!(
                out,
                "**{}**: {}",
                op.node.name,
                op.node.doc.join(" ").trim()
            )
            .unwrap();
            writeln!(out).unwrap();
        }
    }
}

fn render_handler_decl(out: &mut String, decl: &Decl) {
    let Decl::HandlerDef {
        name, doc, body, ..
    } = decl
    else {
        return;
    };

    writeln!(out, "### {}\n", name).unwrap();
    writeln!(out, "```saga").unwrap();
    write!(out, "handler {}", name).unwrap();
    if !body.effects.is_empty() {
        let effs: Vec<String> = body
            .effects
            .iter()
            .map(|e| {
                let mut s = e.name.clone();
                for arg in &e.type_args {
                    s.push(' ');
                    s.push_str(&format_type_expr(arg));
                }
                s
            })
            .collect();
        write!(out, " for {}", effs.join(", ")).unwrap();
    }
    if !body.needs.is_empty() {
        let needs: Vec<String> = body.needs.iter().map(format_effect_ref).collect();
        write!(out, " needs {{{}}}", needs.join(", ")).unwrap();
    }
    writeln!(out).unwrap();
    writeln!(out, "```\n").unwrap();
    render_doc(out, doc);
}

fn render_trait_decl(out: &mut String, decl: &Decl) {
    let Decl::TraitDef {
        name,
        doc,
        type_params,
        supertraits,
        methods,
        ..
    } = decl
    else {
        return;
    };

    writeln!(out, "### {}\n", name).unwrap();
    writeln!(out, "```saga").unwrap();
    write!(out, "trait {}", name).unwrap();
    for p in type_params {
        write!(out, " {}", p).unwrap();
    }
    if !supertraits.is_empty() {
        let supers: Vec<String> = supertraits
            .iter()
            .map(|s| {
                if s.type_args.is_empty() {
                    s.name.clone()
                } else {
                    let args: Vec<String> = s.type_args.iter().map(format_type_expr).collect();
                    format!("{} {}", s.name, args.join(" "))
                }
            })
            .collect();
        write!(out, " : {}", supers.join(" + ")).unwrap();
    }
    writeln!(out, " {{").unwrap();
    for m in methods {
        write!(out, "  fun {} : ", m.node.name).unwrap();
        for (label, ty) in &m.node.params {
            if label.is_empty() || label.starts_with('_') {
                write!(out, "{} -> ", format_type_expr(ty)).unwrap();
            } else {
                write!(out, "({}: {}) -> ", label, format_type_expr(ty)).unwrap();
            }
        }
        writeln!(out, "{}", format_type_expr(&m.node.return_type)).unwrap();
    }
    writeln!(out, "}}").unwrap();
    writeln!(out, "```\n").unwrap();
    render_doc(out, doc);

    // Render individual method docs
    for m in methods {
        if !m.node.doc.is_empty() {
            writeln!(out, "**{}**: {}", m.node.name, m.node.doc.join(" ").trim()).unwrap();
            writeln!(out).unwrap();
        }
    }
}

fn render_val_decl(out: &mut String, decl: &Decl) {
    let Decl::Val { name, doc, .. } = decl else {
        return;
    };

    writeln!(out, "### {}\n", name).unwrap();
    writeln!(out, "```saga").unwrap();
    writeln!(out, "val {}", name).unwrap();
    writeln!(out, "```\n").unwrap();
    render_doc(out, doc);
}

// --- Type expression formatting (string output, mirroring LSP's type_display) ---

fn format_type_expr(ty: &TypeExpr) -> String {
    // Check for tuple sugar first
    if let Some(args) = collect_tuple_args(ty) {
        let inner: Vec<String> = args.iter().map(|a| format_type_expr(a)).collect();
        return format!("({})", inner.join(", "));
    }

    match ty {
        TypeExpr::Named { name, .. } => name.clone(),
        TypeExpr::Var { name, .. } => name.clone(),
        TypeExpr::App { func, arg, .. } => {
            format!("{} {}", format_type_expr(func), format_type_expr_atom(arg))
        }
        TypeExpr::Arrow {
            from,
            to,
            effects,
            effect_row_var,
            ..
        } => {
            let arrow = format!("{} -> {}", format_type_expr(from), format_type_expr(to));
            if effects.is_empty() {
                arrow
            } else {
                let effs: Vec<String> = effects.iter().map(format_effect_ref).collect();
                let mut needs = effs.join(", ");
                if let Some((var, _)) = effect_row_var {
                    needs.push_str(&format!(", ..{}", var));
                }
                format!("{} needs {{{}}}", arrow, needs)
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

/// Format a type in "atom" position: wrap App and Arrow in parens.
fn format_type_expr_atom(ty: &TypeExpr) -> String {
    if collect_tuple_args(ty).is_some() {
        return format_type_expr(ty);
    }
    match ty {
        TypeExpr::App { .. } | TypeExpr::Arrow { .. } => format!("({})", format_type_expr(ty)),
        _ => format_type_expr(ty),
    }
}

fn format_effect_ref(e: &EffectRef) -> String {
    if e.type_args.is_empty() {
        e.name.clone()
    } else {
        let args: Vec<String> = e.type_args.iter().map(format_type_expr).collect();
        format!("{} {}", e.name, args.join(" "))
    }
}

fn format_trait_bound(b: &TraitBound) -> String {
    let traits: Vec<String> = b
        .traits
        .iter()
        .map(|t| {
            if t.type_args.is_empty() {
                t.name.clone()
            } else {
                let args: Vec<String> = t.type_args.iter().map(format_type_expr).collect();
                format!("{} {}", t.name, args.join(" "))
            }
        })
        .collect();
    format!("{}: {}", b.type_var, traits.join(" + "))
}

/// Collect tuple type arguments: Tuple applied to N args -> Some(args)
fn collect_tuple_args(ty: &TypeExpr) -> Option<Vec<&TypeExpr>> {
    // Walk left spine of App nodes to find Tuple at root
    let mut args = Vec::new();
    let mut current = ty;
    loop {
        match current {
            TypeExpr::App { func, arg, .. } => {
                args.push(arg.as_ref());
                current = func.as_ref();
            }
            TypeExpr::Named { name, .. } if name == "Tuple" => {
                if args.is_empty() {
                    return None;
                }
                args.reverse();
                return Some(args);
            }
            _ => return None,
        }
    }
}
