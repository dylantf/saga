use std::fmt::Write;
use std::fs;
use std::path::{Path, PathBuf};

use saga::ast::*;
use saga::lexer::Lexer;
use saga::parser::Parser;

/// One module to be rendered: declared module name and the path of the source file.
pub struct DocModule {
    pub name: String,
    pub path: PathBuf,
}

/// Generate markdown documentation for the given modules.
///
/// Writes one `<ModuleName>.md` per module under `output_dir`, plus an `index.md`
/// linking them with one-line summaries pulled from each module's doc comment.
pub fn generate_docs(modules: &[DocModule], output_dir: &Path) {
    fs::create_dir_all(output_dir).unwrap_or_else(|e| {
        eprintln!("Error creating output directory: {}", e);
        std::process::exit(1);
    });

    let mut summaries: Vec<(String, Option<String>)> = Vec::new();

    for module in modules {
        let source = match fs::read_to_string(&module.path) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("Error reading {}: {}", module.path.display(), e);
                continue;
            }
        };

        let tokens = match Lexer::new(&source).lex() {
            Ok(t) => t,
            Err(e) => {
                eprintln!("Lex error in {}: {:?}", module.name, e);
                continue;
            }
        };

        let program = match Parser::new(tokens).parse_program() {
            Ok(p) => p,
            Err(e) => {
                eprintln!("Parse error in {}: {}", module.name, e.message);
                continue;
            }
        };

        let mdx = render_module(&module.name, &program);
        let out_path = output_dir.join(format!("{}.md", module.name));
        fs::write(&out_path, &mdx).unwrap_or_else(|e| {
            eprintln!("Error writing {}: {}", out_path.display(), e);
            std::process::exit(1);
        });

        summaries.push((module.name.clone(), module_summary(&program)));
    }

    summaries.sort_by(|a, b| a.0.cmp(&b.0));
    let index = render_index(&summaries);
    let index_path = output_dir.join("index.md");
    fs::write(&index_path, &index).unwrap_or_else(|e| {
        eprintln!("Error writing {}: {}", index_path.display(), e);
        std::process::exit(1);
    });

    eprintln!(
        "  {} Generated docs for {} modules in {}",
        super::color::green("Done."),
        summaries.len(),
        output_dir.display()
    );
}

fn module_summary(decls: &[Decl]) -> Option<String> {
    for decl in decls {
        if let Decl::ModuleDecl { doc, .. } = decl {
            let line = doc.iter().find(|l| !l.trim().is_empty())?;
            return Some(line.trim().to_string());
        }
    }
    None
}

fn render_index(summaries: &[(String, Option<String>)]) -> String {
    let mut out = String::new();
    writeln!(out, "---").unwrap();
    writeln!(out, "title: Modules").unwrap();
    writeln!(out, "---").unwrap();
    writeln!(out).unwrap();
    writeln!(out, "# Modules\n").unwrap();
    for (name, summary) in summaries {
        match summary {
            Some(s) => writeln!(out, "- [{0}]({0}.md) — {1}", name, s).unwrap(),
            None => writeln!(out, "- [{0}]({0}.md)", name).unwrap(),
        }
    }
    out
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

    for decl in decls {
        match decl {
            Decl::TypeDef { public: true, .. } => types.push(decl),
            Decl::TypeAlias { public: true, .. } => types.push(decl),
            Decl::RecordDef { public: true, .. } => types.push(decl),
            Decl::FunSignature { public: true, .. } => functions.push(decl),
            Decl::EffectDef { public: true, .. } => effects.push(decl),
            Decl::HandlerDef { public: true, .. } => handlers.push(decl),
            Decl::TraitDef { public: true, .. } => traits.push(decl),
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

    // Functions
    if !functions.is_empty() {
        writeln!(out, "## Functions\n").unwrap();
        for decl in &functions {
            render_fun_signature(&mut out, decl);
        }
    }

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
    write_needs_row(out, effects, effect_row_var);

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
            deriving,
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
            write_deriving(out, deriving);
            writeln!(out, "```\n").unwrap();
            render_doc(out, doc);
        }
        Decl::TypeAlias {
            name,
            doc,
            type_params,
            body,
            ..
        } => {
            writeln!(out, "### {}\n", name).unwrap();
            writeln!(out, "```saga").unwrap();
            write!(out, "type alias {}", name).unwrap();
            for p in type_params {
                write!(out, " {}", p).unwrap();
            }
            writeln!(out, " = {}", format_type_expr(body)).unwrap();
            writeln!(out, "```\n").unwrap();
            render_doc(out, doc);
        }
        Decl::RecordDef {
            name,
            doc,
            type_params,
            fields,
            deriving,
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
            write_deriving(out, deriving);
            writeln!(out, "```\n").unwrap();
            render_doc(out, doc);
        }
        _ => {}
    }
}

/// Render a ` deriving (...)` line when the type derives any traits.
fn write_deriving(out: &mut String, deriving: &[String]) {
    if deriving.is_empty() {
        return;
    }
    writeln!(out, "  deriving ({})", deriving.join(", ")).unwrap();
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
        write_needs_row(out, &op.node.effects, &op.node.effect_row_var);
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
        write!(out, "{}", format_type_expr(&m.node.return_type)).unwrap();
        write_needs_row(out, &m.node.effects, &m.node.effect_row_var);
        writeln!(out).unwrap();
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
        TypeExpr::Symbol { name, .. } => format!("'{}", name),
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
            if effects.is_empty() && effect_row_var.is_empty() {
                arrow
            } else {
                let mut parts: Vec<String> = effects.iter().map(format_effect_ref).collect();
                for (var, _) in effect_row_var {
                    parts.push(format!("..{}", var));
                }
                format!("{} needs {{{}}}", arrow, parts.join(", "))
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

/// Render a trailing ` needs {...}` row from named effects plus open row
/// variables, or nothing when both are empty. Shared by function signatures,
/// effect operations, and trait methods.
fn write_needs_row<S>(out: &mut String, effects: &[EffectRef], effect_row_var: &[(String, S)]) {
    if effects.is_empty() && effect_row_var.is_empty() {
        return;
    }
    let mut parts: Vec<String> = effects.iter().map(format_effect_ref).collect();
    for (var, _) in effect_row_var {
        parts.push(format!("..{}", var));
    }
    write!(out, " needs {{{}}}", parts.join(", ")).unwrap();
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
