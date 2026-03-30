// Core Erlang IR types and pretty-printer.

// --- IR types ---

pub struct CModule {
    pub name: String,
    pub exports: Vec<(String, usize)>, // (fun_name, arity)
    pub funs: Vec<CFunDef>,
}

pub struct CFunDef {
    pub name: String,
    pub arity: usize,
    pub body: CExpr, // always a Fun at the top level
}

#[derive(Debug, Clone)]
pub enum CExpr {
    Lit(CLit),
    Var(String),
    /// `fun (Params) -> Body`
    Fun(Vec<String>, Box<CExpr>),
    /// `let <Var> = Val in Body`
    Let(String, Box<CExpr>, Box<CExpr>),
    /// `apply Func(Args)` -- local/closure call
    Apply(Box<CExpr>, Vec<CExpr>),
    /// `call 'Mod':'Fun'(Args)` -- inter-module call
    Call(String, String, Vec<CExpr>),
    /// `case Scrutinee of Arms end`
    Case(Box<CExpr>, Vec<CArm>),
    /// `{Elems}` -- tuple
    Tuple(Vec<CExpr>),
    /// `[Head|Tail]`
    Cons(Box<CExpr>, Box<CExpr>),
    /// `[]`
    Nil,
    /// `fun 'name'/arity` -- reference to a module-local function by name
    FunRef(String, usize),
    /// `<E1, E2, ...>` -- Core Erlang values expression (multi-value scrutinee)
    Values(Vec<CExpr>),
    /// `letrec 'name'/arity = fun(...) -> ... in Body`
    LetRec(Vec<(String, usize, CExpr)>, Box<CExpr>),
    /// `receive <Arms> after <Timeout> -> <TimeoutBody>`
    Receive(Vec<CArm>, Box<CExpr>, Box<CExpr>),
    /// `try Expr of OkVar -> OkBody catch <Class, Reason, Trace> -> CatchBody`
    Try {
        expr: Box<CExpr>,
        ok_var: String,
        ok_body: Box<CExpr>,
        catch_vars: (String, String, String), // (class, reason, trace)
        catch_body: Box<CExpr>,
    },
    /// `#{seg1,seg2,...}#` -- binary construction
    Binary(Vec<CBinSeg<CExpr>>),
}

#[derive(Debug, Clone)]
pub struct CArm {
    pub pat: CPat,
    pub guard: Option<CExpr>, // None = always match ('true' guard omitted)
    pub body: CExpr,
}

#[derive(Debug, Clone)]
pub enum CPat {
    Var(String),
    Lit(CLit),
    Wildcard,
    Tuple(Vec<CPat>),
    Cons(Box<CPat>, Box<CPat>),
    Nil,
    /// `Pat = Var` -- alias pattern
    Alias(String, Box<CPat>),
    /// `<P1, P2, ...>` -- Core Erlang value pattern (multi-arg case arm)
    Values(Vec<CPat>),
    /// `#{seg1,seg2,...}#` -- binary pattern
    Binary(Vec<CBinSeg<CPat>>),
}

#[derive(Debug, Clone)]
pub enum CLit {
    Int(i64),
    Float(f64),
    Atom(String),
    Str(String),
}

/// A single segment in a binary expression or pattern.
#[derive(Debug, Clone)]
pub enum CBinSeg<T> {
    /// A literal byte: `#<N>(8,1,'integer',['unsigned'|['big']])`
    Byte(u8),
    /// A variable-length binary splice: `#<T>('all',8,'binary',['unsigned'|['big']])`
    BinaryAll(T),
}

impl CExpr {
    /// Collect all `Var` references whose name starts with `_Handle_` into `out`.
    pub fn collect_handle_refs(&self, out: &mut std::collections::HashSet<String>) {
        match self {
            CExpr::Var(v) if v.starts_with("_Handle_") => {
                out.insert(v.clone());
            }
            CExpr::Var(_) | CExpr::Lit(_) | CExpr::Nil | CExpr::FunRef(_, _) => {}
            CExpr::Fun(_, body) => body.collect_handle_refs(out),
            CExpr::Let(_, val, body) => {
                val.collect_handle_refs(out);
                body.collect_handle_refs(out);
            }
            CExpr::Apply(func, args) => {
                func.collect_handle_refs(out);
                for a in args {
                    a.collect_handle_refs(out);
                }
            }
            CExpr::Call(_, _, args) => {
                for a in args {
                    a.collect_handle_refs(out);
                }
            }
            CExpr::Case(scrut, arms) => {
                scrut.collect_handle_refs(out);
                for arm in arms {
                    if let Some(g) = &arm.guard {
                        g.collect_handle_refs(out);
                    }
                    arm.body.collect_handle_refs(out);
                }
            }
            CExpr::Tuple(elems) | CExpr::Values(elems) => {
                for e in elems {
                    e.collect_handle_refs(out);
                }
            }
            CExpr::Cons(h, t) => {
                h.collect_handle_refs(out);
                t.collect_handle_refs(out);
            }
            CExpr::LetRec(defs, body) => {
                for (_, _, e) in defs {
                    e.collect_handle_refs(out);
                }
                body.collect_handle_refs(out);
            }
            CExpr::Receive(arms, timeout, timeout_body) => {
                for arm in arms {
                    if let Some(g) = &arm.guard {
                        g.collect_handle_refs(out);
                    }
                    arm.body.collect_handle_refs(out);
                }
                timeout.collect_handle_refs(out);
                timeout_body.collect_handle_refs(out);
            }
            CExpr::Try { expr, ok_body, catch_body, .. } => {
                expr.collect_handle_refs(out);
                ok_body.collect_handle_refs(out);
                catch_body.collect_handle_refs(out);
            }
            CExpr::Binary(segs) => {
                for seg in segs {
                    if let CBinSeg::BinaryAll(e) = seg {
                        e.collect_handle_refs(out);
                    }
                }
            }
        }
    }
}

// --- Printer ---

pub fn print_module(m: &CModule) -> String {
    let mut p = Printer::new();

    // Module header
    let exports: Vec<String> = m
        .exports
        .iter()
        .map(|(name, arity)| format!("'{}'/{}", name, arity))
        .collect();
    p.push(&format!("module '{}' [{}]", m.name, exports.join(", ")));
    p.newline();
    p.push("  attributes []");
    p.newline();

    for fun in &m.funs {
        p.newline();
        p.push(&format!("'{}'/{} =", fun.name, fun.arity));
        p.newline();
        p.with_indent(2, |p| p.print_expr(&fun.body));
        p.newline();
    }

    p.newline();
    p.push("end");
    p.newline();
    p.buf
}

struct Printer {
    buf: String,
    indent: usize,
    wildcard_counter: usize,
}

impl Printer {
    fn new() -> Self {
        Printer {
            buf: String::new(),
            indent: 0,
            wildcard_counter: 0,
        }
    }

    fn push(&mut self, s: &str) {
        self.buf.push_str(s);
    }

    fn newline(&mut self) {
        self.buf.push('\n');
        for _ in 0..self.indent {
            self.buf.push(' ');
        }
    }

    fn with_indent<F: FnOnce(&mut Self)>(&mut self, n: usize, f: F) {
        self.indent += n;
        f(self);
        self.indent -= n;
    }

    fn print_expr(&mut self, expr: &CExpr) {
        match expr {
            CExpr::Lit(lit) => self.print_lit(lit),

            CExpr::Var(v) => self.push(v),

            CExpr::Fun(params, body) => {
                self.push(&format!("fun ({}) ->", params.join(", ")));
                self.with_indent(2, |p| {
                    p.newline();
                    p.print_expr(body);
                });
            }

            // Let chains: print as a flat sequence rather than deeply nested
            CExpr::Let(var, val, body) => {
                self.push(&format!("let <{}> =", var));
                self.with_indent(2, |p| {
                    p.newline();
                    p.print_expr(val);
                });
                self.newline();
                self.push("in");
                self.newline();
                self.print_expr(body);
            }

            CExpr::LetRec(defs, body) => {
                self.push("letrec");
                self.with_indent(4, |p| {
                    for (name, arity, fun_body) in defs {
                        p.newline();
                        p.push(&format!("'{}'/{}  =", name, arity));
                        p.with_indent(2, |p| {
                            p.newline();
                            p.print_expr(fun_body);
                        });
                    }
                });
                self.newline();
                self.push("in");
                self.newline();
                self.print_expr(body);
            }

            CExpr::Apply(func, args) => {
                self.push("apply ");
                self.print_expr(func);
                self.push("(");
                self.print_expr_list(args);
                self.push(")");
            }

            CExpr::Call(module, func, args) => {
                self.push(&format!("call '{}':'{}'", module, func));
                self.newline();
                self.with_indent(2, |p| {
                    p.push("(");
                    p.print_expr_list(args);
                    p.push(")");
                });
            }

            CExpr::Case(scrutinee, arms) => {
                self.push("case ");
                self.print_expr(scrutinee);
                self.push(" of");
                for arm in arms {
                    self.with_indent(2, |p| {
                        p.newline();
                        p.push("<");
                        p.print_pat(&arm.pat);
                        p.push(">");
                        p.push(" when ");
                        match &arm.guard {
                            Some(guard) => p.print_expr(guard),
                            None => p.push("'true'"),
                        }
                        p.push(" ->");
                        p.with_indent(2, |p| {
                            p.newline();
                            p.print_expr(&arm.body);
                        });
                    });
                }
                self.newline();
                self.push("end");
            }

            CExpr::Tuple(elems) => {
                self.push("{");
                self.print_expr_list(elems);
                self.push("}");
            }

            CExpr::Cons(head, tail) => {
                self.push("[");
                self.print_expr(head);
                self.push("|");
                self.print_expr(tail);
                self.push("]");
            }

            CExpr::Nil => self.push("[]"),

            CExpr::FunRef(name, arity) => self.push(&format!("'{}'/{}", name, arity)),

            CExpr::Values(es) => {
                self.push("<");
                self.print_expr_list(es);
                self.push(">");
            }

            CExpr::Receive(arms, timeout, timeout_body) => {
                self.push("receive");
                for arm in arms {
                    self.with_indent(2, |p| {
                        p.newline();
                        p.push("<");
                        p.print_pat(&arm.pat);
                        p.push(">");
                        p.push(" when ");
                        match &arm.guard {
                            Some(guard) => p.print_expr(guard),
                            None => p.push("'true'"),
                        }
                        p.push(" ->");
                        p.with_indent(2, |p| {
                            p.newline();
                            p.print_expr(&arm.body);
                        });
                    });
                }
                self.newline();
                self.push("after");
                self.with_indent(2, |p| {
                    p.newline();
                    p.print_expr(timeout);
                    p.push(" ->");
                    p.with_indent(2, |p| {
                        p.newline();
                        p.print_expr(timeout_body);
                    });
                });
                self.newline();
            }

            CExpr::Try { expr, ok_var, ok_body, catch_vars: (class, reason, trace), catch_body } => {
                self.push("try");
                self.with_indent(2, |p| {
                    p.newline();
                    p.print_expr(expr);
                });
                self.newline();
                self.push(&format!("of <{}> ->", ok_var));
                self.with_indent(2, |p| {
                    p.newline();
                    p.print_expr(ok_body);
                });
                self.newline();
                self.push(&format!("catch <{}, {}, {}> ->", class, reason, trace));
                self.with_indent(2, |p| {
                    p.newline();
                    p.print_expr(catch_body);
                });
            }

            CExpr::Binary(segs) => self.print_binary_segs_expr(segs),
        }
    }

    fn print_expr_list(&mut self, exprs: &[CExpr]) {
        for (i, e) in exprs.iter().enumerate() {
            if i > 0 {
                self.push(", ");
            }
            self.print_expr(e);
        }
    }

    fn print_lit(&mut self, lit: &CLit) {
        match lit {
            CLit::Int(n) => self.push(&n.to_string()),
            CLit::Float(f) => {
                let s = f.to_string();
                // Core Erlang requires a decimal point to distinguish floats from integers
                if s.contains('.') {
                    self.push(&s);
                } else {
                    self.push(&format!("{}.0", s));
                }
            }
            CLit::Atom(a) => self.push(&format!("'{}'", a)),
            CLit::Str(s) => {
                if s.is_ascii() {
                    self.push(&format!("\"{}\"", escape_str(s)));
                } else {
                    // Non-ASCII codepoints can't reliably be represented in Core
                    // Erlang string literals (which are Latin-1). Emit as an
                    // explicit cons list of integer codepoints instead.
                    self.print_unicode_str(s);
                }
            }
        }
    }

    /// Emit a string as a nested cons list of integer codepoints:
    /// `[cp1|[cp2|...[cpN|[]]...]]`
    fn print_unicode_str(&mut self, s: &str) {
        let codepoints: Vec<u32> = s.chars().map(|c| c as u32).collect();
        for cp in &codepoints {
            self.push(&format!("[{}|", cp));
        }
        self.push("[]");
        for _ in &codepoints {
            self.push("]");
        }
    }

    fn print_bin_seg_byte(&mut self, b: u8) {
        self.push(&format!(
            "#<{}>(8,1,'integer',['unsigned'|['big']])",
            b
        ));
    }

    fn print_binary_segs_expr(&mut self, segs: &[CBinSeg<CExpr>]) {
        self.push("#{");
        for (i, seg) in segs.iter().enumerate() {
            if i > 0 {
                self.push(",");
            }
            match seg {
                CBinSeg::Byte(b) => self.print_bin_seg_byte(*b),
                CBinSeg::BinaryAll(expr) => {
                    self.push("#<");
                    self.print_expr(expr);
                    self.push(">('all',8,'binary',['unsigned'|['big']])");
                }
            }
        }
        self.push("}#");
    }

    fn print_binary_segs_pat(&mut self, segs: &[CBinSeg<CPat>]) {
        self.push("#{");
        for (i, seg) in segs.iter().enumerate() {
            if i > 0 {
                self.push(",");
            }
            match seg {
                CBinSeg::Byte(b) => self.print_bin_seg_byte(*b),
                CBinSeg::BinaryAll(pat) => {
                    self.push("#<");
                    self.print_pat(pat);
                    self.push(">('all',8,'binary',['unsigned'|['big']])");
                }
            }
        }
        self.push("}#");
    }

    fn print_pat(&mut self, pat: &CPat) {
        match pat {
            CPat::Var(v) => self.push(v),
            CPat::Wildcard => {
                let n = self.wildcard_counter;
                self.wildcard_counter += 1;
                self.push(&format!("_W{n}"));
            }
            CPat::Lit(lit) => self.print_lit(lit),
            CPat::Tuple(elems) => {
                self.push("{");
                for (i, p) in elems.iter().enumerate() {
                    if i > 0 {
                        self.push(", ");
                    }
                    self.print_pat(p);
                }
                self.push("}");
            }
            CPat::Cons(head, tail) => {
                self.push("[");
                self.print_pat(head);
                self.push("|");
                self.print_pat(tail);
                self.push("]");
            }
            CPat::Nil => self.push("[]"),
            CPat::Alias(var, pat) => {
                self.push(&format!("{} = ", var));
                self.print_pat(pat);
            }
            // CPat::Values holds the contents of a multi-value arm pattern.
            // The surrounding <> are always emitted by the case arm printer,
            // so print only the comma-separated inner patterns here.
            CPat::Values(ps) => {
                for (i, p) in ps.iter().enumerate() {
                    if i > 0 {
                        self.push(", ");
                    }
                    self.print_pat(p);
                }
            }
            CPat::Binary(segs) => self.print_binary_segs_pat(segs),
        }
    }
}

fn escape_str(s: &str) -> String {
    s.replace('\\', "\\\\")
        .replace('"', "\\\"")
        .replace('\n', "\\n")
        .replace('\t', "\\t")
}
