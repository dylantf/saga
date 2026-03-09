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
    /// `try Expr of SuccessVar -> SuccessBody catch Class, Reason, Stack -> CatchBody`
    Try {
        expr: Box<CExpr>,
        success_var: String,
        success_body: Box<CExpr>,
        catch_class: String,
        catch_reason: String,
        catch_stacktrace: String,
        catch_body: Box<CExpr>,
    },
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
}

#[derive(Debug, Clone)]
pub enum CLit {
    Int(i64),
    Float(f64),
    Atom(String),
    Str(String),
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
}

impl Printer {
    fn new() -> Self {
        Printer {
            buf: String::new(),
            indent: 0,
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

            CExpr::Try {
                expr,
                success_var,
                success_body,
                catch_class,
                catch_reason,
                catch_stacktrace,
                catch_body,
            } => {
                self.push("try");
                self.with_indent(2, |p| {
                    p.newline();
                    p.print_expr(expr);
                });
                self.newline();
                self.push(&format!("of <{}> ->", success_var));
                self.with_indent(2, |p| {
                    p.newline();
                    p.print_expr(success_body);
                });
                self.newline();
                self.push(&format!(
                    "catch <{},{},{}> ->",
                    catch_class, catch_reason, catch_stacktrace
                ));
                self.with_indent(2, |p| {
                    p.newline();
                    p.print_expr(catch_body);
                });
            }
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
            CLit::Float(f) => self.push(&f.to_string()),
            CLit::Atom(a) => self.push(&format!("'{}'", a)),
            CLit::Str(s) => self.push(&format!("\"{}\"", escape_str(s))),
        }
    }

    fn print_pat(&mut self, pat: &CPat) {
        match pat {
            CPat::Var(v) => self.push(v),
            CPat::Wildcard => self.push("_"),
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
                self.print_pat(pat);
                self.push(&format!(" = {}", var));
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
        }
    }
}

fn escape_str(s: &str) -> String {
    s.replace('\\', "\\\\")
        .replace('"', "\\\"")
        .replace('\n', "\\n")
        .replace('\t', "\\t")
}
