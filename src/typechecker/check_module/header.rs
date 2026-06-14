use std::collections::{BTreeSet, HashMap};

use crate::token::Span;

// --- Module export types ---

/// Inference-free interface data for a parsed module.
///
/// This is intentionally plain, owned data: no `NodeId`s, no references into a
/// checker, and no inferred type state. It is the pre-inference surface needed
/// to build module scopes for cyclic import groups.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct ModuleHeader {
    pub module_name: Option<String>,
    pub imports: Vec<HeaderImport>,
    pub functions: HashMap<String, HeaderFunction>,
    pub unannotated_functions: Vec<String>,
    pub types: HashMap<String, HeaderTypeDecl>,
    pub records: HashMap<String, HeaderRecordDecl>,
    pub traits: HashMap<String, HeaderTraitDecl>,
    pub effects: HashMap<String, HeaderEffectDecl>,
    pub handlers: HashMap<String, HeaderHandlerDecl>,
    pub re_exports: Vec<HeaderReExport>,
    pub re_export_all: Vec<HeaderReExportAll>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct HeaderImport {
    pub module: String,
    pub alias: Option<String>,
    pub exposing: Option<HeaderExposing>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HeaderExposing {
    All { public: bool },
    Items(Vec<HeaderExposedItem>),
}

impl HeaderExposing {
    pub fn from_ast(exposing: &crate::ast::Exposing) -> Self {
        header_exposing(exposing)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HeaderExposedItem {
    pub name: String,
    pub alias: Option<String>,
    pub public: bool,
}

impl HeaderExposedItem {
    pub fn surface_name(&self) -> &str {
        self.alias.as_deref().unwrap_or(&self.name)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HeaderVisibility {
    Public,
    Opaque,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HeaderReExport {
    pub surface_name: String,
    pub origin_module: String,
    pub origin_name: String,
    pub visibility: HeaderVisibility,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HeaderReExportAll {
    pub origin_module: String,
    pub visibility: HeaderVisibility,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HeaderFunction {
    pub public: bool,
    pub params: Vec<(String, HeaderTypeExpr)>,
    pub return_type: HeaderTypeExpr,
    pub effects: Vec<HeaderEffectRef>,
    pub effect_row_vars: Vec<String>,
    pub where_clause: Vec<HeaderTraitBound>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HeaderTypeParam {
    pub name: String,
    pub kind: crate::ast::Kind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HeaderTypeDecl {
    Adt {
        public: bool,
        opaque: bool,
        type_params: Vec<HeaderTypeParam>,
        constructors: Vec<HeaderConstructor>,
    },
    Alias {
        public: bool,
        type_params: Vec<HeaderTypeParam>,
        body: HeaderTypeExpr,
    },
}

impl HeaderTypeDecl {
    pub fn arity(&self) -> usize {
        match self {
            HeaderTypeDecl::Adt { type_params, .. } | HeaderTypeDecl::Alias { type_params, .. } => {
                type_params.len()
            }
        }
    }

    pub fn public(&self) -> bool {
        match self {
            HeaderTypeDecl::Adt { public, .. } | HeaderTypeDecl::Alias { public, .. } => *public,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HeaderConstructor {
    pub name: String,
    pub fields: Vec<HeaderConstructorField>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HeaderConstructorField {
    pub label: Option<String>,
    pub ty: HeaderTypeExpr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HeaderRecordDecl {
    pub public: bool,
    pub type_params: Vec<HeaderTypeParam>,
    pub fields: Vec<(String, HeaderTypeExpr)>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HeaderTraitDecl {
    pub public: bool,
    pub type_params: Vec<HeaderTypeParam>,
    pub is_functional: bool,
    pub supertraits: Vec<HeaderTraitRef>,
    pub methods: Vec<HeaderTraitMethod>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HeaderTraitMethod {
    pub name: String,
    pub params: Vec<(String, HeaderTypeExpr)>,
    pub return_type: HeaderTypeExpr,
    pub effects: Vec<HeaderEffectRef>,
    pub effect_row_vars: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HeaderEffectDecl {
    pub public: bool,
    pub type_params: Vec<HeaderTypeParam>,
    pub operations: Vec<HeaderEffectOp>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HeaderEffectOp {
    pub name: String,
    pub params: Vec<(String, HeaderTypeExpr)>,
    pub return_type: HeaderTypeExpr,
    pub effects: Vec<HeaderEffectRef>,
    pub effect_row_vars: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HeaderHandlerDecl {
    pub public: bool,
    pub effects: Vec<HeaderEffectRef>,
    pub needs: Vec<HeaderEffectRef>,
    pub where_clause: Vec<HeaderTraitBound>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HeaderEffectRef {
    pub name: String,
    pub type_args: Vec<HeaderTypeExpr>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HeaderTraitBound {
    pub type_var: String,
    pub traits: Vec<HeaderTraitRef>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HeaderTraitRef {
    pub name: String,
    pub type_args: Vec<HeaderTypeExpr>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HeaderTypeExpr {
    Named(String),
    Var(String),
    App {
        func: Box<HeaderTypeExpr>,
        arg: Box<HeaderTypeExpr>,
    },
    Arrow {
        from: Box<HeaderTypeExpr>,
        to: Box<HeaderTypeExpr>,
        effects: Vec<HeaderEffectRef>,
        effect_row_vars: Vec<String>,
    },
    Record(Vec<(String, HeaderTypeExpr)>),
    Labeled {
        label: String,
        inner: Box<HeaderTypeExpr>,
    },
    Symbol(String),
}

impl ModuleHeader {
    pub fn from_program(program: &[crate::ast::Decl]) -> Self {
        use crate::ast::Decl;

        let mut header = ModuleHeader::default();
        for decl in program {
            match decl {
                Decl::ModuleDecl { path, .. } => {
                    header.module_name = Some(path.join("."));
                }
                Decl::Import {
                    module_path,
                    alias,
                    exposing,
                    ..
                } => {
                    let module = module_path.join(".");
                    header.imports.push(HeaderImport {
                        module: module.clone(),
                        alias: alias.clone(),
                        exposing: exposing.as_ref().map(header_exposing),
                    });
                    if let Some(exposing) = exposing {
                        collect_header_re_exports(&mut header, &module, exposing);
                    }
                }
                Decl::FunSignature {
                    public,
                    name,
                    params,
                    return_type,
                    effects,
                    effect_row_var,
                    where_clause,
                    ..
                } => {
                    header.functions.insert(
                        name.clone(),
                        HeaderFunction {
                            public: *public,
                            params: params
                                .iter()
                                .map(|(name, ty)| (name.clone(), header_type_expr(ty)))
                                .collect(),
                            return_type: header_type_expr(return_type),
                            effects: effects.iter().map(header_effect_ref).collect(),
                            effect_row_vars: row_var_names(effect_row_var),
                            where_clause: where_clause.iter().map(header_trait_bound).collect(),
                        },
                    );
                }
                Decl::FunBinding { name, .. } => {
                    header.unannotated_functions.push(name.clone());
                }
                Decl::TypeDef {
                    public,
                    opaque,
                    name,
                    type_params,
                    variants,
                    ..
                } => {
                    header.types.insert(
                        name.clone(),
                        HeaderTypeDecl::Adt {
                            public: *public,
                            opaque: *opaque,
                            type_params: header_type_params(type_params),
                            constructors: variants
                                .iter()
                                .map(|variant| HeaderConstructor {
                                    name: variant.node.name.clone(),
                                    fields: variant
                                        .node
                                        .fields
                                        .iter()
                                        .map(|(label, ty)| HeaderConstructorField {
                                            label: label.clone(),
                                            ty: header_type_expr(ty),
                                        })
                                        .collect(),
                                })
                                .collect(),
                        },
                    );
                }
                Decl::TypeAlias {
                    public,
                    name,
                    type_params,
                    body,
                    ..
                } => {
                    header.types.insert(
                        name.clone(),
                        HeaderTypeDecl::Alias {
                            public: *public,
                            type_params: header_type_params(type_params),
                            body: header_type_expr(body),
                        },
                    );
                }
                Decl::RecordDef {
                    public,
                    name,
                    type_params,
                    fields,
                    ..
                } => {
                    header.records.insert(
                        name.clone(),
                        HeaderRecordDecl {
                            public: *public,
                            type_params: header_type_params(type_params),
                            fields: fields
                                .iter()
                                .map(|field| {
                                    let (name, ty) = &field.node;
                                    (name.clone(), header_type_expr(ty))
                                })
                                .collect(),
                        },
                    );
                }
                Decl::TraitDef {
                    public,
                    name,
                    type_params,
                    functional_dependency,
                    supertraits,
                    methods,
                    ..
                } => {
                    header.traits.insert(
                        name.clone(),
                        HeaderTraitDecl {
                            public: *public,
                            type_params: header_type_params(type_params),
                            is_functional: functional_dependency.is_some(),
                            supertraits: supertraits.iter().map(header_trait_ref).collect(),
                            methods: methods
                                .iter()
                                .map(|method| HeaderTraitMethod {
                                    name: method.node.name.clone(),
                                    params: method
                                        .node
                                        .params
                                        .iter()
                                        .map(|(name, ty)| (name.clone(), header_type_expr(ty)))
                                        .collect(),
                                    return_type: header_type_expr(&method.node.return_type),
                                    effects: method
                                        .node
                                        .effects
                                        .iter()
                                        .map(header_effect_ref)
                                        .collect(),
                                    effect_row_vars: row_var_names(&method.node.effect_row_var),
                                })
                                .collect(),
                        },
                    );
                }
                Decl::EffectDef {
                    public,
                    name,
                    type_params,
                    operations,
                    ..
                } => {
                    header.effects.insert(
                        name.clone(),
                        HeaderEffectDecl {
                            public: *public,
                            type_params: header_type_params(type_params),
                            operations: operations
                                .iter()
                                .map(|op| HeaderEffectOp {
                                    name: op.node.name.clone(),
                                    params: op
                                        .node
                                        .params
                                        .iter()
                                        .map(|(name, ty)| (name.clone(), header_type_expr(ty)))
                                        .collect(),
                                    return_type: header_type_expr(&op.node.return_type),
                                    effects: op
                                        .node
                                        .effects
                                        .iter()
                                        .map(header_effect_ref)
                                        .collect(),
                                    effect_row_vars: row_var_names(&op.node.effect_row_var),
                                })
                                .collect(),
                        },
                    );
                }
                Decl::HandlerDef {
                    public, name, body, ..
                } => {
                    header.handlers.insert(
                        name.clone(),
                        HeaderHandlerDecl {
                            public: *public,
                            effects: body.effects.iter().map(header_effect_ref).collect(),
                            needs: body.needs.iter().map(header_effect_ref).collect(),
                            where_clause: body
                                .where_clause
                                .iter()
                                .map(header_trait_bound)
                                .collect(),
                        },
                    );
                }
                _ => {}
            }
        }
        let annotated = header.functions.keys().cloned().collect::<BTreeSet<_>>();
        header.unannotated_functions = header
            .unannotated_functions
            .into_iter()
            .collect::<BTreeSet<_>>()
            .into_iter()
            .filter(|name| !annotated.contains(name))
            .collect();
        header
    }

    pub fn public_type_names(&self) -> impl Iterator<Item = (&String, &HeaderTypeDecl)> {
        self.types.iter().filter(|(_, decl)| decl.public())
    }
}

fn collect_header_re_exports(
    header: &mut ModuleHeader,
    origin_module: &str,
    exposing: &crate::ast::Exposing,
) {
    match exposing {
        crate::ast::Exposing::All { public: true, .. } => {
            header.re_export_all.push(HeaderReExportAll {
                origin_module: origin_module.to_string(),
                visibility: HeaderVisibility::Public,
            });
        }
        crate::ast::Exposing::Items(items) => {
            header
                .re_exports
                .extend(
                    items
                        .iter()
                        .filter(|item| item.public)
                        .map(|item| HeaderReExport {
                            surface_name: item.surface_name().to_string(),
                            origin_module: origin_module.to_string(),
                            origin_name: item.name.clone(),
                            visibility: HeaderVisibility::Public,
                        }),
                );
        }
        _ => {}
    }
}

fn header_exposing(exposing: &crate::ast::Exposing) -> HeaderExposing {
    match exposing {
        crate::ast::Exposing::All { public, .. } => HeaderExposing::All { public: *public },
        crate::ast::Exposing::Items(items) => HeaderExposing::Items(
            items
                .iter()
                .map(|item| HeaderExposedItem {
                    name: item.name.clone(),
                    alias: item.alias.clone(),
                    public: item.public,
                })
                .collect(),
        ),
    }
}

fn header_type_params(params: &[crate::ast::TypeParam]) -> Vec<HeaderTypeParam> {
    params
        .iter()
        .map(|param| HeaderTypeParam {
            name: param.name.clone(),
            kind: param.kind,
        })
        .collect()
}

fn row_var_names(vars: &[(String, Span)]) -> Vec<String> {
    vars.iter().map(|(name, _)| name.clone()).collect()
}

fn header_effect_ref(effect: &crate::ast::EffectRef) -> HeaderEffectRef {
    HeaderEffectRef {
        name: effect.name.clone(),
        type_args: effect.type_args.iter().map(header_type_expr).collect(),
    }
}

fn header_trait_bound(bound: &crate::ast::TraitBound) -> HeaderTraitBound {
    HeaderTraitBound {
        type_var: bound.type_var.clone(),
        traits: bound.traits.iter().map(header_trait_ref).collect(),
    }
}

fn header_trait_ref(trait_ref: &crate::ast::TraitRef) -> HeaderTraitRef {
    HeaderTraitRef {
        name: trait_ref.name.clone(),
        type_args: trait_ref.type_args.iter().map(header_type_expr).collect(),
    }
}

fn header_type_expr(ty: &crate::ast::TypeExpr) -> HeaderTypeExpr {
    use crate::ast::TypeExpr;

    match ty {
        TypeExpr::Named { name, .. } => HeaderTypeExpr::Named(name.clone()),
        TypeExpr::Var { name, .. } => HeaderTypeExpr::Var(name.clone()),
        TypeExpr::App { func, arg, .. } => HeaderTypeExpr::App {
            func: Box::new(header_type_expr(func)),
            arg: Box::new(header_type_expr(arg)),
        },
        TypeExpr::Arrow {
            from,
            to,
            effects,
            effect_row_var,
            ..
        } => HeaderTypeExpr::Arrow {
            from: Box::new(header_type_expr(from)),
            to: Box::new(header_type_expr(to)),
            effects: effects.iter().map(header_effect_ref).collect(),
            effect_row_vars: row_var_names(effect_row_var),
        },
        TypeExpr::Record { fields, .. } => HeaderTypeExpr::Record(
            fields
                .iter()
                .map(|(name, ty)| (name.clone(), header_type_expr(ty)))
                .collect(),
        ),
        TypeExpr::Labeled { label, inner, .. } => HeaderTypeExpr::Labeled {
            label: label.clone(),
            inner: Box::new(header_type_expr(inner)),
        },
        TypeExpr::Symbol { name, .. } => HeaderTypeExpr::Symbol(name.clone()),
    }
}

#[cfg(test)]
mod module_header_tests {
    use super::*;

    fn parse(src: &str) -> crate::ast::Program {
        let tokens = crate::lexer::Lexer::new(src).lex().expect("lex");
        crate::parser::Parser::new(tokens)
            .parse_program()
            .expect("parse")
    }

    #[test]
    fn module_header_is_extractable_from_ast_only() {
        let program = parse(
            r#"
module A

import B (pub Choice as BChoice, helper)
import C (pub ..)

pub fun render : (user: User a) -> String needs {Log} where {a: Label}
render user = user.name

pub type Choice a = Left a | Right String
pub opaque type Secret = Secret Int
pub type alias Name = String
pub record User a { name: String, value: a }

pub trait Label a {
  fun label : a -> String needs {Log}
}

pub effect Ask a {
  fun ask : Unit -> a needs {Log}
}

pub handler ask_once for Ask String needs {Log} {
  ask () = resume "ok"
}
"#,
        );

        let header = ModuleHeader::from_program(&program);

        assert_eq!(header.module_name.as_deref(), Some("A"));
        assert_eq!(
            header
                .imports
                .iter()
                .map(|i| i.module.as_str())
                .collect::<Vec<_>>(),
            vec!["B", "C"]
        );
        assert_eq!(
            header.re_exports,
            vec![HeaderReExport {
                surface_name: "BChoice".to_string(),
                origin_module: "B".to_string(),
                origin_name: "Choice".to_string(),
                visibility: HeaderVisibility::Public,
            }]
        );
        assert_eq!(
            header.re_export_all,
            vec![HeaderReExportAll {
                origin_module: "C".to_string(),
                visibility: HeaderVisibility::Public,
            }]
        );

        let render = header.functions.get("render").expect("render signature");
        assert!(render.public);
        assert_eq!(render.effects[0].name, "Log");
        assert_eq!(render.where_clause[0].traits[0].name, "Label");

        let choice = header.types.get("Choice").expect("Choice type");
        assert_eq!(choice.arity(), 1);
        let HeaderTypeDecl::Adt {
            opaque,
            constructors,
            ..
        } = choice
        else {
            panic!("expected ADT");
        };
        assert!(!opaque);
        assert_eq!(
            constructors
                .iter()
                .map(|c| c.name.as_str())
                .collect::<Vec<_>>(),
            vec!["Left", "Right"]
        );

        let secret = header.types.get("Secret").expect("Secret type");
        let HeaderTypeDecl::Adt { opaque, .. } = secret else {
            panic!("expected opaque ADT");
        };
        assert!(opaque);

        let user = header.records.get("User").expect("User record");
        assert_eq!(
            user.fields
                .iter()
                .map(|(name, _)| name.as_str())
                .collect::<Vec<_>>(),
            vec!["name", "value"]
        );

        let label = header.traits.get("Label").expect("Label trait");
        assert_eq!(label.methods[0].name, "label");
        assert_eq!(label.methods[0].effects[0].name, "Log");

        let ask = header.effects.get("Ask").expect("Ask effect");
        assert_eq!(ask.operations[0].name, "ask");
        assert_eq!(ask.operations[0].effects[0].name, "Log");

        let handler = header.handlers.get("ask_once").expect("handler");
        assert_eq!(handler.effects[0].name, "Ask");
        assert_eq!(handler.needs[0].name, "Log");
    }
}
