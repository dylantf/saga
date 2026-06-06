//! A-normal form (ANF) pass for the new uniform translation path.
//!
//! Input/output: `ast::Program`. ANF doesn't change the type, it only enforces
//! the atom/complex invariant at sub-positions. Monadic translation runs in a
//! later stage.
//!
//! Per the planning doc ("Stage 9. ANF / let-normalize"):
//!
//! - Every non-atomic sub-position is lifted to a `let`. Atoms (vars,
//!   literals, all-atomic constructors, lambdas) stay in place.
//! - ANF is per-computation-context: it does not cross lambda / case-arm /
//!   if-branch / handler-arm / with-body boundaries.
//! - `NodeId` discipline: relocated source expressions keep their NodeId
//!   (built via the same `id`/`span`); new wrapper nodes (synthetic `let`
//!   binders, replacement `Var` refs) get fresh NodeIds via `Expr::synth`.
//! - Fresh-name generator (`FreshNames`) lives here initially; promote later
//!   if another stage needs its own.

mod expr;
#[cfg(test)]
mod tests;

use crate::ast::{self, Annotated, Decl, Expr, HandlerArm, HandlerBody, NodeId};
use crate::codegen::resolve::{ResolutionMap, ResolvedCodegenKind};
use std::collections::HashSet;

/// Fresh-name generator for ANF-introduced bindings.
///
/// The `__anf_` prefix is intentionally distinct from the old path's `__eff`
/// so generated names are visually distinguishable in emitted `.core` files
/// during the benchmark toggle.
pub(crate) struct FreshNames {
    counter: u32,
}

impl FreshNames {
    pub fn new() -> Self {
        Self { counter: 0 }
    }

    pub fn fresh(&mut self, tag: &str) -> String {
        let n = self.counter;
        self.counter += 1;
        format!("__anf_{tag}{n}")
    }
}

/// Entry point. ANF-normalize every declaration in the program.
///
/// `resolution` is consulted to flag dict-constructor references as
/// non-atomic: under uniform CPS dict ctors are callables whose value
/// form is a fun reference, not a materialized tuple. Marking them
/// non-atomic lifts each reference into a `let v = DictRef in …` —
/// the translator then emits the let's value as a zero-arg `App`
/// (CPS-calling the ctor) so `v` is bound to the materialized tuple.
/// `None` skips the rewrite (tests that bypass resolution).
pub fn normalize(p: ast::Program, resolution: Option<&ResolutionMap>) -> ast::Program {
    let dict_ctor_node_ids = resolution
        .map(collect_dict_ctor_node_ids)
        .unwrap_or_default();
    let mut anf = Anf {
        fresh: FreshNames::new(),
        dict_ctor_node_ids,
    };
    p.into_iter().map(|d| anf.norm_decl(d)).collect()
}

fn collect_dict_ctor_node_ids(resolution: &ResolutionMap) -> HashSet<NodeId> {
    resolution
        .iter()
        .filter_map(|(nid, sym)| {
            let is_dict_ctor = sym.name.starts_with("__dict_")
                && matches!(
                    sym.kind,
                    ResolvedCodegenKind::BeamFunction { .. }
                        | ResolvedCodegenKind::ExternalFunction { .. }
                );
            is_dict_ctor.then_some(*nid)
        })
        .collect()
}

pub(super) struct Anf {
    pub(super) fresh: FreshNames,
    pub(super) dict_ctor_node_ids: HashSet<NodeId>,
}

impl Anf {
    fn norm_decl(&mut self, decl: Decl) -> Decl {
        match decl {
            Decl::FunBinding {
                id,
                name,
                name_span,
                params,
                guard,
                body,
                span,
            } => Decl::FunBinding {
                id,
                name,
                name_span,
                params,
                guard: guard.map(|g| Box::new(self.anf_expr(*g))),
                body: self.anf_expr(body),
                span,
            },
            Decl::Let {
                id,
                name,
                name_span,
                annotation,
                value,
                span,
            } => Decl::Let {
                id,
                name,
                name_span,
                annotation,
                value: self.anf_expr(value),
                span,
            },
            Decl::Val {
                id,
                doc,
                public,
                name,
                name_span,
                annotations,
                value,
                span,
            } => Decl::Val {
                id,
                doc,
                public,
                name,
                name_span,
                annotations,
                value: self.anf_expr(value),
                span,
            },
            Decl::ImplDef {
                id,
                doc,
                trait_name,
                trait_name_span,
                trait_type_args,
                target_type,
                target_type_span,
                type_params,
                where_clause,
                where_apps,
                needs,
                methods,
                routed_derive_info,
                dangling_trivia,
                span,
            } => {
                let methods = methods
                    .into_iter()
                    .map(|ann| {
                        let mut m = ann.node;
                        m.body = self.anf_expr(m.body);
                        Annotated {
                            node: m,
                            leading_trivia: ann.leading_trivia,
                            trailing_comment: ann.trailing_comment,
                            trailing_trivia: ann.trailing_trivia,
                        }
                    })
                    .collect();
                Decl::ImplDef {
                    id,
                    doc,
                    trait_name,
                    trait_name_span,
                    trait_type_args,
                    target_type,
                    target_type_span,
                    type_params,
                    where_clause,
                    where_apps,
                    needs,
                    methods,
                    routed_derive_info,
                    dangling_trivia,
                    span,
                }
            }
            Decl::HandlerDef {
                id,
                doc,
                public,
                name,
                name_span,
                body,
                recovered_arms,
                dangling_trivia,
                span,
            } => Decl::HandlerDef {
                id,
                doc,
                public,
                name,
                name_span,
                body: self.norm_handler_body(body),
                recovered_arms,
                dangling_trivia,
                span,
            },
            Decl::DictConstructor {
                id,
                name,
                dict_params,
                methods,
                method_effects,
                method_open_rows,
                impl_effects,
                span,
            } => Decl::DictConstructor {
                id,
                name,
                dict_params,
                methods: methods.into_iter().map(|m| self.anf_expr(m)).collect(),
                method_effects,
                method_open_rows,
                impl_effects,
                span,
            },
            other => other,
        }
    }

    pub(super) fn norm_handler_body(&mut self, body: HandlerBody) -> HandlerBody {
        let arms = body
            .arms
            .into_iter()
            .map(|ann| {
                let arm = self.norm_handler_arm(ann.node);
                Annotated {
                    node: arm,
                    leading_trivia: ann.leading_trivia,
                    trailing_comment: ann.trailing_comment,
                    trailing_trivia: ann.trailing_trivia,
                }
            })
            .collect();
        let return_clause = body
            .return_clause
            .map(|arm| Box::new(self.norm_handler_arm(*arm)));
        HandlerBody {
            effects: body.effects,
            needs: body.needs,
            where_clause: body.where_clause,
            arms,
            return_clause,
        }
    }

    pub(super) fn norm_handler_arm(&mut self, arm: HandlerArm) -> HandlerArm {
        HandlerArm {
            id: arm.id,
            op_name: arm.op_name,
            qualifier: arm.qualifier,
            params: arm.params,
            body: Box::new(self.anf_expr(*arm.body)),
            finally_block: arm.finally_block.map(|b| Box::new(self.anf_expr(*b))),
            span: arm.span,
        }
    }

    /// Run ANF in a fresh computation context (lambda body, branch, arm body).
    pub(super) fn anf_expr(&mut self, e: Expr) -> Expr {
        let mut bindings = Vec::new();
        let tail = self.normalize_into(e, &mut bindings);
        expr::finish(bindings, tail)
    }
}
