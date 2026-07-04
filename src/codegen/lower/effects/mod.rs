//! Effect-system lowering: CPS transform, handler building, BEAM-native ops.
//!
//! Split across submodules by concern:
//! - `ops`      — effect-op lowering plans, static tail-resume, return/evidence lambdas
//! - `call`     — `lower_effect_call` and BEAM-native op-fun synthesis
//! - `with`     — `lower_with` blocks, handler chains, op-handler fun building
//! - `handlers` — handler-to-tuple lowering, normalization, named/inline planning
//! - `analysis` — free-var collection, pending-let placement, scoped bindings, native helpers
//!
//! The shared plan/handler types and `impl NamedHandlerItem` live here and reach
//! the submodules via `use super::*`.

use std::collections::HashSet;

use crate::ast::{Expr, HandlerArm, Stmt};
use crate::codegen::cerl::CExpr;

mod analysis;
mod call;
mod handlers;
mod ops;
mod with;

pub(crate) struct PendingLet {
    pub(crate) var: String,
    pub(crate) val: CExpr,
    pub(crate) deps: HashSet<String>,
}

#[derive(Clone)]
pub(crate) enum NamedHandlerItem {
    Static {
        canonical: String,
        info: Box<super::HandlerInfo>,
    },
    Conditional {
        cond_var: String,
        cond_ce: Box<CExpr>,
        then_info: Box<super::HandlerInfo>,
        else_info: Box<super::HandlerInfo>,
    },
    Dynamic {
        tuple_var: String,
        effects: Vec<String>,
        has_return: bool,
    },
}

#[derive(Clone)]
pub(crate) enum OpHandlerPlan {
    Inline {
        arms: Vec<HandlerArm>,
    },
    Static {
        arm: HandlerArm,
        source_module: Option<String>,
        effect_name: String,
        handler_canonical: String,
        captures: Vec<(String, Expr)>,
    },
    Conditional {
        cond_var: String,
        then_arm: Option<HandlerArm>,
        then_source: Option<String>,
        else_arm: Option<HandlerArm>,
        else_source: Option<String>,
    },
    Dynamic {
        element_expr: CExpr,
    },
    BeamNative {
        handler_canonical: String,
    },
    Passthrough,
}

pub(crate) enum EffectOpLoweringPlan {
    DirectNative { handler_canonical: String },
    DirectStaticTailResume { plan: super::StaticTailResumeOp },
    EvidenceLookup { trace_shape: String },
}

pub(crate) enum StaticTailResumeDirectBody {
    Expr(Expr),
    Block(Vec<Stmt>),
}

pub(crate) enum WithHandlerLayer {
    Named {
        reference: crate::ast::NamedHandlerRef,
    },
    Inline {
        arms: Vec<HandlerArm>,
        return_clause: Option<Box<HandlerArm>>,
    },
}

impl NamedHandlerItem {
    pub(crate) fn effects(&self) -> &[String] {
        match self {
            NamedHandlerItem::Static { info, .. } => &info.effects,
            NamedHandlerItem::Conditional { then_info, .. } => &then_info.effects,
            NamedHandlerItem::Dynamic { effects, .. } => effects,
        }
    }

    pub(crate) fn has_return_clause(&self) -> bool {
        match self {
            NamedHandlerItem::Static { info, .. } => info.return_clause.is_some(),
            NamedHandlerItem::Conditional {
                then_info,
                else_info,
                ..
            } => then_info.return_clause.is_some() || else_info.return_clause.is_some(),
            NamedHandlerItem::Dynamic { has_return, .. } => *has_return,
        }
    }
}
