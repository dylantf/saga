//! Trait-neutral deforestation pass: inline statically-known dict-method calls
//! (collapsing parameterized dict chains, including across modules) and fold the
//! constructors they expose — constant record-field projection, β-reduction of
//! immediately-applied lambdas, and case-of-known-constructor collapse.
//!
//! Historically this pass also cancelled the `Generic` representation tree
//! (`Rep__T`/`Leaf`/`Labeled`/…), which is why it is still named `generic_fold`;
//! that machinery was removed with the Generic deriving system. What remains is
//! the general dict/constant optimizer, which applies to ordinary trait dispatch.
//!
//! See the submodules:
//! - `externals`  — collecting cross-module dict-ctors/funs as inline sources
//! - `folder`     — the `Folder` engine and `fold_program` entry point
//! - `rewrite`    — local rewrite rules (known-ctor matching, β-reduction)
//! - `substitute` — variable substitution and AST traversal helpers
//!
//! Shared types, constants, and the view structs live here and reach the
//! submodules via `use super::*`.

pub(crate) use crate::ast::{
    Annotated, CaseArm, ComprehensionQualifier, Decl, Expr, ExprKind, Handler, HandlerArm,
    HandlerBody, HandlerItem, NodeId, Pat, Program, Stmt, StringPart,
};
pub(crate) use crate::codegen::resolve::{ResolutionMap, ResolvedCodegenKind, ResolvedSymbol};
pub(crate) use crate::desugar::{freshen_expr_ids, freshen_pat_ids};
pub(crate) use std::collections::HashMap;

mod externals;
mod folder;
mod rewrite;
mod substitute;

// Public API surface.
pub use externals::{external_ctors_from_modules, external_funs_from_modules};
pub use folder::fold_program;

// Crate-internal re-exports so submodules reach each other via `use super::*`.
pub(crate) use externals::*;
pub(crate) use rewrite::*;
pub(crate) use substitute::*;

/// Maximum inline-chain depth per call site. A parameterized dict chain deeper
/// than this (a deeply nested record, or a recursive type) bottoms out as an
/// ordinary dict-passing call — correct, just unfused. `Rep` trees are shallow
/// (bounded by field/constructor nesting), so this is generous in practice.
pub(crate) const INLINE_FUEL: u32 = 64;

/// Maximum body size (expression node count) of a plain function eligible for
/// "inline-to-cancel" carry. Keeps the carried-function set small (dispatch
/// helpers like `apply_name_style`) and bounds the code a single inline can add.
pub(crate) const FUN_INLINE_SIZE_CAP: usize = 64;

/// A parameterized `DictConstructor` defined in another compiled module, with
/// the producer's resolution map for carrying its body's name resolutions.
pub struct ExternalCtor<'a> {
    pub source_module: &'a str,
    pub dict_params: &'a [String],
    pub methods: &'a [Expr],
    pub resolution: &'a ResolutionMap,
    pub record_types: &'a HashMap<NodeId, String>,
    pub constructors: &'a HashMap<NodeId, String>,
}

/// External dict constructors keyed by dict-constructor name.
pub type ExternalCtors<'a> = HashMap<String, ExternalCtor<'a>>;

/// A plain function from another compiled module, carried for "inline-to-cancel"
/// (see [`Folder::try_inline_fun`]). Only single-clause, guardless, dispatch-shaped,
/// non-self-recursive functions are carried (see [`carryable_fun`]). Keyed by bare
/// function name; a name defined as a carryable function in more than one module is
/// dropped (see [`external_funs_from_modules`]), so a bare-name match is unambiguous.
pub struct ExternalFun<'a> {
    pub source_module: &'a str,
    pub params: &'a [Pat],
    pub body: &'a Expr,
    pub resolution: &'a ResolutionMap,
    pub record_types: &'a HashMap<NodeId, String>,
    pub constructors: &'a HashMap<NodeId, String>,
}

/// External carryable plain functions keyed by bare function name.
pub type ExternalFuns<'a> = HashMap<String, ExternalFun<'a>>;

/// Result of folding a module: the rewritten program plus resolution entries for
/// inlined cross-module nodes (keyed by their fresh NodeId), to be merged into
/// the consumer's resolution map *after* `resolve_names` so they override any
/// consumer-scope resolution of those fresh nodes.
pub struct FoldOutput {
    pub program: Program,
    pub carried_resolution: ResolutionMap,
    pub carried_record_types: HashMap<NodeId, String>,
    pub carried_constructors: HashMap<NodeId, String>,
    pub carried_constructor_names: HashMap<String, String>,
    /// Resolution for **cross-module producer-local functions** referenced by an
    /// inlined body, keyed by unqualified name (anchored to the producer module).
    /// The id-keyed `carried_resolution` is fragile: subsequent fold rewrites
    /// re-freshen and duplicate the inlined nodes, orphaning the id mapping. A
    /// freshened reference to a producer-private helper (e.g. `io_open`) is then
    /// unresolvable in the consumer's scope and would lower to an unbound
    /// variable. These name-keyed entries are registered into the consumer's
    /// resolve scope (filling gaps only, so the consumer's own names win), so the
    /// reference resolves to a remote call regardless of its (re-freshened) id.
    pub carried_names: HashMap<String, ResolvedSymbol>,
}

/// One dict constructor available for inlining — local (`resolution: None`) or
/// external (carry the producer's resolution).
pub(crate) struct CtorView<'a> {
    pub(crate) source_module: Option<&'a str>,
    pub(crate) dict_params: &'a [String],
    pub(crate) methods: &'a [Expr],
    pub(crate) resolution: Option<&'a ResolutionMap>,
    pub(crate) record_types: Option<&'a HashMap<NodeId, String>>,
    pub(crate) constructors: Option<&'a HashMap<NodeId, String>>,
}

/// One plain function available for "inline-to-cancel" — local (`resolution: None`)
/// or external (carry the producer's resolution).
pub(crate) struct FunView<'a> {
    pub(crate) source_module: Option<&'a str>,
    pub(crate) params: &'a [Pat],
    pub(crate) body: &'a Expr,
    pub(crate) resolution: Option<&'a ResolutionMap>,
    pub(crate) record_types: Option<&'a HashMap<NodeId, String>>,
    pub(crate) constructors: Option<&'a HashMap<NodeId, String>>,
}

pub(crate) struct Folder<'a> {
    pub(crate) ctors: HashMap<&'a str, CtorView<'a>>,
    pub(crate) funs: HashMap<&'a str, FunView<'a>>,
    pub(crate) carried: ResolutionMap,
    pub(crate) carried_record_types: HashMap<NodeId, String>,
    pub(crate) carried_constructors: HashMap<NodeId, String>,
    pub(crate) carried_constructor_names: HashMap<String, String>,
    pub(crate) carried_names: HashMap<String, ResolvedSymbol>,
}
