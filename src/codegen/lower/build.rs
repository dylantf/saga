//! The builder of the typed back-end tree (`codegen::ir`).
//!
//! Shallow for now: it builds one node from one AST node and leaves the
//! children as `Ast`. It is the only code that reads the side tables
//! (resolution, record layouts, constructor atoms, types) for the constructs
//! it builds; the lowerer reads the node. A field that cannot be determined
//! is an internal compiler error, never a default.

use crate::ast::{Expr, ExprKind, NodeId};
use crate::codegen::effect_position;
use crate::codegen::ir::{CtorRef, FnRef, FnRepr, Val};
use crate::codegen::resolve::{ResolvedCodegenKind, ResolvedSymbol};
use crate::codegen::runtime_shape::{CallableAbi, ValueRepr};
use crate::typechecker::Type;

use super::Lowerer;
use super::util::{arity_and_effects_from_type, core_var, mangle_ctor_atom};

impl<'a> Lowerer<'a> {
    /// `expr` as an operand of `operand_of`. The one place operands are
    /// made: an operand is a value, and one that is not means the body it
    /// is in did not pass through `effect_normal_body`. Stop instead of
    /// lowering it where it stands (with an identity continuation, if it
    /// performs). A BEAM guard expression is exempt: its operators nest.
    pub(super) fn operand<'e>(&self, expr: &'e Expr, operand_of: &str) -> Val<'e> {
        if !self.in_beam_guard
            && !effect_position::is_operand(expr, &|node| self.performs_effect(node))
        {
            panic!(
                "internal compiler error: {} reached lowering as an operand of {operand_of} \
                 in {}.{}: its body was not normalized",
                effect_position::construct_name(expr, &|node| self.performs_effect(node)),
                self.current_semantic_module_name(),
                self.current_function,
            );
        }
        Val::Ast(expr)
    }

    fn operands<'e>(
        &self,
        exprs: impl IntoIterator<Item = &'e Expr>,
        operand_of: &str,
    ) -> Vec<Val<'e>> {
        (exprs.into_iter())
            .map(|expr| self.operand(expr, operand_of))
            .collect()
    }

    /// Build the value `expr` is. Only called for the value forms the
    /// lowerer has handed over (`lower_expr`).
    pub(super) fn build_val<'e>(&self, expr: &'e Expr) -> Val<'e> {
        match &expr.kind {
            ExprKind::Lit { value, .. } => Val::Lit(value),
            ExprKind::Var { name, .. } => match self.resolved.get(&expr.id) {
                Some(symbol) => self.function_value(expr.id, symbol),
                // Not a module-level or imported function: a named handler
                // used as a value, or a local variable.
                None => {
                    let handler = (self.known_handler_binding_name(expr.id, name))
                        .unwrap_or_else(|| name.clone());
                    self.handler_ref(handler)
                        .unwrap_or_else(|| Val::Local(core_var(name)))
                }
            },
            ExprKind::QualifiedName { name, .. } => {
                if let Some(ctor) = self.qualified_constructor(expr.id) {
                    return Val::Ctor {
                        ctor: self.ctor_ref(&ctor, 0),
                        args: Vec::new(),
                    };
                }
                // A named handler is a value, not a function of no arguments.
                if let Some(handler) = (self.known_handler_binding_name(expr.id, name))
                    .and_then(|handler| self.handler_ref(handler))
                {
                    return handler;
                }
                match self.resolved.get(&expr.id) {
                    Some(symbol) => self.function_value(expr.id, symbol),
                    None => Val::Local(core_var(name)),
                }
            }
            ExprKind::Constructor { name, .. } => {
                let ctor = self.resolved_constructor_name_for(expr.id, name);
                match self.value_type(expr.id) {
                    Some(ty @ Type::Fun(..)) => {
                        let arity = arity_and_effects_from_type(&ty).0;
                        Val::CtorFn {
                            ctor: self.ctor_ref(&ctor, arity),
                            arity,
                        }
                    }
                    _ => Val::Ctor {
                        ctor: self.ctor_ref(&ctor, 0),
                        args: Vec::new(),
                    },
                }
            }
            ExprKind::Tuple { elements, .. } => Val::Tuple(self.operands(elements, "a tuple")),
            ExprKind::RecordCreate {
                name,
                fields,
                record_name,
            } => {
                let order = self
                    .record_create_field_order(record_name.as_deref(), expr.id, name)
                    .unwrap_or_else(|| {
                        panic!(
                            "codegen: cannot resolve field layout for record `{name}` \
                             (node {:?}, module `{}`). The record's type could not be \
                             determined here, so its tuple layout is unknown.",
                            expr.id,
                            self.current_semantic_module_name(),
                        )
                    });
                let ctor = self
                    .current_record_type_name(expr.id)
                    .and_then(|name| self.canonical_constructor_key_for(name))
                    .unwrap_or_else(|| self.resolved_constructor_name_for(expr.id, name));
                Val::Record {
                    tag: mangle_ctor_atom(&ctor, &self.constructor_atoms, None),
                    arity: order.len(),
                    fields: self.record_slots(fields, |field| {
                        order.iter().position(|declared| declared == field)
                    }),
                }
            }
            ExprKind::AnonRecordCreate { fields, .. } => {
                let mut sorted: Vec<&str> = fields.iter().map(|(n, _, _)| n.as_str()).collect();
                let tag = crate::ast::anon_record_tag(&sorted);
                sorted.sort();
                Val::Record {
                    tag,
                    arity: sorted.len(),
                    fields: self.record_slots(fields, |field| {
                        sorted.iter().position(|declared| *declared == field)
                    }),
                }
            }
            ExprKind::FieldAccess {
                expr: record,
                field,
                record_name,
            } => {
                let slot = (record_name.as_deref())
                    .and_then(|record| self.record_fields.get(record))
                    .and_then(|fields| fields.iter().position(|f| f == field))
                    .unwrap_or_else(|| {
                        panic!(
                            "codegen: could not resolve record type for field access '.{}' at node {:?} (record_name={:?})",
                            field, record.id, record_name
                        )
                    });
                Val::Field {
                    base: Box::new(self.operand(record, "field access")),
                    slot,
                }
            }
            ExprKind::DictMethodAccess {
                dict,
                method_index,
                trait_name,
            } => Val::DictMethod {
                dict: Box::new(self.operand(dict, "a dictionary access")),
                slot: self.trait_method_tuple_index(trait_name, *method_index) + 1,
                nullary: self.trait_method_is_nullary(trait_name, *method_index),
                pure_view: self.pure_view_of_effectful_method(dict, trait_name, *method_index),
            },
            ExprKind::DictSuperAccess {
                dict,
                supertrait_index,
                ..
            } => Val::DictSuper {
                dict: Box::new(self.operand(dict, "a dictionary access")),
                slot: supertrait_index + 1,
            },
            ExprKind::DictRef { name, .. } => match self.resolved.get(&expr.id) {
                Some(symbol) if matches!(symbol.kind, ResolvedCodegenKind::Intrinsic { .. }) => {
                    panic!(
                        "dict ref resolved to non-dictionary codegen kind: {}",
                        symbol.canonical_name
                    )
                }
                Some(symbol) => match self.function_value(expr.id, symbol) {
                    Val::Const(dict) => Val::Dict(dict),
                    constructor => constructor,
                },
                None => match self.fun_info.get(name) {
                    Some(info) => {
                        let target = FnRef {
                            module: None,
                            name: name.clone(),
                            abi: info.abi.clone(),
                        };
                        match info.arity() {
                            0 => Val::Dict(target),
                            _ => Val::Fn {
                                target,
                                repr: FnRepr::Bare,
                            },
                        }
                    }
                    None => Val::DictParam(core_var(name)),
                },
            },
            _ => panic!(
                "internal compiler error: {} is not a value form the builder builds ({}.{})",
                effect_position::construct_name(expr, &|node| self.performs_effect(node)),
                self.current_semantic_module_name(),
                self.current_function,
            ),
        }
    }

    /// The fields of a record literal, in written order, each with the slot
    /// `slot_of` gives its name.
    fn record_slots<'e>(
        &self,
        fields: &'e [(String, crate::token::Span, Expr)],
        slot_of: impl Fn(&str) -> Option<usize>,
    ) -> Vec<(usize, Val<'e>)> {
        fields
            .iter()
            .map(|(name, _, value)| {
                let slot = slot_of(name).unwrap_or_else(|| {
                    panic!(
                        "internal compiler error: record literal in {}.{} has a field `{name}` \
                         its record type does not declare",
                        self.current_semantic_module_name(),
                        self.current_function,
                    )
                });
                (slot, self.operand(value, "a record literal"))
            })
            .collect()
    }

    /// The canonical constructor a qualified name resolved to, if it did.
    pub(super) fn qualified_constructor(&self, node_id: NodeId) -> Option<String> {
        self.maybe_resolved_constructor_name_for(node_id)
            .filter(|ctor| self.is_known_constructor(ctor))
    }

    /// The runtime shape of the constructor with canonical name `name`
    /// applied to `argc` arguments.
    pub(super) fn ctor_ref(&self, name: &str, argc: usize) -> CtorRef {
        let bare = name.rsplit('.').next().unwrap_or(name);
        match bare {
            "Nil" if argc == 0 => CtorRef::Nil,
            "True" if argc == 0 => CtorRef::Bool(true),
            "False" if argc == 0 => CtorRef::Bool(false),
            "Cons" if argc == 2 => CtorRef::Cons,
            _ => match super::beam_interop::exit_reason_bare_atom(bare) {
                Some(atom) if argc == 0 => CtorRef::Atom(atom),
                _ => CtorRef::Tagged(mangle_ctor_atom(name, &self.constructor_atoms, None)),
            },
        }
    }

    /// The named handler `name` as a value, when it has a definition to
    /// build the value from.
    fn handler_ref<'e>(&self, name: String) -> Option<Val<'e>> {
        self.handler_defs
            .contains_key(&self.resolve_handler_name(&name))
            .then_some(Val::HandlerRef(name))
    }

    /// A name resolved to a function, constant or intrinsic, used as a value.
    fn function_value<'e>(&self, node_id: NodeId, symbol: &ResolvedSymbol) -> Val<'e> {
        if let ResolvedCodegenKind::Intrinsic { arity, .. } = symbol.kind {
            return Val::Intrinsic {
                name: symbol.name.clone(),
                arity,
            };
        }
        let abi = self.declared_abi(node_id, symbol);
        let target = self.fn_ref(symbol, abi);
        let abi = &target.abi;
        // A function that takes no arguments is never a closure.
        let repr = match abi.user_arity {
            0 => FnRepr::Bare,
            _ => self.fn_repr(abi, node_id),
        };
        if abi.expanded_arity() == 0 {
            Val::Const(target)
        } else if symbol.source_module.is_none() {
            Val::LocalFn { target, repr }
        } else {
            Val::Fn { target, repr }
        }
    }

    /// How the function with convention `abi` is represented as the value
    /// the node `node_id` is (a reference to it or a partial application of
    /// it): by the node's own type.
    pub(super) fn fn_repr(&self, abi: &CallableAbi, node_id: NodeId) -> FnRepr {
        match &abi.evidence {
            None => FnRepr::Bare,
            Some(evidence)
                if self.value_repr_of(node_id) == Some(ValueRepr::Bare)
                    && evidence.static_slots().is_empty() =>
            {
                FnRepr::BareEmptyRow
            }
            Some(_) => FnRepr::Tagged,
        }
    }

    /// An application whose head is a constructor (by name, or a qualified
    /// name that resolved to one): data built from its arguments.
    pub(super) fn build_ctor_app<'e>(&self, expr: &'e Expr) -> Option<Val<'e>> {
        let (head, args) = app_head_and_args(expr);
        let ctor = match &head.kind {
            ExprKind::Constructor { name, .. } => self.resolved_constructor_name_for(head.id, name),
            ExprKind::QualifiedName { .. } => self.qualified_constructor(head.id)?,
            _ => return None,
        };
        Some(Val::Ctor {
            ctor: self.ctor_ref(&ctor, args.len()),
            args: self.operands(args, "a constructor"),
        })
    }

    /// The declared convention of the function `symbol` names. The
    /// resolution map does not know the effects of a function of the module
    /// being emitted (or the convention of a block-local one); the lowerer's
    /// own table does.
    fn declared_abi(&self, node_id: NodeId, symbol: &ResolvedSymbol) -> CallableAbi {
        match &symbol.kind {
            ResolvedCodegenKind::BeamFunction {
                erlang_mod: None,
                name,
                abi,
            } if abi.evidence.is_none() => self
                .resolved_fun_info(node_id, name)
                .map_or_else(|| abi.clone(), |info| info.abi.clone()),
            ResolvedCodegenKind::BeamFunction { abi, .. }
            | ResolvedCodegenKind::ExternalFunction { abi, .. } => abi.clone(),
            ResolvedCodegenKind::Intrinsic { .. } => {
                unreachable!("an intrinsic has no calling convention")
            }
        }
    }

    /// Where the function `symbol` names is defined, as seen from the code
    /// being lowered, with the convention `abi`.
    pub(super) fn fn_ref(&self, symbol: &ResolvedSymbol, abi: CallableAbi) -> FnRef {
        let source = symbol.source_module.as_deref();
        let foreign = source != Some(self.current_source_module.as_str());
        let (module, name) = match &symbol.kind {
            ResolvedCodegenKind::BeamFunction {
                erlang_mod: Some(module),
                name,
                ..
            } => (Some(module.clone()), name.clone()),
            // An external function of another module is called through its
            // Saga wrapper, except from an inlined handler of that module,
            // which calls the Erlang function itself.
            ResolvedCodegenKind::ExternalFunction {
                erlang_mod,
                name,
                target_erlang_mod,
                target_name,
                ..
            } if foreign => {
                if self.current_handler_source_module.as_deref() == source {
                    (Some(target_erlang_mod.clone()), target_name.clone())
                } else {
                    (Some(erlang_mod.clone()), name.clone())
                }
            }
            ResolvedCodegenKind::ExternalFunction { name, .. }
            | ResolvedCodegenKind::BeamFunction { name, .. } => {
                self.module_function(source, name, abi.expanded_arity())
            }
            ResolvedCodegenKind::Intrinsic { .. } => {
                unreachable!("an intrinsic is not a function of a module")
            }
        };
        FnRef { module, name, abi }
    }

    /// The function `name` of the Saga module `source` (the module being
    /// emitted when `None`).
    pub(super) fn module_function(
        &self,
        source: Option<&str>,
        name: &str,
        arity: usize,
    ) -> (Option<String>, String) {
        match source.filter(|source| *source != self.current_source_module) {
            Some(source) => {
                let (module, name) = self
                    .imported_handler_external_target(source, name, arity)
                    .unwrap_or_else(|| (Self::module_name_to_erlang(source), name.to_string()));
                (Some(module), name)
            }
            None => (None, name.to_string()),
        }
    }
}

/// The head of an application chain and its arguments, in order.
pub(super) fn app_head_and_args(expr: &Expr) -> (&Expr, Vec<&Expr>) {
    let mut args = Vec::new();
    let mut head = expr;
    while let ExprKind::App { func, arg } = &head.kind {
        args.push(arg.as_ref());
        head = func.as_ref();
    }
    args.reverse();
    (head, args)
}
