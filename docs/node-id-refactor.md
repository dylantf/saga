# Node ID Refactor

## Motivation

AST nodes are currently identified by `Span` (source location). This is used to key evidence in the elaborator (`HashMap<Span, Vec<TraitEvidence>>`) and type info for LSP (`HashMap<Span, Type>`). Spans are not unique identifiers -- two expressions can share a span (desugaring, derived code), and the elaborator has to carefully pick "the right span" to look up evidence (e.g. using `func.span()` instead of the `App`'s span). This coupling is fragile and a recurring source of subtle bugs.

## Design

Add a monotonic `NodeId(u32)` to every `Expr` variant, allocated by the parser. This gives every expression a stable, unique identity that downstream passes can use as a key.

Side tables on `Checker` replace span-keyed maps:
- `evidence_at: HashMap<NodeId, Vec<TraitEvidence>>` (evidence for elaboration)
- `type_at: HashMap<NodeId, Type>` (replaces `type_at_span`, used by LSP)
- Future: `effects_at`, `source_map: HashMap<NodeId, Span>` if spans are ever decoupled from AST nodes

The elaborator keys on `NodeId` instead of `Span`. All "use the Var's span not the App's span" heuristics become "use the node ID", which is unambiguous.

## Migration phases

### Phase 1 + 4: Add NodeId to Expr, decouple span from variants [DONE]

- `Expr` is now a struct: `{ id: NodeId, span: Span, kind: ExprKind }`.
- The old `enum Expr` is renamed to `enum ExprKind`, with `span` removed from all variants.
- `NodeId(u32)` allocated by the parser (starting at 1; 0 is reserved for synthetic nodes).
- `Expr::synth(span, kind)` creates synthetic nodes (elaboration, derive, normalize).
- `PartialEq` on `Expr` compares `kind` only (span and id are metadata, not identity).

### Phase 2: Switch evidence to NodeId [DONE]

- `TraitEvidence.span` replaced with `TraitEvidence.node_id`.
- `pending_constraints` is now `(String, Type, Span, NodeId)` -- span kept for error messages, node_id for evidence keying.
- Elaborator uses `evidence_by_node: HashMap<NodeId, Vec<TraitEvidence>>` instead of `evidence_by_span`.
- `resolve_dict` and `try_inline_tuple_show` take `NodeId` instead of `Span` for lookup.
- All call sites pass `expr.id` or `func.id` -- the "use the Var's span not the App's span" heuristic is now "use the Var's node ID", which is unambiguous.

### Phase 3: Migrate type_at to NodeId [DONE]

- Split into two maps: `type_at_node: HashMap<NodeId, Type>` for Expr nodes, `type_at_span: HashMap<Span, Type>` for Pat bindings (which don't have NodeIds).
- `record_type(node_id, ty)` for expressions, `record_type_at_span(span, ty)` for patterns.
- LSP `find_name_at_offset` returns `Option<NodeId>` alongside name/span; `type_at_name` tries node ID first, falls back to span.
- `CheckResult` exposes `type_at_node()` and `type_at_span()` lookup methods.

### Phase 4: Decouple spans from Expr [DONE - merged into Phase 1]

Completed as part of Phase 1. Span lives on the `Expr` struct, not in `ExprKind` variants.
