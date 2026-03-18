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

### Phase 2: Switch evidence to NodeId

- `TraitEvidence` keyed by `NodeId` instead of `Span`.
- Checker records evidence by node ID; elaborator looks up by node ID.
- Delete all span-matching heuristics in `elaborate.rs`.
- `pending_constraints` becomes `(String, Type, Span, NodeId)` so resolved evidence gets stored under the right node.

### Phase 3: Migrate type_at_span to NodeId

- `type_at_span: HashMap<Span, Type>` becomes `type_at: HashMap<NodeId, Type>`.
- LSP lookups go through a `NodeId` -> `Type` table (resolve span to node via a reverse map or AST walk).
- Improves LSP accuracy for overlapping spans.

### Phase 4: Decouple spans from Expr [DONE - merged into Phase 1]

Completed as part of Phase 1. Span lives on the `Expr` struct, not in `ExprKind` variants.
