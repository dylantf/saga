# Formatter Audit

## Priority fixes

- [x] **Merge the two `format_handler_arm`s** — `decl.rs:443` and `expr.rs:569` are diverging copies. The `expr.rs` version handles zero-arg ops with explicit `()`, the `decl.rs` version does not. Should be a single function in `helpers.rs`.

- [x] **Deduplicate `escape_string`** — `helpers.rs:28` and `expr.rs:648` (`escape_interp_string`) are identical. Should be one function.

- [x] **Extract the braced-body loop in `decl.rs`** — `format_record_def`, `format_effect_def`, `format_trait_def`, `format_handler_def`, and `format_impl_def` all repeat the same `hardline + trivia + content + trailing` loop with dangling trivia and `nest(2, body) + hardline + "}"`. Could share `format_braced_body` from `expr.rs` or a generalized version of it.

- [ ] **No trivia support on binop/chain operands** — `BinOp` (`+`, `<>`, etc.) uses plain `Expr` operands with no trivia slots at all. `PipeBack`/`ComposeForward`/`ComposeBack` (`<|`, `>>`, `<<`) have `Annotated<Expr>` segments in the AST but the parser always uses `Annotated::bare` (empty trivia). Only `Pipe` (`|>`) attaches trivia to segments. This means comments interleaved in multi-line binop or compose chains will be lost or misattached. Needs parser-level work to attach trivia to operands, then formatter updates to emit it.

## Lower priority

- [x] **Parallel `format_type_expr` and `format_type_expr_str`** — `type_expr.rs` has two complete type formatters that implement the same logic independently. The `_str` version exists because `format_effect_ref_str` and `format_where_clause` build strings. These could build `Doc` values instead and render to `String` when needed.

- [x] **Doc-comment + header preamble duplicated across all defs** — Six definition formatters all start with the same `if !doc.is_empty() { ... }` block and build a header string with `pub ` prefix and type params.

- [x] **`format_needs` has an unreachable early-return** — `type_expr.rs:100-102` checks if effects are empty, but every call site already guards on the same condition. Not a bug, but obscures the contract.

- [x] **`format_comma_list` doesn't handle empty lists** — An empty record `Foo {}` would render with odd spacing/trailing comma in break mode.

- [x] **Interp string expression rendering uses magic width** — `expr.rs:635` and `expr.rs:691` use `pretty(10000, &doc)` to force single-line. Should be a named constant or a dedicated "render flat" API.

- [~] **`sort_imports` allocates unnecessarily** — Clones the entire decls slice then clones individual imports again. Not worth optimizing: runs once per file with a handful of imports, and avoiding the clones would require index-based sorting that adds complexity for negligible gain.
