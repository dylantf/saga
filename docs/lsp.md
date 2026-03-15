# LSP Implementation Plan

## Architecture

A `dylang-lsp` binary that speaks JSON-RPC over stdin/stdout. The VSCode extension
(already in `editors/vscode/`) points to this binary. Use `tower-lsp` or `lsp-server`
Rust crate for protocol boilerplate.

On each file save: lex, parse, typecheck, report diagnostics. On hover/completion:
look up the position in the AST, query the typechecker's env.

Prerequisite: a line index utility that maps byte offsets (Span) to line:column
positions, since the LSP protocol uses line:column.

## Phase 1: Immediately useful

- `textDocument/diagnostic` -- red squiggles on type errors. Run the typechecker,
  convert TypeError spans to LSP ranges, report as diagnostics.
- `textDocument/hover` -- show type on hover. Find the AST node at the cursor
  position, look up its type in the checker's env, format as a string.
- `textDocument/completion` -- suggest variables, constructors, effect ops in scope.
  Query the checker's env, constructors map, and effect ops at the cursor position.

## Phase 2: Navigation

- `textDocument/definition` -- go-to-definition. Needs source location tracking on
  definitions (function defs, type defs, effect defs). The AST already has Span on
  most nodes.
- `textDocument/references` -- find all usages of a symbol across the project.
- `textDocument/signatureHelp` -- show function signature while typing arguments.

## Phase 3: Polish

- `textDocument/formatting` -- auto-format (requires building a formatter first).
- `textDocument/codeAction` -- quick fixes: add missing import, add `needs` clause,
  add missing pattern arm, wrap with handler.
- `textDocument/rename` -- rename symbol across files.

## What the typechecker already provides

- `env`: variable name -> Scheme (types for hover)
- `constructors`: constructor name -> Scheme (completion)
- `effects`: effect name -> ops (completion for effect ops)
- `handlers`: handler name -> info (completion for `with`)
- `traits`: trait name -> methods (completion)
- `TypeError` with `Span` (diagnostics)
- `Span` on every AST node (position mapping)

## Incremental checking

Phase 1 can do full re-check on save. For larger projects, incremental checking
would re-check only changed files and their dependents. The module system's
dependency graph (from imports) enables this. Not needed initially.
