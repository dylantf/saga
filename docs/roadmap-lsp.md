# LSP Roadmap

## Architecture

`dylang-lsp` binary speaks JSON-RPC over stdin/stdout. VSCode extension in `editors/vscode/`
launches it. Built on `tower-lsp`. Per-project checker caching, `snapshot()` pattern for
lock-free hover/goto/completion.

## Phase 1: Core

- [x] Diagnostics -- red squiggles on type errors
- [x] Multi-error reporting (no cascading noise via `Type::Error`)
- [x] Pretty type variables in errors (`Tuple a b` not `Tuple ?343 ?344`)
- [x] Hover -- show type on hover (uses annotations when available, includes labels)
- [x] Hover -- trait constraints shown (`a -> Unit where {a: Show}`)
- [x] Go-to-definition -- local (same file)
- [x] Go-to-definition -- cross-module (user modules, not stdlib)
- [x] Go-to-definition -- module name click opens module file
- [x] Go-to-definition -- effect calls (two-hop: `op!` → handler arm, handler arm → effect op definition)
- [x] Completion -- variables, functions, constructors, effects, handlers, keywords
- [x] Completion -- type info in detail field with constraints
- [x] Module support -- imports resolve, module map per project root
- [x] Restart command in VSCode palette
- [x] Deadlock prevention (snapshot cloning, no lock held across async)
- [x] Panic recovery in check_file

## Phase 2: Type information gaps

- [x] Hover on local variables (let bindings inside function bodies)
- [x] Hover on function parameters
- [x] Hover on pattern-bound variables (case arms, lambda params)
- [x] Per-expression type storage (`HashMap<Span, Type>`) in typechecker
- [x] Resolved types at usage site (show `Int -> Int` not `a -> a` when hovering a call site of a polymorphic function; currently `type_at_name` checks FunAnnotation first and returns the generic type)

## Phase 3: Navigation

- [x] Find all references
- [x] Signature help (show param names/types while typing function arguments)
- [x] Document symbols (outline view)

## Phase 3.5: Type-position navigation

- [x] Go-to-definition on type/effect names in annotations and handler `for` clauses
- [x] Spans on all AST nodes (TypeExpr, name_span on TypeDef/RecordDef/EffectDef/TraitDef)
- [x] Code action -- add missing handler arms (single + bulk)
- [ ] Find references for type/effect names (handlers, needs clauses, annotations that reference a type/effect)
- [ ] Hover on type names (show type definition summary for user-defined types)
- [ ] Autocomplete for record field names

## Phase 4: Editing support

- [ ] Code actions -- add missing import
- [ ] Code actions -- add `needs` clause
- [ ] Code actions -- add missing pattern arm
- [x] Code actions -- add missing handler methods
- [ ] Code actions -- add missing trait impl methods
- [ ] Rename symbol (local scope)
- [ ] Rename symbol (cross-file)

## Phase 5: Polish

- [ ] Formatter (`textDocument/formatting`)
- [ ] Incremental checking (re-check only changed files + dependents)
- [ ] Workspace support (multi-root projects)
- [ ] Semantic tokens (richer syntax highlighting from type info)

## Known issues

- Completion is not context-aware: shows functions when typing a type name and vice versa. Currently we just filter out qualified names (`String.contains` etc.) from the default list, but ideally completion should know if you're in type position (after `:`, `->`) vs expression position (after `=`, inside blocks) and show only relevant items.
- No dot-completion for module-qualified names yet (`MathLib.` should show exports)

## Maybe:

- [ ] Go-to-definition for stdlib types/functions (show source or signature)
      Not sure if we'll ship the stdlib in a readable format. We have hover types already + docs.
