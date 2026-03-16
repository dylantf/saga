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
- [x] Completion -- variables, functions, constructors, effects, handlers, keywords
- [x] Completion -- type info in detail field with constraints
- [x] Module support -- imports resolve, module map per project root
- [x] Restart command in VSCode palette
- [x] Deadlock prevention (snapshot cloning, no lock held across async)
- [x] Panic recovery in check_file

## Phase 2: Type information gaps

- [ ] Hover on local variables (let bindings inside function bodies)
- [ ] Hover on function parameters
- [ ] Hover on pattern-bound variables (case arms, lambda params)
- [ ] Per-expression type storage (`HashMap<Span, Type>`) in typechecker
- [ ] Resolved types at usage site (show `Int -> Unit` not `a -> Unit` for `print 42`)

## Phase 3: Navigation

- [ ] Go-to-definition for stdlib types/functions (show source or signature)
- [ ] Find all references
- [ ] Signature help (show param names/types while typing function arguments)
- [ ] Document symbols (outline view)

## Phase 4: Editing support

- [ ] Code actions -- add missing import
- [ ] Code actions -- add `needs` clause
- [ ] Code actions -- add missing pattern arm
- [ ] Rename symbol (local scope)
- [ ] Rename symbol (cross-file)

## Phase 5: Polish

- [ ] Formatter (`textDocument/formatting`)
- [ ] Incremental checking (re-check only changed files + dependents)
- [ ] Workspace support (multi-root projects)
- [ ] Semantic tokens (richer syntax highlighting from type info)

## Known issues

- Hover doesn't work on local variables inside function bodies (env is restored after checking)
- Completion shows all prelude names even when not relevant to context
- No dot-completion for module-qualified names yet (`MathLib.` should show exports)
