# Suggested Handlers

## Problem

When an effect propagates up to `main` (or any function missing a handler), the error message can't suggest which handler to use. The user sees:

```
`main` uses effects {Stdio} but no handler is provided.
```

But doesn't know that `console` is the handler they want.

## Proposal: `@suggested_handler` annotation

Attach a `@suggested_handler` annotation to an effect definition, pointing at the default/recommended handler:

```
@suggested_handler(console)
pub effect Stdio {
  fun print : String -> Unit
  fun eprint : String -> Unit
  fun read : String -> String
}
```

## Compiler behavior

When the "no handler provided" error fires for `main`, look up the unhandled effects. If any have a `@suggested_handler` annotation, include the handler name in the error message:

```
`main` uses effects {Stdio} but no handler is provided. Use `with` to handle them, e.g.:

  main () = {
    ...
  } with console
```

For multiple unhandled effects with suggestions:

```
  } with { console, fs }
```

## LSP integration

The annotation attaches to the effect's AST node, so the LSP can:

- **Quick-fix code action**: "Add `with console`" as a one-click fix when `Stdio` is unhandled
- **Hover info**: Show the suggested handler when hovering over an effect name
- **Completion**: When typing `with`, suggest handlers for the unhandled effects in scope

## Scope

- Works for stdlib effects (`Stdio` → `console`, `File` → `fs`, etc.)
- Works for user-defined effects — anyone can annotate their own effects
- No hardcoded knowledge in the compiler; entirely driven by annotations
