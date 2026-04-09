# Handler Bundling

## Motivation

Multi-effect handlers require implementing all arms in one place. This means
swapping environments (dev vs prod, test vs real) requires either:

1. Writing separate multi-effect handlers that duplicate bundling logic
2. Using multiple independent conditional bindings

```
# Without bundling: three separate conditionals
let logger = if prod then sentry_log else console_log
let db = if prod then postgres_db else sqlite_db
let http = if prod then real_http else mock_http
run_app () with { logger, db, http }

# Or: two multi-effect handlers with duplicated arms
handler prod_env for Log, Db, Http { ... }
handler dev_env for Log, Db, Http { ... }
```

Bundling lets you compose existing handlers into a single unit:

```
let prod = bundle { sentry_log, postgres_db, real_http }
let dev = bundle { console_log, sqlite_db, mock_http }

let env = if prod_mode then prod else dev
run_app () with env
```

## Semantics

A bundle composes independently-defined handlers into a single `Handler` value.

```
bundle { sentry_log, postgres_db, real_http }
# : Handler (Log, Db, Http)
```

### Needs merging

The bundle's `needs` is the union of all bundled handlers' needs:

```
handler sentry_log for Log needs {Http} { ... }
handler postgres_db for Db needs {Net} { ... }

bundle { sentry_log, postgres_db }
# : Handler (Log, Db)    needs {Http, Net}
```

### Order semantics

Bundle order should follow the same nested semantics as `with` blocks. If a
future `bundle {a, b}` is installed, it should behave like installing `a`
inside `b` in lexical order:

```
bundle { custom_log, full_env }
# custom_log handles Log first; other effects fall through to full_env
```

That keeps bundling aligned with:

```dy
expr with {custom_log, full_env}
```

rather than inventing a separate "last one wins" composition rule.

### Nesting

Bundles can include other bundles:

```
let base = bundle { console_log, sqlite_db }
let full = bundle { base, real_http }
```

## Open questions

### Syntax

Several options:

```
# Keyword
let env = bundle { sentry_log, postgres_db }

# Bare tuple (with already accepts multiple handlers)
let env = (sentry_log, postgres_db)

# No new syntax — just allow with to accept a list
let handlers = [sentry_log, postgres_db]
run_app () with handlers
```

`bundle { ... }` is the most explicit. Reusing tuple syntax may be confusing
since tuples have different semantics elsewhere.

### Inline arms in bundles

Should bundles allow mixing named handlers with inline arms?

```
let env = bundle {
  sentry_log,
  postgres_db,
  fail reason = Err(reason),    # inline arm in bundle?
}
```

This would make bundles and `with` blocks nearly identical in syntax. May be
cleaner to keep bundles as composition-only (named handlers and other bundles)
and leave inline arms to `with` blocks.

## Compilation

A bundle would compile to the same tuple-of-lambdas representation as a handler
binding. At `with` sites, the tuple would be destructured to extract
per-operation functions. Semantically it should be equivalent to manually
writing the same ordered handlers in a `with` block.
