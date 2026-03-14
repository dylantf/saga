# @external FFI Support

## Context

The language targets BEAM and needs interop with Erlang/OTP. Currently, builtin functions (Dict.*, Int.to_float, etc.) have type signatures hardcoded in Rust and BIF mappings hardcoded in codegen. This change adds `@external` syntax so FFI functions are declared in `.dy` files. The compiler trusts the type annotation and emits a direct call. No auto-marshaling.

To make this work seamlessly, `Result` and `Maybe` constructors must match Erlang conventions in their runtime representation. This is a prerequisite change.

Full design doc: `docs/ffi-design.md`

## Part 1: ADT representation alignment

Change how `Result` and `Maybe` compile to match Erlang conventions:

| Constructor | Current | New |
|---|---|---|
| `Ok(v)` | `{'Ok', v}` | `{ok, v}` |
| `Err(e)` | `{'Err', e}` | `{error, e}` |
| `Some(v)` | `{'Some', v}` | `v` (bare value) |
| `None` | `{'None'}` | `undefined` |

### Files
- `src/codegen/lower/mod.rs` - constructor lowering, pattern matching
- `src/codegen/lower/exprs.rs` - constructor call lowering
- `src/codegen/lower/pats.rs` - pattern lowering for case arms
- `src/codegen/tests.rs` - update all tests referencing `'Ok'`, `'Err'`, `'Some'`, `'None'`
- `src/elaborate.rs` - builtin Show methods reference these atoms (Int.parse wrapping, Dict.get wrapping, etc.)

### Key changes
- Constructor atoms for Ok/Err/Some/None need special-casing (lowercase, and `Err` -> `error` not `err`)
- `Some(v)` no longer wraps in a tuple, it's just the bare value
- `None` is the atom `undefined`, not a tuple
- Pattern matching on Maybe: `None` matches `undefined`, `Some(v)` matches anything else (wildcard) -- `undefined` arm must come first
- Pattern matching on Result: `Ok(v)` matches `{ok, V}`, `Err(e)` matches `{error, E}` -- standard tuple patterns with lowercase atoms
- All existing codegen for Dict.get (maps:find wrapping), Int.parse, Float.parse need updating since they construct Some/None

### Verification
- `cargo test` -- all tests pass after updating assertions
- Manually inspect emitted Core Erlang for Maybe/Result construction and pattern matching

## Part 2: @external syntax

### Syntax
```
@external("erlang", "lists", "reverse")
fun reverse (list: List a) -> List a
```

### Files
- `src/token.rs` - add `At` token
- `src/lexer.rs` - emit `At` when `@` not followed by `"` (raw string)
- `src/ast.rs` - add `Decl::ExternalFun { runtime, module, func, name, params, return_type, effects, where_clause, span }`
- `src/parser/decl.rs` - parse `@external(...)` + `fun` signature (no body). Reject `pub @external` (or allow it, TBD per open question in design doc)
- `src/typechecker/check_decl.rs` - register type scheme from annotation (reuse annotation resolution logic)
- `src/elaborate.rs` - when call targets an external function, emit `Expr::ForeignCall`
- `src/codegen/lower/mod.rs` - `Expr::ForeignCall` already lowers correctly (lines 1001-1020). Skip `ExternalFun` decls (no body to emit). Remove `lower_builtin_dict`, `lower_builtin_list`, `lower_builtin_conversion` as mappings move to .dy files.
- `src/typechecker/mod.rs` - remove hardcoded Dict/conversion builtin schemes (lines ~711-1030)

### Prelude files
- Create `src/prelude/Std/Dict.dy` with @external declarations for maps:* BIFs
- Rewrite `src/prelude/Std/List.dy` with @external declarations for lists:*/erlang:* BIFs
- Create `src/prelude/Std/Int.dy` and `src/prelude/Std/Float.dy` for conversion builtins
- `foldl` wrapper needed (arg swap: language f(acc, elem) vs erlang f(elem, acc))

### Verification
- `cargo test`
- Parser tests for @external syntax
- Typechecker tests for external function schemes
- Codegen tests for direct BIF emission
- End-to-end: example program calling OTP functions via @external
