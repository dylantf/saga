# FFI Design

## Overview

FFI to Erlang via `@external` annotations, following Gleam's model but without constraining our ADT representation.

## Syntax

```
@external("erlang", "lists", "reverse")
fun reverse (list: List a) -> List a
```

Three string args: target, module, function. Type signature is mandatory and trusted by the compiler (no inference, no runtime validation).

## Compiler work

Minimal:
1. Parse `@external` annotation
2. Require full type signature (params + return)
3. Emit a direct call: `call 'lists':'reverse'(List)`

No special codegen beyond a qualified foreign call.

## Representation alignment

Compile `Result` and `Maybe` constructors to match Erlang conventions:

| Constructor | Current codegen | New codegen |
|-------------|----------------|-------------|
| `Ok(v)`     | `{'Ok', v}`    | `{ok, v}`   |
| `Err(e)`    | `{'Err', e}`   | `{error, e}`|
| `Some(v)`   | `{'Some', v}`  | `v` (bare)  |
| `None`      | `{'None'}`     | `undefined` |

`Maybe` maps to Erlang's `V | undefined` convention. `Some(v)` is just the bare value with no wrapping tuple. `None` is the atom `undefined`. This matches how Erlang/Elixir handle optionality (process dictionaries, ETS lookups, maps:get, etc.).

`Result` maps to Erlang's `{ok, V} | {error, E}` convention directly.

**Pattern matching implications:** `case x of Some(v) -> ... | None -> ...` compiles to:
```erlang
case X of
  'undefined' -> ...   % None branch
  V -> ...             % Some(v) branch, V is the unwrapped value
end
```
The `None`/`undefined` arm must come first (specific before wildcard).

## FFI categories

**Direct FFI (no shim needed):**
- Functions returning plain values: ints, floats, strings, atoms, lists, maps
- Functions returning `{ok, V} | {error, E}` (if Result matches)
- Functions returning `true | false` (Bool already compiles to atoms)

**Direct FFI for Maybe (V | undefined):**
- Functions returning `V | undefined` now work directly since `Maybe` compiles to `V | undefined`

**Needs a .erl shim:**
- Functions returning `V | false` (e.g. `lists:keyfind`)
- Anything with a truly ad-hoc return convention

**Shim example:**
```erlang
% dylang_ffi.erl
keyfind(Key, List) ->
    case lists:keyfind(Key, 1, List) of
        false -> undefined;
        Tuple -> Tuple
    end.
```

```
@external("erlang", "dylang_ffi", "keyfind")
fun keyfind (key: k) (list: List (k, v)) -> Maybe (k, v)
```

## Open questions

- Do we want `@external` on the same line or as a separate declaration?
- Should we support `@external("javascript", ...)` from day one for a future JS backend?
- How to handle Erlang functions with variable arity (e.g. `io:format`)?
