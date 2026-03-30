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

| Constructor | Current codegen | New codegen  |
| ----------- | --------------- | ------------ |
| `Ok(v)`     | `{'Ok', v}`     | `{ok, v}`    |
| `Err(e)`    | `{'Err', e}`    | `{error, e}` |
| `Just(v)`   | `{'Just', v}`   | `{just, v}`  |
| `None`      | `{'None'}`      | `{none}`     |

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

## Bridge files

When an `@external` call targets a module that doesn't exist in the Erlang standard library, you need a **bridge file**: a `.erl` file that implements the native side of the FFI.

### How bridge files are discovered

1. **Stdlib bridges** are embedded in the compiler binary via `include_str!` and written to the build directory automatically. These live in `src/stdlib/` with the naming convention `<Module>.bridge.erl` (e.g. `File.bridge.erl`).

2. **User/library bridges** are discovered by scanning the project root for `.erl` files (skipping `_build/` and `tests/`). Any `.erl` file found is copied to the build directory and compiled alongside the generated `.core` files.

### Writing a bridge file

The `-module(name)` in your `.erl` file must match the module name referenced in `@external`. For example:

```
# File.dy
@external("erlang", "dylang_file", "read_file")
fun read_file : (path: String) -> Result String String
```

```erlang
%% File.bridge.erl
-module(dylang_file).
-export([read_file/1]).

read_file(Path) ->
    case file:read_file(Path) of
        {ok, Bin} -> {ok, Bin};
        {error, Reason} -> {error, atom_to_binary(Reason)}
    end.
```

### Type representation conventions

Your bridge functions must return values that match how the compiler represents types at runtime on the BEAM:

| Type                         | BEAM representation      | Example                    |
| ---------------------------- | ------------------------ | -------------------------- |
| `Int`                        | Integer                  | `42`                       |
| `Float`                      | Float                    | `3.14`                     |
| `String`                     | Binary                   | `<<"hello">>`              |
| `Bool`                       | Atoms `true` / `false`   | `true`                     |
| `Unit`                       | Atom `unit`              | `unit`                     |
| `List a`                     | Erlang list              | `[1, 2, 3]`                |
| `(a, b)`                     | Tuple                    | `{1, <<"hi">>}`            |
| `Ok v`                       | `{ok, V}`                | `{ok, <<"contents">>}`     |
| `Err e`                      | `{error, E}`             | `{error, <<"not found">>}` |
| `Just v`                     | Bare value `V`           | `<<"hello">>`              |
| `Nothing`                    | Atom `undefined`         | `undefined`                |
| Custom variant `Foo x y`     | `{module_Foo, X, Y}`     | `{shapes_Circle, 5}`       |
| Custom nullary variant `Foo` | `{module_Foo}` (1-tuple) | `{std_file_NotFound}`      |

Key gotchas:

- `Err` maps to the atom `error`, not `err`
- `Nothing` / `None` is `undefined`, not `nil` or `none`
- `Just` / `Some` is the bare unwrapped value, no tuple wrapper
- `Unit` is the atom `unit`, not an empty tuple `{}`
- Custom ADT constructors use the module prefix: `MyVariant` in module `Foo` becomes `foo_MyVariant`
- Nullary custom constructors are still wrapped in a 1-tuple: `NotFound` becomes `{std_file_NotFound}`, not bare `std_file_NotFound`. This differs from prelude builtins like `True`/`False` which are bare atoms

## Open questions

- Do we want `@external` on the same line or as a separate declaration?
- Should we support `@external("javascript", ...)` from day one for a future JS backend?
- How to handle Erlang functions with variable arity (e.g. `io:format`)?
