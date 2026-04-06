# Dynamic Type — Safe BEAM Interop

## Problem

Data from outside the type system arrives as untyped Erlang terms: FFI calls,
ETS lookups, messages from non-dylang processes, database drivers, decoded
binary protocols. Without a safe bridge, you either trust the data blindly or
can't interop with the Erlang ecosystem.

## Audience

`Std.Dynamic` is an escape hatch for **library authors** wrapping Erlang
packages, not something application developers should reach for. The expected
layering:

```
Erlang lib (pgo, jason, etc.)
  ↓ @external returning Dynamic
Std.Dynamic (decoders)
  ↓ library author writes typed wrapper
Typed wrapper library (e.g. a Postgres or JSON lib)
  ↓ app developer uses this
Application code
```

Application developers should never see `Dynamic`. If they do, the library
wrapper is incomplete.

## Design

### Dynamic type

`Dynamic` is an opaque type wrapping a raw Erlang term:

```
opaque type Dynamic = Dynamic
```

FFI functions can return `Dynamic` directly — since `@external` trusts the type
signature, no bridge file is needed:

```
@external("erlang", "pgo", "query")
fun raw_query : String -> List Dynamic -> Dynamic
```

### DecodeError

Single-variant ADT with positional fields: expected type, found type, path.

```
pub type DecodeError =
  | DecodeError String String (List String)
  deriving (Eq)
```

### Decoder type

A simple ADT pairing a decode function with a placeholder/default value. The
placeholder is used during error accumulation — when a field fails to decode,
the handler resumes with the default so subsequent decoders can keep running.

```
pub type Decoder a =
  | Decoder (Dynamic -> Result a DecodeError) a
```

### Primitive decoders

Exposed as `val` bindings (not functions — `Decoder` is data, not a computation):

```
pub val string = Decoder decode_string_raw ""
pub val int = Decoder decode_int_raw 0
pub val float = Decoder decode_float_raw 0.0
pub val bool = Decoder decode_bool_raw False
```

Each `decode_*_raw` function is an `@external` backed by a 2-line Erlang guard
check in the bridge file.

### Decode effect

Decoding uses the effect system for composition and error accumulation. The
`Decode` effect has two polymorphic operations:

```
pub effect Decode {
  fun decode_field : String -> Decoder a -> a
  fun decode_element : Int -> Decoder a -> a
}
```

The `a` is a free type variable, freshened per call site — so each `decode_field!`
can decode a different type. Same pattern as `Fail`'s `fun fail : e -> a`.

### Error accumulation via handler

`Dynamic.run` provides the handler. It uses the same continuation trick as
`run_body` in `Std.Test` and the `collecting` handler in
`examples/20-validation-applicative.dy`:

```
pub fun run : Dynamic -> (Unit -> a needs {Decode}) -> Result a (List DecodeError)
run data f = {
  let (value, errors) = f () with {
    decode_field name dec = {
      let result = case raw_field_lookup name data {
        Ok dyn -> run_decoder dec dyn
        Err e -> Err e
      }
      case result {
        Ok decoded -> {
          let (v, errs) = resume decoded
          (v, errs)
        }
        Err e -> {
          let (v, errs) = resume (decoder_default dec)
          (v, e :: errs)
        }
      }
    }
    # decode_element is identical but uses element_lookup instead
    return v = (v, [])
  }
  case errors {
    [] -> Ok value
    _ -> Err errors
  }
}
```

On success: resume with the decoded value, thread through accumulated errors.
On failure: resume with the placeholder, prepend the error. Every field runs
regardless of earlier failures. At the end, empty errors -> `Ok`, otherwise
`Err` with all collected errors.

### Combinators

```
pub fun list_of : Decoder a -> Decoder (List a)
pub fun optional : Decoder a -> Decoder (Maybe a)
```

### Utilities

```
pub fun from_erlang : a -> Dynamic    # wrap any BEAM term (identity at runtime)
pub fun classify : Dynamic -> String  # human-readable type name for errors
```

## Usage

### Library author wrapping an Erlang package

```
import Std.Dynamic as Dynamic
import Std.Dynamic (Dynamic, Decode, from_erlang, string, int)

@external("erlang", "pgo", "query")
fun raw_query : String -> List Dynamic -> Dynamic

pub fun get_user : Int -> Result User DbError
get_user id = {
  let raw = raw_query "SELECT name, age FROM users WHERE id = $1" [from_erlang id]
  Dynamic.run raw (fun () -> {
    let name = Decode.decode_field! "name" string
    let age = Decode.decode_field! "age" int
    User { name, age }
  })
  |> Result.map_err to_db_error
}
```

The application developer just calls `get_user` — no Dynamic, no decoders.

### Error accumulation

If both fields have wrong types, you get both errors back:

```
let result = Dynamic.run bad_data (fun () -> {
  let name = Decode.decode_field! "name" string
  let age = Decode.decode_field! "age" int
  (name, age)
})
# Err([DecodeError("String", "Int", []), DecodeError("Int", "String", [])])
```

### Tuple/positional decoding (e.g. database rows)

```
let result = Dynamic.run row (fun () -> {
  let name = Decode.decode_element! 0 string
  let age = Decode.decode_element! 1 int
  User { name, age }
})
```

## Why an effect, not an opaque Decoder type

Gleam uses an opaque `Decoder(t)` type with continuation-passing combinators
(`use name <- decode.field("name", decode.string)`). We considered this but
chose an effect-based approach because:

1. **Flat syntax** — `let name = decode_field! "name" string` is a normal `let`
   binding with `!`. No nesting, no `use` syntax, no `mapN` combinators.
2. **Error accumulation via existing machinery** — the handler continuation trick
   (`resume` with a placeholder, collect errors) is the same pattern already used
   in `Std.Test` and the validation example. No new abstraction needed.
3. **Idiomatic to the language** — effects are dylang's mechanism for this kind
   of contextual computation. Using them here means library authors already know
   how it works.

The Gleam approach bakes error accumulation into the `Decoder` type itself
(always returns `(value, errors)` tuple). Our approach keeps `Decoder` simple
(just a function + default) and lets the effect handler manage accumulation.

## Implementation

### Erlang bridge (`std_dynamic_bridge.erl`)

~100 lines. Exports:

- `decode_string/1`, `decode_int/1`, `decode_float/1`, `decode_bool/1` — guard checks
- `field_lookup/2` — `maps:find/2`, error if not a map
- `element_lookup/2` — `erlang:element/2` for tuples, list nth for lists (0-indexed)
- `decode_list/2` — iterate list with decoder, prepend index to error path
- `decode_optional/2` — nil/undefined/null -> `{nothing}`, otherwise inner decoder
- `classify/1` — guard chain -> type name string
- `from_erlang/1` — identity

### Compiler registration

- `Std.Dynamic` added to `BUILTIN_MODULES` in `check_module.rs`
- `std_dynamic_bridge.erl` added to `stdlib_bridge_files()` in `build.rs`

No compiler changes were needed for the types or effects — opaque types,
polymorphic effect operations, and inline handlers all worked with existing
infrastructure.

### Bug fix: qualified calls with effectful callbacks

During implementation we discovered that `lower_qualified_call` in
`src/codegen/lower/mod.rs` did not handle `param_absorbed_effects` — so calling
`Dynamic.run` (or any cross-module function taking an effectful callback) via
qualified syntax would panic. Fixed by adding the same `lambda_effect_context`
setup that the unqualified call path already had.

## Use cases

- **Erlang/Elixir library interop**: return values from FFI calls
- **ETS**: untyped term storage
- **Process messages from non-dylang processes**: unknown message shapes
- **Database drivers**: rows as Erlang tuples/lists
- **JSON/msgpack/ETF**: after initial parse, walk the resulting BEAM terms
