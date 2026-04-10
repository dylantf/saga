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

A simple ADT wrapping a decode function. Decoders are pure values — same input
always produces the same output, no side effects.

```
pub type Decoder a =
  | Decoder (Dynamic -> Result a DecodeError)
```

There is intentionally no fallback/default value carried with the decoder.
Decoding is fail-fast at the call site; for accumulating multi-field
validation, use the `Validate` effect pattern (see
`examples/20-validation-applicative.dy`) on top of already-decoded values.

### Primitive decoders

Exposed as `val` bindings (not functions — `Decoder` is data, not a computation):

```
pub val string = Decoder decode_string_raw
pub val int = Decoder decode_int_raw
pub val float = Decoder decode_float_raw
pub val bool = Decoder decode_bool_raw
```

Each `decode_*_raw` function is an `@external` backed by a 2-line Erlang guard
check in the bridge file.

### Applying a decoder

Three pure functions cover the common shapes. None of them are effects —
decoding the same `Dynamic` always yields the same `Result`, so there's
nothing for the effect system to track.

```
pub fun decode : Decoder a -> Dynamic -> Result a DecodeError
pub fun decode_field : String -> Decoder a -> Dynamic -> Result a DecodeError
pub fun decode_element : Int -> Decoder a -> Dynamic -> Result a DecodeError
```

`decode` runs a decoder against a `Dynamic` directly. `decode_field` looks up
a key in a map-like Dynamic and decodes its value. `decode_element` does the
same for tuple/list elements by index.

For chaining multiple decode operations together, use `do...else`:

```
let result = do {
  Ok(name) <- decode_field "name" string data
  Ok(age)  <- decode_field "age" int data
  Ok(User { name, age })
} else {
  Err(e) -> Err(e)
}
```

The first failing field aborts the chain and returns its `DecodeError`. This
is fail-fast by design — see "Fail-fast vs. accumulation" below for the
rationale.

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
import Std.Dynamic (Dynamic, decode_field, from_erlang, string, int)

@external("erlang", "pgo", "query")
fun raw_query : String -> List Dynamic -> Dynamic

pub fun get_user : Int -> Result User DbError
get_user id = {
  let raw = raw_query "SELECT name, age FROM users WHERE id = $1" [from_erlang id]
  do {
    Ok(name) <- decode_field "name" string raw
    Ok(age)  <- decode_field "age" int raw
    Ok(User { name, age })
  } else {
    Err(e) -> Err(to_db_error e)
  }
}
```

The application developer just calls `get_user` — no Dynamic, no decoders.

### Tuple/positional decoding (e.g. database rows)

For positional decoding where the cursor needs to advance per call (database
rows are the canonical case), wrap `decode_element` in a small effect at the
library boundary so callers don't write indices manually. See the saga_pgo
`PgRow` effect for a working example. The pattern is a state-passing handler
that threads the cursor through `resume`:

```
pub effect PgRow {
  fun column : Decoder a -> a
}

# Library-internal: handle PgRow against a row Dynamic by threading
# a cursor and calling decode_element directly.
fun run_row : Dynamic -> (Unit -> a needs {PgRow}) -> Result a DecodeError
run_row row body = {
  let cursored = body () with {
    column dec = fun cursor -> {
      case decode_element cursor dec row {
        Ok(v) -> (resume v) (cursor + 1)
        Err(e) -> Err(e)
      }
    }
    return value = fun _ -> Ok(value)
  }
  cursored 0
}
```

User code then writes:

```
fun () -> User {
  id: PgRow.column! uuid,
  name: PgRow.column! string,
  age: PgRow.column! int,
}
```

with no indices and direct record construction. This pattern is **library
machinery**, not something `Std.Dynamic` provides — different positional
sources (SQL rows, binary protocols, etc.) want different cursor semantics.

## Fail-fast vs. accumulation

`Std.Dynamic` is intentionally fail-fast: the first decode error aborts the
chain. This is a deliberate design choice, not a limitation of the
implementation. The reasoning:

1. **Decode errors are usually programmer errors, not user input errors.** A
   wrong-type column or a missing field means the schema and the code are out
   of sync. Knowing that "and the next three fields were also wrong" doesn't
   help you fix it any faster — you fix the schema once and all the errors
   disappear together.

2. **Accumulation requires placeholder values.** To resume past a failed
   decode and keep going, the continuation needs a value of the right type.
   The only sources of one are (a) per-type defaults baked into the decoder
   (which forces every type to have an arbitrary "zero", surfacing as
   user-visible API noise like `uuid`'s default of all-zeros) or (b) unsafe
   sentinels that can crash if observed by intervening pure code. Neither is
   acceptable for the common case.

3. **Pure functions compose better.** With `decode`/`decode_field`/
   `decode_element` as plain functions returning `Result`, users can chain
   them with `do...else`, `Result.and_then`, `Result.map`, or whatever else
   they already know. No special handlers, no CPS, no continuation reshape
   gotchas.

When accumulation **is** the right shape — typically form validation or
multi-field business-rule checking on data that has already been decoded into
typed values — the `Validate` effect pattern from
`examples/20-validation-applicative.dy` handles it cleanly without needing
placeholder defaults. The trick there is that validators take typed values as
arguments and return `Unit`, so there's never a continuation that needs a
value of an arbitrary type. Two-phase: decode fail-fast first, then validate
accumulating second.

## Why pure functions, not an effect

An earlier iteration used a `Decode` effect with `Dynamic.run` as the runner.
This was removed because:

1. **Decoding is deterministic.** `decode dec dyn` produces the same `Result`
   every time it's called with the same arguments — there's no clock, no
   randomness, no I/O, no observable side effect. The Erlang term may have
   come from an effectful operation originally (a query, a parse), but
   inspecting it after the fact is pure. Effects exist to track operations
   whose semantics depend on context the caller can't see; decoding has no
   such context.

2. **The accumulation use case didn't justify the cost.** The original
   motivation for the effect was error accumulation (many fields, one report
   of all the failures). But accumulation requires placeholder defaults
   (point 2 above), and the placeholders force every decoder type to carry an
   arbitrary "zero" value. Once we accepted fail-fast as the right default,
   the effect added CPS overhead and a handler for no benefit.

3. **Stacking handlers is fragile.** The previous design also exposed a sharp
   edge: a library handler that wrapped `Dynamic.run`'s computation with its
   own state-passing transform (e.g. a row-cursor handler) would silently
   mismatch continuation reshape types at runtime. The handler stack
   typechecked but the continuations had incompatible wrapper types and
   crashed with `function_clause` errors. Removing the effect removes the
   surface area for this class of bug.

The Gleam comparison: Gleam uses an opaque `Decoder(t)` type with
continuation-passing combinators (`use name <- decode.field("name",
decode.string)`). That works fine but requires the `(value, errors)` tuple
to be baked into every decoder, which is essentially the same trade-off we
declined here. dylang's `Decoder` is just `Dynamic -> Result a DecodeError`,
and chaining is whatever Result-combinator pattern the user prefers.

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

No compiler changes were needed for the types -- opaque types and parametric
ADTs all worked with existing infrastructure.

## Use cases

- **Erlang/Elixir library interop**: return values from FFI calls
- **ETS**: untyped term storage
- **Process messages from non-dylang processes**: unknown message shapes
- **Database drivers**: rows as Erlang tuples/lists
- **JSON/msgpack/ETF**: after initial parse, walk the resulting BEAM terms
