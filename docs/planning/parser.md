# JSON Parser Library — Design Planning

Status: **planning**. No code yet. This document captures the full design discussion so it can be picked up later without rebuilding context.

## Problem

dylang needs a JSON parser. JSON is ubiquitous — almost every real application deals with it at some boundary (HTTP APIs, config files, messages, etc.). The questions this document addresses:

1. Where should the library live (stdlib vs package)?
2. What types does it expose?
3. How does it handle error accumulation (multiple bad fields at once)?
4. How do users decode nested records ergonomically?
5. What does the language need to add to support it?

## Audience & Layering

Two distinct audiences matter here:

- **Library authors** — people writing FFI wrappers around Erlang packages. They use `Std.Dynamic` and work with raw BEAM terms.
- **Application developers** — people decoding JSON into their domain types. They should never touch `Std.Dynamic`; they should use a typed parser library.

The JSON library is a *library author's product* that becomes the *application developer's tool*. It sits between `Std.Dynamic` and application code.

### The four-layer architecture

```
Layer 4: Application code
         (uses JSON package)

Layer 3: Domain libraries (JSON, Postgres, YAML, TOML, MessagePack, ...)
         opaque typed wrappers over Dynamic
         expose format-specific parsers and combinators

Layer 2: Std.Validation (optional, not in scope for v1)
         Generic Validator type, merge/map/and_then combinators
         parameterized over the source value type

Layer 1: Std.Dynamic
         FFI primitives: Dynamic type, raw type tests, field/element lookups
         audience: library authors only

Layer 0: Erlang interop (FFI)
         @external bindings, raw BEAM terms
```

**The core rule**: `Dynamic` should not appear in the public API of any layer-3 library. Each domain library defines its own opaque wrapper type (e.g. `Json.Value`) and keeps `Dynamic` as an implementation detail. Application code never imports `Std.Dynamic`.

This is a layering discipline, not a language-enforced rule. It should be documented (probably as an item in `docs/language-design.md`) so future library authors follow it.

## Why a Package, Not stdlib

The JSON library should be a **separate package**, installed alongside dylang like saga_pgo, not shipped in `Std.Json`.

**Reasons:**

1. **Keeps stdlib minimal.** stdlib should contain core types and the things you can't build without compiler support. JSON parsers are pure library code — no compiler cooperation needed.

2. **Sets the right precedent.** If JSON goes in stdlib, the next request is YAML, then TOML, then MessagePack, then Protobuf. Every format has the same justification. Drawing the line at zero (no format libraries in stdlib) keeps stdlib from bloating.

3. **Iteration speed.** A package can ship fixes and new features independently of the compiler. A stdlib library is locked to compiler release cadence.

4. **Multiple implementations are healthy.** With JSON as a package, someone can build `json_fast`, `json_streaming`, `json_strict`, etc. They coexist. Applications pick. If JSON is in stdlib, the stdlib version wins by inertia.

5. **JSON is not part of the language.** It's a 1999 serialization format unrelated to dylang's type system, effect system, or runtime model. Languages with small stdlibs (Rust, OCaml, Zig) don't ship JSON parsers. Languages with big stdlibs (Python, Go) do. dylang's stdlib leans toward the smaller side, and this is the natural place to draw the line.

6. **Package management already exists.** saga_pgo demonstrates the infrastructure (`project.toml`, `deps/`, `dylang.lock`, Hex integration) is in place. No barrier to treating JSON the same way.

## Core Types

### The opaque value type

```
opaque type Value = Value Dynamic
```

`Json.Value` is a newtype wrapper around `Dynamic`. Runtime-free (it's just a tag). The type discipline ensures:

- Users can't pass arbitrary FFI return values into a JSON parser
- Users can't accidentally mix JSON values with SQL rows or other Dynamic-backed types
- Library internals can still use `Std.Dynamic` operations by pattern-matching `Value dyn`

### The parser type

```
pub type Parser a = Parser (Value -> Result a (List ParseError))
```

A `Parser a` is a wrapped function from `Value` to either a typed value or a list of errors. The list-of-errors shape is what enables accumulation — multiple independent failures can be collected.

Key properties:
- **Pure.** A parser is a deterministic function. Same input always produces the same result.
- **Composable.** Parsers combine via `merge`, `map`, `and_then`, `field`, etc.
- **No placeholder values.** Because accumulation happens at the `merge` level (tuple-of-Results into Result-of-tuple), there's never a need for per-decoder default values.

### Errors

```
pub type ParseError = {
  path : List String,      # e.g. ["users", "3", "email"]
  expected : String,       # e.g. "String matching email regex"
  got : String,            # e.g. "Int"
  message : Option String, # optional custom message from refinements
}

pub type JsonError =
  | InvalidJson String              # layer-1 failure: malformed JSON syntax
  | InvalidShape (List ParseError)  # layer-2 failure: valid JSON, wrong shape
```

The two-variant `JsonError` cleanly distinguishes "your JSON was malformed" from "your JSON was valid but didn't match the schema." Applications can handle them differently (e.g. different HTTP status codes).

## Entry Points

```
# Layer 1: JSON string → Value (just the parse, no schema check)
pub fun parse_string : String -> Result Value JsonError

# Layer 2: Value → typed (schema validation against a parser)
pub fun run : Parser a -> Value -> Result a (List ParseError)

# Combined convenience
pub fun parse : Parser a -> String -> Result a JsonError
parse p s = case parse_string s {
  Ok(v) -> case run p v {
    Ok(typed) -> Ok(typed)
    Err(errs) -> Err(InvalidShape errs)
  }
  Err(e) -> Err(e)
}
```

Most users call `parse` directly. The two-step form is available for when you want to parse once and run multiple parsers against the same value, or inspect the raw `Value` before parsing.

## Primitives

```
pub val string : Parser String
pub val int    : Parser Int
pub val float  : Parser Float
pub val bool   : Parser Bool
```

Each primitive wraps a type guard from `Std.Dynamic`:

```
pub val string = Parser (fun (Value dyn) ->
  case Std.Dynamic.decode Std.Dynamic.string dyn {
    Ok(s) -> Ok(s)
    Err(e) -> Err([translate_error e])
  })
```

The library handles the wrapping so users never see the underlying `Std.Dynamic.Decoder`. From the user's perspective, `Json.string` is just a `Parser String`.

## Combinators

### Object field extraction

```
pub fun field : String -> Parser a -> Parser a
field name (Parser inner) = Parser (fun (Value dyn) ->
  case Std.Dynamic.field_lookup name dyn {  # requires Std.Dynamic change (see below)
    Ok(child_dyn) -> case inner (Value child_dyn) {
      Ok(v) -> Ok(v)
      Err(errs) -> Err(List.map (prefix_path name) errs)
    }
    Err(_) -> Err([missing_field_error name])
  })
```

`field "name" string` is a parser that looks up `"name"` in the object and decodes it as a string. Errors get their path prefixed with the field name, so nested errors produce full paths like `users[3].email`.

### Array element extraction (two flavors)

```
# Decode every element with the same parser
pub fun list_of : Parser a -> Parser (List a)

# Decode a specific index (less common, mostly for tuple-shaped arrays)
pub fun element : Int -> Parser a -> Parser a
```

### Nullable / optional

```
pub fun optional : Parser a -> Parser (Maybe a)
optional (Parser inner) = Parser (fun (Value dyn) ->
  case Std.Dynamic.classify dyn {
    "Null" -> Ok(Nothing)
    _ -> case inner (Value dyn) {
      Ok(v) -> Ok(Just v)
      Err(errs) -> Err(errs)
    }
  })
```

Decodes `null` as `Nothing`, everything else as `Just (inner result)`.

### Default values

```
pub fun or_default : a -> Parser (Maybe a) -> Parser a
or_default d p = map (Maybe.unwrap_or d) p
```

Convenience for "this field is optional, use this default if missing." Note: the default is a *user-provided value for missing optional fields*, not a placeholder for failed decoding. Completely different concept from the deleted `Decoder a` default.

## The Merge / Map Pattern

The core of applicative accumulation:

```
pub fun merge : Parser a -> Parser b -> Parser (a, b)
merge (Parser f) (Parser g) = Parser (fun v ->
  case (f v, g v) {
    (Ok(a), Ok(b))       -> Ok((a, b))
    (Err(e1), Err(e2))   -> Err(e1 ++ e2)
    (Err(e), Ok(_))      -> Err(e)
    (Ok(_), Err(e))      -> Err(e)
  })

pub fun map : (a -> b) -> Parser a -> Parser b
map f (Parser g) = Parser (fun v -> Result.map f (g v))
```

`merge` combines two parsers into a parser of tuples, **accumulating errors when both sides fail**. `map` applies a function to the result of a parser.

Together they're Turing-complete for applicative composition (no need for `decode2`/`decode3`/.../`decode8` helpers). For a 4-field record, you chain three merges and one map:

```
let user_parser : Parser User =
  merge
    (merge
      (merge
        (field "name" string)
        (field "age" int))
      (field "email" string))
    (field "role" string)
  |> map (fun ((((name, age), email), role)) -> User { name, age, email, role })
```

This is ugly as hand-written code. The `<-` record-builder syntax (see below) makes it readable.

### Inspiration: F# `MergeSources` + `BindReturn`

This pattern is directly borrowed from F#'s applicative computation expressions. An F# validation builder defines exactly two methods:

```fsharp
member _.BindReturn(x, f) = Result.map f x      // ← our `map`
member _.MergeSources(x, y) = Result.merge x y  // ← our `merge`
```

And F#'s `let! ... and! ... return ...` syntax desugars to chained `MergeSources` calls followed by `BindReturn`. Our `<-` record-builder syntax is the same desugaring, specialized for record literals.

The key insight from the F# example: **only two primitives are needed** (`merge` and `map`), not a family of `tupN`/`decodeN` functions. The surface syntax does the work of chaining them.

### Monadic escape hatch

For cases where a parser needs to branch on a previously-decoded value (e.g. "if type is 'admin', require a permissions field"):

```
pub fun and_then : (a -> Parser b) -> Parser a -> Parser b
and_then f (Parser g) = Parser (fun v -> case g v {
  Ok(a) -> case f a {
    Parser h -> h v
  }
  Err(errs) -> Err(errs)
})
```

This is monadic — it's the sequential "bind" operation. Useful for discriminated unions and cross-field validation, but loses applicative accumulation (because the second parser depends on the first's success). Use `merge` for independent fields, `and_then` for dependent decisions.

### Cross-field validation after applicative phase

```
# Validate after extraction
let signup_parser : Parser Signup =
  (SomeSignupBuilder {
    email            <- field "email" (string |> matches email_regex),
    password         <- field "password" (string |> min_length 8),
    confirm_password <- field "confirm_password" string,
  })
  |> and_then (fun form ->
    if form.password == form.confirm_password
    then Parser.pure form
    else Parser.fail [make_error "passwords do not match"])
```

The applicative phase extracts and validates per-field. The `and_then` phase does cross-field checks that need all fields present. Errors from both phases merge into one list.

## Refinement Combinators

String length, range checks, regex, format validation, transforms:

```
pub fun min_length : Int -> Parser String -> Parser String
pub fun max_length : Int -> Parser String -> Parser String
pub fun matches    : Regex -> Parser String -> Parser String
pub fun min        : Int -> Parser Int -> Parser Int
pub fun max        : Int -> Parser Int -> Parser Int
pub fun refine     : (a -> Bool) -> String -> Parser a -> Parser a
pub fun transform  : (a -> Result b String) -> Parser a -> Parser b
```

These compose via `|>`:

```
field "email" (string |> matches email_regex |> min_length 5)
field "age" (int |> min 0 |> max 150)
field "dob" (string |> transform DateTime.from_iso_string)
```

Each refinement wraps a parser in another parser that runs the inner parser and then applies the extra check/transform. Failure modes accumulate in the `ParseError` list.

## Fail-Fast vs Accumulation

`merge` accumulates. The primitive parsers fail-fast within themselves (a String decoder doesn't try to decode halfway). Refinements fail-fast per refinement (if `min_length 5` fails, `matches email_regex` doesn't run on that same value).

At the record level, users choose their semantics:

- **Pure `merge` chain (or `<-` record builder):** accumulates across independent fields. Every field's parser runs, errors combine.
- **`and_then` chain:** fail-fast across dependent fields. First failure aborts the chain.

For forms and API request validation, the default should be `merge`. For config parsing where early errors invalidate later ones, `and_then` is sometimes clearer.

## The `<-` Record-Builder Syntax

The big language feature this library wants. With it, the ugly manual `merge` chain becomes:

```
let user_parser : Parser User = User {
  name  <- field "name" string,
  age   <- field "age" int,
  email <- field "email" string,
  role  <- field "role" string,
}
```

### Desugaring rules

A record literal with **at least one** `<-` field becomes a call chain of `merge` + `map`. A record literal with only `:` fields is unchanged (normal record construction).

**Case 1: all `<-` fields**

```
User {
  name <- pname,
  age  <- page,
}
```

Desugars to:

```
map (fun ((name, age)) -> User { name, age }) (merge pname page)
```

**Case 2: three or more `<-` fields**

Merge chain is left-associative, producing a left-nested tuple:

```
User { a <- pa, b <- pb, c <- pc, d <- pd }
```

Desugars to:

```
map
  (fun ((((a, b), c), d)) -> User { a, b, c, d })
  (merge (merge (merge pa pb) pc) pd)
```

**Case 3: mixed `<-` and `:` fields**

`:` fields are captured by the constructor lambda's closure:

```
User {
  name    <- field "name" string,
  age     <- field "age" int,
  role:   Admin,
  tenant: current_tenant_id,
}
```

Desugars to:

```
map
  (fun ((name, age)) -> User { name, age, role: Admin, tenant: current_tenant_id })
  (merge (field "name" string) (field "age" int))
```

`<-` field RHS is evaluated once, at record-literal-construction time, to produce the parser. `:` field RHS is evaluated once, at record-literal-construction time, and the result is baked into the closure. Both happen at the same moment; the difference is what they produce (a `Parser X` vs an `X`).

**Case 4: single `<-` field**

Skip the `merge`, use `map` directly:

```
User { name <- pname, role: Admin }
```

Desugars to:

```
map (fun name -> User { name, role: Admin }) pname
```

**Case 5: zero `<-` fields**

Not desugared. Regular record construction, existing semantics.

### Name resolution for `merge` and `map`

The compiler emits `merge` and `map` as bare identifiers, resolved via normal name lookup at the call site. This is the `RebindableSyntax` approach (borrowed from Haskell).

```
import Json (merge, map, field, string, int)
let user_parser = User { name <- ..., age <- ... }  # uses Json.merge, Json.map
```

Different imports → different semantics. `import Pg.RowDecoder (merge, map)` would produce `Pg.RowDecoder` values. `import Std.Validation (merge, map)` would produce generic `Validator` values. The compiler doesn't hardcode any specific type.

Trade-off: users must import `merge` and `map` in any module where they use `<-` syntax. Small papercut, but avoids coupling the language to a specific stdlib module.

### Factory functions with effects

Mixed `<-` and `:` enables parser-factory patterns where setup work happens outside the parser definition:

```
fun make_user_parser : Config -> Parser User needs {Db, Log}
make_user_parser config = {
  log! "info" "building user parser"
  let allowed_roles = db_query! "SELECT role FROM allowed_roles"
  let max_age = config.max_age_years

  User {
    name       <- field "name" (string |> min_length 1 |> max_length config.max_name_length),
    age        <- field "age" (int |> max max_age),
    role       <- field "role" (string |> one_of allowed_roles),
    created_by: config.current_user_id,
    tenant_id:  config.tenant_id,
  }
}
```

The factory does effectful setup (DB query, log) once. The parser bakes the results (`allowed_roles`, `max_age`, `current_user_id`, `tenant_id`) into itself as closure captures. Applying the parser to JSON reuses all of these — the DB query doesn't re-run per parse.

### What the syntax doesn't support

Cross-field value references inside the literal. You can't write:

```
User {
  first_name <- field "first" string,
  last_name  <- field "last" string,
  full_name:  first_name <> " " <> last_name,   # ERROR: first_name not in scope
}
```

The `<-` fields are applicative (independent), so there's no moment where `first_name` is "in scope" for the `:` field expression. Handle this with a post-process `map`:

```
User {
  first_name <- field "first" string,
  last_name  <- field "last" string,
} |> map (fun u -> { u | full_name: u.first_name <> " " <> u.last_name })
```

Or don't store the derived value — compute it on demand from the base fields.

### Implementation sketch

Pieces involved:

1. **Parser change** (`src/parser/expr.rs`): add `ident <- expr` as a third field-binding form, alongside `ident : expr` and `ident` (punning). ~30 lines.

2. **AST change** (`src/ast.rs`): add a new variant to the record-field binding enum. ~15 lines.

3. **Desugar pass** (`src/desugar.rs` or a new module): when visiting a `RecordLit`, check if any fields use `<-`. If so:
   - Partition into `<-` (parsed) and `:` (literal) fields
   - Build left-associative merge chain from the parsed fields in source order
   - Build constructor lambda: nested-tuple parameter matching the merge chain's shape, body is the original record literal with `<-` fields replaced by variable references
   - Emit `map <lambda> <merge_chain>`
   - Preserve source spans on the generated nodes so type errors point back to the original `<-` lines
   - ~150 lines including span preservation

4. **Typechecker**: no changes. It sees the desugared form and checks it normally.

5. **Lowerer / codegen**: no changes.

6. **Tests**: desugaring golden tests for each case above, plus end-to-end tests using the JSON package once it exists. ~100 lines.

**Total compiler churn: ~300-400 lines.** No type system changes, no HKTs, no new traits, no lowering work.

### Error message quality

With naive span preservation, a type error in a `<-` field body would reference the desugared `map` expression rather than the original record line. This should be fixed by threading source spans carefully through the desugar pass:

- The constructor lambda's body carries the span of the original `User { ... }` literal
- Each binding in the nested tuple pattern carries the span of its source `<-` line
- The merge chain's individual nodes carry the spans of their source `<-` RHS expressions

When the typechecker unifies the lambda body with the expected record type and finds a mismatch, it should use the span of the specific binding that mismatches. This is extra work but standard desugaring hygiene.

Without span preservation, the feature ships but error messages are mediocre. It's fine to land the basic feature first and polish spans iteratively.

## Changes Needed in `Std.Dynamic`

Very small set of changes to support the JSON package (or any external package) building format parsers:

### Make internal helpers public

Currently private, should become public (one-line changes):

```
pub fun field_lookup : String -> Dynamic -> Result Dynamic DecodeError
pub fun element_lookup : Int -> Dynamic -> Result Dynamic DecodeError
```

(These are currently `raw_field_lookup` and `raw_element_lookup`. The `raw_` prefix should be dropped when making them public.)

Without this change, external packages would either have to reimplement field lookup via their own `@external` bindings, or reach into `Std.Dynamic`'s bridge file from outside, which is ugly.

### (Optional) A path-prefixing helper

If building proper error paths from external packages is clunky, consider:

```
pub fun prefix_path : String -> DecodeError -> DecodeError
```

…as a public helper. Might not be needed if the `ParseError` type is defined in the JSON package and can manipulate its own `path` field directly. Decide while implementing.

### (Optional, much later) Extract `Std.Validation`

If a second format library (YAML, TOML, etc.) wants the same `merge`/`map`/`and_then` shape, extract those combinators into a generic `Std.Validation` module parameterized over the source type:

```
module Std.Validation

pub type Validator src a = Validator (src -> Result a (List ValidationError))

pub fun map : (a -> b) -> Validator src a -> Validator src b
pub fun merge : Validator src a -> Validator src b -> Validator src (a, b)
pub fun and_then : (a -> Result b (List ValidationError)) -> Validator src a -> Validator src b
```

**Not in scope for v1.** Don't build the abstraction on spec. Only extract when a second consumer exists.

## Package Structure

Directory layout, following saga_pgo conventions:

```
dy_json/  (or whatever the package name ends up being)
├── project.toml
├── dy_json_bridge.erl        # FFI bridge to OTP json module
├── lib/
│   └── Json.dy               # main module: Value, Parser, combinators, entry points
├── tests/
│   └── json_test.dy          # unit tests for primitives, combinators, error cases
└── examples/
    └── nested_decode.dy      # demo: nested record decode, success + failure paths
```

Single-file library to start. If it grows past ~500 lines, consider splitting:

```
lib/
├── Json.dy                   # re-exports Value, Parser, parse, run
├── Json/
│   ├── Parser.dy             # primitives and combinators
│   ├── Refinements.dy        # min_length, matches, transform, etc.
│   └── Error.dy              # ParseError, JsonError, path helpers
```

### The Erlang bridge

```erlang
-module(dy_json_bridge).
-export([parse_string/1]).

parse_string(Bin) when is_binary(Bin) ->
    try
        {ok, json:decode(Bin)}      % OTP 27+ built-in
    catch
        error:Reason ->
            {error, format_parse_error(Reason)}
    end.

format_parse_error(Reason) ->
    % Convert OTP json error term into a user-friendly string
    iolist_to_binary(io_lib:format("~p", [Reason])).
```

~30 lines total including error formatting. Depends on OTP 27+ for the built-in `json` module; for older OTP, swap in `jiffy`/`thoas`/`jsone` as a dependency in `project.toml`.

## Implementation Plan

Ordered for incremental value. Each step is shippable on its own.

### Step 1: Std.Dynamic cleanup (no new package yet)

- Make `raw_field_lookup` → `field_lookup` public
- Make `raw_element_lookup` → `element_lookup` public
- Verify nothing else in stdlib needs to become public for external libraries to work
- Update `docs/dynamic-type.md` to reflect that these helpers are intended for library authors
- **~30 lines changed across 2-3 files. ~10 minutes.**

### Step 2: Document the layering rule

- Add a new item to `docs/language-design.md` section 15 ("Settled Decisions") articulating the layering: stdlib = primitives, packages = domain libraries, `Dynamic` doesn't appear in public APIs of layer-3 libraries
- Or put this in a new `docs/library-design.md` if it grows to multiple related rules
- **~30-50 lines of documentation. ~20 minutes.**

### Step 3: Create the JSON package skeleton

- New project directory (`dy_json/` or whatever naming convention)
- `project.toml`, `dy_json_bridge.erl` with stub `parse_string`
- `lib/Json.dy` with just `opaque type Value = Value Dynamic` and `parse_string : String -> Result Value JsonError`
- Verify it builds and can be imported from a test project
- **~100 lines + project setup. ~30 minutes.**

### Step 4: Primitive parsers and `run`

- `Parser a` type
- `string`, `int`, `float`, `bool` primitives
- `run : Parser a -> Value -> Result a (List ParseError)`
- `parse : Parser a -> String -> Result a JsonError` convenience wrapper
- Unit tests for each primitive
- **~150 lines. ~1 hour.**

### Step 5: Field and combinators

- `field : String -> Parser a -> Parser a` with path prefixing
- `list_of`, `optional`, `element`
- `merge`, `map`, `and_then`
- Unit tests covering nested records, error accumulation, optional fields
- **~200 lines. ~1-2 hours.**

### Step 6: Refinement combinators

- `min_length`, `max_length`, `matches`, `min`, `max`, `refine`, `transform`
- Tests for each with both success and failure paths
- **~150 lines. ~1 hour.**

### Step 7: Demo example

- `examples/nested_decode.dy` showing a realistic nested record decode
- Both success and failure cases
- Documents the manual `merge` chain form (pre-syntax)
- **~80 lines. ~30 minutes.**

### Step 8: `<-` record-builder syntax (language change)

- Parser change in `src/parser/expr.rs`
- AST change in `src/ast.rs`
- Desugar pass
- Golden tests for each desugaring case
- Update demo example to use the new syntax
- **~400 lines across compiler and tests. ~1 day of focused work.**

Steps 1-7 are package-level work. Step 8 is a language change. Steps 1-7 are enough to ship a usable JSON library; step 8 is the quality-of-life improvement that makes it delightful.

**Recommended order**: 1, 2, 3, 4, 5, 7, (use the library on a real project for a week), 6, 8. Step 6 (refinements) is lower priority than demonstrating the core works. Using it on a real project between 7 and 8 validates the design before committing to a compiler change.

## Open Questions

1. **Package name.** `dy_json`, `dylang_json`, just `json`? Matches whatever convention has been established.

2. **Bridge library.** OTP 27+ built-in vs `jiffy`/`thoas`/`jsone`? OTP 27 is simplest (no dependency) but excludes users on older OTP. Probably start with OTP 27 built-in and add fallbacks later if requested.

3. **Whether to ship `Std.Validation` at all.** Currently decided NO (premature). Revisit if a second format library wants the same combinators.

4. **Error path representation.** Is `List String` sufficient, or do we want typed path segments (`| Field String | Index Int`)? The typed version is slightly nicer for tooling but adds complexity. Probably start with `List String` and upgrade if tooling wants it.

5. **Streaming support.** Does v1 need to handle huge JSON documents that don't fit in memory? Almost certainly not — keep it simple, add streaming in a v2 if anyone asks.

6. **Schema introspection.** Zod-style `Schema` type that carries both a parse function *and* an introspectable shape ADT (for generating JSON Schema, OpenAPI specs, forms, etc.). Powerful but bigger commitment. **Not in scope for v1.** Can be added later as either a new type (`Json.Schema a`) or an evolution of `Parser a` without breaking existing code.

7. **Mutually recursive parsers.** How does a recursive type (like a JSON tree where each node contains a list of children) define its decoder? Since dylang `val` is eager, you can't write `let tree_parser = Parser (fun v -> ... tree_parser ...)` directly. Workaround: define as a `fun` taking `Unit`, call `tree_parser ()` at the recursion point. Document this in the README.

8. **Cross-field validation ergonomics.** The `and_then` post-process pattern works but is somewhat awkward. Is there a better idiom? Probably fine for v1 — most cross-field validation is rare enough.

9. **Compile-time schema validation.** Could the compiler check that a `Parser User` actually produces values of type `User` (i.e., that the field names and types in the parser match the record definition)? With the `<-` syntax it does this implicitly because the record literal has to be valid. Without it, users can write parsers that typecheck but produce the wrong record shape. Worth thinking about, but not blocking.

## Known Gotchas

1. **Recursive parsers need the `fun () -> ...` workaround.** Direct `val` reference to itself won't compile.

2. **`<-` syntax error messages are mediocre without span preservation work.** Ship basic syntax first, polish spans iteratively.

3. **Name collisions on `merge`/`map`.** If a module imports `Json.merge` and `Pg.RowDecoder.merge`, the user must qualify one. Standard import hygiene.

4. **The `<-` syntax doesn't compose with `do...else` blocks.** They're different constructs. `do...else` is for monadic sequential `Result` chaining; `<-` in record literals is for applicative parallel parser composition. Both exist because they solve different problems.

5. **Parser factory functions capture effects at construction time, not at parse time.** This is usually what you want (cache the DB query result in the parser) but occasionally surprising (if you wanted fresh config per parse, you'd need a different shape — build the parser inside a function that's called per parse).

6. **No placeholder values anywhere.** This is a feature. The cost was giving up the old `Std.Dynamic.Decoder a` type that carried defaults. The `merge` pattern replaces accumulation-via-placeholders with accumulation-via-independent-extraction.

## Prior Art

- **F# `let! ... and! ... return ...`** — the applicative computation expression that inspired the `<-` syntax. Same desugaring shape (two builder methods, chained `MergeSources` + final `BindReturn`).
- **Haskell `Validation` applicative** — same accumulation semantics via `Semigroup e`.
- **Elm `Json.Decode.Pipeline`** — `|> required "name" string |> required "age" int` style. Less ergonomic than our target because Elm doesn't have record-literal sugar.
- **Zod (TypeScript)** — schema-as-data with introspection. Our `Parser a` is intentionally *simpler* (pure function, no introspection) for v1. Zod-style introspection is a possible v2 extension.
- **Gleam `gleam_stdlib/dynamic`** — closest in spirit. Uses opaque `Decoder(t)` with CPS-style combinators. Our design differs in using `merge`/`map` instead of their `use` syntax.

## References

- `docs/dynamic-type.md` — the `Std.Dynamic` redesign that made this all possible
- `docs/language-design.md` section 15 — settled decisions and design rules
- `examples/20-validation-applicative.dy` — the `Validate` effect pattern, which is the closest existing dylang code to applicative validation
- `src/stdlib/Dynamic.dy` — the stdlib module this library builds on
- saga_pgo project layout — the reference for how a layer-3 package is structured
