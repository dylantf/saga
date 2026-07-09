# Macro-Based User-Extensible Derives

> Status: exploratory design notes, not an accepted implementation plan.
>
> This is a possible future replacement for the removed Generic/fundep/Symbol
> deriving system. It should not revive that type-level machinery.

## Context

Saga previously supported user-extensible derives through a `Generic`
representation, functional dependencies, type-level `Symbol`s, generic trait
implementations over a structural representation, and a compiler
deforestation/specialization pass. That design worked, including for
`ToJson`, `FromJson`, database projections, and other library-defined traits,
but it had two substantial costs:

1. User-facing metaprogramming became type-level programming. Each new use
   case invited more kind, solver, functional-dependency, associated-type, or
   specialization machinery.
2. The runtime Generic walk required a large optimizer pass to recover the
   direct code that a hand-written implementation would have produced.

The system and its removal are documented in:

- [User-Extensible Derives via Generic](../archive/user-extensible-derives.md)
- [Generic Deriving](../archive/generic-deriving.md)
- [Type-Level Symbols](../archive/type-symbols.md)
- [Removing the Type-Level Trinity](remove-type-level-trinity.md)

The motivating question for a future macro system is narrower:

> Can a library author derive an ordinary implementation of an ordinary
> user-defined trait from the shape of a declaration, without turning the
> trait solver into a compile-time programming language?

The proposed answer is a constrained, hygienic, declaration-oriented macro
system. A derive macro inspects one declaration at compile time and emits the
same first-order Saga declarations a user could have written by hand.

## Goals

The initial system should support library-defined derives such as:

- `ToJson` and `FromJson`
- `ToSchema` for OpenAPI and other schema formats
- binary, CSV, database, and configuration codecs
- validators and property-test generators
- other structural trait implementations whose behavior follows record fields
  or ADT variants

It should provide:

- direct generated code with no runtime reflection or Generic representation
- hygienic names and definition-site resolution
- generated code that goes through normal resolution, typechecking, trait
  coherence, elaboration, and lowering
- deterministic and cacheable expansion
- useful source spans and inspectable expansions
- a stable macro API that is smaller than the compiler's internal Rust AST
- a path to declaration/endpoint macros later without requiring them in the
  first version

## Non-goals

The first system should not provide:

- arbitrary typechecker queries from macros
- dependent types, associated-type normalization, or trait-solver reflection
- runtime Generic representations
- token-stream rewriting or arbitrary new grammar
- arbitrary module rewriting
- filesystem, network, clock, randomness, process, or FFI access during macro
  execution
- direct compile-time emission of files such as `openapi.json`
- a general `comptime` facility that can both reflect on types and synthesize
  declarations

These boundaries matter. If a macro can ask the compiler to infer arbitrary
expressions, normalize types, enumerate implementations, or recursively invoke
the trait solver, the old type-level feature pressure reappears through a new
API.

## Core model

A library defines a trait and a derive provider for it. Syntax below is
illustrative; no particular spelling is decided here.

```saga
pub trait ToJson a {
  fun to_json : a -> Json
}

@derive_provider(ToJson)
pub macro derive_to_json : DeriveInput -> MacroResult
derive_to_json input = ...
```

A consumer writes:

```saga
@derive(Json.ToJson, Json.FromJson)
@json(rename_all: "camelCase")
pub record User {
  id: Int,
  display_name: String,
  password: String @json(skip),
}
```

or, if the existing syntax remains the public surface:

```saga
pub record User {
  id: Int,
  display_name: String,
  password: String,
} deriving (Json.ToJson, Json.FromJson)
```

The `ToJson` provider receives a stable description of `User` and emits an
ordinary implementation equivalent to:

```saga
impl ToJson for User {
  to_json user = Encode.object [
    ("id", to_json user.id),
    ("displayName", to_json user.display_name),
  ]
}
```

`FromJson` emits direct decoding and construction:

```saga
impl FromJson for User needs {Fail Json.Error} {
  from_json json = User {
    id: Decode.at "id" from_json json,
    display_name: Decode.at "displayName" from_json json,
    password: "",
  }
}
```

There is no intermediate `Rep__User`, no runtime structural walk, and no need
for Generic deforestation. The generated program is already the optimized
shape.

## Derive-provider resolution

There are several plausible source syntaxes.

### Trait-associated default provider

```saga
@derive_provider(ToJson)
pub macro derive_to_json : DeriveInput -> MacroResult
```

Then `deriving (ToJson)` resolves the trait and its default provider. This is
the most ergonomic form and preserves the current derive syntax.

The registration should obey coherence-like rules: within a resolved package
graph there is at most one default derive provider for a trait. Normally the
trait's defining package should own the default provider.

### Explicit provider

```saga
record Event { ... }
  deriving (ToJson via Json.tagged)
```

This supports multiple structural encodings without global provider
selection. A reasonable design may offer a default provider and permit `via`
as an override.

### Separate macro namespace

The trait and derive macro may share a source name while living in distinct
namespaces, similar to a type and constructor namespace. For example,
`Json.ToJson` in a `deriving` position can resolve to a derive provider while
`ToJson` in a constraint position resolves to the trait. This keeps call sites
short but adds namespace rules that must be made explicit.

No choice is required for an initial compiler spike. The important semantic
rule is that a derive request resolves to a specific macro artifact before
the macro executes.

## Macro input

Macros should not receive the compiler's internal Rust AST directly. That
would permanently couple user libraries to parser and compiler refactors.
Instead, Saga should expose a versioned, deliberately small macro data model.
For example:

```saga
pub record DeriveInput {
  declaration: TypeDeclaration,
  requested_trait: Path,
  attributes: List Attribute,
  source: SourceInfo,
}

pub type TypeDeclaration =
  | RecordDeclaration RecordInfo
  | AdtDeclaration AdtInfo

pub record RecordInfo {
  name: Name,
  parameters: List TypeParameter,
  fields: List FieldInfo,
  visibility: Visibility,
  attributes: List Attribute,
}

pub record FieldInfo {
  name: Name,
  field_type: Syntax Type,
  attributes: List Attribute,
  source: SourceInfo,
}

pub record AdtInfo {
  name: Name,
  parameters: List TypeParameter,
  variants: List VariantInfo,
  visibility: Visibility,
  attributes: List Attribute,
}
```

This representation should be semantic enough that macro authors do not parse
source text, but syntactic enough that producing it does not require arbitrary
type inference. Macro names and imported providers must be resolved before
execution. Field types can remain hygienic `Syntax Type` values and be
resolved/typechecked normally after expansion.

The macro API needs explicit versioning. Adding a compiler-internal AST field
must not be an ecosystem-breaking macro ABI change.

## Macro output and hygiene

Rust-style token streams are maximally flexible but make every macro author
partially responsible for parsing Saga. Prefer category-aware syntax objects:

```saga
Syntax Expr
Syntax Type
Syntax Pattern
Syntax Decl
Syntax Name
```

Quotation and splicing could look approximately like:

```saga
quote decl {
  impl ToJson for #{input_type} {
    to_json value =
      Encode.object #{field_entries}
  }
}
```

A `Syntax Expr` may only be spliced into an expression position, a
`Syntax Type` into a type position, and so on. This catches malformed
expansions earlier than a general token stream.

Names introduced by a macro are hygienic by default. References written in
the macro definition resolve in the macro's definition context; syntax
spliced from the input retains its call-site context. The API can expose
explicit operations for the uncommon cases:

```saga
fresh_name! "value"
call_site_name "field_helper"
qualified_name ["SagaJson", "Encode", "object"]
```

Generated code should not need to inject imports into the consumer. A quoted
reference to `Encode.object` should carry semantic identity from the macro
package rather than relying on whatever `Encode` means at the invocation site.

## Execution model

The intended long-term model is that procedural macros are written in Saga,
compiled separately, and executed by the compiler as build-time artifacts.
This creates a bootstrapping constraint:

- a macro must already be compiled before it expands a consumer module
- a macro cannot use itself while it is being compiled
- dependency and project build ordering must distinguish macro providers from
  ordinary runtime modules

For dependency packages, `saga install`/build can compile declared macro
modules before compiling consumers. Path dependencies should follow the same
ordering, preserving their fast-iteration workflow. Same-package macros can
be supported through an acyclic macro-module dependency graph; the first MVP
may reasonably require macros to live in a separate dependency or separately
compiled macro target.

Because the compiler is Rust and Saga runs on the BEAM, execution likely
requires a worker boundary. Possibilities include:

1. a persistent isolated BEAM worker speaking ETF to the compiler
2. a short-lived BEAM worker per package/build
3. a future restricted compile-time interpreter

The first option is likely the most practical, but should be validated with a
spike. The protocol should exchange versioned macro input/output values, not
compiler Rust objects.

## Compile-time capabilities and determinism

Saga's effect system is a natural way to describe the permitted macro
capabilities:

```saga
pub macro derive_to_json :
  DeriveInput -> List (Syntax Decl)
  needs {MacroDiagnostics, FreshNames}
```

The compiler supplies handlers for diagnostics and fresh hygienic names.
Macro entry points should otherwise be pure. In particular, macro code should
not receive handlers for:

- file or environment access
- network access
- clock or randomness
- actors/process creation
- mutable global state
- arbitrary Erlang FFI

Effects alone are not a security boundary because `@external` could bypass
them. Macro artifacts must either reject FFI in their transitive closure or
execute in a genuinely isolated process/environment. NIFs must not be loaded
into the compiler process.

Deterministic execution enables expansion caching. A cache key can include:

```text
macro artifact hash
+ macro API/ABI version
+ normalized DeriveInput
+ invocation attributes
+ compiler expansion version
```

Macro execution should also have time, memory, expansion-depth, and output-size
limits so accidental recursion cannot hang a build.

## Compiler phase placement

The current pipeline already has a derive-expansion phase:

```text
Parse
  -> Derive Expansion
  -> Desugar
  -> Typecheck / Name Resolution
  -> Elaborate
  -> Lower
```

User macros fit conceptually where built-in derives run today, but require a
small front-end split:

```text
Parse modules
  -> collect module/import/type/trait/macro headers
  -> resolve macro providers
  -> expand attached/derive macros
  -> resolve and typecheck the expanded ordinary Saga program
  -> elaborate and lower normally
```

Macro expansion should not invoke the normal typechecker recursively. The
macro emits declarations; the normal pipeline checks them once after
expansion.

Generated declarations should be spliced immediately after their parent, as
current derive expansion does. This preserves predictable registration order
and gives the generated code a clear source origin.

Whether macro-generated declarations may themselves request expansion needs
a firm rule. A bounded fixed-point expansion is possible, but the first
version should probably prohibit generated macro definitions and cap recursive
derive expansion to a small explicit depth.

## Generic parameters and generated constraints

A derive for:

```saga
record Page a {
  items: List a,
}
```

will usually generate:

```saga
impl ToJson for Page a where {a: ToJson} {
  ...
}
```

Computing provably minimal constraints would require consulting trait
resolution and risks recreating type-level improvement. The initial policy
should be deliberately conservative:

- add the derived trait bound for each type parameter occurring in a relevant
  serialized/schema field
- omit parameters that do not occur in relevant fields
- permit an explicit attribute to override or suppress generated bounds

For example:

```saga
@json(bounds: {a: ToJson})
record Page a { ... }
```

An occasional conservative bound is preferable to a macro API that embeds the
trait solver.

## OpenAPI and schema generation

OpenAPI needs macros, but macros should generate ordinary schema and endpoint
descriptions rather than directly writing the final document.

### Type schemas

A library defines:

```saga
pub trait ToSchema a {
  fun schema : TypeWitness a -> Schema
}
```

`TypeWitness` here is only illustrative; it need not be the removed `Proxy`
or require type-level Symbols. A derive macro generates:

```saga
impl ToSchema for User {
  schema _ = Schema.object "User" [
    Schema.required "id" Schema.int,
    Schema.required "name" Schema.string,
  ]
}
```

The schema library, not the macro system, should handle named components,
references, and recursive types. Derivation only emits the direct structural
description for one type.

### Endpoints

A later attached declaration macro could consume a typed endpoint declaration:

```saga
@http.endpoint(POST, "/users")
pub fun create_user :
  CreateUserInput
  -> Result User ApiError
  needs {Repo}
```

and generate:

- the Edda request/response adapter
- body/path/query decoding
- an `OperationSpec` value referring to `ToSchema` implementations
- a route value or registration declaration

A normal Saga command or program then combines the generated values and
serializes `openapi.json`. Keeping file output outside expansion preserves
determinism and lets the same schema values be tested or served dynamically.

A plain `Request -> Response` handler does not expose enough type information
to infer an API contract. An endpoint macro therefore needs a typed endpoint
surface or explicit metadata; it should not guess semantics from arbitrary
handler bodies.

## Diagnostics and tooling

Generated code must not be invisible. At minimum, provide an expansion view:

```text
saga expand
saga expand Api.User
saga expand --macro Json.ToJson
```

Every generated node should retain:

- the invocation span
- the input field/variant span, when applicable
- the macro-definition span
- an expansion-origin chain

A useful diagnostic should look like:

```text
No implementation of `ToJson` for `SecretKey`

generated while deriving `ToJson` for `User`
  at src/User.saga:12
required by generated field `User.credentials`
  at src/User.saga:16
```

The primary underline should usually point at the consumer field or derive
request, not an opaque generated buffer. Macro authors should be able to emit
structured errors and warnings against specific input spans.

The LSP should expose generated implementations for go-to-definition and
hover, while clearly labeling them as generated. Expansion should be cached
and shared between CLI and LSP builds.

## Coherence and visibility

Generated implementations remain ordinary implementations. Existing trait
coherence, overlap, visibility, and orphan rules apply after expansion. A
macro must not receive a privileged route around them.

A derive provider may generate:

- an implementation of its associated trait for the attached type
- hygienic private helper declarations owned by that expansion

The first version should not allow a derive provider to generate arbitrary
public peers, implementations of unrelated traits, or changes to the original
declaration. Those broader roles can be introduced explicitly later.

## Relationship to `comptime`

Compile-time value evaluation and declaration generation are related but
should remain distinct:

- `comptime` evaluates a pure expression early and produces a value
- a macro receives syntax/declaration metadata and produces syntax

If general `comptime` can inspect inferred types and emit declarations, it is
already a procedural macro and reflection system. Keeping the phases separate
gives Saga a smaller initial design and avoids quietly rebuilding dependent
type-level computation.

A future pure constant evaluator may share the macro worker/runtime, but it
does not need access to `DeriveInput` or syntax construction.

## Suggested implementation sequence

### Phase 0: execution spike

- Hand-build a `DeriveInput` for one record in Rust.
- Compile a small Saga macro module separately.
- Invoke it in an isolated BEAM worker.
- Return a minimal structured declaration or expression over ETF.
- Measure startup, persistent-worker, serialization, and diagnostic costs.

This phase should decide whether executing Saga macros during compilation is
operationally reasonable before adding source syntax.

### Phase 1: derive-only MVP

- Add macro-package/artifact declarations and build ordering.
- Add the versioned record/ADT reflection model.
- Add hygienic declaration/type/expression quotation and splicing.
- Associate one provider with one user-defined trait.
- Permit generated trait impls and private helpers only.
- Expand before ordinary resolution/typechecking.
- Implement `saga expand`.
- Prove the path with a small `ToJson` library.

### Phase 2: production derives

- Structured field/variant attributes.
- Generic-parameter bound generation and explicit overrides.
- Expansion caching and LSP integration.
- Better source mapping and macro backtraces.
- Execution limits and FFI enforcement.
- Implement `FromJson` and `ToSchema` as real consumer libraries.

### Phase 3: attached declaration macros

- Add an explicit peer/function role rather than expanding derive privileges.
- Prototype typed HTTP endpoints and generated `OperationSpec` values.
- Keep route/schema aggregation in ordinary Saga code.

### Phase 4: reconsider `comptime`

Only after procedural macros have real users, evaluate whether pure
compile-time value evaluation solves separate use cases. Do not make it a
second route to the same declaration-generation power by accident.

## Open questions

1. What source syntax associates a derive provider with a trait?
2. Should `via` permit alternative providers, or should configuration be
   expressed entirely through attributes?
3. Are macro modules a separate package target, a separate module class, or
   ordinary modules compiled in a special dependency phase?
4. Is a persistent isolated BEAM worker fast and deterministic enough for CLI
   and LSP use?
5. What is the smallest stable `Syntax` and declaration-reflection ABI?
6. How are definition-context resolved names serialized across the macro ABI?
7. Can macro artifacts transitively depend on ordinary Saga libraries, and
   how is FFI excluded from that graph?
8. How are conservative generic bounds overridden without inventing a second
   constraint language?
9. May generated declarations trigger further derive expansion, and what is
   the depth/fixed-point rule?
10. How are macro dependency cycles diagnosed?
11. Does the current import-summary work before derive expansion remain
    useful, or should macro-provider resolution become a small dedicated
    front-end phase?
12. What artifact format and cache invalidation rules are needed for published
    Hex packages containing macros?

## Decision criterion

This proposal is worthwhile if a library-defined derive can generate code
essentially identical to a hand-written implementation while the compiler
only needs to understand:

- macro build ordering and execution
- a stable declaration/syntax data model
- hygiene and source mapping
- expansion caching and limits

It is not worthwhile if implementing ordinary derives again requires the
compiler to expose trait solving, inferred-type reflection, runtime Generic
representations, or a new specialization pipeline. The purpose of macros here
is to move structural code generation into an explicit compile-time phase,
not to reconstruct the removed type-level system under different names.
