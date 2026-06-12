# Module System

Saga modules are declared in source files with `module Foo.Bar` and imported by
declared module name, not by file path. Project mode scans `.saga` files under
the project and dependency source roots to build a module map from declared name
to path.

The module system has two related jobs:

- build the source-level scope used by name resolution
- load and cache the semantic metadata needed by typechecking, elaboration, LSP,
  and codegen

## Import Surface

The common forms are:

```saga
import Math
import Math as M
import Math (add, double)
import Math (add as plus)
import Math (..)
```

`import Math` makes qualified names such as `Math.add` available. Selective and
all-exposing imports also add bare user-visible names. Item aliases only change
the local surface spelling: `plus` still resolves to the origin identity
`Math.add`.

Re-exports are written inside an import exposing list:

```saga
import Math (pub add as plus)
import Std.List (pub ..)
```

A re-export does not create a new definition. It adds a surface name that points
at the original canonical identity. Codegen, trait impl lookup, docs, and LSP
should continue to treat the name as originating in the defining module.

## Name Resolution Contract

Imports are processed before body inference. They build a `ScopeMap` containing
user-visible names and their canonical identities. Then `resolve_names` records
semantic identity in `ResolutionResult` by source `NodeId`.

That means later compiler phases should not guess meaning from raw spelling.
For example, `plus` imported from `Math (add as plus)` resolves as `Math.add`;
the alias is local syntax, not a semantic target.

See [name-resolution.md](name-resolution.md) for the resolver architecture.

## Loading And Exports

For acyclic imports, loading is still recursive and on-demand:

1. Resolve the imported module name through the module map.
2. Parse, derive-expand, and desugar the imported file.
3. Typecheck the imported module.
4. Collect its `ModuleExports`.
5. Register canonical exports into the importing checker.
6. Merge the import's user-visible scope entries.

`ModuleExports` is the full post-typechecking interface. It includes inferred
schemes, record metadata, trait/effect/handler metadata, trait impls, def IDs,
docs, and codegen information. It is cached per module so repeated imports are
cheap and so codegen can compile every checked module without rechecking.

## Cyclic Imports

Saga supports the common cyclic case where two modules import each other's
types, constructors, records, re-exports, and explicitly annotated functions.

For example:

```saga
module A
import B (BThing, make_b)

pub type AThing = AThing BThing

pub fun make_a : Unit -> AThing
make_a () = AThing (make_b ())
```

```saga
module B
import A (AThing, make_a)

pub type BThing = BThing

pub fun make_b : Unit -> BThing
make_b () = BThing
```

The compiler handles this with strongly connected components and module
headers.

### Module Graphs And SCCs

The typechecker builds an import graph from module import declarations and uses
Tarjan SCCs to detect cyclic groups. The normal non-cyclic path remains
recursive and on-demand. When an import target is part of a real SCC, the whole
component is loaded together.

The graph is cached on the checker. If building a full graph fails because an
unrelated module-map entry is stale, the cycle probe falls back to the import
closure reachable from the module being loaded. Errors in the reachable closure
still surface normally.

### ModuleHeader

`ModuleHeader` is the pre-inference interface for a module. It is extracted by
walking the parsed AST, without calling body inference.

It contains plain owned data for:

- module name and imports
- exposed type names, arities, ADT constructors, records, and fields
- declared public function annotations
- unannotated function names, for better cyclic-boundary diagnostics
- trait, effect, and handler declarations, enough to recognize and reject
  unsupported cyclic-boundary uses
- re-export edges, including `pub name as surface` and `pub ..`

It deliberately does not contain `NodeId`s or borrows into checker state. It is
in-memory today, but shaped like data that could become an incremental interface
seed later.

LSP metadata is kept separate. During SCC loading, the checker derives a small
sidecar from the parsed programs to preserve def IDs and docs for names imported
from sibling headers. This keeps `ModuleHeader` clean while still making hover,
go-to-definition, and references work.

### Header-Based Scope

When checking a module inside an SCC, imports of sibling modules are resolved
from headers instead of recursively loading the target module's full exports.
Header scope construction records the same canonical identities as normal
imports wherever the header surface is supported.

Re-export edges are followed to their origin. An explicit re-export chain must
ground in a real definition; a chain such as A re-exporting `x` from B while B
re-exports `x` from A is a re-export cycle and is rejected. For `pub ..`,
revisiting a module while searching for a missing name is treated as "not found"
rather than as an error, so legal mutual facade imports do not produce false
cycle diagnostics.

After header scopes are installed, each module in the SCC is typechecked. Once
all members have been checked, full `ModuleExports` and codegen metadata are
collected and cached as usual.

## Cyclic Boundary Rules

Supported across a cyclic import boundary:

- public ADTs and their public constructors
- public records and their constructors/fields
- type aliases whose header type expressions can be converted without body
  inference
- public functions with explicit annotations, as long as the cyclic boundary
  does not require trait/effect/handler metadata
- re-exports that ground in supported definitions

Rejected across a cyclic import boundary:

- unannotated functions; add a type annotation
- traits and trait methods
- effects and effect operations
- handlers
- functions whose annotations carry trait constraints
- functions whose annotations mention effects, including effects hidden inside
  callback parameter or return types

Those unsupported cases need metadata that depends on body checking, impl
collection, handler checking, or effect solving. The compiler rejects them with a
cycle-aware diagnostic instead of partially registering them and producing a
misleading later error.

Local implementation details do not cross this boundary. A public annotated
function may call a private unannotated helper in its own module; the importer
only sees the public annotation. What is not allowed is importing the private
unannotated helper itself, or relying on an unannotated public function across
the cycle.

## Important Files

- `src/typechecker/check_module/header.rs`: `ModuleHeader` extraction
- `src/typechecker/check_module/graph.rs`: import graph and Tarjan SCCs
- `src/typechecker/check_module/scc.rs`: cycle probe and graph fallback
- `src/typechecker/check_module/header_scope.rs`: header import scope and
  re-export edge resolution
- `src/typechecker/check_module/header_register.rs`: pre-register supported
  SCC header metadata into a checker
- `src/typechecker/check_module/header_lsp.rs`: LSP metadata surface for header
  imports
- `src/typechecker/check_module/import_scope.rs`: normal post-export import
  scope construction
- `src/typechecker/check_module/exports.rs`: full post-typechecking
  `ModuleExports`
