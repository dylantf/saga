# Doc Generation

Plan for `dylang docs` CLI command and Hex publishing integration.

## Doc Comment Syntax

Already implemented: `#@` doc comments attach to the next definition.

Module-level docs: `#@` before the `module` declaration attaches to the module itself. Same syntax, positional rule — doc comment before `module` = module doc.

```
#@ A collection of math utilities for vectors and matrices.
#@ Supports 2D and 3D operations.
module Math.Vector

#@ Add two vectors element-wise.
pub fun add : Vector -> Vector -> Vector
add a b = ...
```

Doc content is Markdown, top to bottom. Conventions:

- First line is a short summary (used in index pages, hover, etc.)
- Longer description follows if needed
- `## Examples` section with code blocks
- No `@param`/`@return` tags — the type signature covers that

## `dylang docs` Command

Generates a static HTML site from a project's `.dy` source files.

### Pipeline

1. Parse all `.dy` files in the project (reuse existing parser)
2. Extract `#@` comments + type signatures + pub declarations from the AST
3. Render Markdown content to HTML (`pulldown-cmark` or similar Rust crate)
4. Syntax-highlight code blocks using the existing TextMate grammar (via `syntect`, which reads `.tmLanguage.json` natively in Rust)
5. Generate HTML pages per module with nav, search, and cross-linking
6. Output to `_build/docs/`

### Page Structure

- `index.html` — package overview, list of modules
- `ModuleName.html` per module — module doc, then each pub function/type/effect/handler with signature + doc

### Search

Static search index (JSON) built at generation time, with client-side JS search. Same approach as ExDoc, rustdoc, etc.

## EEP-48 Doc Chunks

Separate from HTML generation. Embeds docs in `.beam` files for cross-language BEAM interop (visible in IEx `h()`, Erlang shell, etc.).

### Format

The `Docs` chunk payload is an Erlang term:

```erlang
{docs_v1, erl_anno:new(0), erlang, <<"text/markdown">>, ModuleDoc, #{}, FunctionDocs}
```

Where:

- `ModuleDoc` — `#{<<"en">> => <<"markdown content">>}` or `none`
- `FunctionDocs` — list of `{{function, Name, Arity}, Anno, [Signature], Doc, Meta}` tuples

### Injection Approach

Post-process `.beam` files after `erlc`. Add an `erl -noshell` step that reads the `.beam`, appends the `Docs` chunk via `beam_lib`, and writes it back. The compiler already shells out to `erlc`/`erl`, so this fits the existing build flow.

```
.core -> erlc -> .beam -> erl (inject Docs chunk) -> .beam with docs
```

This is independent of HTML doc generation — do it even if `dylang docs` isn't being run, so all published `.beam` files have docs embedded.

## Hex Publishing

### Package Publishing

`dylang publish` command that:

1. Builds the project
2. Runs `dylang docs` to generate HTML into `doc/`
3. Packages a Hex tarball (metadata + source + docs)
4. Pushes to hex.pm

### HexDocs Integration

HexDocs hosts arbitrary static HTML — only requirement is `doc/` with an `index.html`. Register `"build_tool": "dylang"` in package metadata so Hex calls `dylang docs` for doc builds. This is how Gleam does it.

The HTML output is entirely ours — full control over styling, layout, and highlighting. No dependency on ExDoc or Makeup.

## Syntax Highlighting

Use the existing VS Code TextMate grammar (`.tmLanguage.json`) for highlighting in generated docs. In Rust, `syntect` reads TextMate grammars natively — no separate grammar to maintain.

For the language website (course, language tour), use Shiki (JS) which also consumes TextMate grammars. Same grammar file, consistent highlighting everywhere.

## Ordering

Suggested implementation order:

1. **Module doc syntax** — `#@` before `module` declaration
2. **`dylang docs` command** — basic HTML generation (modules, functions, types)
3. **EEP-48 chunks** — inject into `.beam` files during build
4. **`dylang publish`** — Hex integration
5. **Polish** — search, cross-linking, effects/handlers in docs
