# Plan: Token-Level Trivia Attachment

## Context

The formatter needs to preserve all comments through a parse→format round-trip. The current approach attaches comments during parsing via `collect_trivia()` / `collect_trailing_comment()` calls sprinkled across ~35 sites in the parser. This is fragile: `skip_terminators()` eats comments, lookahead interferes with trivia, and every new parser feature must manually handle comments. We've been patching individual call sites and it keeps breaking.

The fix: move the trailing-vs-leading decision into the lexer, where it's trivial (same line = trailing, after newline = leading). Comments, doc comments, blank lines, and terminators all become trivia attached to tokens. The parser never sees them and just promotes trivia from boundary tokens to AST nodes.

## Files to modify

- `src/token.rs` — `Spanned` struct, `Token` enum, new `Trivia` enum
- `src/lexer.rs` — restructure `lex()` to collect trivia onto tokens
- `src/parser/mod.rs` — remove `collect_trivia`, `collect_trailing_comment`, `skip_terminators`, `collect_doc_comments`; simplify `parse_program_annotated`
- `src/parser/expr.rs` — remove all trivia collection calls, fix pipe lookahead (simplifies), use token trivia
- `src/parser/decl.rs` — remove all trivia collection calls, fix type-param stop conditions, use token trivia
- `src/ast.rs` — `Trivia` enum moves to `token.rs`, `Annotated` and `dangling_trivia` stay

## Step 1: Token/Trivia restructure (`src/token.rs`)

Add `Trivia` enum and trivia fields to `Spanned`:

```rust
#[derive(Debug, Clone, PartialEq)]
pub enum Trivia {
    BlankLine,
    Comment(String),
    DocComment(String),
}

#[derive(Debug, Clone)]
pub struct Spanned {
    pub token: Token,
    pub span: Span,
    pub leading_trivia: Vec<Trivia>,
    pub trailing_comment: Option<String>,
}
```

Remove from `Token` enum: `Comment(String)`, `DocComment(String)`, `BlankLine`, `Terminator`.

`trailing_comment` is `Option<String>` rather than `Vec<Trivia>` because there can only ever be one same-line comment (the line ends after it). No `Trivia::Newline` variant needed — newlines are implicit boundaries, not data the formatter needs.

## Step 2: Lexer changes (`src/lexer.rs`)

The core rule: **a comment on the same line as the preceding token is that token's trailing comment. A comment on its own line is leading trivia on the next token.**

The lexer accumulates `pending_trivia: Vec<Trivia>` between significant tokens. When it emits a significant token, the pending trivia becomes that token's `leading_trivia`. After emitting, it immediately checks if a same-line comment follows and attaches it as `trailing_comment`.

Algorithm:

```
pending_trivia = []
seen_newline_since_last_token = true  // start of file counts as after newline

loop:
  skip horizontal whitespace (spaces/tabs)

  if EOF:
    emit Eof token with leading_trivia = pending_trivia
    break

  if '\n' or ';':
    handle blank line detection:
      if previous char was also newline (or comment consumed its newline):
        push BlankLine to pending_trivia
    seen_newline_since_last_token = true
    continue

  if '#':
    read comment/doc-comment text
    if NOT seen_newline_since_last_token AND tokens is non-empty:
      // same line as previous token → trailing
      tokens.last_mut().trailing_comment = Some(text)
    else:
      // own line → leading on next token
      push Comment/DocComment to pending_trivia
    consume trailing newline
    seen_newline_since_last_token = true
    continue

  // significant token
  lex the token
  emit with leading_trivia = take(pending_trivia), trailing_comment = None
  seen_newline_since_last_token = false
```

Key changes from current lexer:

- No more `should_emit_terminator` / `Terminator` emission — terminators are gone
- No more `prev_token` tracking for terminator logic
- `nesting` / `nesting_stack` still needed for brace/paren matching but not for terminator decisions
- BlankLine detection simplifies: consecutive newlines (after accounting for comment newline consumption) produce `Trivia::BlankLine`

## Step 3: Parser simplification (`src/parser/mod.rs`)

Remove entirely:

- `skip_terminators()` — nothing to skip, trivia isn't in the token stream
- `collect_trivia()` — trivia is already on tokens
- `collect_trailing_comment()` — already on tokens
- `collect_doc_comments()` — doc comments are in token trivia

`parse_program_annotated()` becomes:

```rust
pub fn parse_program_annotated(&mut self) -> Result<AnnotatedProgram, ParseError> {
    let mut decls = Vec::new();
    while !matches!(self.peek(), Token::Eof) {
        let start = self.pos;
        let decl = self.parse_decl()?;
        let leading = std::mem::take(&mut self.tokens[start].leading_trivia);
        let trailing = self.tokens[self.pos - 1].trailing_comment.take();
        decls.push(Annotated {
            node: decl,
            leading_trivia: leading,
            trailing_comment: trailing,
        });
    }
    // EOF token's leading trivia = comments at end of file
    let trailing = std::mem::take(&mut self.tokens[self.pos].leading_trivia);
    Ok(AnnotatedProgram { declarations: decls, trailing_trivia: trailing })
}
```

`parse_program()` stays as `parse_program_annotated() + strip_annotations()`.

## Step 4: Parser — fix Terminator-dependent code

Three patterns currently depend on `Token::Terminator`:

**A. `skip_terminators()` calls (~30 sites)** — Delete all calls. They're no-ops now.

**B. Stop conditions using Terminator (~3 sites in decl.rs)**:

- Type def params: `while !matches!(self.peek(), Token::Eq | Token::Terminator | Token::Eof)` → change to `while matches!(self.peek(), Token::Ident(_))` (only lowercase idents are type params)
- Handler recovery: `Token::Eq | Token::Terminator | Token::RBrace | Token::Eof` → `Token::Eq | Token::RBrace | Token::Eof`
- Handler error recovery skip: `Token::Terminator | Token::RBrace | Token::Eof` → `Token::RBrace | Token::Eof` (or use a smarter recovery heuristic)

**C. Pipe lookahead (expr.rs)**: Currently peeks past Terminator/Comment/BlankLine tokens to find `|>` on the next line. With trivia on tokens, `|>` is just the next token. Delete the entire lookahead block — pipes across lines just work.

**D. `with` keyword lookahead (expr.rs)**: Similar pattern checking for `Token::Terminator` before `with`. Delete — `with` is just the next token.

## Step 5: Parser — container trivia promotion (`src/parser/expr.rs`, `src/parser/decl.rs`)

For every braced container (blocks, case, effect, handler, trait, impl, record, do, receive, inline handler), replace the `collect_trivia` / `collect_trailing_comment` pattern:

**Before:**

```rust
self.expect(Token::LBrace)?;
let mut leading_trivia = self.collect_trivia();
while !matches!(self.peek(), Token::RBrace) {
    // parse item
    let trailing_comment = self.collect_trailing_comment();
    items.push(Annotated { node: item, leading_trivia, trailing_comment });
    leading_trivia = self.collect_trivia();
}
let dangling_trivia = leading_trivia;
self.expect(Token::RBrace)?;
```

**After:**

```rust
self.expect(Token::LBrace)?;
while !matches!(self.peek(), Token::RBrace) {
    let start = self.pos;
    // parse item
    items.push(Annotated {
        node: item,
        leading_trivia: std::mem::take(&mut self.tokens[start].leading_trivia),
        trailing_comment: self.tokens[self.pos - 1].trailing_comment.take(),
    });
}
let dangling_trivia = std::mem::take(&mut self.tokens[self.pos].leading_trivia);
self.expect(Token::RBrace)?;
```

Dangling trivia falls out naturally: comments before `}` are in `}`'s `leading_trivia`.

**Type def variants** (no braces): The save/restore hack goes away entirely. After parsing a variant, the next significant token is either `|` (more variants), `Deriving`, or something else (next declaration). No comments in the stream to interfere with lookahead.

## Step 6: AST cleanup (`src/ast.rs`)

- Move `Trivia` enum to `token.rs` (or just use `token::Trivia` directly)
- Remove old `Trivia` from `ast.rs`, update `Annotated` to use `token::Trivia`
- `Annotated`, `AnnotatedProgram`, `dangling_trivia` fields all stay as-is
- `strip_annotations()` stays

## Step 7: Formatter updates (`src/formatter/`)

Minimal changes — update imports if `Trivia` moved. The `format_trivia()` helper works the same. If we drop `Trivia::Newline` (not in the enum), no changes to format logic.

## Step 8: Downstream passes

All passes that consume the AST (desugar, elaborate, typechecker, codegen) use `..` to ignore trivia fields or `Annotated::bare()` / `dangling_trivia: vec![]` for synthesized nodes. These should need no changes since the `Annotated` shape is unchanged.

## Migration Strategy

This touches the lexer/parser boundary so it's largely all-at-once, but can be done in 3 commits:

1. **Lexer**: Add trivia to `Spanned`, populate in lexer, remove `Comment`/`DocComment`/`BlankLine`/`Terminator` from Token enum. Fix all Token enum match exhaustiveness errors across the codebase.
2. **Parser**: Remove `skip_terminators`/`collect_trivia`/`collect_trailing_comment`, update `parse_program_annotated` and all container parsing to use token trivia. Fix the 3 Terminator stop conditions.
3. **Cleanup**: Remove dead code, run clippy, verify.

## Verification

- `cargo test` — all 663+ tests pass
- `cargo run --bin dylang -- check examples/scratch.dy` — parses OK
- `cargo run --bin dylang -- fmt examples/scratch.dy` — all 40 comments preserved in correct positions
- `cargo clippy` — clean
- `diff <(cargo run --bin dylang -- fmt examples/scratch.dy) examples/scratch.dy` — only intentional formatting differences (indentation, line breaking), no lost comments
