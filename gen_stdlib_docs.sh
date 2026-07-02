#!/usr/bin/env bash
# Regenerate the stdlib reference markdown and drop it into the saga-website repo.
#
# The website's stdlib section is auto-discovered from the .md files in
# app/content/stdlib/ (its git-tracked source of truth). This runs `saga docs`
# over src/stdlib and writes the output straight there.
set -euo pipefail

SAGA_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WEBSITE_DIR="${SAGA_WEBSITE_DIR:-$HOME/projects/saga-website}"
OUT_DIR="$WEBSITE_DIR/app/content/stdlib"

if [ ! -d "$WEBSITE_DIR" ]; then
  echo "error: saga-website not found at $WEBSITE_DIR" >&2
  echo "       set SAGA_WEBSITE_DIR to override" >&2
  exit 1
fi

echo "Generating stdlib docs -> $OUT_DIR"
cargo run --quiet --bin saga -- docs --dir "$SAGA_DIR/src/stdlib" --output "$OUT_DIR"
echo "Done."
