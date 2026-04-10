#!/usr/bin/env bash
cargo build --bin saga 2>&1

for f in examples/*.saga; do
  name=$(basename "$f")
  [ "$name" = "scratch.saga" ] && continue

  echo "=== $name ==="
  cargo run --quiet --bin saga -- run "$f" 2>&1
  echo
done
