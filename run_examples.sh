#!/usr/bin/env bash
cargo build --bin dylang 2>&1

for f in examples/*.dy; do
  name=$(basename "$f")
  [ "$name" = "scratch.dy" ] && continue

  rm -rf examples/_build
  echo "=== $name ==="
  cargo run --quiet --bin dylang -- run "$f" 2>&1
  echo
done
