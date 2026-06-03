#!/usr/bin/env bash
start="${1:-}"
stop="${2:-}"

if [ "$#" -gt 2 ]; then
  echo "usage: $0 [start-number [stop-number]]" >&2
  exit 2
fi
case "$start" in
  ''|*[!0-9]*)
    if [ -n "$start" ]; then
      echo "usage: $0 [start-number [stop-number]]" >&2
      exit 2
    fi
    ;;
esac
case "$stop" in
  ''|*[!0-9]*)
    if [ -n "$stop" ]; then
      echo "usage: $0 [start-number [stop-number]]" >&2
      exit 2
    fi
    ;;
esac

cargo build --bin saga 2>&1

for f in examples/*.saga; do
  name=$(basename "$f")
  [ "$name" = "scratch.saga" ] && continue
  if [ -n "$start" ]; then
    number="${name%%-*}"
    case "$number" in
      ''|*[!0-9]*) continue ;;
    esac
    [ "$number" -lt "$start" ] && continue
    [ -n "$stop" ] && [ "$number" -gt "$stop" ] && continue
  fi

  echo "=== $name ==="
  cargo run --quiet --bin saga -- run "$f" 2>&1
  echo
done
