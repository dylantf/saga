#!/usr/bin/env bash
set -euo pipefail

# Targeted optimizer diagnostics. Keep this sequential: Saga example runs share
# _build/script.beam and can collide if run concurrently.
#
# Benchmark mode defaults to the release compiler and `saga run --release` so
# the per-example script build cache can stay warm. Override with:
#   SAGA_BIN=target/debug/saga SAGA_RUN_PROFILE=dev bash scripts/optimizer_sweep.sh bench

mode="${1:-all}"
repeat="${2:-1}"
run_profile="${SAGA_RUN_PROFILE:-release}"

examples=(
  "examples/25-state-effect.saga"
  "examples/29-actors.saga"
  "examples/30-pingpong.saga"
  "examples/32-monitor.saga"
  "examples/49-dynamic.saga"
  "examples/54-choose-backtracking.saga"
  "examples/55-nqueens-solver.saga"
)

if [[ "$mode" != "stats" && "$mode" != "bench" && "$mode" != "all" ]]; then
  echo "usage: bash scripts/optimizer_sweep.sh [stats|bench|all] [repeat]" >&2
  exit 2
fi

if ! [[ "$repeat" =~ ^[1-9][0-9]*$ ]]; then
  echo "repeat must be a positive integer" >&2
  exit 2
fi

run_saga() {
  if [[ -n "${SAGA_BIN:-}" ]]; then
    "$SAGA_BIN" "$@"
  else
    cargo run --quiet --bin saga -- "$@"
  fi
}

elapsed_ms() {
  local start_ns="$1"
  local end_ns="$2"
  echo $(((end_ns - start_ns) / 1000000))
}

run_stats() {
  for example in "${examples[@]}"; do
    echo "=== stats: $example ==="
    run_saga inspect "$example" --stage monadic-stats
    echo
  done
}

run_bench() {
  local default_bin="target/release/saga"
  if [[ "$run_profile" == "release" ]]; then
    cargo build --quiet --release --bin saga
  else
    default_bin="target/debug/saga"
    cargo build --quiet --bin saga
  fi

  for example in "${examples[@]}"; do
    echo "=== bench: $example ==="
    echo "profile: $run_profile"
    local total_ms=0

    for i in $(seq 1 "$repeat"); do
      local output
      output="$(mktemp)"
      local start_ns
      local end_ns
      start_ns="$(date +%s%N)"
      local args=(run "$example")
      if [[ "$run_profile" == "release" ]]; then
        args=(run --release "$example")
      fi
      if SAGA_BIN="${SAGA_BIN:-$default_bin}" run_saga "${args[@]}" >"$output" 2>&1; then
        end_ns="$(date +%s%N)"
        local ms
        ms="$(elapsed_ms "$start_ns" "$end_ns")"
        total_ms=$((total_ms + ms))
        printf "run %d/%d: %sms\n" "$i" "$repeat" "$ms"
      else
        cat "$output"
        rm -f "$output"
        exit 1
      fi
      rm -f "$output"
    done

    if [[ "$repeat" -gt 1 ]]; then
      printf "avg: %sms\n" $((total_ms / repeat))
    fi
    echo
  done
}

case "$mode" in
  stats)
    run_stats
    ;;
  bench)
    run_bench
    ;;
  all)
    run_stats
    run_bench
    ;;
esac
