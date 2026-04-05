#!/bin/bash

exclude=(-not -path './target/*' -not -path '*/_build/*' -not -path '*/deps/*')

rs=$(find . -name '*.rs' "${exclude[@]}" -print0 | xargs -0 wc -l | tail -1 | awk '{print $1}')
dy=$(find . -name '*.dy' "${exclude[@]}" -print0 | xargs -0 wc -l | tail -1 | awk '{print $1}')
erl=$(find . -name '*.erl' "${exclude[@]}" -print0 | xargs -0 wc -l | tail -1 | awk '{print $1}')

total=$((rs + dy + erl))

printf "%-15s %6d\n" "Rust (.rs)" "$rs"
printf "%-15s %6d\n" "Dylang (.dy)" "$dy"
printf "%-15s %6d\n" "Erlang (.erl)" "$erl"
echo "----------------------"
printf "%-15s %6d\n" "Total" "$total"
