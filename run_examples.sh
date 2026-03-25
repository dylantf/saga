rm -rf examples/_build && \
for f in examples/*.dy; \
do result=$(cargo run --bin dylang -- run "$f" 2>&1); rc=$?; \
if [ $rc -ne 0 ]; then echo "FAIL: $f"; \
echo "$result" | tail -5; echo; else echo "OK: $f"; fi; \
done