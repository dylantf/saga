# Optimization Fixtures

These examples are a source fixture corpus for the post-classifier optimizer
work. They were copied from the previous `selective-uniform` attempt so we can
reuse the useful case coverage without porting that lowerer architecture.

Use these as probes for optimization facts and emitted Core shape. Correctness
must continue to fall back to the existing direct-first lowering path when an
optimization cannot be proven.

Initial focus:

1. Direct specialization for statically known, pure tail-resumptive effect
   handlers.
2. Trait/dictionary call-site specialization once per-method effect shapes are
   explicit enough.
3. Generic-derived specialization, starting with narrow `ToJson` shapes.

The `selective-uniform/` directory is historical coverage. It should be
curated as individual cases graduate into the current optimizer pipeline.
