# fri-bench — generation-versus-upstream evidence

The wall-clock and allocation halves of the benchmark gate
(docs/status.md cites this directory): the pinned upstream prover and
the emitted zkc prover over the same sp1-core-shape instance. The
numbers live in RECORD.md and are recorded evidence, not CI gates —
the deterministic half of the gate is test/Emit/emit-fri-scale.test,
which runs the whole pipeline at the ci-mid instance and holds the
emitted wire to byte equality before the upstream judge grades it.

Usage: python3 gen.py (emits the instance-A prover crate under
generated/), then cargo bench (wall clock) and cargo run --release
(allocation totals). p3-maybe-rayon's parallel feature stays off in
this graph so both grinds are serial ascending scans; enabling it on
either side would measure different work and break wire determinism.
