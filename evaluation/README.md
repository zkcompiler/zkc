# Evaluation

This directory contains optional, version-pinned integration evidence. It is
not required to build the compiler, and its results are scoped to the exact
fixtures and revisions named here.

## Semantic revalidation probes

[`r2-protocol-model/`](r2-protocol-model/README.md) is a temporary,
standard-library-only clean-room probe for the `FRI-Grind-1` design witness.
It compares candidate semantic factorizations and named failure boundaries; it
is not a compiler component, protocol implementation, or security evaluator.

## Plonky3

[`upstream/plonky3-replay/`](upstream/plonky3-replay/README.md) is the active
evaluation harness. One locked Rust crate provides:

- upstream BabyBear/Poseidon2 duplex observations;
- deterministic proof capture and verifier replay;
- mutation checks;
- a value-faithful prover fill consumed by zkc's native endpoint path; and
- a grading judge that decodes zkc's canonical wire into the pinned upstream
  proof shape and hands it to the upstream verifier, so acceptance comes from
  an implementation zkc does not own.

The corresponding lit coverage is in
[`plonky3-replay.test`](../test/Evidence/plonky3-replay.test),
[`plonky3-fri-value-faithful.mlir`](../test/Oir/plonky3-fri-value-faithful.mlir),
[`plonky3-duplex-replay.test`](../test/Oir/plonky3-duplex-replay.test),
[`prover-real-fill.test`](../test/Oir/prover-real-fill.test),
[`emit-fri-prover.test`](../test/Emit/emit-fri-prover.test), and
[`emit-fri-scale.test`](../test/Emit/emit-fri-scale.test). These checks do
not establish general Plonky3 conformance, protocol soundness, or production
readiness.

[`fri-bench/`](fri-bench/README.md) records generation-versus-upstream
benchmark evidence: the pinned upstream prover and an emitted zkc prover
timed over the same instance, with the emitted wire held byte for byte to a
recorded golden wire before anything is timed. The measured numbers live in
[`RECORD.md`](fri-bench/RECORD.md) with machine, revision, and instance
provenance; the soundness-accounting alignment against upstream's
p3-security tooling lives in [`PRICING.md`](fri-bench/PRICING.md). These are
recorded evidence, not CI gates; only the deterministic byte-equality scale
gate runs in lit.

## Regression provenance

Two current PIR regression pairs are derived from public source history.
The fixtures model only transcript ordering and material binding; they do not
execute the named systems.

| Fixtures | Reviewed source coordinates | Modeled boundary |
|---|---|---|
| `linea-rlc-*` | Linea [before](https://github.com/Consensys/linea-contracts-fix/commit/65238564c9dd6bee9669116dcec0b72e689662ae) and [after](https://github.com/Consensys/linea-contracts-fix/commit/4ff29606881d576264b282957808e56fb62460a8) | Equation material precedes its random-linear-combination challenge. |
| `sp1-rlc-*` | `p3-fri` [0.1.4-succinct](https://crates.io/crates/p3-fri/0.1.4-succinct) and [0.2.0-succinct](https://crates.io/crates/p3-fri/0.2.0-succinct); Plonky3 [repair](https://github.com/Plonky3/Plonky3/commit/b5ec4d96bc752e78990db0707f6b60c4f3d9930a) | Opening values precede their random-linear-combination challenge. |

The executable fixtures and C++/Python parity checks are in
[`ordered-rlc-parity.test`](../test/Evidence/ordered-rlc-parity.test).
