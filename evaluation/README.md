# Evaluation

This directory contains optional, version-pinned integration evidence. It is
not required to build the compiler, and its results are scoped to the exact
fixtures and revisions named here.

## Plonky3

[`upstream/plonky3-replay/`](upstream/plonky3-replay/README.md) is the active
evaluation harness. One locked Rust crate provides:

- upstream BabyBear/Poseidon2 duplex observations;
- deterministic proof capture and verifier replay;
- mutation checks; and
- a value-faithful prover fill consumed by zkc's native endpoint path.

The corresponding lit coverage is in
[`plonky3-replay.test`](../test/Evidence/plonky3-replay.test),
[`plonky3-fri-value-faithful.mlir`](../test/Oir/plonky3-fri-value-faithful.mlir),
[`plonky3-duplex-replay.test`](../test/Oir/plonky3-duplex-replay.test), and
[`prover-real-fill.test`](../test/Oir/prover-real-fill.test). These checks do
not establish general Plonky3 conformance, protocol soundness, or production
readiness.

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
