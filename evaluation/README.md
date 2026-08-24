# Evaluation

This directory contains optional, version-pinned integration evidence. It is
not required to build the compiler, and its results are scoped to the exact
fixtures and revisions named here.

## Semantic revalidation witnesses and probes

These packages are temporary R2 research instruments. They are not compiler
components, protocol implementations, security evaluators, or evidence that a
listed portfolio case is supported. Their results have different strengths and
must not be summarized as one green test count.

| Package | Classification | Retained evidence and exact limit |
|---|---|---|
| [`r2-protocol-model/`](r2-protocol-model/README.md) | Repaired `FRI-Grind-1` fixture witness | A 41-case frozen replay-verified corpus and 39 local tests close the named finite source-residual pressure. The model stops before authenticated FRI opening and acceptance; it is not a native FRI/IOR case. |
| [`r2-p01-schnorr/`](r2-p01-schnorr/README.md) | Retained T3 portfolio case `P01` | The prior 62-test snapshot failed cold review on modeled causality, equal-content occurrence aliasing, and incomplete independent-basis closure. The staged repair now passes 69/69 tests: 8 semantic, 27 execution/Interface, 8 provenance/diagnostics, 13 Relations/Analysis, and 13 report/replay. Its rotated source-bound report executes 45 cases—22 affirmative and 23 nonaffirmative—with 39 distinct public codes, and reproduces Fresh `c=3,z=3` and FS v3 `c=6,z=2`, proof `1002`. A separately coded query path is bound to the executed package initializer and shared term and semantic dependencies; it is diversity evidence, not independent semantic authority. The refrozen expected projection and minimal copied-checkout replay pass. Separate lifecycle and provenance cold rechecks pass on the final identity, closing Gate 10 and retaining P01 at T3 only for this exact finite scope. |
| [`r2-probe-commitment/`](r2-probe-commitment/) | Cross-cutting commitment/opening invariant probe | Thirty-three unit tests. It is not portfolio case `P02`. |
| [`r2-probe-logup/`](r2-probe-logup/) | Cross-cutting LogUp claim-routing invariant probe | Twenty-nine unit tests. It is not portfolio case `P03` or any other numbered case. |
| [`r2-probe-value-bridges/`](r2-probe-value-bridges/) | Cross-cutting value-bridge invariant probe | Eighteen unit tests. It is not portfolio case `P04`. |
| [`r2-probe-guard-cost/`](r2-probe-guard-cost/) | Cross-cutting guard-cost invariant probe | Twenty-two unit tests. It is not portfolio case `P05`. |

The protocol namespace is reserved: `Pnn` names primary protocol cases, `Vnn`
recent variants, and `Hnn` holdouts. Cross-cutting packages use
`r2-probe-<subject>` and `R2-<SUBJECT>-...` codes so their existence cannot be
mistaken for portfolio progress.

Run P01's current suite and source-bound public replay from the repository
root:

```sh
python3 -m unittest discover -s evaluation/r2-p01-schnorr/tests -v
python3 evaluation/r2-p01-schnorr/run.py --check
```

The runner builds and strictly verifies the report before reading the expected
projection. Its successful comparison is exact finite replay evidence, not a
cryptographic theorem or complete diagnostic reachability result.

[`coverage.py`](coverage.py) produces a manually curated live boundary-coverage
snapshot. It pools reached boundaries across instruments and relies on an
authored invariant-to-boundary map, so its labels prioritize review; they are
not R2 closure verdicts. [`reachability.py`](reachability.py) instruments the
current suites and reports declared versus fired result codes. A fired code is
not proof that the boundary discharges an invariant, and an unreached code is
not automatically a defect.

Run the current diagnostics from the repository root:

```sh
python3 evaluation/coverage.py
python3 evaluation/reachability.py
python3 evaluation/reachability.py --witness r2-p01-schnorr --list-unreachable
```

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
