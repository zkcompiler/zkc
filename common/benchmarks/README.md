# Benchmarks

The benchmark suite compares compiled zkc protocols with independent implementations.
It uses explicit, already-built tools and writes a new evidence directory. It never
builds dependencies, tunes the machine, changes runtime limits or retries failed samples.

## Run

Build the benchmark client in the development environment:

```sh
cargo build --release --locked -p zkc-benchmarks
python3 common/benchmarks/run.py list
python3 common/benchmarks/run.py run \
  --suite schnorr --suite sumcheck \
  --compiler build/compiler/zkc-compile --runtime target/release/zkc \
  --worker target/release/zkc-benchmarks \
  --output build/experiments/benchmarks
```

All executable options are file paths. Select individual workloads with repeated
`--case`, or families with repeated `--suite`; combining them takes their intersection.
With neither option, all families are required, including the optional Monero build.
The default is four fresh processes per implementation/operation, two warmup
samples and five measured samples per process, one call per sample. `--processes`,
`--warmups`, `--samples` and `--iterations` make these choices explicit. A quick
correctness trial can use `--processes 1 --warmups 0 --samples 1`.
`--source` selects the project source tree. The executing harness and its imported
helpers always come from this checkout; both sets of consumed files are captured.

`--threads` sets `RAYON_NUM_THREADS` (default one), not a universal thread limit.
Workers record their observed exit thread count and confirm the requested environment
and affinity. `--cpu` optionally binds the
experiment and its children to one allowed CPU. The harness does not change the
frequency governor, turbo or SMT. `--seed` shuffles case/operation blocks;
each implementation pair runs consecutively, with order reversed on alternating repetitions.
An odd requested process count leaves one extra repetition in one direction.
The schedule seed does not seed production prover randomness. Builds or other CPU-intensive work
should finish before measurements start. Small process counts and busy hosts
produce exploratory measurements, not reliable rankings.

### Monero

Build `monero-benchmark` with the [pinned reference build](../tests/reference/monero/README.md)
in Release mode, then supply both `--monero /path/to/monero-benchmark` and
`--monero-source /path/to/pinned/monero`. The benchmark uses upstream randomness;
the reference's deterministic replay wrapper is linked only into `monero-reference`.
Run `--suite monero` to measure aggregation counts 1, 2, 4, 8 and 16.

## Workloads

| Family | Definition | Comparison |
|---|---|---|
| Schnorr | BLS12-381 G1/Fr, Spongefish 0.7.4 SHAKE128, 80-byte proof | Ordinary library and construction versus direct arkworks/Spongefish calls |
| Monero BP+ | 64-bit amounts, mixed test values, pinned Monero transcript and binary encoding | Ordinary library versus upstream C++ prover/verifier |
| Sumcheck | Public multilinear table, 16–4,096 entries, contiguous halves, MSB-first variables, pair-valued rounds | Ordinary Sumcheck library versus an independent linear-time Rust implementation |

Sumcheck's [Entry](projects/sumcheck/main.zkc) binds the ordered table, claim and
round count using an authored Spongefish construction. Its verifier evaluates
the public table, so verification is linear in table size. It has no PCS or
zero-knowledge claim. The independent implementation must produce identical
proof bytes. The other two provers use fresh randomness, so proofs are checked
by cross-verification, not byte equality.

These are complete implementation-stack comparisons. Monero uses different curve
and multiexponentiation code; zkc also performs input admission, interpretation,
service management and result reconstruction. Ratios do not isolate compiler
overhead. All calls in one case reuse a fixed public statement and witness;
this is repeated-statement throughput, not a changing-statement or batch-verification
workload. Input identities and these distinctions are retained in each contract.

## Measurement boundaries

| Metric | Included |
|---|---|
| Compilation process | CLI, project capture, compiler and package publication; repeated with package identity checked |
| Admission | First package capture, authentication and native admission per zkc worker; excludes reading package bytes |
| First call | First invocation in a fresh worker, including the first warmup when enabled |
| Repeated API calls | Transcript initialization and statement binding, proof encoding/decoding and protocol execution; Host also performs adaptation and checks |
| CLI observation | A separate prove/verify process including file I/O and admission; one exploratory observation per case |
| Process peak RSS | Worker lifetime high-water mark, including setup, warmups, reports and proof retention; not per-call or incremental allocation |
| CPU time | Process CPU clock over each call, including clock instrumentation; may exceed wall time with parallel work |

Input JSON decoding and request construction precede each Host timer. Reference
inputs are decoded before the loop; reference-owned table copies happen inside
the protocol call. Protocol temporaries (including reference transcript states and C++ proof objects)
are destroyed inside the timer. Returned Host reports or reference proof byte buffers
are consumed and destroyed outside it, as are proof file writes. The next call starts after those outputs are consumed. Warmups are retained
but excluded from summaries. The timer floor is reported and never subtracted.
The Host client currently consumes inline JSON inputs without external file resolvers
or setup authorities. New workloads can add those through the ordinary Host API.
Runtime work counters come from the last successful call, not from the wall timer;
cumulative allocation counters are not peak memory.

The process journal's wall time includes the entire worker, including preparation,
all calls and output writing. It must not be confused with the per-call timer.
No attempt is made to flush filesystem or CPU caches. Compilation, negative controls
and preparation checks can warm system caches before timed workers. Upstream Monero
initializes generator and multiexponentiation tables once per process; first-call
timing includes that cost, while repeated calls reuse those tables.

## Correctness and evidence

Before measuring a case, both implementations verify both proofs and reject a
changed statement, truncation and trailing bytes. Every timed verification must
accept. Every produced proof, including warmups, is retained and verified by the
other implementation after all timed workers exit. Deterministic proofs must match
the control bytes on every call, including CLI execution. Randomized provers must
not repeat a proof across controls, CLI calls or workers. A failed gate, timeout, crash, missing sample or changed
captured input invalidates the run's timing summaries and ratios. Partial evidence
remains available; failures are never dropped from a favorable aggregate.
Timed verifiers consume the same reference-produced proof bytes. Negative controls
require proof rejection; an unrelated execution or resource-limit failure does not pass.

Each output directory contains:

- `plan.json`: selected matrix, contracts, sample plan, seed, schedule, host and input identities.
- `manifest.json`: plan information, outcomes, raw worker samples and correctness results.
- `report.md`, `summary.json`, `summary.csv`: descriptive summaries.
- `capture/`, `packages/`, `cases/`, `runs/`: consumed source files, compiled artifacts, inputs, proofs and command journals.

Summaries use each process's median as one observation. Ratios pair corresponding
process repetitions and report their median and dispersion; no significance test
or performance pass/fail threshold is inferred. Raw samples remain available for
other analyses.

```sh
python3 common/benchmarks/run.py report RUN/manifest.json --output NEW_REPORT
python3 common/benchmarks/run.py compare BASELINE/manifest.json CURRENT/manifest.json
```

Cross-run comparison requires matching workload contracts, sampling choices and
host metadata. It cannot establish that background load was equal. Binary hashes
identify selected executables; captured sources do not prove how those binaries
were built. Workers report compiler/optimization facts; unoptimized client builds
and client builds with debug assertions are refused. This does not certify
dependency optimization or exclude per-package profile overrides. An allowlist records performance-related
environment variables without copying unrelated credentials. Dynamic library closures are not captured. Generated results stay
under ignored build directories; published numbers should cite retained evidence.

## Architecture and extension

- [`bench/workloads.py`](bench/workloads.py): case sizes, protocol inputs, semantics and optional upstream requirements.
- [`bench/suites.py`](bench/suites.py): common source preparation, compilation and interoperability controls.
- [`bench/runner.py`](bench/runner.py): capture, scheduling, worker lifecycle and evidence retention.
- [`bench/results.py`](bench/results.py): worker validation, summaries and comparison.
- [`zkc-benchmarks`](../../crates/zkc-benchmarks): generic Host client and independent Rust algorithms.
- [`monero.cpp`](monero.cpp): upstream C++ client using the same worker result contract.

Add a workload definition and an independent client where needed. Reuse the common
Entry adapter for source protocols; add another adapter for a genuinely different
measurement boundary. The scheduler and statistics contain no protocol algorithms.
Benchmark clients have no test-only execution provider and introduce no production
runtime branches. This design follows the explicit worker/warmup separation in
[pyperf](https://pyperf.readthedocs.io/en/stable/run_benchmark.html) and the setup,
interleaving and timing-boundary guidance in
[Google Benchmark](https://google.github.io/benchmark/user_guide.html).

The existing [protocol mathematics comparison](protocol-math.md) measures source
and compiler policies for FRI, AIR/STARK and machine protocols. It shares the
process journal with this suite and retains its different measurement contract.

## Validation

```sh
cargo test --locked -p zkc-benchmarks
uv run --no-sync --locked pytest common/tests/harness/test_benchmarks.py \
  common/tests/harness/test_protocol_measurements.py
uv run --no-sync --locked ruff check common/benchmarks
python3 common/tests/check_docs.py --all
```

Harness controls cover malformed and incomplete worker results, process failure,
timeout cleanup, input mutation, complete-run summaries and comparison contracts.
Real protocol gates require the selected built tools and optional upstream build.
