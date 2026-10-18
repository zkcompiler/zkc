# Benchmarks

One scheduler measures independent protocol implementations, ordinary source
programs, and composed library workloads. Results remain separate by operation,
shape, input policy and timing boundary. There is no aggregate score or implicit
family weight. STARKs have more coverage because their distinct dimensions need
separate experiments, not because their cases count as extra votes.

## Run

Use explicit, already-built executables. The harness does not build dependencies,
tune the host, raise execution limits or retry failed samples.

```sh
cargo build --release --locked -p zkc-benchmarks
python3 common/benchmarks/run.py list
python3 common/benchmarks/run.py run --preset smoke \
  --compiler build/compiler/zkc-compile --runtime target/release/zkc \
  --worker target/release/zkc-benchmarks \
  --output build/experiments/benchmarks
```

The output directory must be new. Runs are exploratory by default: they do not
acquire a host-wide lock and can overlap with development work. Use repeated
baseline/current comparisons under similar load to identify broad trends;
concurrent timings do not establish small speedups.

Pass `--exclusive` to either benchmark entry point to acquire
`/tmp/zkc-benchmark-execution.lock` across preparation, timing and validation.
Exit 75 means another cooperating session owns the slot. Do not wrap the harness
in another acquisition or delete the lock file. Workers inherit the owned
descriptor so the slot remains held if the supervisor is killed.

`coordination.json` records whether the run was `uncoordinated` or `exclusive`,
its start/end times and, for exclusive runs, lock acquisition time. An exclusive
lock coordinates cooperating suites; it does not stop ordinary builds or isolate
unrelated host activity. Schedule a quiet interval explicitly for precise results.
Ordinary builds and tests should use separate output directories and bounded
parallelism, without a host-wide benchmark lock.

Selection options intersect:

- `--case NAME`: individual case; repeat to select several.
- `--suite NAME`: family; repeat to select several.
- `--preset smoke`: a fixed, small list covering the major execution paths.
- `--preset stark`: AIR (both single-table profiles), FRI, polynomial, extension, transcript and machine cases.
- `--preset execution`: all source controls and library workloads, without an external reference build.
- `--preset all` (default): everything, including the optional Monero comparison.

The default is four **sequential** fresh processes per implementation/operation,
two warmup samples and five measured samples per process, one call per sample.
`--processes`, `--warmups`, `--samples` and `--iterations` override these choices.
A correctness trial can use `--processes 1 --warmups 0 --samples 1`; it is not a
stable performance estimate. `--source` selects project/library sources; the
executing harness remains this checkout. Both are identified and captured.

Use `--compiler-option=--fuse-collect-fold` to measure an explicit compilation
choice; repeat `--compiler-option` to combine supported switches. The manifest
records the choices and captures the resulting packages. Compare separate runs
with identical sources, inputs and worker settings. A smaller intermediate or
instruction count does not by itself establish a timing improvement.

`--threads` sets `RAYON_NUM_THREADS` (default one), not a universal thread limit.
`--cpu` pins the suite and children to one allowed CPU. Workers check the requested
environment and affinity. The harness records governor/turbo/SMT settings but does
not change them. `--seed` shuffles case/operation blocks; paired implementations
run consecutively with their order reversed on alternate process repetitions.
Child processes receive a recorded, allowlisted environment: tool paths, temporary
paths, allocator/thread settings and explicit locale controls. Ambient feature
switches, Python injection paths and unrelated credentials are not inherited.
The schedule seed does not seed production prover randomness. Input generators use fixed,
recorded algorithms and seeds, with full generated inputs retained.

### External Monero comparison

Build `monero-benchmark` using the [pinned reference build](../tests/reference/monero/README.md)
in Release mode, then supply `--monero /path/to/monero-benchmark` and
`--monero-source /path/to/pinned/monero`. The client uses upstream randomness;
the deterministic replay wrapper is linked only into `monero-reference`.
`--suite monero` compares counts 1, 2, 4, 8 and 16.

## Coverage

| Family | Dimensions and purpose | Evidence limit |
|---|---|---|
| `schnorr` | BLS12-381 G1/Fr, Spongefish 0.7.4 SHAKE128 | Cross-verification with independent arkworks/Spongefish client |
| `monero` | BP+ proving/verification, 64-bit amounts, 1–16 commitments | Upstream C++ comparison; fixture amounts and small masks, not a sampled wallet workload |
| `sumcheck` | Public tables of 16–65,536 elements | Independent Rust algorithm; verifier includes linear public-table evaluation, no PCS |
| `finite` | Identical pointwise polynomial + sum as reduction, collect + sum, bulk operations, total collect–fold and total fold; KoalaBear and BLS12-381 Fr; 0/17/1,024/8,192 elements | Independent Python expectations; exposes source-form recognition and materialization differences |
| `scan` | Scalar ordered scan and bulk prefix sum; 17/1,024/4,096 elements | Full output check; source-form comparison, no presumed storage-release benefit |
| `control` | Rectangular nested loops, branches, indexing and carried state | Independent of machine libraries; not an unseen statistical holdout |
| `matrix` | Rectangular matrix-vector multiplication, dense and sparse occupancy | Python expectations; R1CS-like arithmetic, not a full proof system |
| `polynomial` | Dense coset evaluation/interpolation, base and degree-eight extension, 32–8,192 elements | Every evaluation and recovered coefficient checked; includes equality work |
| `extension` | Dense degree-eight extension multiplication, 1/17/1,024 elements | All coordinates vary; no general claim about other extension towers |
| `curve` | BLS12-381 point generation, vector scaling, MSM | Composed workload; scalar identity oracle shares native group kernels |
| `pairing` | 2/8/32 BN254 pairings and scalar multiplication | Bilinearity consistency, not Groth16/KZG or independent kernel validation |
| `transcript` | Independent round-count and payload-size variation | Ordered challenge recurrence and payload check; Merlin construction |
| `fri` | Domain size, dense polynomial degree bound and query count vary separately | Same-stack proof validation; degree bound is not domain size |
| `air` | Trace height, width and evaluation blowup vary separately | Quadratic recurrence with first/last/transition constraints; one table |
| `stark` | The `air` shapes through the [parameterized library](../../libraries/stark/README.md#parameterized-single-table-argument): quartic challenges, Poseidon2 multi-opening Merkle trees, constant final polynomial | Same AIR and queries as `air`, so the two profiles compare directly; same-stack proof verification |
| `bulletproofs` | BP+ source workload, counts 1/3/8/16; changing statements and preparation policies | Retained conformance inputs; independent comparisons remain in `monero` |
| `machine` | LogUp/grand-product, optional memory absent/present | Correlated STARK library regression; small fixtures, not a production zkVM scaling study |

The [source catalog](bench/coverage.py) records exact dimensions, operation mix,
category and limitations. Each run also records its oracle, input identities and
generated source/asset digests.
The two total finite forms use one explicit `math fn`, so collect and fold share
a numerical unit. Ordinary function calls can introduce separate ordered units;
collect–fold composition does not cross those boundaries.
Python oracles execute outside the SDK timer. They use dense deterministic field
values, including nonzero higher extension coordinates; the curve and pairing
controls explicitly use weaker algebraic consistency checks.

Broader coverage does not establish universal performance. Full Groth16/KZG,
recursive proving, production zkVM traces, other fields/hash families,
concurrent services and other CPUs remain separate experiments. Apply application
weights during interpretation, document them, and retain the unweighted rows.
Do not compare two workloads merely because both are called FRI or pairing.

## Changing statements and preparation

Source proof workloads can cycle distinct inputs through one admitted Entry.
Run workloads keep fixed inputs; `--input-count` does not change them:

```sh
python3 common/benchmarks/run.py run --case bulletproofs-3 \
  --input-count 3 --preparation both --warmups 3 --samples 9 --iterations 1 \
  --compiler build/compiler/zkc-compile --runtime target/release/zkc \
  --worker target/release/zkc-benchmarks --output build/experiments/reuse
```

Warmups and samples must each contain complete input cycles. Every invocation is
identified; reports retain first visits and repeated times **per statement** as
well as the declared schedule's aggregate. This is sequential reuse, not batch
verification. Every generated proof is checked against its own statement.

`--preparation enabled|disabled|both` selects matched source-proof jobs. Preparation
costs stay inside SDK calls; entries, retained bytes and hits are observed after
each call. `--preparation-entries N` lowers the default 128-entry bound for a
saturation control; the default byte bound and execution capacities stay unchanged.
It is recorded in the contract, not silently applied to other runs. Workers report the native default and the bounds passed to the Entry. Effective
statistics must respect those bounds; disabled preparation must retain no state.
Reports include final entries, retained bytes and hits. A bounded store need not
improve a workload, and hits alone do not establish a timing benefit. The machine fixtures support fixed inputs
only; BP+ uses at most four fixture patterns times the commitment count through
ordered permutations. Distinct public statements are checked before timing.
External comparison families retain their fixed-statement contracts and default
preparation policy.

## Measurement boundaries

| Metric | Boundary |
|---|---|
| Package capture | Authentication/capture after reading package bytes |
| Admission | Native Entry admission after capture; the existing `admission_ns` total is capture + admission |
| Decode/call | Fresh JSON decoding and request construction from preloaded bytes, before every Host call |
| SDK call | Input adaptation/admission, execution, service lifecycle and named output reconstruction; source controls also execute their result checks |
| First call / first visit | First invocation in a worker / first invocation for each statement, including warmup calls |
| Final diagnostics | One materialization after the last SDK call, measured separately |
| RSS snapshots | OS-reported worker lifetime high-water marks before/after final diagnostics and before serializing the final report |
| Process wall time | Entire worker, including setup, all calls and evidence writes |
| Compilation | External comparison: repeated CLI compilation; source controls: one compiler-process observation, excluding generation |
| CLI observation | Separate proof process including I/O and admission; exploratory, external comparison cases only |

Do not add medians of different boundaries to estimate end-to-end latency. Peak
RSS is not incremental allocation or live VM storage; retained inputs, allocator
state and observations contribute. These snapshots precede final report JSON
serialization; they are not an external measurement of the entire process peak. OS accounting can
be approximate. Runtime work counters describe the final call, not an allocation
profile. Intrusive profilers are separate experiments and must not supply release
latency rankings or causal percentages by subtraction.

Reference clients decode before their loops. Production protocol temporaries are
destroyed inside the call timer; returned reports/proof buffers are consumed
outside it. Only the final Host report is retained. Proof files are written
outside the SDK timer and verified after all timed workers finish. Input decoding,
proof I/O and observation still affect process time and memory. No caches are
flushed; preparation and correctness checks can warm system caches. The timer
floor is recorded and never subtracted.

## Execution counts

For runtime attribution, build a separate worker with execution observations:

```sh
cargo build --release --locked -p zkc-benchmarks --features execution-counts \
  --target-dir target/counts
python3 common/benchmarks/run.py run --preset execution --execution-counts \
  --compiler build/compiler/zkc-compile --runtime target/release/zkc \
  --worker target/counts/release/zkc-benchmarks \
  --warmups 0 --samples 2 --processes 2 --output build/experiments/counts
```

The harness requires the requested feature state and source workloads, permits at
most 128 calls per worker, and omits timing summaries and comparisons for these
runs. Raw clock readings remain diagnostic evidence. Default runtime builds have
zero-sized counters; enabling the Cargo feature adds storage and observation
work. Counts reveal reached control flow, so they are host diagnostics, not a
public-information projection.

`lifecycle.calls[].execution_counts` contains fixed event counters and native
invocations grouped by operation contract. The histogram combines instantiated
types and implementations of a contract; workload dimensions and captured
artifacts retain those distinctions. Do not infer a universal cost per call. Snapshot construction happens when
Host collects completion reports; JSON materialization happens after the SDK
call. Each participant and attempt contributes once. Reports retain per-input
first visits and deduplicate equal repeated vectors with their multiplicities.
`counts_repeatable` compares complete ordered count sequences across processes
(`null` with only one process);
variation must be explained before fitting a deterministic cost model.

| Counter group | Unit and boundary |
|---|---|
| `charged_instructions`, `replayed_instructions` | Successful instruction charges executed directly or replayed from public preparation; their sum equals resource instruction usage |
| `local_*` | Reached local instructions after a successful charge; `local_release` is an uncharged storage instruction |
| Native operation histogram, `native_operand_values` | Actual backend invocations and top-level operand values copied into invocation scratch |
| `created_frames`, `backend_enter_calls`, `backend_leave_calls` | Actual frame construction and attempted backend boundary calls; successful execution balances enters/leaves |
| `value_validation_calls`, `backend_validation_calls` | Runtime validation and backend validation requests; exclude checks performed internally by a backend |
| `retention_plan_calls`, `retention_planned_values` | Ledger planning requests and their top-level input values |
| `retention_commit_values`, `retention_release_values`, `retention_unpin_values` | Top-level ledger references, including return pins and replay; not heap allocations |
| `computation_reuse_hits` | Successful public computation replay |

Counts include validation and planning performed by explicit Host preflight calls such as delivery checks; they describe the actual Host invocation, not a minimal abstract schedule.

Counts alone do not identify time costs. Use clean release measurements on the
same artifacts and inputs, and report correlated counters when they cannot
separate candidate causes. No per-operation clocks or allocator interception are
installed. Failed Runner initialization has no snapshot; this mode measures
successful benchmark calls rather than failure profiles.

## Correctness and evidence

External comparisons cross-verify both directions and check deterministic proof
identity or randomized proof uniqueness. Source proofs use same-stack verification
and separate format, changed-statement and semantic controls. Semantic controls
use an invalid witness under the same public statement (FRI/transcript), a
canonical claim mutation (AIR/machine), or a canonical response mutation (BP+). The FRI control evaluates a polynomial one degree beyond the allowed bound.
Each refusal is tested in a fresh Entry and after one valid call
in the same Entry. Changing-input schedules also test a swapped proof. Every timed verifier
must accept; every produced proof, including warmups, is retained and validated.
Run programs must return a typed `accepted = true`; every source Run control also
tests a generator-supplied incorrect expectation at that acceptance gate. These are bounded execution checks,
not proof-system soundness results.

Controls check the observed refusal layer: framing for malformed proofs, binding
or verification for changed statements, and verification for semantic mutations.
Raw proof codecs perform format checks in the authored verifier, so those
controls require a verification refusal instead. The compiled Entry selects the
format. The worker records the error code and stop kind. Known format refusals include
the driver's subsequent cancellation. Truncation also permits the separately
recorded bounded-byte-read refusal, which alone does not identify the buffer read.
Failed calls retain preparation statistics before and after the refusal. Some
workloads have no eligible preparation, and early format failures need not reach
a prepared operation; a preceding successful call alone does not prove a hit.
Crashes, timeouts, unrelated cancellation and resource-limit failures do not pass.
Any failed gate, incomplete matrix or changed captured input invalidates the whole
run's timing summaries and comparisons. Failed evidence is retained.

Outputs include `plan.json`, `manifest.json`, `coordination.json`, reports in
Markdown/JSON/CSV, captured sources/inputs, packages, every produced proof and
command journals. An append-only `progress.jsonl` records worker completion; full
reports are written at phase boundaries, outside the timed worker sequence.
Summaries use medians of process medians. Paired ratios are
descriptive, not significance tests; no timing threshold decides correctness.

```sh
python3 common/benchmarks/run.py report RUN/manifest.json --output NEW_REPORT
python3 common/benchmarks/run.py compare BASELINE/manifest.json CURRENT/manifest.json
```

Cross-run comparison requires matching contracts, sampling and host metadata.
Binary hashes identify selected executables; adjacent source revisions do not
prove build provenance. Worker optimization facts do not certify every dependency.
Performance environment variables are allowlisted; dynamic library closures and
unrelated host activity are not captured. Publish measurements with retained evidence.

## Extension and validation

[`workloads.py`](bench/workloads.py) and [`suites.py`](bench/suites.py) own external
comparisons. [`coverage.py`](bench/coverage.py) and [`execution.py`](bench/execution.py)
own source cases. Both use [`runner.py`](bench/runner.py), [`io.py`](bench/io.py),
[`results.py`](bench/results.py), and the generic
[`zkc-benchmarks`](../../crates/zkc-benchmarks) Host worker. Add an ordinary source
workload and oracle, not a production protocol-specific executor.

[`protocol_math.py`](protocol-math.md) retains its distinct compiler-policy/CLI
comparison contract and shares the journal and optional execution lock. Research drivers
remain supporting evidence. This design follows worker/warmup separation in
[pyperf](https://pyperf.readthedocs.io/en/stable/run_benchmark.html) and explicit
boundaries/interleaving in [Google Benchmark](https://google.github.io/benchmark/user_guide.html).

```sh
cargo test --locked -p zkc-benchmarks
uv run --no-sync --locked pytest common/tests/harness/test_benchmarks.py \
  common/tests/harness/test_benchmark_coverage.py common/tests/harness/test_protocol_measurements.py \
  common/tests/harness/test_processes.py
uv run --no-sync --locked ruff check common/benchmarks
python3 common/tests/check_docs.py --all
```

Unit checks cover oracles, catalog dimensions, locks, lifecycle evidence, process
failure, incorrect acceptance, input identity and complete-run summaries. Real
benchmark matrices are opt-in and require the selected built tools.
