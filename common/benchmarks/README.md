# Protocol measurements

[`protocol_math.py`](protocol_math.py) compares complete FRI, imported AIR/STARK,
machine LogUp and machine grand-product proofs through the existing compiler
and native CLI. It uses Python's standard library and the maintained
[`processes`](../../scripts/processes.py) lifecycle helper. It does not import
pytest integration modules, build tools, synchronize dependencies or modify
the selected source trees. Input preparation reuses the maintained example
scripts and their small adapter dependencies.

## Run a comparison

Run from a checkout with Python 3.12 or later. Supply existing executables as
file paths; there is no PATH search or implicit build-directory selection.
The output directory must not exist. The baseline HEAD must match the requested
revision supplied with `--baseline-revision`, and every consumed baseline file must match that
commit. Current source may be dirty: its exact consumed files are copied and
hashed. Finish library edits before starting a comparison.

```sh
python3 common/benchmarks/protocol_math.py \
  --baseline-revision COMMIT \
  --baseline-source /path/to/original-checkout \
  --baseline-compiler /path/to/baseline/zkc-compile \
  --baseline-runtime /path/to/baseline/zkc \
  --baseline-opt /path/to/baseline/zkc-opt \
  --current-source /path/to/current-checkout \
  --current-compiler /path/to/current/zkc-compile \
  --current-runtime /path/to/current/zkc \
  --current-opt /path/to/current/zkc-opt \
  --repetitions 3 --release-storage --interactive-storage \
  --output build/experiments/protocol-measurements
```

The matrix always contains baseline default, current default and current
`--no-finite-bulk`. `--release-storage` adds current default with storage release
as its own policy; it does not silently change either default. The same binary
paths may be supplied for both sources to isolate source changes. Distinct
binaries compare the combined source/tool changes. A binary's SHA-256 is its
identity here; the adjacent source revision is **not** a verified build provenance
claim. Installed source modules embedded in the compiler belong to that binary.

`--baseline-only` omits all current arguments and runs just baseline default for
prototyping. Repeat `--case NAME` to select a subset. `--timeout SECONDS` bounds
each subprocess (default 300); a timeout is a failed sample. There is no silent
retry, higher runtime capacity, skipped refusal or timing threshold. Existing
runtime capacity records and work limits are retained in each report.

## Workloads

| Case | Profile and inputs |
|---|---|
| `fri-32`, `fri-64` | 32/64 Ext8 evaluations, degree below 8/16, 3/4 folds, 8 queries |
| `fri-1024` | 1,024 Ext8 evaluations, degree below 64, 6 folds, 8 queries |
| `air-stark-32`, `air-stark-64`, `air-stark-1024` | Imported recurrence Bundle, fixed 8-row trace, 32/64/1,024 evaluation points, 8 queries and OOD attempts |
| `machine-logup-absent`, `machine-product-absent` | Arithmetic-only fixture: CPU/program height 4; optional memory absent; 64-point domain |
| `machine-logup-present`, `machine-product-present` | Store/load fixture: CPU/program height 16, memory height 32; 64-point domain |

Each source's project manifest supplies modules and captured assets. The tool
copies the selected Entry into the output and changes only exact FRI/STARK
profile anchors; an unknown or repeated anchor refuses. FRI inputs use integer
polynomial evaluation in the documented Ext8 field. AIR/STARK and machine inputs
come from their example preparation scripts. Baseline and current public/witness
documents must agree before measurements start.

These are bounded implementation profiles. The 1,024-point cases add a larger
evaluation domain; they do not constitute a scaling study. The imported recurrence's height remains eight; changing its
evaluation domain does not create a larger AIR. Machine shapes exercise both
presence paths and both interaction reductions. They are not general zkVM
workloads or evidence of cryptographic soundness.

## What is measured

| Field | Meaning |
|---|---|
| `compile_wall_seconds` | Direct `language-package` process: capture, frontend, checked realization/lowering, serialization and process/output-transport overhead |
| `frontend_emit_wall_seconds` | Separate `language-emit` process: capture, analysis, Entry closure, checked translation and original IR emission; not parsing alone |
| `preparation` | Optional, separate `zkc-opt` preparation invocation, stage microseconds, before/after operation counts, decision/capacity remarks and prepared inventory |
| `original_inventory` | Static generic logical operation and binding-declaration counts from the packaged original |
| `emitted_inventory` | Static executable kernel binding/contract/implementation inventory and op-site counts in all emitted functions/participants, including unused definitions |
| `prove`, `verify` | Separate native CLI process wall times, including package admission, I/O, transcript, execution and cleanup; report counters remain separate |
| `instructions`, `iterations` | Executed work reported by the native runner |
| `logical_bytes` | Cumulative logical byte work; not physical memory |
| `total_value_bytes` | Cumulative fresh retained-value allocation charge; not peak or exit memory |
| `ring_work`, `external_work` | Provider work counters, with their reported limits; not wall time |
| `package`, `proof` | Exact serialized file sizes and SHA-256 identities |
| `exit_storage` | Proof report live counters when exposed; otherwise `null` with explicit missing-field names |
| `interactive_storage` | Optional separate interactive Entry, per-role exit usage/live resource units/retained output units and raw report |

Supplying each `--*-opt` enables `trace-mathematics` using the same finite-bulk
policy on the independently emitted original. Successful diagnostics must
contain stage measurements; unsupported tools fail visibly. Omitting it records
unavailable preparation data. Remarks are retained without repeating the entire
IR on every diagnostic. Original and prepared IR are retained separately.

The full compiler CLI does not expose internal realization timing. The separate
preparation run therefore does **not** identify every decision of full package
compilation, participant demand lowering, or proof construction. Do not subtract
the frontend process time from total compile time to invent realization time.
Do not sum nested stage times or infer aggregate work allowances from operation
counts: the CLI exposes stage records and capacity remarks, not the observer's
complete work-budget structure. Storage release is a later physical policy and
does not change this preparation pass.

The current proof report does not expose live retained-value bytes or live
resource units. `--interactive-storage` obtains available exit counters through
the corresponding interactive protocol instead. The product case adds an
interactive Entry to an output-local copy. Interactive execution uses its own
randomness/session and is a separate observation; it is not Fiat–Shamir proof
timing or a substitute for missing proof live counters. Exit storage can be zero
after release. Neither it nor cumulative allocation measures peak memory or RSS.

## Evidence and acceptance

The output contains only a source snapshot, prepared cases, process journals and
repeated run artifacts. No complete build tree or optional upstream workspace
is required. Runtime/compiler shared-library dependencies must already work in
the selected environment. Each run retains its package, proof, IR, diagnostic
stream, JSON CLI reports, commands, exit codes and wall times. Source inputs,
dependency locks, binaries, measurement code, Python version and host details
are recorded. Only named locale/Python environment overrides are recorded;
arbitrary inherited environment and dynamic-library closure are not captured.

`manifest.json` retains all samples, `summary.json` and `summary.csv` give
min/median/max per case and variant. Execution is serial with variant order
rotated by repetition. There are no warmups, cache flushes or CPU pinning. All
repetitions, including the first, are retained; timings are advisory. Diagnostic
processes are separately timed but can still affect cache state. Binary/source
changes detected at the end invalidate the comparison. The copied inputs and
original failed attempts remain available for inspection.

Subprocess output is captured through pipes to avoid timeout polling intervals
dominating short runs. Wall timing stops after process completion/output capture,
before the tool writes its retained stdout/stderr files. The tool therefore
temporarily holds each subprocess output in memory; it is not a memory profiler.

Acceptance is hard: every requested compile, policy check, frontend identity
check, available diagnostic pass, proof production, verification and changed-public
refusal must succeed. Optional interactive storage
observations must also accept. A failed cell has no timing summary; the command
returns nonzero if any cell fails. No equality of proof bytes across different
source packages is required: source/policy changes can change transcript
bindings. This checks the selected public statement's acceptance and rejection
controls, not a general equivalence theorem.

## Focused checks

```sh
uv run --no-sync --locked pytest common/tests/harness/test_protocol_measurements.py
uv run --no-sync --locked ruff check common/benchmarks/protocol_math.py \
  common/tests/harness/test_protocol_measurements.py
python3 common/tests/check_docs.py --all
```

The harness checks independent FRI values, input preparation from a minimal
copied source closure, profile selection, explicit tool selection, baseline
identity, inventories, missing report fields, failed-run retention, timeout
cleanup and a controlled end-to-end trial. These checks require no compiled
project tools; actual native measurements require the supplied executables.
