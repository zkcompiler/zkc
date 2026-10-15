# Structured native bridge

This optional bridge imports actual original protocol-profile MLIR with shared
helpers, finite folds and nested Local control into the common Lean region
semantics. The first profile is single participant and immutable Boolean,
unsigned index, BLS12-381 scalar and scalar-vector values. See the
[native format](../../../docs/spec/formats/structured-source.md),
[formal contract](../../docs/spec/structured-source.md) and
[protocol targets](../../docs/design/structured-native-import.md).

## Reproduce

From the repository root in the pinned development environment:

```sh
cmake --build build/compiler --target zkc-compile zkc-structured_reference-test -j 4
(cd lean && lake build)
python3 lean/bridges/structured/check.py \
  --report build/experiments/structured-source/report.json
```

To add production execution comparisons, build `zkc` and supply it explicitly:

```sh
cargo build --release --locked -p zkc-tools --bin zkc
python3 lean/bridges/structured/check.py \
  --runtime target/release/zkc \
  --report build/experiments/structured-source-runner/report.json
```

The report records the source revision, deterministic seed, exact commands,
exported source and snapshot hashes, and retained executable hashes. Each run
allocates a fresh directory under `runs/` beside the selected report and copies
its executables there before testing. The selected report is atomically marked
`running` before setup, then `pass`, `failed` or `interrupted`; it identifies the
run directory and its own retained report. Setup failures exit nonzero and
cannot leave the previous success selected or overwrite its tools.
`--compiler`, `--reference`, `--lean`, `--cases` and
`--seed` select explicit tools and generated cases. Failed comparisons retain
their source, requests and outputs beside the report.

Each run also retains `source-before.tar.gz` and a per-file byte manifest. This
is a snapshot of **all tracked and nonignored untracked project files**, using
current working bytes, including modified authored fixtures, proofs, all local
imports, drivers, manifests and toolchain pins. Deleted tracked paths are
listed in the manifest. Archived contents are verified against the captured
bytes. This costs one compressed project tree per run; it avoids a manually
maintained partial source list. Ignored build outputs, `.git` history and
external dependency caches are excluded. Reproduction still needs the pinned
Lean toolchain and external packages from `lake-manifest.json`; this is not a
hermetic archive of the host or of the native compiler build environment.
Extract the source archive into an empty directory to recover its working
tree. Initialize a Git repository and commit the restored tree there before
rerunning these drivers (Git supplies their source inventory and revision); the retained report still
identifies the original revision and archived bytes. Build Lean with the pinned
dependencies and supply the archived native tools through the explicit flags.

## What is compared

The C++ test reference independently traverses original native SSA operands,
blocks and helper definitions. It does not read the exported JSON or call the
writer. Lean decodes the writer's arrays, independently checks their admission,
forms shared `Source.Region` bodies and runs owned operation meanings. A Python
integer reference checks arithmetic modulo the actual BLS12-381 scalar modulus.
Optional Runner cases additionally traverse preparation and realization with
ordinary native providers in both default finite selection and forced loop mode.

Cases cover ordered two-result accumulation; empty-result callbacks that abort;
empty, singleton and longer domains; predicate-before-step behavior; helper
reuse at distinct actual arguments; exact bound provenance through nested helper
calls and reordered/repeated helper results; identical finite invariant actuals;
nested conditionals; ordinary and conditional counted loops; capture
forwarding; original Protocol guards; and full-size scalar arithmetic. Actual
`.zkc` Entries exercise both element and indexed accumulation through frontend
elaboration. Well-formed result permutations
and changed stop reasons are accepted as different programs. Malformed dormant
bodies, cycles, unsupported vocabulary, extra fields, invalid references and
wrong same-typed containers/captures are refused.
Boundary cases also compare exactly 4096 instructions and a complete 1 MiB
export, including its final newline. The reference counts stored instructions
in the same units as the format; its dynamic execution budget is separate.
Used Unicode and newline-containing helper names traverse native export,
independent import and evaluation without renaming.

Runner comparison observes ordered outputs, completed versus stopped execution,
the stop class, and empty active-frame/live-resource counts for these bounded
runs. It does not equate the full native event, diagnostic or resource model to
the Lean process. A nonzero Runner exit can report an expected semantic stop;
the bridge checks the structured result before classifying it.

## Actual proof subjects

The native [`total-state.mlir`](../../../compiler/test/fixtures/finite/total-state.mlir)
and [`unit-state.mlir`](../../../compiler/test/fixtures/finite/unit-state.mlir)
are the canonical subjects. Their retained JSON is `protocol-structured` output.
The bridge compares the source-byte digest, the entire exported snapshot and regenerated
transparent constructor data used by
[`TotalState`](../../ZkcExamples/Structured/TotalState.lean) and
[`UnitState`](../../ZkcExamples/Structured/UnitState.lean).

```sh
python3 lean/bridges/structured/snapshot.py \
  lean/bridges/structured/fixtures/total-state.json \
  lean/ZkcExamples/Structured/TotalStateData.lean \
  --namespace ZkcExamples.Structured.TotalStateData
```

The renderer emits data only. Admission and semantic equations are separate
kernel-checked declarations. Changing a fixture requires reviewing those
equations, rather than merely updating an identity string.
UTF-8 names remain data inside escaped Lean string literals. The independent
renderer check compiles generated declarations and compares their exact Unicode
codepoints in the kernel, including controls, quotes, backslashes, multibyte
length boundaries and text resembling Lean declarations. Its CLI control also
runs under an ASCII locale; source files and tool output use explicit UTF-8:

```sh
python3 lean/checks/check_structured_renderer.py
```

This check runs in `just test-lean`. It does not turn the renderer into a proved
translator.

`TotalState.process_eq_checked_reference` proves the ordered pair fold for
arbitrary lists, including refusal outside the unsigned-index domain.
`UnitState.process_eq_checked_reference` proves the complete result: an admitted
nonempty list aborts exactly when its predicate enables the zero-result step.
Both are parametric in the scalar commutative ring. They are equations for the
actual admitted constructor subjects; no finite test enumeration supplies them.

## Scalar inlining pairs

Two tiny authored single-role Entries retain mathematical helpers in their
original native MLIR:

| Subject | Scalar contract | Helper structure |
|---|---|---|
| [`schnorr-response.zkc`](fixtures/schnorr-response.zkc) | `nonce + challenge * secret` | One response helper |
| [`sumcheck-claim.zkc`](fixtures/sumcheck-claim.zkc) | `(1-r) * a0 + r * a1` | One claim helper calling the same weighted-product helper twice |

The Sumcheck source uses `weighted(a0, 1 - r) + weighted(a1, r)`; the decimal
literal is admitted by kernel reduction. Both computations are scalar
ingredients of protocols, without group operations or interactive security
claims.

[`SchnorrResponse`](../../ZkcExamples/Structured/SchnorrResponse.lean) and
[`SumcheckClaim`](../../ZkcExamples/Structured/SumcheckClaim.lean) prove complete
process equality between each exact imported original and the actual prepared
candidate, for every input in any `CommRing F` with `DecidableEq F`. Each client
uses named checked-body contracts. The response proof applies
`Structured.inline_invoke`, whose lookup/body premise covers every actual tuple;
it preserves stops and the caller's suffix without a totality assumption.
The controls in `Tests.StructuredInlining` cover stopping and returning
zero-result helpers, suffix stops, retained caller values, repeated arguments
and ordered multiple results.

The retained mutation changes only the prepared response entry's addition to
subtraction. It passes native formation and Lean admission. The kernel proves
that `(nonce, challenge, secret) = (2, 3, 5)` returns `17` in the original model
and `-13` in the mutated integer model.

After building Lean and the existing native tools, reproduce from the root:

```sh
python3 lean/bridges/structured/inlining.py \
  --compiler build/compiler/zkc-compile \
  --optimizer build/compiler/zkc-opt \
  --reference build/compiler/test/zkc-structured_reference-test \
  --report build/experiments/structured-inlining/report.json
```

This focused sibling reuses the bridge driver. It runs `language-emit` and
`language-interface`, then the actual
`--zkc-prepare-protocol="simplify=false optimize-finite=false"` command. It
exports both sides with `protocol-structured`, independently admits them,
compares exact retained MLIR/JSON/constructor bytes, and rechecks the proof
sources. Candidate snapshots use the format's `original` tag because each
export describes its supplied native input; their input is the retained
prepared MLIR. The entry contains no helper calls, although dormant helper
declarations remain in the module.

Default finite comparisons use four boundary/example tuples and sixteen seeded
full-size scalar tuples per subject, through both direct native SSA and Lean
execution. The admitted mutation is also compared. Reports retain commands,
outputs, complete project-source bytes and tool copies with hashes, toolchain,
affinity and thread settings. The
existing `just test-lean-native` scope includes this sibling. Host-level lock
coordination belongs to the invoking validation session.

`--write-fixtures` intentionally replaces the retained native subjects, exports
and constructor data. It never generates or changes semantic proofs; review
the changed subject and its checked body equations. These files follow the
`TotalStateData` pattern as actual proof subjects. Research logs and executable
copies remain in the run directory under `build/experiments`. Regeneration also
retains `source-after.tar.gz` so the archive contains the resulting fixture
bytes as well as the original working sources.

These model equations and finite native comparisons are separate evidence.
The writer, parser and renderer are tested executable boundaries. This package
does not prove C++ export correctness, frontend translation, native lowering,
production arithmetic/sampling, runtime capacity equivalence or protocol
security. The complete Schnorr and Sumcheck targets require later group,
communication, service and interactive-control support.
