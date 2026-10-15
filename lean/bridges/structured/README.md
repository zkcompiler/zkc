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
copies its executables before testing. Use separate report directories to keep
different runs distinct. `--compiler`, `--reference`, `--lean`, `--cases` and
`--seed` select explicit tools and generated cases. Failed comparisons retain
their source, requests and outputs beside the report.

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

`TotalState.process_eq_checked_reference` proves the ordered pair fold for
arbitrary lists, including refusal outside the unsigned-index domain.
`UnitState.process_eq_checked_reference` proves the complete result: an admitted
nonempty list aborts exactly when its predicate enables the zero-result step.
Both are parametric in the scalar commutative ring. They are equations for the
actual admitted constructor subjects; no finite test enumeration supplies them.

These model equations and finite native comparisons are separate evidence.
The writer, parser and renderer are tested executable boundaries. This package
does not prove C++ export correctness, frontend translation, native lowering,
production arithmetic/sampling, runtime capacity equivalence or protocol
security. The complete Schnorr and Sumcheck targets require later group,
communication, service and interactive-control support.
