# Actual constructed participant bridge

This bridge reads the actual source-checked native verifier, including expanded
selected Local handlers. It uses the existing construction command and checker.
It does not generate a reference verifier in place of the candidate.

## Build and extract

From the repository root, build the native compiler using the
[development guide](../../../docs/development/README.md). From `lean/`:

```sh
lake build
lake env lean Tests/Constructed.lean
```

The default build includes the `constructed-source` executable and its audited
replay module. The proof modules use the existing module system.

Using a retained protocol-profile source and strict native proof policy:

```sh
build/compiler/zkc-compile protocol-construct-proof source.mlir policy.json > candidate.mlir
python3 lean/bridges/constructed/extract.py source.mlir policy.json candidate.mlir Snapshot.json --namespace ActualVerifier
python3 lean/bridges/constructed/extract.py source.mlir policy.json candidate.mlir Snapshot.json --namespace ActualVerifier --check
cd lean
.lake/build/bin/constructed-source ../Snapshot.json
lake env lean ../Snapshot.lean
```

`extract.py` writes exact JSON and transparent Lean constructors. The generated
module contains the JSON syntax tree, a kernel-checked structural decoding
equation, an admission theorem, an `Imported snapshot`, and its equality to the
actual checker result. Text parsing and the executable text-capacity preflight remain outside the
decoding equation. The kernel proof checks structural interpretation and its
list, reference and control-depth limits.
`--check` regenerates both artifacts
and refuses any difference. The native command rechecks the entire supplied
candidate; a detached hash does not authenticate anything.

The [native schema](../../../docs/spec/formats/constructed-source.md) and
[formal contract](../../docs/spec/constructed-source.md) own the carrier and laws.
Primitive meanings remain explicit. Returned transcript state is retained.
Native provider descriptions, including Merlin, are never relabeled as ideal RO
implementations. Protocol/security normalization belongs to a separate consumer.

## Maintained controls

From the repository root:

```sh
python3 lean/bridges/constructed/check.py
python3 lean/bridges/constructed/codec_check.py
python3 lean/bridges/constructed/boundary_check.py
python3 lean/bridges/constructed/control_check.py
```

All accept `--compiler`, `--optimizer`, and `--output`. Outputs default to
`build/experiments/constructed`; source, policy, actual candidate, generic SSA,
JSON, generated Lean and run reports are retained there. Generated artifacts
are not checked into the repository.

The first driver compiles actual Helpers/Reordered Schnorr and Helpers/Horner
two-round Sumcheck sources. It checks every generated admission declaration and
records its transitive axioms in `axioms.log`,
then compares an independent interpreter of generic native SSA with execution
of the admitted Lean program. The test interpretation uses Z/97 arithmetic and
a deterministic state-sensitive transcript. This checks received values,
operand wiring, state successors, all final results, guard order and primitive
stops; it does not validate BLS arithmetic or Merlin.

The codec driver compiles a selected Stream-codec Schnorr construction, retains
actual range selection/decode guards/finalization, and checks valid, invalid-point,
invalid-scalar, truncated and trailing-byte cases under an explicit tokenized
codec interpretation. These are bridge execution controls, not a production
parser conformance theorem.

The boundary driver checks an actual authored decoder abort, retaining the
preceding primitive effects. The control driver compares runtime bounded loops,
nesting and sequential loops, actual indices, captured inputs, carried provider
state, zero iterations, bound refusal and provider stops. The exporter uses the
structured carrier for these bodies; general native branches, parameter-selected
counts and control inside selected Local handlers still refuse. The Lean model
also has checked branches, without claiming a native export for them.

Refusal controls include malformed shape/version, out-of-range references and
projections, wrong result types, malformed/missing replies, native candidate
mutation and detached carrier mutation. Well-typed stale-state and wrong-payload
substitutions admit but fail replay against the actual candidate's primitive
operands. The formal controls also cover explicit
terminal stops and rejection of unreachable instruction tails.

The replay request is `["zkc.constructed-run/0", input-tokens, replay]`; a replay
entry is `[[primitive-name, actual-operand-tokens], ["return", result-tokens]]`
or `[[primitive-name, actual-operand-tokens], ["stop", stop-reason]]`. The batch
carrier is `["zkc.constructed-runs/0", requests]`. Scalar `i1` tokens must be 0 or
1; other tokens are opaque naturals. Every reached request is checked, including
unused primitive results. Missing replies stop as `incomplete`; mismatches and
wrong reply shapes stop as `refused`. Event logs include attempted requests.
Replay does not supply or prove a cryptographic primitive interpretation.
