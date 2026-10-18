# Transcript-construction bridge

`check.py` connects the compiled `example::Proof` Schnorr Entry to the
[formal transcript-construction rule](../../docs/spec/fiat-shamir.md). It is part
of `python3 common/tests/run.py lean-native`.

## Reproduce

From the repository root, with the compiler and the main Lean package built:

```sh
python3 lean/bridges/construction/check.py --output build/experiments/construction/run-1
```

`--compiler` selects `zkc-compile` (default `build/compiler/zkc-compile`) and
`--lake` the Lake executable. `--output` must be a new or empty directory.
`--write` rewrites the retained Lean data from the fresh export instead of
requiring it to be unchanged.

## What is checked

1. `language-emit` and `language-bundle` produce the Entry's original source and
   native deployment; the deployment must name the emitted bytes, and its
   policy is retained.
2. `protocol-construct-proof` constructs the candidate, and
   [`protocol-constructed-participant`](../../../docs/spec/formats/constructed-participant.md)
   checks and exports its validator. `protocol-structured` exports the original.
   Both exports must name the same source bytes and policy.
3. `lean/ZkcExamples/Construction/SchnorrProofData.lean` (rendered by the
   structured bridge's `snapshot.py`) and `SchnorrProofParticipant.lean`
   (rendered by `render.py`) must equal the fresh renderings byte for byte.
4. A generated Lean file runs `checkExport` in the kernel on the fresh export,
   which must be accepted with axioms among `propext`, `Classical.choice` and
   `Quot.sound`, and on three mutated exports, which must be refused: the first
   observation absorbs the base instead of the commitment, the challenge reads
   the host transcript before the commitment is observed, and the challenge
   origin names the delivery site.
5. Two mutated candidates must be refused by the native checker before export:
   the validator's challenge reusing its host transcript (exactly
   `native-proof-candidate` with the affine-reuse diagnostic) and a challenge
   origin naming the delivery site (exactly `native-proof-correspondence`).

The retained `report.json` lists commands, exit statuses, hashes and checks.

## Boundaries

`render.py` classifies operations by exact name, operation binding and attribute
set. An unrecognized operation is retained as unsupported for the rule to
refuse; a recognized one with another shape refuses the export. It decodes each
origin's canonical bytes, requires a flat template and re-encodes it exactly. It
parses printed MLIR types of the scalar, transcript and coordinate sorts and
refuses others. Native exporter correctness, this rendering, and the meanings of
native kernels are tested boundaries, not theorems.
