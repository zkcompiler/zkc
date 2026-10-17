# Transcript-construction bridge

`check.py` connects five compiled proof Entries, `example::Proof` of the
Schnorr, Sumcheck and composed Sumcheck example projects and
`example::AndProof` and `example::EqualityProof` of the Sigma example project, to
the
[formal transcript-construction rule](../../docs/spec/fiat-shamir.md) and the
[participant projection rule](../../docs/spec/participant-projection.md). It is
part of `python3 common/tests/run.py lean-native`.

## Reproduce

From the repository root, with the compiler and the main Lean package built:

```sh
python3 lean/bridges/construction/check.py --output build/experiments/construction/run-1
```

`--compiler` selects `zkc-compile` (default `build/compiler/zkc-compile`) and
`--lake` the Lake executable. `--output` must be a new or empty directory; each
subject writes into its own subdirectory. `--write` rewrites the retained Lean
data this bridge owns from the fresh export instead of requiring it to be
unchanged.

## What is checked

For each subject:

1. `language-emit` and `language-bundle` produce the Entry's original source and
   native deployment; the deployment must name the emitted bytes, and its
   policy is retained.
2. `protocol-construct-proof` constructs the candidate, and
   [`protocol-constructed-participant`](../../../docs/spec/formats/constructed-participant.md)
   checks and exports its validator. `protocol-structured` exports the original.
   Both exports must name the same source bytes and policy.
3. The retained Lean data must equal the fresh renderings byte for byte: for
   Schnorr `lean/ZkcExamples/Construction/SchnorrProofData.lean` (rendered by the
   structured bridge's `snapshot.py`) and `SchnorrProofParticipant.lean`
   (rendered by `render.py`); for Sumcheck the structured bridge's own
   `lean/ZkcExamples/Structured/SumcheckSourceData.lean`, which this bridge only
   compares, and `SumcheckProofParticipant.lean`; for the composed Sumcheck
   `ComposedSumcheckProofData.lean` and `ComposedSumcheckProofParticipant.lean`;
   for the Sigma Entries `SchnorrAndProofData.lean`,
   `SchnorrAndProofParticipant.lean`, `ChaumPedersenProofData.lean` and
   `ChaumPedersenProofParticipant.lean` (their typed bodies, printed by the
   structured bridge's `bodies.py`, are not compared: `structured_views` admits
   the original from them in the kernel). For Sumcheck the comparison is also the
   pin that the Proof Entry's original export is the admitted Sumcheck source of
   the security theorems (check
   `regenerated:lean/ZkcExamples/Structured/SumcheckSourceData.lean`).
4. A generated Lean file runs the composed check `checkCompiled` in the kernel
   on the fresh export against the admitted original program, which must be
   accepted with axioms among `propext`, `Classical.choice` and `Quot.sound`; the
   fresh original snapshot must be the retained one. Mutated exports must be
   refused for their named obligations. For Schnorr: the first observation
   absorbs the base instead of the commitment, the challenge reads the host
   transcript before the commitment is observed, the challenge origin names the
   delivery site, and the final comparison compares the base with itself. For
   Sumcheck: the challenge origin names the delivery site, the round check is
   dropped, the claim update adds the low term twice, and the loop yields the
   claim it started with. For the composed Sumcheck: the conjunction reads the
   left check twice, and the right terminal check reads the left reduction's
   point and claim. For both Sigma Entries: the second observation absorbs the
   first commitment, a comparison compares the base with itself, and the
   conjunction reads the first check twice. Every mutation that keeps the transcript wiring is accepted
   by `checkExport` alone and refused by the projection rule. The same file
   checks that the Lean model of the canonical occurrence encoding
   (`templateTree`) encodes every exported template to exactly its native bytes.
5. Mutated candidates must be refused by the native checker before export. For
   Schnorr: the validator's challenge reusing its host transcript (exactly
   `native-proof-candidate` with the affine-reuse diagnostic) and a challenge
   origin naming the delivery site (exactly `native-proof-correspondence`). For
   both Sumcheck subjects: a constant changed in the prepared body of the last
   terminal check helper (exactly `native-proof-correspondence`); the Lean rules
   read helper calls with the original's checked helpers, so this is the native
   boundary. For both Sigma Entries: a challenge origin naming the delivery site
   (exactly `native-proof-correspondence`).

The retained `report.json` lists commands, exit statuses, hashes and checks per
subject.

## Boundaries

`render.py` classifies operations by exact name, operation binding and attribute
set, including `arith.andi` on Booleans as the Boolean conjunction. An
unrecognized operation is retained as unsupported for the rule to refuse; a
recognized one with another shape refuses the export
(`lean/checks/check_construction_renderer.py` exercises the conjunction). It
decodes each origin's canonical bytes into a template with its application and
repeat steps, requires the static coordinate array to be empty and re-encodes it
exactly. It parses printed MLIR types of the scalar, vector, index, transcript
and coordinate sorts and refuses others. Native exporter correctness, this
rendering, and the meanings of native kernels are tested boundaries, not
theorems.
