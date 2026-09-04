# R2 Clean-Room Protocol Probe

This disposable standard-library-only probe executes the
[`FRI-Grind-1` charter](../../docs-next/notes/semantic-revalidation-and-redesign/r2-protocol-witnesses/README.md).
It imports no zkc C++, MLIR, registry, generated vocabulary, or
`reference/oracle` code. Frozen facts and research deductions are recorded in
the [source record](../../docs-next/notes/semantic-revalidation-and-redesign/r2-protocol-witnesses/source-and-research.md).

## Run

From the repository root:

```sh
python3 evaluation/r2-protocol-model/run.py
python3 evaluation/r2-protocol-model/run.py --check
python3 -m unittest discover -s evaluation/r2-protocol-model/tests -v
```

The first command emits canonical JSON; `--output PATH` writes it.
`--repo-root PATH` may make the loaded checkout explicit but must resolve to
that same checkout: Python imports are fixed before arguments are parsed, so a
different checkout must invoke its own runner. `cases/expected-results.json`
is a separately authored drift oracle, not a separately implemented checker.
The tests exercise decisive boundaries. The repaired snapshot also passed a
context-isolated, non-authoring replay from a minimal copied checkout.

## Current evidence contract

The first lean refreeze reproduced exactly but failed cold semantic closure.
The adjacent [cold review and repair decision](../../docs-next/notes/semantic-revalidation-and-redesign/r2-protocol-witnesses/cold-review-and-repair.md)
records that failed-witness evidence, the repair contract, and the hashes of
the passing repaired refreeze. The first hashes identify only the failed
attempt and are retained rather than overwritten.

The repaired executor distinguishes one FS source-residual execution, one
external non-FS-derived Fresh grinding support point, one FS-coupled Fresh
grinding execution, and one FS-coupled Fresh no-grinding execution. Successful
canonical forms end at `fri-terminal-not-modeled`; separate transition cases
cover bounded-strategy `Abort` and verifier `Reject`. The repaired refreeze and
non-authoring replay pass. Immediate rejection is a witness-local short
circuit for the modeled check/route predicate, not paper-trace equivalence.

The former abstract authenticated-opening terminal is withdrawn as
self-fulfilling. Any synthesized `Accept`, FRI-completeness, or
`local_completion` result is invalid R2 evidence. The external Fresh form proves
exact tape provenance and absence of an FS-record dependency only. It does not
establish uniformity, stochastic independence, nonce-before-tape authoring, or
general non-anticipation. Coupled tapes remain limited comparison evidence.

`InputBundleId` names the Statement and base prover inputs.
`ExecutionRequestId` closes over the scenario, application context, evaluator
basis, realization-specific search/fixed-nonce/tape controls, aggregate
resources, `CoreDerivationKind`, source fixture, and source package. Admission
reconstructs the package and requires its exact `InputBundle` plus either the
exact fixture grinding Core or exact drop-grinding projection. Request-local
search may intentionally override the package default.

`ApplicationContextId` is intentional semantic FS initialization, so changing
it is expected to rotate challenges. Evaluator, source, resource, and search
identities remain validation/provenance controls. Evaluator source digests
provide drift evidence only; they are neither semantic identities nor proofs of
equivalence. The evaluator basis binds separate request-execution and
qualification caps. Qualification pre-admits aggregate target-plus-dependency
replay, requalifies dependencies, exactly reexecutes the target, and records
aggregate actual usage.

`terms.py` defines one witness-local `SemanticRegimeId` and one bounded closed
finite-term ABI for tagged null, booleans, integers, UTF-8 text, bytes, canonical
sequences, and sorted string-keyed maps. Identities bind the regime, an ASCII
domain, and the encoded preimage; unsupported regimes are rejected. This is not
a universal v0 ABI.

The current fixture supplies an anchor reference but no independently
identified relation-side public value. The frozen executable's affirmative
Statement bridge is withdrawn; repair must return `MissingDependency`. A
positive bridge requires a qualified Protocol Statement occurrence, an
independently identified relation-side operand, and an explicit typed map.
The executable reports no grinding-event or protocol-success probability. A
hybrid is reported only after an identified skeleton/realization factorization
and checked composition laws; otherwise it stays open.

`r2model/frigrind.py` owns finite semantic terms, source grounding, and
witness-local scenario admission. `execution.py` owns the fixed-strategy
executor, terminal laws, request admission, and replay qualification; it is not
a general adversary semantics. Durable semantics must instead parameterize
execution by protocol, strategy, inputs, and verifier coins. `relations.py`
owns Core-derived relation shapes, reusable validation profiles, exact run
evidence, hybrid factorization, and bridge judgments. `report.py` assembles a
bounded identity graph rather than duplicating traces or schemas. Its replay
basis binds the `relations.py`, `report.py`, and `run.py` source digests; the
expected-results oracle freezes that basis together with semantic roots,
execution and relation identities, cases, root identities, and the report
identity. `terms.py` owns the explicit local regime and term ABI.
`cases/frigrind-invocation.json` supplies the concrete invocation;
`cases/frigrind-external-fresh.json` supplies the external Fresh support point.

R2 remains active and Stage 4B inactive. The probe establishes finite
structural falsification results only—not FRI, FS, grinding, ROM/QROM, current
implementation, distributional uniformity or independence, artifact-authoring
chronology, general non-anticipation, probability, theorem applicability,
security, or final-architecture claims. Delete or relocate it when R2 is
absorbed; no durable specification may depend on this directory.
