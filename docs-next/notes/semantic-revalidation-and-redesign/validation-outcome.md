# R1 Cold Validation Outcome

> **Document kind:** Temporary failed-gate and validation record
> **Document state:** Active
> **Owner:** `project`
> **Authority:** None. This page records falsification results and amendments;
> it neither selects a semantic model nor authorizes R2 or Stage 4B.
> **Input boundary:** Context-isolated validators received the frozen public-
> ready brief and inspected only the repository evidence needed to test it.
> They did not read `docs/private/` and did not edit the checkout.
> **Disposition:** Absorb any durable method consequence, then delete this page
> with the cycle package after the final validation gate.

## 1. Validation identity and independence boundary

The first cold pass ran on branch `feat/value-profiles` at commit
`6cea581c45dffe48f8ee1123c8066f10aa650d73`. Three fresh, context-isolated
reviewers independently covered Fiat--Shamir/execution, Relations/identity,
and method/current-system claims. Two reviewers used additional context-
isolated subreviews for narrow counterexample searches.

This is independent role separation inside the same review session. It is not
claimed to be an external human audit, a different organization, or an
independent implementation. Agreement counts only where the repository
evidence and counterexample survive reconstruction.

## 2. Frozen first-pass inputs

The reviewers verified the branch, commit, and all three published hashes
before reading beyond the brief.

| Frozen input | SHA-256 |
|---|---|
| R0 baseline | `a779e5a9153cdbddb16efc6e188e6f660fd4387481656082765166cc5a29df72` |
| Pre-validation R1 adjudication | `e50e804af28b073a1458779369949378ca9dcede92c88d225b2be14b91fe0d75` |
| Pre-validation R1 invariant ledger | `f65ab53f22478c111937b9a1c8f08b50a222d69733644703a43f92d2b5ef4ac4` |

## 3. First-pass gate result

**Result: failed, with the central diagnosis preserved.** The pass found one
material factual reversal, multiple solution-smuggling requirements, two new
current-system findings, and several scope/status errors. Treating agreement
on the architecture as a pass would have defeated the purpose of the gate.

| Correction class | Material result incorporated into the amended record |
|---|---|
| Public-coin eligibility | Reversed FS-5 from partial confirmation to `Confirmed`: verifier-private invocation data can influence a prover-visible Wire-only verifier message that FS drops without an admission rejection. |
| Identity and ABI requirements | Restricted regime lifecycle laws to first-class regimes, scoped canonical-value closure to semantic boundaries, generalized self-binding to acyclicity, and replaced physically disjoint ABI families with kind-safe ABI typing. |
| Transcript requirements | Replaced unconditional exactly-once absorption with declared scope/order/multiplicity, and moved collision-free challenge occurrence naming under the squeeze/sample contract. |
| Strategy and replay | Required causal reproducibility and auditable traces without mandating two separately represented online/replay evaluators. |
| Fresh/FS relation | Retained explicit checked factorization while reopening identical-Core versus related-distinct-Core or bisimulation constructions. |
| Relations | Split whole-domain isomorphism, lossless embedding, and lossy projection; made loss accounting conditional on retained loss and required a grounded source/preimage premise. |
| Cost and evidence | Split raw observation meaning, evidence provenance/uncertainty, Analysis inference, and Compiler comparison among their proper owners. |
| Checked results | Required meaningful semantic negatives while allowing typed mismatch or malformed-evidence outcomes for deterministic derivation and conformance. |
| Derived artifacts | Allowed recomputation, independently checked certificates/proofs, or authenticated derived caches without granting authored semantic authority. |
| Current-system findings | Rebutted CUR-1 and CUR-6, reopened CUR-2, narrowed CUR-4 and CUR-7, strengthened CUR-3/CUR-5/CUR-8, and added CUR-9/CUR-10. |
| Method and prior art | Confirmed governance inconsistency, narrowed the implementation-planning claim, and partially confirmed bounded 2023 Wizard/Linea operational use without claiming an unchanged internal layer. |

## 4. Conclusions that survived falsification

All cold reviewers preserved the following central result:

- the target lacks a faithful first-class and complete Statement-to-challenge
  binding path;
- authored observation bits do not derive required transcript material;
- Protocol execution lacks a causal strategy-generation bridge;
- regimes, canonical boundary values, algorithms, and totality evidence do not
  yet form an independently executable identity bottom;
- Relations lacks constructible grounding, fact/schema, and regime contracts;
- no target lane owns directional lossy projection and its grounded loss;
- canonical ROBDD guards create a real unbounded-resource risk;
- temporary/durable duplication and governance inconsistency require later
  normalization; and
- none of those findings refutes the main Protocol/Core/interpretation,
  Interface/Plan/Relation, or Analysis/Compiler factorization.

These are closure and model-selection obligations, not security or correctness
claims about a future implementation.

## 5. First amended candidate

The adjudication and ledger were amended without changing durable semantic
pages, current specifications, production code, tests, or Stage 4B state.

| Amended input | SHA-256 |
|---|---|
| R0 baseline | `a779e5a9153cdbddb16efc6e188e6f660fd4387481656082765166cc5a29df72` |
| Amended R1 adjudication | `0ec508998bd2ece07b2399125479a59cb86d5c4d857b1ae2bd80cb260eab8a49` |
| Amended R1 invariant ledger | `f556098af17600fffd951350a43d72eb2279ad52e284ef513819d13646d8c2ff` |

## 6. First amended follow-up

**Result: failed under the stricter slice rule.** The overall validator
synthesis found the record passable, but two independent slices found that the
adjudication still described first-class regime lifecycle and literal
same-Core Fresh/FS as surviving decisions while the ledger reopened both
representations. Because a cold reader should not have to resolve that
ambiguity by implication, those slice failures controlled the gate.

The second amendment made the static/first-class regime split and the
identical-Core/related-Core/bisimulation fork explicit in the adjudication. It
also clarified cross-domain value ownership, removed the concrete FRI fixture
from the invariant itself, bounded the temporary-note count historically, and
clarified the deliberate current PIR/OIR label asymmetry and DOC-4 title.

## 7. Second amended candidate

| Amended input | SHA-256 |
|---|---|
| R0 baseline | `a779e5a9153cdbddb16efc6e188e6f660fd4387481656082765166cc5a29df72` |
| Second amended R1 adjudication | `29fafd1e0dccd0bb08eb7c0c3e558b037d2237d33349c36a458d080339e6af17` |
| Second amended R1 invariant ledger | `905f573c257b74ef36d33301070fc38d10138e9fe7cc10f337ebc786b0967afb` |

## 8. Final follow-up gate

**Status: Complete. Result: PASS.** A fresh context-isolated falsifier verified
the second amended hashes before and after review and found no remaining
material contradiction or solution-smuggling requirement. In particular, it
confirmed:

- common regime closure is distinct from conditional first-class lifecycle and
  static version/change laws;
- the checked Fresh/FS relationship survives while same-Core,
  related-distinct-Core, and bisimulation-style constructions remain open;
- F-02 ownership and X-05 fixture independence are exact;
- the M-7, CUR-2, DOC-4, and REG-6 clarifications match their live owners; and
- links, authority boundaries, hashes, and inactive Stage 4B state are
  consistent.

R1 is complete and R2 may activate. This pass authorizes only the R2 witness
program; it ratifies no final semantic model, theorem, implementation claim, or
Stage 4B activation. Any later evidence that defeats an R1 classification or
requirement reopens the exact affected item under X-06 rather than silently
changing this historical hash set.
