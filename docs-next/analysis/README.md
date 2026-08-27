# Protocol Property Analysis

> **Document kind:** Domain index
> **Document state:** Active non-normative K3-C target
> **Target alignment:** Bounded minimum Analysis kernel over K1, K2, and K3-B
> **Provisional owner:** `analysis`
> **Authority:** None during transition. The current property calculus remains
> governed by the [Soundness Kernel specification](../../docs/spec/soundness.md).
> The pages in this directory define a redesign target only; they establish no
> theorem, property, implementation support, migration result, or consumer
> reliance.

## Purpose

`analysis/` owns conditional property judgments over exact admitted subjects.
It does not own those subjects, their execution, relation satisfaction, or the
truth of an imported theorem. Its minimum active pipeline is:

```text
finite K2/K3-B subject S
  -> finite relation-bound Fresh proposition and conditional judgment

abstract asymptotic family F
  + independently established family Fresh source-property judgment
  + exact family theorem-applicability judgment
  + retained theorem-truth premise
  -> conditional family Fiat--Shamir target judgment

conditional family target judgment
  + exact pointwise correspondence (F,n0,S,ell0)
  -> conditional finite-member target judgment
```

This is intentionally smaller than the earlier Stage 4A catalog. K3-C closes
one reusable ingress and these typed seams; it does not finish every Analysis
family. In particular, the finite judgment for `S` neither establishes the
all-`n` source property of `F` nor enters the AFK family transport directly.
K3-C defines no native proof basis that mints that family source-property
capability, so the family transport currently returns `CannotAnswer` unless an
independent proof authority supplies it.

## Owns

- finite, purpose-specific manifests selecting exact source-owned views and
  checked results;
- strategy classes, adversary interfaces, quantifier order, oracle and
  public-coin models, scheduling, resources, outcomes, and failures;
- the common question, hypothesis-free goal, conditional proposition, basis,
  support, validation, qualified-result, and authority disciplines;
- family-specific properties and their exact negative meaning;
- theorem schemas and exact applicability questions;
- typed quantitative expressions, theorem-specific transforms, and exact
  imports of authenticated loss-bearing occurrences;
- property transport over an affirmative source judgment and an affirmative
  theorem-applicability result; and
- Analysis cold replay of semantic/checker dependencies, kept separate from
  Protocol replay and cryptographic rewind.

## Does not own

- K1 identity, value, algorithm, failure, evaluation, or capability mechanics;
- `InteractiveCore`, Protocol, generated execution, deterministic replay,
  transcript construction, or `CheckedFSConstruction`;
- relation definitions, Interfaces, instances, satisfaction, Protocol/Plan
  bindings, bridge-use enumeration, or occurrence-local loss export;
- theorem truth, formal proof import, concrete hash security, or ROM
  realization;
- Compiler decisions, OIR validity, projection correctness, realization,
  endpoints, Evidence appraisal, or reliance; or
- a universal `Verified` state.

Structural admission and property establishment never alias. In particular,
an admitted FS Protocol or checked construction establishes no source property,
no theorem applicability, and no transported target property.

## Exact dependencies

The active minimum reads:

- [Executable Semantic Foundations](../foundation/executable-foundations.md)
  for `SemanticContentId`, canonical values, evaluation outcomes, and
  process-local authority;
- [Interactive Core](../pir/interactive-core.md) for admitted Protocols,
  `PublicBindingView`, `StrategyDecisionView`, `PublicCoinView`, `EffectView`,
  `ClaimReductionView`, `ExecutionView`, generated execution, and replay;
- [Fiat--Shamir](../pir/fiat-shamir.md) for
  `TranscriptDeclarationView`, `RequiredInfluenceView`,
  `ChallengeTransitionView`, `FSConstructionView`, and the checked same-Core
  Fresh/FS construction;
- [Interfaces and Plans](../pir/interfaces-and-plans.md) for exact external
  Statement and prover Witness roles; and
- [Relation Model](../relations/relation-model.md) plus
  [Protocol Correspondence](../relations/protocol-correspondence.md) for
  admitted relation meaning, checked Statement/claim/witness correspondence,
  run-grounded occurrences, directional bridge uses, and qualified lossy-use
  exports.

Every source remains owned by its producer. Analysis declares the exact fields
it reads and checks adequacy; it cannot reconstruct a second Core, transcript,
relation, occurrence graph, or authored loss count.

## Active K3-C profiles

The bounded active set is:

1. **Finite relation-bound Schnorr special soundness.** The Statement, claim,
   Witness role, relation instance, verifier equation, and accepting event come
   from exact K2/K3-B sources. Its universal pair quantifier is over one finite
   native profile, not an asymptotic family and not an AFK source theorem.
2. **Abstract classical-ROM Fresh-to-FS transport.** One exact asymptotic
   family description is matched to one exact theorem profile. The initial
   profile is the three-move, adaptive-statement specialization of Attema,
   Fehr, and Klooß for a `2`-special-sound family. It requires an independently
   established uniform all-`n` source property, exact family experiment and
   map correspondences, a finite bounded-bitstring oracle-index carrier, one
   fixed challenge cardinality `N` shared by all family members, a total
   uniform challenge process, an exact `0 <= Q < N` query domain, theorem
   truth, and the theorem-specific
   quantitative transform. This is an explicit restricted-query subprofile,
   not the full all-`Q` Definition 10 property.
3. **Pointwise family/member specialization.** A separately checked exact
   correspondence relates one representable family member `(F,n0)` to one
   native subject `(S,ell0)` and substitutes the family formulas pointwise. It
   cannot generalize a finite subject to all `n`.

These profiles are different propositions with different source authority. A
concrete run may pressure-test their occurrence maps; it never proves any
universal or asymptotic property.

## Qualified outcomes

Analysis preserves these outer distinctions:

```text
Affirmative(exact conditional judgment)
Negative(family-defined semantic counterexample)
Unsupported(exact family, model, or construct is outside the selected profile)
CannotAnswer(missing named semantic premise or source authority)
Refused(prohibited use or failed post-authentication applicability condition)
Malformed(noncanonical or structurally invalid input)
DeterministicLimitExceeded(no semantic answer)
CheckerFailure(implementation or admitted-provider disagreement)
```

Failed proof search is not a semantic negative. `Unsupported`,
`CannotAnswer`, `Refused`, and `CheckerFailure` are not interchangeable.

## Deliberate deferrals

The following earlier Stage 4A surfaces are not active K3-C contracts:

- general Protocol equality, trace refinement, declared change,
  distributional distance, and cost families;
- plain soundness, zero knowledge, malicious-verifier games, QROM,
  round-by-round and restoration families, and multi-prover independence;
- generic property composition, structural Core composition, coverage,
  persistence formats, caches, proof languages, theorem libraries, and
  external certificate systems; and
- whole-application security or artifact-wide discharge.

Adding one requires a separate family profile, exact source manifest,
experiment, theorem or rule edge, quantitative semantics, falsifiers, and a
named consumer. It is not achieved by adding a flag to either initial profile.

## Documents

- [Analysis Semantic Model](analysis-model.md) owns the common minimum ingress,
  experiment, identity, hypothesis, basis, authority, and outcome contracts.
- [Semantic Relations](semantic-relations.md) owns the exact K3-B relation
  source seam and the initial relation-bound property coordinates.
- [Cryptographic Properties](cryptographic-properties.md) owns the two selected
  experiment/property profiles and typed quantitative language.
- [Transport and Replay](transport-composition-and-replay.md) owns theorem
  applicability, property transport, loss-ledger consumption, and the three
  non-interchangeable replay notions.

The [Analysis and Compiler Architecture](../project/analysis-and-compiler-architecture.md)
records the larger federated decision. Compiler remains downstream and cannot
consume an unqualified or unsupported Analysis result.
