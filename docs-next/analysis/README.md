# Protocol Property Analysis

> **Document kind:** Domain index
> **Document state:** Active non-normative K3-C target; its finite executable
> join was exercised by bounded K3-E, while owner profile preimages remain open
> **Target alignment:** Bounded minimum Analysis kernel over K1, K2, and K3-B;
> its selected finite P01/Schnorr path has K3-E executable join evidence, while
> broader Analysis families remain deferred
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
- the exact Analysis language-profile contents, total bounded
  `AnalysisBodyV0` compiler, body-formation laws, and adequacy evaluators;
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
  for `SemanticContentId`, standalone `SemanticLanguageProfileId`, exact
  profile-import closure, canonical values, evaluation outcomes, the inert
  source-authority envelope, and process-local authority;
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
it reads through owner field coordinates, invokes one exact adequacy evaluator,
and consumes the owner's inert binding plus any separately fresh capability;
it cannot reconstruct a second Core, transcript, relation, occurrence graph,
or authored loss count.

## Profile topology and K3-E evidence boundary

The target Analysis identities are profile-qualified. A standalone common
kernel profile owns only the shared calculus; a bounded cryptographic-property
profile directly imports that kernel and the exact-used K3-B Relations profile;
the latter's exact closure reaches the Interface/Plan and K2 PIR/FS profiles;
an AFK semantic-transport profile imports the property profile; and a narrow
theorem-source-validation profile imports that semantic-transport profile.
Redundant direct K2 edges are forbidden. Once their owner-local preimages are
published, these are exact profile IDs with exact no-extra import closures, not
family/revision labels. Dependency flows kernel -> property -> semantic
transport -> theorem-source validation and never backward. An unrelated future
profile therefore does not rotate an existing body; changing an actually used
upstream profile intentionally rotates its downstream consumers.

K3-E supplies bounded executable evidence only for this finite profile
topology, exact authentication, and expected local/downstream rotation. It does
not own Analysis semantics or publish the final profile identities. In
particular, the current symbolic-law and host-dispatch profile objects are
correspondence surrogates and must not become the ideal typed Analysis
preimages. Each Analysis owner must publish its complete six-field profile
preimage, exact typed law-source bytes, and independently reconstructible full
typed ID before any dependent K4 ID is treated as persistent and before K5
freeze.

The AFK semantic theorem schema, questions, goals, propositions, and semantic
bases remain under the semantic-transport profile. The child profile governs
the theorem-source-validation body and the exact support, validation-basis,
operation-policy, and judgment bodies that consume or govern the resulting
validation-bearing result. This makes validation evolution flow into
validation-bearing descendants without feeding back into theorem meaning.

Every active portable body has one total, bounded `AnalysisBodyV0` encoding.
Question, goal, and proposition remain distinct: the question owns family,
subjects, context, and payload; the goal contains only its question ID and
derives the hypothesis-free conclusion; the proposition adds exactly one
hypothesis-context ID. Semantic and validation identities remain separate.
Live capabilities, evaluator processes, observations, and owner-local handles
have no portable encoding arm.

The active kind table is intentionally small. Experiment-local records,
theorem-local binders, resource entries, role-map clauses, and quantitative
subterms remain nested in their nearest durable owner. Foreign objects retain
their producer-owned IDs rather than receiving `analysis.*` aliases. Probe-only
fixtures use `probe.k3c.*` and may not enter an Analysis identity, judgment,
authority binding, support record, or closure claim. A new `analysis.*` kind is
therefore a specification change requiring an exact body, profile assignment,
compiler arm, formation law, and locality tests; it is not a convenience for a
host-language helper class.

That separation also applies to imported theorems. An
`AnalysisTheoremSchemaId` commits only the exact restricted semantic statement,
typed templates, and conclusion reconstruction law. Bibliographic revision,
PDF digest and locators, ImportedPaperOnly or checked-proof status, and
truth-discharge metadata live in a distinct
`AnalysisTheoremSourceValidationId`. Source-only changes rotate validation or
support, not theorem-truth questions or goals; a semantic statement change
rotates the theorem ID and every downstream validation/support reference.

The K2/K3-B ingress is similarly exact:

- invocation values come only from the Fresh and Fiat--Shamir PIR
  `PublicSetupInvocationView` values, whose public-entry sequences must agree;
  never from a static binding declaration or a copied caller assignment;
- every PIR static-view read uses `PIRStaticViewFieldCoordinate`, the owner
  `RequiredPIRViewReadClosure`, an exact inert view binding, and a matching
  fresh capability;
- the acceptance premise closes the selected Check/Terminal leaves through
  the complete producer/guard/scope/effect dependency set;
- Fresh and Fiat--Shamir target semantics retain distinct Protocol-qualified
  relation bindings, Plan Witness bindings, correspondence results, and
  grounding coordinates; a producer-checked shape comparison never aliases or
  derives one axis from the other;
- Relations ingress reads the one tagged `CorrespondenceQuestionBody` and an
  exact checked-result binding; it has no variant-specific shadow body; and
- source and judgment policy summaries are derived from authenticated exact-used
  bindings and owner-profiled closure preimages, never supplied as independent
  claims and never treated as authority.

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

An additive exact classical FRI control now supplies bounded candidate
pressure outside this active profile set. It forms distinct round-by-round and
restricted state-restoration questions, checks the three-fold scalar-terminal
Algorithm-1 shape, and evaluates one exact rational substitution as
non-vacuous. The question statuses remain `NotEvaluated`; theorem truth is
`NotEstablished`; theorem applicability is `NotEvaluated`; no property is
established. The instrument uses a bespoke finite carrier rather than the
durable Analysis profile, body, source-manifest, and authority contracts.
Promoting either family therefore requires an explicit profile/catalog
revision rather than treating the control as an active judgment.

Source-grounded constructive encodings of classical Sumcheck, modern layered
GKR, a packed Boolean GKR variant, and duplex-sponge Fiat--Shamir now
add further pressure outside the active profile set. They establish that the
first three interactions can be represented structurally and that the literal
duplex-sponge transform needs a distinct PIR construction alternative. They do
not add a
Sumcheck or GKR soundness family, a GKR property-composition rule, a word-RAM
cost judgment, a state-restoration premise, a duplex theorem schema, or a
Fresh-to-duplex transport result. Every such conclusion remains
`Unsupported` or `CannotAnswer` according to the missing exact family and
premises rather than being inferred from the constructive encodings.

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
  general round-by-round and restoration families, and multi-prover
  independence; the exact classical FRI candidate above remains pressure only;
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
