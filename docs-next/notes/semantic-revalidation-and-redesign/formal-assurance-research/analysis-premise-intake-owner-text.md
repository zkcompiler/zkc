# Analysis named-premise intake: the owner text

> **Kind:** owner-text record (formal-assurance research, Analysis pass)
> **State:** Authored 2026-09-03 on a branch stacked on the migration branch;
> repaired after its first independent review and again after its second,
> which closed three of seven questions and left four open on exact grounds
> that are now repaired in the text; the provider-carrier decision packet's
> first two items are adopted in the same repair; the existing Analysis
> packages are not yet migrated to the new fields; a third review round and
> publication remain, the latter the user's gate.
> **Inputs:** the migration decisions on the sampling law and the outcome
> partition (`f0-v2c-decision-inputs.md`, Sections 4, 5, and 10) and the
> intake design of `analysis-named-premise-intake.md`.

## 1. Outcome

The two decisions that moved assumptions out of PIR now have their Analysis
side. A question names every assumption it consumes as a premise with an
identity; a missing premise makes the question `CannotAnswer`; two questions
over the same subjects with different premises have different identities down
to the judgment. Nothing in the pass proves a premise.

| Page | Change |
|---|---|
| `analysis-model.md`, Section 4.1 | the named-premise grammar (kinds, coordinates, bound values, sources, evidence depths, model scopes, body, requirement), the fields that carry premise identities through question, goal, hypothesis node and context, support, and judgment, the intake operation, the identity constructor, the dispatch row, and the binding-map law's new key class |
| `cryptographic-properties.md`, Section 3.2 | the Fresh public-coin distribution premise, the provider outcome-carrier premise over the abstract outcome partition, and the seven premise requirements of the relation-bound Fresh question over the Schnorr subject tuple |
| `cryptographic-properties.md`, Section 7.3 | the Fiat--Shamir family sampler-adequacy and oracle-process premises, scoped to one exact oracle model |
| `profile-publication.md` and the kernel, property, and transport manifests | the kernel owns grammar and intake; the property and transport profiles support `analysis.named-premise` and own the concrete bodies |

Both publication compilers reconstruct the same table; the Analysis kernel and
its five dependents rotate, on top of the migration's seventeen.

## 2. What was changed from the design

- Evidence depths are written out (source-grounded mapping, typed constructive
  binding, frozen executable falsification) instead of the research labels.
- The transport field is a model scope over defined vocabulary: a Fresh
  challenge, one exact distribution profile (the classical random-oracle
  profile of the adaptive experiment is one), exact subjects, or rebind
  required. The design's regime identifiers did not exist in the pages.
- The provider is an exact profile law declaration of the property profile,
  not a new declaration kind; no provider is declared yet, so no provider-map
  premise can be formed until one is published.
- The Plan coordinates carry ordinals into the Plan body rather than a
  strategy-step coordinate the pages do not define.
- The Schnorr entries are constructors over the subject tuple of Section 3,
  not literal digests.
- After the second review: the two law families are bound to the direct
  profile, `ExactModelBindingLaw<P,K>` and `ExactNamedHypothesis<P,K>`, and
  a hypothesis's argument sequence is a per-profile closed schema whose first
  element is the admitted coordinate; every hypothesis declaration and
  constructor is coordinate-first; the provider arm of the bound value is a
  dependent variant over the Protocol; the binding-map value is the premise
  identity under the question's profile and the requirement's kind; the
  relation, witness, prover-state, honest-commit, and honest-respond entries
  are exact bodies over three binding laws and two hypotheses; the
  construction bindings take the statement length; the sampler form is
  derived from the construction's challenge rules and from the family's
  total-uniform sampler premise; and all 31 anonymous hypothesis nodes carry
  their premise set.
- From the provider-carrier decision packet
  (`f2o2-provider-carrier-decision-2026-09-03.md`, items 1 and 2): a provider
  declaration names the lanes its execution model can end in, a lane image is
  `Image(v)` or the explicit `Unmodelled`, a lane is never collapsed onto
  another's image, and a statement over the whole outcome partition consumes
  the tenth premise kind, `OperationalCompletion`.

## 3. What remains

- Two independent review rounds are absorbed
  (`f0v2d1-analysis-premise-text-review.md`); the second closed intake
  soundness, decision fidelity, profile manifests, publication compilers,
  rotation cone, and probe coverage, and its four open questions, name
  closure, constructor consistency, Schnorr bindings, and refreeze inputs,
  are answered in the text as Section 2 records. A third round checks the
  repaired text and the packet's additions.
- The package migration found that the fixed-extractor question adds the
  extractor to its exact subjects while it reused the relation and witness
  premises scoped to the relation question; under the intake's exact-subject
  rule those premises would be refused. The two constructors now take the
  consuming question's scope, and the extractor question forms its own two
  premise identities over its own subjects.
- The package migration (`f0v2d2-analysis-package-migration.md`) found a
  second underdetermined identity: the Fresh premise's coordinate was "the
  public-coin-law declaration named by `S.challenge_ref`" with no
  authenticated projection behind the phrase. The PIR owner places
  `fresh_law` on every challenge entry of the `PublicCoinView`, so the text
  now reads it there: `AnalysisChallengeFreshLawCoordinate(S)` selects the
  leaf and `SchnorrFreshLawRef(S)` is its value. The compact carrier index of
  the model page now names the premise fields the exhaustive schemas carry.
- The intake probe exercises the tenth kind and the `Image`/`Unmodelled`
  lane image with `modelled_lanes` since the package migration.
- Publication, with the migration: the Analysis profiles rotate through the
  kernel.
- Migration of existing question, goal, context, proposition, support, and
  judgment bodies in the Analysis packages to the new fields: the review's
  round-two section states the exact plan for the closure package and its
  dependents (`evaluation/k3-analysis-closure`, the finite cover, the joined
  boundary); it is done, with the closure package at 213 of 213, and its
  remaining `CannotAnswer` names the closure fixture, which does not publish
  the migrated Protocol's declarations and is refrozen at publication.
- The provider declaration for VCVio, item 3 of the decision packet: source
  pin, the closed carrier `Bool`, `modelled_lanes = [Accepted, Rejected]`, and
  the five-lane map for the Fresh Schnorr Protocol; a profile-level
  declaration the owner publishes.
- Two premise kinds the oracle-proof compilation probe found missing for a
  BCS-style soundness statement, round-restoration soundness of the source
  oracle proof and binding of the commitment, together with a coordinate arm
  that refers to an exact prior qualified Analysis judgment; the probe's
  record (`../bcs-compilation/README.md`, Section 11) states the delta, and
  it is taken after the second review round of this text.
- The pre-freeze deep review (`pre-freeze-deep-review-2026-09-04.md`)
  found the family-premise source constructor receiving the asymptotic
  family's subject identity where `FamilyHypothesisSource` requires a
  property-family declaration reference; the two Fiat--Shamir family bindings
  now pass the transport profile's own declarations of
  `TotalUniformChallengeSamplerAdequacy` and
  `ExactClassicalRandomOracleProcess` through
  `AFKTransportPropertyFamilyRef`, and `F` stays the premise coordinate's
  subject. The same review made the public-setup view name its
  run-established bindings; the Schnorr fixed-setup formation now requires
  that sequence to be empty in both issued views as its own premise. The review's
  catalog repair (owner field names, `result_ref` removed) landed with the
  migration text. A fifth review round checks these changes.
- An independent review of this text, as for the migration.

## 4. Non-claims

No distribution, sampler adequacy, oracle process, relation, honesty,
theorem applicability, completeness, security, or provider correspondence is
established; no identity is published.
