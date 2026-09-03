# Analysis Named-Premise Owner-Text Review

> **State:** round three,
> `Negative/F0V2D1-N-ANALYSIS-PREMISE-TEXT-NOT-CLOSED`: the seven owner-text
> questions and the two added in this round are affirmative, and the two
> negatives name the migrated closure package (legacy proxies for the
> relation-bound Fresh identity and the construction sampler form; an
> arbitrary symbol for the completion hypothesis), not the owner text.
> Sections 1--10 retain the round-one record for `7a63432..177cbaa`, the
> Round two section the second round, and the Round three section below is
> the current disposition.
> **Authority:** None. This review changes no Analysis, Relations, Protocol IR,
> or Foundation owner page and publishes no profile identity.
> **Executable evidence:**
> [`evaluation/formal-source-analysis-premise-review-f0v2d1`](../../../../evaluation/formal-source-analysis-premise-review-f0v2d1/README.md)

## 1. Question and aggregate answer

The exact question is whether the proposed Analysis named-premise owner text is
closed enough to freeze: all names and law families resolve, all affected body
constructors remain complete, intake has the requested fail-closed partition,
the selected sampling and outcome-partition decisions are represented exactly,
all seven Schnorr premise coordinates form, the profile manifests and revisions
are exact, and every affected Analysis package has enough information to be
refrozen.

The answer is **no**. Six findings are negative and two are
`CannotAnswer`. The written intake has no default branch, both independent
publication compilers agree, every current manifest declaration is reachable,
and the exact six-profile identity cone is reproducible. Those positive facts
do not repair undefined law names, incomplete constructors, a nonexistent
Plan-ID derivation, manifest-sequence and revision defects, or gaps in the
predecessor probe.

| Review question | Outcome | Stable finding |
|---|---|---|
| Name closure | Negative | `F0V2D1-N-NAME-CLOSURE` |
| Constructor consistency | Negative | `F0V2D1-N-CONSTRUCTOR-CONSISTENCY` |
| Intake soundness | CannotAnswer | `F0V2D1-C-INTAKE-SCOPE-DISPOSITION` |
| Decision fidelity | Negative | `F0V2D1-N-DECISION-FIDELITY` |
| Seven Schnorr premise coordinates | Negative | `F0V2D1-N-SCHNORR-COORDINATES` |
| Profile and manifest closure | Negative | `F0V2D1-N-PROFILE-MANIFESTS` |
| Existing-package migration | CannotAnswer | `F0V2D1-C-REFREEZE-INPUTS` |

Three supporting findings record affirmative compiler agreement, the exact
rotation cone, and a negative predecessor-probe coverage result.

## 2. Name closure

`F0V2D1-N-NAME-CLOSURE` is negative. The coordinate constructors themselves
are introduced by `AnalysisPremiseCoordinate`, and the following requested
owner names resolve in the allowed source domains:

- `AnalysisProfileLawRef`, `AnalysisDistributionProfileId`, and
  `AnalysisAsymptoticProtocolFamilyDefinitionId` in Analysis;
- `RelationSemanticModelId`, `RelationInterfaceId`, and
  `PlanWitnessBindingId` in Relations;
- `ProverPlanId` and the dependent family `ProtocolOutcomeLane(P)` in Protocol
  IR; and
- `AFKClassicalRandomOracleProfileId(S)` in the cryptographic-property page.

All five subject-tuple paths used by `SchnorrNamedPremiseRequirements` also
exist: `fresh_protocol_id`, `challenge_ref`, `relation_semantic_model_id`,
`relation_interface_id`, and
`relation_axis_ingress.fresh.plan_witness_binding_id`.

Seven law or schema parameters have no definition anywhere in the allowed
Analysis, Relations, Protocol IR, or Foundation pages and no corresponding
closed row in the three changed profile manifests:

| Undefined name | Use site |
|---|---|
| `ProviderDeclaration` | `analysis-model.md`, Section 4.1, line 2111 |
| `ClosedProviderCarrier` | `analysis-model.md`, Section 4.1, line 2116 |
| `ExactModelBindingLaw` | `analysis-model.md`, Section 4.1, line 2123 |
| `ExactNamedHypothesis` | `analysis-model.md`, Section 4.1, line 2124 |
| `FreshSamplingHypothesis` | `cryptographic-properties.md`, Section 3.2, line 2179 |
| `SamplerAdequacyHypothesis` | `cryptographic-properties.md`, Section 7.3, line 5457 |
| `OracleProcessHypothesis` | `cryptographic-properties.md`, Section 7.3, line 5473 |

The generic law-reference definition is profile-parameterized, but the four
new generic grammar uses in lines 2111--2124 omit that profile parameter
outside a constructor whose direct profile is fixed. The omission therefore
is not licensed by the notation rule in Section 2.0. In addition,
`ProtocolOutcomeLane` is a dependent family over a Protocol, but line 2118 and
the concrete provider constructor use it as a nullary type.

## 3. Constructor consistency

`F0V2D1-N-CONSTRUCTOR-CONSISTENCY` is negative. The checker scans every
top-level Analysis page, balances each displayed constructor body, and checks
the new required field. None of the affected displays is complete:

| Body | Displays | Complete after the change |
|---|---:|---:|
| `AnalysisQuestionBody` | 11 | 0 |
| `AnalysisGoalBody` | 12 | 0 |
| `AnalysisHypothesisContextBody` | 6 | 0 |
| `AnalysisSupportInstantiationBody` | 5 | 0 |
| derived `AnalysisJudgmentRecordBody` | 1 | 0 |
| concrete `AnalysisNamedPremiseBody<K>` | 4 | 0 |

The first five groups omit their respective
`named_premise_requirements`, `named_premise_bindings`, or
`exact_named_premise_ids` field. The four premise constructors omit the
required literal `kind: exactly K`. The six hypothesis-context displays also
contain thirty anonymous node records that still have only ordinal, goal, and
dependency fields.

Two derived helpers remain stale. `ExactAffirmativeAnalysisJudgmentBody` at
`analysis-model.md:3354` does not derive the judgment's new premise-ID field,
and `CanonicalGoalDagUnion` at lines 3434--3445 rewrites nodes without deriving
or preserving their premise-ID fields. The sentence at line 3140 that a goal
contains only `question_id` directly contradicts the new goal schema.

The identity-sensitivity paragraph in Section 4.2 is also incomplete. It does
not say that changing a named-premise requirement, body, binding, source,
evidence depth, or model scope rotates the premise and every dependent goal,
proposition, support, and judgment identity. Section 5.1 still says an
assumption is represented once only in the hypothesis context, while the new
grammar also places identity-bearing assumptions in named-premise bodies and
propagates their IDs through that same chain.

## 4. Intake soundness

`F0V2D1-C-INTAKE-SCOPE-DISPOSITION` is `CannotAnswer`, not affirmative.
`analysis-model.md`, Section 4.1, lines 3016--3032 explicitly gives:

- missing key or absent premise source to `CannotAnswer`;
- well-formed kind or coordinate mismatch to `Refused`; and
- extra, duplicate, noncanonical, or caller-ordered keys to `Malformed`.

It also lists all four model-scope checks and forms a goal only from the exact
required key set, so there is no written path to an ambient or empty default.
However, step 6 says only “require” and assigns no disposition to a failed
Fresh, exact-subject, or rebind-required scope check. Section 7.3 explicitly
calls an Oracle-model mismatch refused, but that sentence does not classify
the other three variants. The later statement that an unmet requirement is
`CannotAnswer` creates a second plausible reading. The exact requested
`model-scope mismatch -> Refused` partition is therefore underdetermined at
`analysis-model.md:3022-3028`.

The predecessor probe cannot settle this. Both of its evaluators classify an
extra key as `Refused`, contrary to the adopted text's `Malformed`, freeze no
extra-key finding, and do not evaluate the new model-scope carrier at all.
That is `F0V2D1-N-PROBE-COVERAGE`.

## 5. Decision fidelity

`F0V2D1-N-DECISION-FIDELITY` is negative. The prose intent is recognizable:
Fresh uses a named public-coin distribution premise, Fiat--Shamir uses
separate sampler-adequacy and oracle-process premises, the latter are scoped
to one exact distribution model, and provider carrier maps retain the
profile-qualified five- or six-lane Protocol outcome partition.

The exact realization is nevertheless weaker than that intent:

1. the three hypothesis law-term signatures and both provider schema families
   are undefined;
2. `BoundHypothesis` is unary in the grammar, while the Fresh and sampler
   constructors pass a second prose argument beginning “which ...”; that
   prose is not a canonical law-term argument;
3. the provider map uses bare `ProtocolOutcomeLane` instead of
   `ProtocolOutcomeLane(P)`; and
4. no published provider declaration exists, so the provider-map constructor
   has no current inhabitant even before its carrier and lane types are
   checked.

The Fresh-versus-Fiat--Shamir separation and lane counts should be retained in
a repair. They are not enough to claim that the selected decisions have been
realized exactly by the current grammar.

## 6. Seven Schnorr coordinates

`F0V2D1-N-SCHNORR-COORDINATES` is negative. All seven slots are present and
the finite candidate supports the selected ordinals: private witness 0,
witness edge 0, persistent state 0, commit decision/node 0/0, and respond
decision/node 2/0. Those are valid candidate observations, not a proof that
the owner expression forms.

The decisive defect is `PlanOf(S)` at
`cryptographic-properties.md:2212-2214`. It says a `ProverPlanId` is named by
`S.relation_axis_ingress.fresh.plan_witness_binding_id`. The Relations owner
states the opposite: `PlanWitnessBinding` is source-ID-free and contains only
used modules, a `PlanWitnessSurfaceId`, a `RelationInterfaceId`, and witness
edges. It intentionally contains no `ProverPlanId` or Plan-local source
coordinate. Consequently the prover-state, commit, and respond coordinates
cannot be formed from `S`.

There are two additional type defects. `PIRPlanStateCoordinate` and
`PIRPlanRecipeCoordinate` use `Natural` ordinals although the Plan owner keys
those tables by `StrategyStateSlotRef`, `ProverDecisionPointRef`, and
`RecipeNodeRef`. Also, the text says all five relation and Plan premises bind
with `BoundModel`, while commit and respond are hypothesis-shaped in the
adopted design probe; the undefined kind-to-bound-value law supplies no
authoritative resolution.

## 7. Profiles, manifests, and rotation cone

`F0V2D1-N-PROFILE-MANIFESTS` is negative.

- The kernel and cryptographic-property supported-kind sequences equal their
  manifest sequences exactly.
- The semantic-transport catalog and manifest have equal sets but unequal
  literal sequences. The catalog places `analysis.checked-result-coordinate`
  before `analysis.capability-requirement-payload` and
  `analysis.family-read-manifest-schema` before
  `analysis.family-instance-role-map`; the manifest is canonically sorted.
- That literal-sequence violation already exists at the review base. It was
  not introduced by the named-premise change, but the changed owner text and
  manifest preserve it. The existing publication test sorts the owner catalog
  before comparison and therefore masks the publication rule's literal
  sequence requirement.
- All three profile revisions move from 0 to 1. The observed declaration
  bumps are `common-analysis-domain-v0`, the property body compiler, and the
  transport body compiler. The new property premise semantics change the
  selected `property-core-v0` law fragment, and the new family premises change
  the selected `afk-application-v0` law fragment, but both semantic-law
  declarations remain at revision 0.

Both independent publication compilers reconstruct all eighteen indexed
profiles, reject no declaration as unreachable, and agree byte for byte on
current and reconstructed-base tables. The exact range rotates:

1. `analysis-kernel`;
2. `analysis-cryptographic-property`;
3. `analysis-afk-transport`;
4. `analysis-afk-theorem-source-validation`;
5. `analysis-incremental-composition`; and
6. `analysis-incremental-composition-source-validation`.

Compiler agreement is `F0V2D1-A-PUBLICATION-COMPILERS`; the cone is
`F0V2D1-A-ROTATION-CONE`. They are reconstruction results, not a closure
verdict.

## 8. Existing-package migration

`F0V2D1-C-REFREEZE-INPUTS` is `CannotAnswer`. The direct executable Analysis
model in `evaluation/k3-analysis-closure` lacks the new field in all six
affected dataclasses. It has eight question calls, fourteen goal calls, five
hypothesis-node calls, four context calls, one support call, and one judgment
call that must be updated together with encoding, dependency extraction,
formation, identity vectors, and negative tests.

`evaluation/finite-cover-analysis` and `evaluation/k3-integrated-closure`
import that exact model and must be revalidated after its IDs rotate. The
incremental-composition boundary package builds simplified Analysis support
and judgment identities directly and must be migrated or explicitly marked as
a non-target surrogate. The publication package must refreeze the final
profile table, and the predecessor intake probe must align its extra-key and
model-scope cases.

The affected checks are `research.property-analysis`, `research.finite-cover`,
`research.joined-semantic-boundary`,
`research.recursive-composition-boundary`, `research.profile-publication`, and
`research.analysis-premise-intake`.

Mechanical empty values cannot be prescribed for all existing constructors.
The owner text does not define the exact requirement sequence and exact
premise-ID binding map for every existing Fresh, Fiat--Shamir, theorem-truth,
theorem-applicability, family, and member question. Missing evidence therefore
remains `CannotAnswer`; this review does not invent empty requirements or
ambient bindings.

## 9. Proposed delta

These are proposed owner changes, not edits made by this lane.

### 9.1 Close the generic premise grammar

- **Owner page and section:** `docs-next/analysis/analysis-model.md`, Section
  4.1, lines 2091--2165.
- **Exact change:** parameterize `AnalysisProviderDeclaration`,
  `AnalysisProviderOutcomeCarrierMapBody`, `AnalysisNamedPremiseBoundValue`,
  `AnalysisNamedPremiseSource`, and `AnalysisNamedPremiseBody` by the exact
  direct profile `P`; spell every reference as `AnalysisProfileLawRef<P,S>` or
  `AnalysisLawTerm<P,S>`. Add closed law-catalog signatures for
  `ProviderDeclaration`, `ClosedProviderCarrier`,
  `ExactModelBindingLaw<K>`, and `ExactNamedHypothesis<K>`. The binding-law
  signatures must take the selected premise coordinate and exact bound model
  or hypothesis as canonical arguments and return the profile's closed
  acceptance carrier. Replace the provider map with
  `AnalysisProviderOutcomeCarrierMapBody<P,Protocol>` and
  `CanonicalMap<ProtocolOutcomeLane(Protocol),
  CanonicalValue<provider_carrier>>`.
- **Identity effect:** applied atop the current candidate, this changes the
  kernel domain law and rotates the kernel, both semantic branches, and both
  validation children. Increment the kernel profile and
  `common-analysis-domain-v0` revisions again.
- **Evidence:** `research.analysis-premise-text-review` and
  `research.profile-publication`.
- **Reversal condition:** withdraw this delta only if the owner replaces the
  generic law-term design with another fully defined, profile-qualified closed
  carrier and the independent name checker finds no unresolved parameter.
- **Non-claims:** schema closure does not establish any provider mapping,
  sampling fact, hypothesis, property, or theorem.

### 9.2 Make concrete hypotheses canonical values

- **Owner page and section:** `docs-next/analysis/cryptographic-properties.md`,
  Sections 3.2 and 7.3.
- **Exact change:** define and register closed
  `FreshSamplingHypothesis`, `SamplerAdequacyHypothesis`, and
  `OracleProcessHypothesis` signatures. Put the law coordinate and
  distribution-profile ID, and the sampler exhaustion or exact-total form,
  inside each `AnalysisLawTerm.canonical_arguments`; delete both prose
  arguments passed to `BoundHypothesis`. Add `kind:` to all four concrete
  premise bodies.
- **Identity effect:** the property correction rotates the property profile,
  transport profile, and theorem-validation child; the transport correction
  rotates the transport profile and its validation child. Increment the
  property and transport profile revisions, their body-compiler revisions,
  `property-core-v0`, and `afk-application-v0` as applicable.
- **Evidence:** `research.analysis-premise-text-review` and
  `research.analysis-premise-intake`.
- **Reversal condition:** withdraw only if the owner selects exact
  `AnalysisGoalId` hypothesis bindings instead and defines their complete
  question families and coordinate equality law.
- **Non-claims:** a formed law term remains an assumption; it does not prove
  uniform sampling, sampler adequacy, or oracle-process correspondence.

### 9.3 Repair Plan coordinate ownership

- **Owner page and section:** `docs-next/analysis/cryptographic-properties.md`,
  Section 3 and Section 3.2.
- **Exact change:** add `fresh_prover_plan_id: ProverPlanId` to
  `AnalysisSubjectTuple`; require the existing subject-tuple adequacy check to
  authenticate a checked Plan realization and checked witness-surface
  extraction showing that this Plan produced the surface named by the Fresh
  `PlanWitnessBinding`. Define `PlanOf(S) = S.fresh_prover_plan_id`. Change the
  coordinate signatures to `PIRPlanStateCoordinate(ProverPlanId,
  StrategyStateSlotRef)` and `PIRPlanRecipeCoordinate(ProverPlanId,
  ProverDecisionPointRef, RecipeNodeRef)` and retain the selected 0, 0/0, and
  2/0 references only after those typed checks.
- **Identity effect:** every property-profile body that contains the subject
  tuple changes, rotating the property branch and its descendants; the
  incremental branch does not rotate from this delta alone.
- **Evidence:** `research.analysis-premise-text-review` and
  `research.schnorr-relations-plan-candidates`.
- **Reversal condition:** withdraw only if Protocol IR or Relations publishes
  another authenticated coordinate that uniquely joins the binding's
  source-free surface to the exact Plan without embedding a Plan ID in
  Relations.
- **Non-claims:** the join authenticates ownership and typing only; it proves
  neither Plan honesty nor relation satisfaction.

### 9.4 Complete intake, constructors, and identity prose

- **Owner pages and sections:** `docs-next/analysis/analysis-model.md`, Sections
  4.1, 4.2, and 5; `docs-next/analysis/cryptographic-properties.md`, all
  displayed constructors; and
  `docs-next/analysis/transport-composition-and-replay.md`, Sections 3 and 4.
- **Exact change:** add “failure of any model-scope requirement in step 6
  returns `Refused`” and state that it precedes goal formation. Add the required
  fields to all 39 displayed bodies and all thirty hypothesis nodes; derive
  the premise-ID field in the affirmative-judgment and canonical-DAG-union
  helpers. Replace “goal contains only `question_id`” with both goal fields.
  Extend Section 4.2 to state that premise kind, coordinate, bound value,
  source, evidence depth, model scope, requirement sequence, and binding map
  are identity-bearing and rotate every actual dependent body. Reconcile
  Section 5.1 by distinguishing ordinary hypothesis goals from named premise
  assumptions rather than claiming every assumption appears only once in the
  hypothesis DAG.
- **Identity effect:** constructor bodies and every dependent ID rotate under
  their direct profiles. The exact cone is determined only after every
  question's requirement set and every goal's binding map is authored.
- **Evidence:** `research.analysis-premise-text-review`,
  `research.property-analysis`, `research.finite-cover`, and
  `research.joined-semantic-boundary`.
- **Reversal condition:** withdraw only if the owner makes the new fields
  canonically derived and removes them from the body schemas and identity
  encoding everywhere, with equivalent no-default tests.
- **Non-claims:** adding fields or rederiving IDs does not establish any
  premise; unknown bindings remain `CannotAnswer`.

### 9.5 Repair publication metadata

- **Owner page and section:** `docs-next/analysis/analysis-model.md`, Section
  2.0 catalogs; profile manifests for kernel, cryptographic property, and
  semantic transport.
- **Exact change:** reorder the semantic-transport owner catalog to the exact
  manifest sequence. Bump `property-core-v0` and `afk-application-v0` for the
  already changed selected semantics. Any further owner correction should
  increment the directly changed profile and declaration revisions rather
  than reusing revision 1.
- **Identity effect:** catalog repair in the kernel source rotates all six
  Analysis profiles. The two law bumps also make the declaration-level reason
  for the property and transport rotations explicit.
- **Evidence:** `research.analysis-premise-text-review` and
  `research.profile-publication`.
- **Reversal condition:** withdraw only if the publication rule is explicitly
  changed from literal sequence equality to canonical-set equality and both
  compilers and tests adopt that one rule.
- **Non-claims:** matching manifests and compiler agreement do not establish
  semantic correctness of the laws they package.

## 10. Nonclaims

This review is static source, finite candidate, differential compiler, and
impact-inventory evidence. It does not implement the Analysis grammar, select
provider declarations or premise instances, validate a provider, establish a
relation or Plan premise, prove theorem applicability or truth, establish a
cryptographic property, verify a compiler or backend, publish target profiles,
or claim production readiness.

## Round-one handoff

- **Files changed:** added the review package `README.md`, `run.py`, and frozen
  `expected-findings.json`; added this note; registered
  `research.analysis-premise-text-review` in `checks/manifest.json` and the
  `active-source-definition-sequence`; added one row to `evaluation/README.md`;
  and moved lifecycle test pins to 58 research checks, 60 packages, and 33
  active-sequence dispositions. No owner page or profile manifest was edited.
- **Commands:** the direct package check exited 0 in 0.94 seconds. A separate
  current-versus-base invocation of both publication compilers exited 0 in
  0.60 seconds and reproduced eighteen profiles and the six-profile cone. The
  alternate-index `git add -A` exited 0 in 0.35 seconds. Final required checks
  were run with that index and the clone-local offline cache: manifest
  validation exited 0 in under 0.01 seconds; the developer tier exited 0 in
  0.98 seconds with 8/8 checks passing; and the focused check exited 0 in 1.01
  seconds with 1/1 passing. JSON decoding, Python compilation, and
  `git diff --check` also exited 0.
- **Aggregate outcome:**
  `Negative/F0V2D1-N-ANALYSIS-PREMISE-TEXT-NOT-CLOSED` with six negative and
  two `CannotAnswer` review findings.
- **Non-claims:** as listed in Section 10; no owner page, profile identity,
  commit, push, or pull request was produced.
- **Surprises and brief corrections:** the full publication package test was
  already red on this stacked migration state: its six legacy identity pins
  and published table differ from the current migrated source (exit 1 in 3.44
  seconds). The two compiler reconstructions themselves agree; the focused
  review records that narrower fact and does not call the publication suite
  green. The clone's checked-out branch is `lane/analysis-review`, not
  `docs/analysis-premise-intake`, and this clone contains neither `AGENTS.md`
  nor `.claude/CLAUDE.md`; the read-only primary copies were used. The required
  private lane-status append could not be made because the brief also forbids
  writes outside this clone and those ledgers are read-only. Finally, the
  read-only Git object store required a temporary object directory in addition
  to the clone-local alternate index; both were removed after validation. A
  post-cleanup direct lifecycle unittest intentionally lacked that alternate
  index and exited 1 because Git could not see the untracked package; this
  reproduces the brief's inventory warning rather than a package defect. The
  required developer-tier lifecycle check passed with the alternate index.

## Round two

### Scope and aggregate

Round two reviews `8ae0ee1..cb8f382`, including the commits `de6f9e7`
(`repair the analysis premise grammar after review`) and `cb8f382`
(`complete the analysis displays under the requirement law`). The checker no
longer freezes any assertion that a round-one defect persists.

The aggregate is
`CannotAnswer/F0V2D1-C-ANALYSIS-PREMISE-TEXT-NOT-CLOSED`:

| Review question | Round two | Stable finding |
|---|---|---|
| Name closure | CannotAnswer | `F0V2D1-C-NAME-CLOSURE` |
| Constructor consistency | CannotAnswer | `F0V2D1-C-CONSTRUCTOR-CONSISTENCY` |
| Intake soundness | Affirmative | `F0V2D1-A-INTAKE-SOUNDNESS` |
| Decision fidelity | Affirmative | `F0V2D1-A-DECISION-FIDELITY` |
| Schnorr coordinate and binding formation | CannotAnswer | `F0V2D1-C-SCHNORR-BINDINGS` |
| Profile and manifest closure | Affirmative | `F0V2D1-A-PROFILE-MANIFESTS` |
| Existing-package refreeze inputs | CannotAnswer | `F0V2D1-C-REFREEZE-INPUTS` |

The affirmative aggregate
`Affirmative/F0V2D1-A-ANALYSIS-PREMISE-TEXT-CLOSED` is deliberately not
returned because four of the seven questions do not close.

### Findings closed since round one

The old `F0V2D1-C-INTAKE-SCOPE-DISPOSITION` closes. `analysis-model.md`
Section 4.1, lines 3098--3113 now assigns missing source to `CannotAnswer`,
kind or coordinate mismatch and each of the four scope failures to `Refused`,
and malformed key sets to `Malformed`, before goal formation. Section 3.2 of
`cryptographic-properties.md`, lines 2393--2401, explicitly fixes the empty
requirement sequence for every category reached by the three parametric
`NamedPremiseRequirementsOf(family, exact_subjects)` question constructors:
source premise families, asymptotic special soundness, theorem applicability,
and the other property/transport families. No ambient empty default is needed.

The old `F0V2D1-N-DECISION-FIDELITY` closes. Fresh distribution, construction
and family Fiat--Shamir sampler/oracle premises, exact model scopes, the
Protocol-qualified provider lane map, and the separate provider-judgment
requirement are all represented. This is syntactic decision fidelity, not
evidence that any premise is true or any provider exists.

The old `F0V2D1-N-PROFILE-MANIFESTS` closes. All three owner supported-kind
catalogs now equal their manifest sequences, including the transport catalog.
The three profile revisions move from zero to one; the five corresponding
definition bumps are `common-analysis-domain-v0`,
`cryptographic-property-body-v0`, `property-core-v0`,
`afk-transport-body-v0`, and `afk-application-v0`. Both independent
publication compilers agree on current and reconstructed `8ae0ee1` source and
reproduce the same six-profile rotation cone.

The old `F0V2D1-N-PROBE-COVERAGE` closes. The typed and independent predecessor
evaluators now classify an extra key as
`Malformed/API-M-EXTRA-PREMISE` and freeze one
`Refused/API-R-MODEL-SCOPE` mismatch for each of `FreshChallengeOnly`,
`OracleModelOnly`, `ExactSubjectsOnly`, and `RebindRequired`. The probe keeps
the Fresh outcome partition exact and profile-qualified; this round-two review
separately confirms the now-published PIR `ProtocolOutcomeLane(P)` coordinate.

The old broad name, constructor, and coordinate negatives are not carried
forward. Their stated defects were repaired: the requested family names are
now defined, top-level body displays have the new fields, the goal sentence
and two derivation helpers are current, `fresh_prover_plan_id` and its adequacy
clause exist, and Plan coordinates are typed. The narrower successor findings
below concern different residual gaps.

### Findings that remain

`F0V2D1-C-NAME-CLOSURE` remains. Every law family named by this change now has
either a displayed closed-schema statement or a displayed signature, but the
signatures do not all form:

- `analysis-model.md` Section 4.1, lines 2125--2133 defines
  `ExactModelBindingLaw<K>` and `ExactNamedHypothesis<K>` using a free `P` in
  `TotalAnalysisLawSignature<P,...>`.
- Lines 2145--2150 put
  `AnalysisProviderOutcomeCarrierMapBody<P,Protocol>` in a sum whose binders
  are only `<P,K>`, leaving `Protocol` free.
- Lines 2241--2245 and 3091--3094 use bare `AnalysisNamedPremiseId` as the
  binding-map value although lines 3071--3072 define only
  `AnalysisNamedPremiseId<P,K>`.
- `cryptographic-properties.md` Section 3.2, lines 2191--2210 and 2272--2322,
  and Section 7.3, lines 5621--5669 give the five concrete hypothesis
  declarations two or three canonical arguments, while the generic
  `ExactNamedHypothesis<K>` signature admits only one coordinate argument.
- Section 3.2, lines 2362--2365 uses `ell0` in
  `AFKMemberKnowledgeQuestion(S,ell0)` although
  `FiatShamirConstructionPremiseBindings` binds only `S`.

`F0V2D1-C-CONSTRUCTOR-CONSISTENCY` remains. All eleven question, twelve goal,
six context, five support, one derived judgment, and six concrete named-premise
body displays carry their required fields. `ContextPremiseIds` at
`analysis-model.md` lines 2281--2287 agrees with the context schema and defines
`premises(goal)` as exactly `PremiseIdsOfGoal`. The two helper derivations also
carry the IDs. However, only 24 of the actual 31 anonymous nodes use that
fourth component. Add `, premises(goal)` to the nodes beginning at
`cryptographic-properties.md:5196`, `:5364`, `:6100`, `:6102`, `:6109`,
`:6112`, and `:6115`. Because the node schema has no omission default, the
surrounding context-level union cannot make those seven node bodies complete.

`F0V2D1-C-SCHNORR-BINDINGS` remains. The six relation-bound requirements and
the separate provider requirement have formable coordinates. The selected
Plan references are `StrategyStateSlotRef 0`, decision/node `0/0`, and
decision/node `2/0`, and the finite candidate still witnesses those ordinals.
But `SchnorrNamedPremiseBindings` at
`cryptographic-properties.md` lines 2333--2357 constructs only the fresh-coin
premise. The relation, witness, state, commit, and respond entries are prose
`BoundModel`/`BoundHypothesis` descriptions, not complete
`AnalysisNamedPremiseBody` values: they do not fix the exact law reference,
canonical arguments, source, evidence depth per entry, or `model_scope`.
`SchnorrExtractorPremiseBindings` at lines 2359--2360 merely subsets that
underdetermined map. `FiatShamirConstructionPremiseBindings` has the unbound
`ell0` above. `FiatShamirFamilyPremiseBindings` at lines 5680--5687 constructs
both premise bodies but still uses the prose `the form the family declares`
instead of a named, exact profile-law derivation. Consequently the helpers are
not exact enough to form all goal identities.

`F0V2D1-C-REFREEZE-INPUTS` remains. The empty-family sentence determines the
empty cases, but the nonempty binding IDs cannot be frozen until the law
signature and helper gaps above are resolved. The current
`evaluation/k3-analysis-closure` model also lacks
all six new body fields and the named-premise body itself. This review records
the exact migration below but does not implement it.

### Proposed delta

These are owner-page proposals only; this lane did not edit an owner page.

#### Close the dependent law and ID carriers

- **Owner page and section:** `docs-next/analysis/analysis-model.md`, Section
  4.1, lines 2125--2150, 2241--2245, and 3091--3094.
- **Exact change:** bind the direct profile in the family names as
  `ExactModelBindingLaw<P,K>` and `ExactNamedHypothesis<P,K>`. Define a closed
  `NamedHypothesisArgumentSchema<K>` with Fresh arguments
  `[PIRPublicCoinLawCoordinate, AnalysisDistributionProfileId]`, sampler
  arguments `[the admitted family-or-construction coordinate,
  AnalysisDistributionProfileId, SamplerAdequacyForm]`, and oracle arguments
  `[the admitted family-or-construction coordinate,
  AnalysisDistributionProfileId]`; use that schema in
  `ExactNamedHypothesis<P,K>`. Make the provider arm an explicitly dependent
  variant
  `BoundProviderOutcomeCarrierMap<Protocol: ProtocolId>(AnalysisProviderOutcomeCarrierMapBody<P,Protocol>)`.
  Introduce
  `AnalysisNamedPremiseBindingValue<P>(requirement) =
  AnalysisNamedPremiseId<P,requirement.kind>` and use it in both goal and intake
  maps.
- **Identity effect:** the kernel law source changes, so its direct profile and
  every dependent Analysis profile rotate; every question, goal, context,
  proposition, support, and judgment that reaches a changed premise also
  rotates. The direct profile and changed law-declaration revisions must
  advance before publication.
- **Evidence with gate IDs:** `research.analysis-premise-text-review`,
  `research.profile-publication`, and `research.analysis-premise-intake`.
- **Reversal condition:** withdraw only if the owner publishes another closed
  dependent carrier that binds the same profile, kind, Protocol, and canonical
  argument schemas with no body-to-profile inference.
- **Non-claims:** a well-typed law term remains an assumption and proves no
  sampling, relation, Plan, or provider fact.

#### Complete exact premise constructors and binding helpers

- **Owner page and section:**
  `docs-next/analysis/cryptographic-properties.md`, Sections 3.2 and 7.3.
- **Exact change:** change each concrete hypothesis term's first argument to
  its complete admitted premise coordinate and match the closed argument schema
  above. Add concrete six-field constructors for relation predicate, witness
  type, prover state, honest commit, and honest respond. Each must name its
  exact `AnalysisLawTerm` reference and canonical arguments, its exact owner or
  candidate source, its evidence depth, and
  `ExactSubjectsOnly(SchnorrSpecialSoundnessQuestion(S).exact_subjects)`.
  Make `SchnorrNamedPremiseBindings` and
  `SchnorrExtractorPremiseBindings` call intake with IDs of those exact bodies.
  Change `FiatShamirConstructionPremiseBindings` to take `(S,ell0)` and update
  every caller. Replace `the form the family declares` with a named
  `SamplerAdequacyFormOf(F)` profile-law derivation, and spell both family
  premise IDs in the supplied map.
- **Identity effect:** the property and transport semantic laws and direct
  profiles rotate, as do their validation children and every nonempty
  premise-bearing goal/support/judgment. Advance the affected profile, body
  compiler, and semantic-law revisions.
- **Evidence with gate IDs:** `research.analysis-premise-text-review`,
  `research.schnorr-relations-plan-candidates`,
  `research.analysis-premise-intake`, and `research.property-analysis`.
- **Reversal condition:** withdraw only if the owner chooses a different
  complete constructor set whose intake deterministically yields the same
  requirement-keyed premise IDs and whose source/scope rules are explicit.
- **Non-claims:** exact bindings do not establish their hypotheses, relation
  truth, Plan honesty, extractor success, or cryptographic security.

#### Complete the seven node displays

- **Owner page and section:**
  `docs-next/analysis/cryptographic-properties.md`, Sections 7.1, 7.2, and 8.
- **Exact change:** append `premises(goal)` as the fourth component of the
  seven nodes at lines 5196, 5364, 6100, 6102, 6109, 6112, and 6115. Make no
  authored ID choice; the notation already derives exactly
  `PremiseIdsOfGoal`.
- **Identity effect:** each corrected node body and enclosing context rotates,
  followed by every dependent proposition, support, judgment, and transport
  result under the transport profile.
- **Evidence with gate IDs:** `research.analysis-premise-text-review`,
  `research.property-analysis`, and `research.joined-semantic-boundary`.
- **Reversal condition:** withdraw only if the owner removes the fourth node
  field from the schema and replaces it everywhere with an equally exact
  derived, identity-bearing rule.
- **Non-claims:** copying derived IDs into a node does not discharge or prove a
  premise.

### Migration plan: `evaluation/k3-analysis-closure` and four dependent checks

This plan starts only after the proposed owner deltas above determine the exact
nonempty premise IDs. Implementing it in this review would invent inputs, so no
code below was changed.

#### `research.property-analysis` — `evaluation/k3-analysis-closure`

1. **Dataclasses and closed sums.** Add
   `AnalysisNamedPremiseRequirementV0(slot, kind, coordinate)`,
   `AnalysisNamedPremiseBindingV0(requirement, premise_id)`, and
   `AnalysisNamedPremiseBodyV0(kind, coordinate,
   bound_model_or_hypothesis, source, evidence_depth, model_scope)`. Add exact
   variant dataclasses for all nine kinds, seven coordinate arms, three bound
   value arms, four source arms, three evidence depths, and the four model
   scopes. Add `named_premise_requirements` to
   `AnalysisQuestionBodyV0`; `named_premise_bindings` to
   `AnalysisGoalBodyV0`; and `exact_named_premise_ids` to
   `AnalysisHypothesisNodeV0`, `AnalysisHypothesisContextBodyV0`,
   `AnalysisSupportInstantiationBodyV0`, and
   `AnalysisJudgmentRecordBodyV0`. Preserve immutable tuples and canonical
   Foundation byte ordering rather than host string ordering.
2. **Schema tables and encodings.** At
   `reference_model.py:602--709` add the `analysis.named-premise` descriptor
   and append `named-premise-requirements` to question and
   `named-premise-bindings` to goal. Add `exact-named-premise-ids` to node,
   context, support, and judgment descriptors. Register the new body type in
   `_ANALYSIS_EXACT_BODY_TYPES` and the property/transport subject sets.
   Encode the premise body at ordinals 0--5; question requirements at ordinal
   4; goal bindings at ordinal 1; node IDs at ordinal 3; context IDs at ordinal
   2; support IDs at ordinal 2 while shifting existing support ordinals 2--5
   to 3--6; and judgment IDs at ordinal 4 while shifting existing judgment
   ordinals 4--10 to 5--11.
3. **Formation and intake calls.** Implement
   `normalize_named_premise_requirements` and
   `intake_analysis_named_premises` with the exact twelve-branch partition:
   missing source/key `CannotAnswer`, kind/coordinate and all four scope
   mismatches `Refused`, malformed key sets `Malformed`, and no default.
   Authenticate each premise under the question's direct profile before
   `analysis_goal_id` forms. Extend `_require_constructor_profile` to inspect
   named-premise predecessors and reject mixed profiles. Derive
   `PremiseIdsOfGoal`, node equality, reachable `ContextPremiseIds`, and
   `PremiseIdsOfProposition` rather than accepting caller summaries.
4. **Exact constructor calls.** Update all eight
   `AnalysisQuestionBodyV0` calls, fourteen `AnalysisGoalBodyV0` calls, five
   `AnalysisHypothesisNodeV0` calls, four
   `AnalysisHypothesisContextBodyV0` calls, the one support call, and the one
   judgment call. The named surfaces include `_exact_premise_goal_id`,
   `analysis_question_id`, `analysis_goal_id`,
   `analysis_hypothesis_context_id`,
   `_analysis_support_instantiation_id`, and
   `_analysis_judgment_record_id`, plus fixed-extractor, finite-cover
   certificate, theorem-truth, family source/target, applicability, adaptive
   Fiat--Shamir, and family-instance builders. Use explicit empty requirement
   and binding tuples only for the families licensed as empty at
   `cryptographic-properties.md:2393--2401`. The relation-bound Fresh,
   fixed-extractor, construction Fiat--Shamir, and family Fiat--Shamir calls
   receive the exact owner-defined nonempty vectors.
5. **Vectors and negative tests.** Refreeze every inline question, goal,
   context, proposition, support, judgment, checked-result, authority-binding,
   and profile-cone identity vector. Rename the tests at
   `test_reference_model.py:1957`, `:2069`, and `:2743` so they assert
   question-plus-binding-map goal identity, not question-only identity. Add
   independent mutations for omitted/extra/duplicate/reordered requirements
   and bindings; absent source; wrong kind and coordinate; every model-scope
   mismatch; cross-profile premise IDs; noncanonical argument bytes; changed
   premise source/evidence/scope; node/context/support/judgment premise-ID
   omission, surplus, or mismatch; and binding changes that rotate every
   downstream identity without rotating the authenticated question.

#### `research.finite-cover` — `evaluation/finite-cover-analysis`

Rebuild `establish_checked_fixed_extractor()` through the migrated shared model
with the owner-required relation and witness premise pair. Keep the hypothesis
context empty—the named premises are not hypothesis nodes—but change
`test_finite_cover.py:330--440` to require the exact two premise IDs in the
goal, support, and judgment. Refreeze the resulting support, judgment,
checked-result, and authority-binding identities while retaining the existing
308-representative stream and `1d9472...a3dd` stream digest. Add missing,
extra, swapped-coordinate, and scope-mismatch controls; none may fall through
to the finite-cover arithmetic.

#### `research.joined-semantic-boundary` — `evaluation/k3-integrated-closure`

Keep the canonical shared-module load at `reference_model.py:26--75`. Rebuild
every Analysis-side source and family judgment after the shared Analysis-model
identity rotation,
then refreeze the joined result vectors that contain those IDs. Assert that
the OIR branch receives no named-premise body, local source handle, or Analysis
capability—only the already declared inert owner-ID correspondence. Add a
negative cross-consumer mutation showing that swapping an Analysis premise ID
changes/refuses the Analysis judgment without changing the independently
formed OIR projection.

#### `research.recursive-composition-boundary` —
`evaluation/recursive-composition-boundary`

The package currently hashes simplified support and judgment dictionaries at
`reference_model.py:1411--1445` rather than exact Analysis bodies. Keep it explicitly
a surrogate, but add an `exact_named_premise_ids` field to both payloads,
derived as the canonical union of premise IDs of their actual goals. The
current incremental families are empty only if their owner family contracts
say so; encode an explicit empty tuple in that case. Add negative tests for an
omitted, extra, duplicate, reordered, or caller-authored premise-ID summary and
refreeze all derived composition judgment IDs. Do not import
`evaluation/k3-analysis-closure`
unless this check is deliberately promoted from surrogate to exact Analysis
consumer.

#### `research.profile-publication` —
`evaluation/semantic-profile-publication`

After the owner deltas and Analysis reference-model migration settle, advance
the directly changed
profile/declaration revisions, run both publication compilers, and regenerate
`docs-next/pir/profiles/published-identities.json` from the agreed table.
Refreeze tests at `tests/test_publication.py:122--153` and the expected
property/transport/validation rotation cone. Add a mutation for the new
`analysis.named-premise` schema and each appended body field so a missing
descriptor, wrong ordinal, or stale semantic-law revision is rejected. This
step publishes identity metadata only; it does not validate any premise.

## Handoff

- **Files changed:** round-two rewrites of the review package `README.md`,
  `run.py`, and `expected-findings.json`; the Round two section and this
  handoff in the existing note; `model.py`, `independent.py`, `run.py`,
  `fixture.json`, `README.md`, and `expected-findings.json` in the predecessor
  intake probe; and the probe's existing row in `evaluation/README.md`. No
  owner page, profile manifest, checks manifest, lifecycle registry, directory
  README, or Analysis migration target was edited.
- **Commands:** clone-local alternate-index staging exited 0 in 0.47 seconds.
  With that index, `python3 -B checks/run.py validate` exited 0 in 0.04
  seconds; `python3 -B checks/run.py run --tier developer` exited 0 in 1.08
  seconds with 8/8 checks passing; and `python3 -B checks/run.py run --check
  research.analysis-premise-text-review` exited 0 in 1.06 seconds with 1/1
  passing. The direct intake probe exited 0 in 0.03 seconds, and the direct
  review package exited 0 in 1.00 seconds. JSON decoding, Python compilation,
  and `git diff --check` also exited 0. The alternate index, clone-local object
  directory, and clone-local UV cache were removed after the run.
- **Aggregate outcome:**
  `CannotAnswer/F0V2D1-C-ANALYSIS-PREMISE-TEXT-NOT-CLOSED` with three
  affirmative and four `CannotAnswer` review questions. The four listed
  `cannot_answer_findings` are the complete non-closure list.
- **Non-claims:** this is static source review, two-path finite intake evidence,
  publication reconstruction, and a migration inventory. It does not implement
  the Analysis reference-model migration, publish semantics, prove a
  premise/property/theorem,
  establish relation satisfaction or Plan honesty, validate a provider,
  verify a compiler/backend, or claim production security.
- **Surprises and where the brief was wrong:** the owner text contains 31
  anonymous hypothesis nodes, not the stated 30; seven nodes still lack the
  required fourth component, so the assertion that every node was completed is
  false. The clone still has no local `AGENTS.md` or `.claude/CLAUDE.md`, so
  their read-only primary-checkout copies were used. The workflow's private
  status append cannot be performed because this lane must not write outside
  the clone and the private ledgers are read-only. The existing
  `checks/manifest.json` descriptions remain round-one metadata because the
  brief expressly prohibited manifest edits; the executable packages and the
  existing evaluation index row carry the round-two state. The command details
  above come from the required alternate-index checks.

## Round three

This verification round reviews `27871e7..e950263`. It reruns the original
seven questions and adds the profile-specific hypothesis argument-schema
question and the cross-surface provider lane/completion question. The owner
text closes every previously open text question. The aggregate nevertheless
remains `Negative/F0V2D1-N-ANALYSIS-PREMISE-TEXT-NOT-CLOSED` because two
requirements fail in the migrated Analysis closure package, not because an
owner-page signature remains underdetermined.

| Review question | Outcome | Stable finding |
|---|---|---|
| Name closure | Affirmative | `F0V2D1-A-NAME-CLOSURE` |
| Constructor consistency | Affirmative | `F0V2D1-A-CONSTRUCTOR-CONSISTENCY` |
| Intake soundness | Affirmative | `F0V2D1-A-INTAKE-SOUNDNESS` |
| Decision fidelity | Affirmative | `F0V2D1-A-DECISION-FIDELITY` |
| Schnorr coordinate and binding formation | Affirmative | `F0V2D1-A-SCHNORR-BINDINGS` |
| Profile and manifest closure | Affirmative | `F0V2D1-A-PROFILE-MANIFESTS` |
| Existing-package refreeze | Negative | `F0V2D1-N-MIGRATED-IDENTITY-INPUTS` |
| Hypothesis argument-schema closure | Affirmative | `F0V2D1-A-HYPOTHESIS-ARGUMENT-SCHEMAS` |
| Provider lane and completion consistency | Negative | `F0V2D1-N-MIGRATED-COMPLETION-LAW` |

### Closed owner-text questions

`F0V2D1-A-NAME-CLOSURE` is affirmative. In
`docs-next/analysis/analysis-model.md` Section 4.1, lines 2150--2165 bind both
the direct profile and premise kind and route hypotheses through the
profile-specific `NamedHypothesisArgumentSchema<P,K>`. Lines 2181--2188 make
the provider arm dependent on its Protocol. Lines 2283--2294 define the goal
map through `AnalysisNamedPremiseBindingValue`, and lines 3120--3121 retain the
profile-and-kind-indexed premise identity. In
`docs-next/analysis/cryptographic-properties.md`, lines 2578--2594 bind
`ell0` in the construction helper and lines 3104--3109 pass it from the goal.
Lines 477--486 now derive `SchnorrFreshLawRef(S)` from the value of the exact
authenticated `fresh_law` leaf.

`F0V2D1-A-CONSTRUCTOR-CONSISTENCY` is affirmative. The current census is
eleven question, twelve goal, six context, five support, one judgment, and
twelve concrete premise-body displays. All carry their schema-required fields.
All thirty-one anonymous hypothesis nodes now carry `premises(goal)`; the seven
formerly incomplete displays are complete. The notation remains derived as
exactly `PremiseIdsOfGoal` by `analysis-model.md` lines 2305--2336.

`F0V2D1-A-INTAKE-SOUNDNESS` and `F0V2D1-A-DECISION-FIDELITY` remain
affirmative. `analysis-model.md` lines 3140--3162 still classify missing source
or key as `CannotAnswer`, kind, coordinate, and all four scope mismatches as
`Refused`, and malformed key sets as `Malformed`, with no default. The
construction and family premise lanes remain separate, provider requirements
remain outside the relation-bound Fresh question, and a whole-partition
provider statement adds operational completion when the provider models only
part of the partition.

`F0V2D1-A-SCHNORR-BINDINGS` is affirmative for the owner text.
`cryptographic-properties.md` lines 2302--2323 fix the six requirements.
Lines 2334--2357 fix the three exact model-binding laws and two honest
hypotheses. Lines 2365--2460 define the relation, witness, state, commit, and
respond bodies with all six premise fields. Lines 2537--2560 spell all six
relation-question bindings. Lines 2562--2576 form new relation and witness
premise identities over the extractor question's own exact subjects rather
than reusing the relation-question identities. Lines 2578--2594 spell both
construction bindings. Lines 5921--5939 spell both family bindings and use
`SamplerAdequacyFormOf(F)`.

`F0V2D1-A-HYPOTHESIS-ARGUMENT-SCHEMAS` is affirmative. The property schema at
`cryptographic-properties.md` lines 2204--2219 has five closed rows covering
six declarations: Fresh, construction sampler, construction oracle,
operational completion, honest commit, and honest respond. The transport
schema at lines 5851--5858 has two rows covering family sampler and family
oracle. Every declaration's first and only first-class coordinate argument is
the coordinate admitted for its kind; every later argument is named by its
row. The observed arities are respectively 2, 3, 2, 2, 1, 1, 3, and 2. No
declaration has a free or extra argument.

`F0V2D1-A-PROFILE-MANIFESTS` is affirmative. The three supported-kind
sequences equal their manifests. Both publication compilers agree on the
current source and the review-base source and independently reproduce the same
six-profile Analysis rotation cone. The three profile revisions and their
definition revisions were already at revision 1 at both endpoints of this
review range; this round observes no additional manifest revision transition.

### Independent premise-bearing identity reconstruction

The review implements its own encoders for premise kind, coordinate, law term,
bound value, source, evidence depth, scope, requirement, binding, question, and
goal bodies. It calls the Foundation profiled-content identity primitive
directly and does not call the migrated package's Analysis body encoder or
identity former. The family constructor is invoked only to obtain the lazy
observed comparison body; the independent path then recomputes every premise,
question, and goal identity from that body data.

For the migrated relation-bound Fresh Schnorr goal, the independent path
reproduces:

- direct profile digest
  `9d894e73918111ecc4e68e652a759cceb321fc7f4747132f182957975f8b3e13`;
- question digest
  `93caf8913796aa3433a922d57867925987ca291a9b69d83e3f304eb92d2a8f7e`;
- goal digest
  `79dcc80fff8307a7d2ab79ba523220ce0e17337bef2af0f6ba19fbe6cb17ccb4`;
  and
- six premise digests: commit `85eba04d...e5d3`, respond
  `9ce08ab5...0b4c`, witness `ec4ac4e9...179b`, relation
  `8c5fa7a9...4287`, Fresh coin `6fbcb132...64fb`, and prover state
  `8b0945b2...90ea`.

That exact migrated goal is not owner-determined. The reconstruction proves
what the migrated bytes say, not that the bytes use the owner-prescribed
coordinate. `evaluation/k3-analysis-closure/reference_model.py` lines
15872--15878 puts the encoded challenge occurrence coordinate in
`PIRPublicCoinLawCoordinate`. The owner instead requires the value of the
authenticated `fresh_law` leaf. The imported
`evaluation/k2-protocol-fiat-shamir/reference_model.py`
`PublicCoinChallengeProjection` at lines 2115--2122 contains only
`challenge_coordinate`, `domain_coordinate`, and `challenge_domain`; it has no
fresh-law coordinate or value. This is a concrete package mismatch, not a
remaining owner-text ambiguity.

For the migrated target family goal, the independent path reproduces:

- direct profile digest
  `9a251526a43529fe73899b81bf5241ee850e12c088c80629461aecd2926e886f`;
- question digest
  `ee652f7c36a086c67db3d075aeb8a93c2caec0b1007d457b7fcab0fb24281fc5`;
- sampler premise digest
  `7e0126095e8b31bde80e07c0b6043204ad10e3adba3a3714e9bea5559cec0fbb`;
- oracle-process premise digest
  `358db81101d8038121451a98c95de2f9e8be37d6aa3821fec48b5aeff3dd8ed8`;
  and
- goal digest
  `9c49308e1e89c5da7f01b783dd323428fb71470fe3acfd9a31d021d47ca1b2f2`.

The family identity is owner-determined: its coordinate, exact-total sampler
form, oracle model, family source, evidence depth, scope, and two law
declaration references all match the transport-profile rows. The migrated
premise identities as a whole are nevertheless not owner-determined because
the relation-bound goal above and the construction sampler below still use
proxy inputs. The fixed-extractor relation/witness pair now uses the consuming
question's exact subjects and matches the repaired owner rule. No provider
premise identity forms because no provider declaration is published.

### Remaining negative findings and proposed replacements

`F0V2D1-N-MIGRATED-IDENTITY-INPUTS` records two exact replacements:

1. At `evaluation/k3-analysis-closure/reference_model.py` lines 15872--15878,
   replace the challenge-coordinate proxy with the exact
   `ProtocolDeclarationRef<"pir.public-coin-law">` value selected by
   `challenges[S.challenge_ref].fresh_law` in the authenticated
   `PublicCoinView`. The imported source must first expose that leaf; adding a
   locally inferred declaration or converting the challenge occurrence
   coordinate is not an admissible replacement.
2. At the same file's lines 16127--16132, replace the legacy
   `construction.max_attempts` branch with `SamplerAdequacyFormOf(T)` derived
   from T's identity-bearing `challenge_rules`: `ExactTotal` exactly when every
   rule has `maximum_draws = 1`, otherwise `RetryWithExhaustion` of the maximum
   per-rule value. The imported legacy construction at
   `evaluation/k2-protocol-fiat-shamir/reference_model.py` lines 1743--1749 has
   no `challenge_rules`, so this requires an authenticated current
   construction carrier rather than a field rename.

`F0V2D1-N-MIGRATED-COMPLETION-LAW` records one further replacement. The six
lane names and `Image | Unmodelled` law agree across the PIR partition,
Analysis kernel/property text, intake probe, and migrated model. The tenth kind
also exists in every surface. However,
`evaluation/k3-analysis-closure/reference_model.py` lines 869--898 has no
`operational-completion-hypothesis-v0` declaration row, while its test at
lines 888--900 supplies the arbitrary symbol
`operational-completion-hypothesis`. Add the exact property-profile semantic-law
declaration with classification `exact-named-hypothesis`, obtain its profile
declaration reference through the same exact resolver used by the other
hypotheses, and use canonical arguments
`[PIRProtocolOutcomePartitionCoordinate(P), provider]`. The unpublished
provider test may still fail closed before premise formation; it must not use
that earlier failure to mask an arbitrary law reference.

The exact remaining refreeze inputs are therefore:

1. the authenticated `fresh_law` declaration leaf for the migrated Schnorr
   Protocol;
2. identity-bearing construction `challenge_rules` and every rule's
   `maximum_draws` value;
3. a published property-profile provider declaration and closed provider
   carrier before either provider-bound premise may form; and
4. the exact property-profile operational-completion hypothesis declaration
   reference.

There is no owner-page `Proposed delta` in this round. The owner pages already
state each required replacement exactly; the defects are in the migrated
instrument and its legacy imported carrier. No owner page, profile manifest,
intake probe, or migrated package was edited by this verification lane.

## Handoff

Files changed:

- `evaluation/formal-source-analysis-premise-review-f0v2d1/run.py` now asks the
  nine round-three questions, reconstructs the relation-bound and family goals
  with independently written encoders, and freezes the two migrated-package
  mismatches instead of treating missing inputs as affirmative evidence.
- `evaluation/formal-source-analysis-premise-review-f0v2d1/expected-findings.json`
  freezes the twelve findings and the `Negative` aggregate.
- `evaluation/formal-source-analysis-premise-review-f0v2d1/README.md` states the
  exact question, result, owner-determined identities, remaining refreeze
  inputs, and pass/non-claim boundary.
- `checks/manifest.json` and `evaluation/README.md` describe the rerun without
  adding a new package or lifecycle object.
- This note adds `Round three` and this handoff. No owner page, migrated
  package, directory README, lifecycle entry, or lifecycle count pin changed.

Commands run before this handoff, with observed exit status and wall time:

- Python AST compilation plus JSON decoding of the changed executable and
  frozen findings: exit 0; this preflight was not separately timed.
- `git diff --check`: exit 0, 0.06 s.
- `python3 -B evaluation/formal-source-analysis-premise-review-f0v2d1/run.py`
  for the machine-readable result: exit 0, 13.13 s.
- `python3 -B evaluation/formal-source-analysis-premise-review-f0v2d1/run.py --check`:
  exit 0, 12.99 s; 12/12 frozen findings matched, including 2 `Negative`, 0
  `CannotAnswer`, and aggregate `Negative`.
- Alternate-index initialization with a clone-local object directory:
  `git read-tree HEAD` exited 0 in 0.00 s and `git add -u` exited 0 in 0.47 s.
- `python3 -B checks/run.py validate` under the alternate index: exit 0,
  0.04 s; 77 checks and 6 tiers validated.
- `python3 -B checks/run.py run --tier developer` under the alternate index and
  clone-local offline uv cache: exit 0, 1.78 s; 9/9 checks passed.
- `python3 -B checks/run.py run --check research.analysis-premise-text-review`
  under the same environment: exit 0, 12.96 s; 1/1 check passed.

Aggregate outcome: all nine review questions close. Seven are affirmative and
two are negative; none is `CannotAnswer`. The Analysis owner text is closed,
but the migrated executable package is not yet owner-determined because its
Fresh premise and construction sampler form use legacy proxies, and its
operational-completion test supplies an arbitrary hypothesis symbol. The check
passes because those negative results exactly match the frozen expectation.

Non-claims: this rerun does not repair or refreeze the migrated package, publish
a provider, authenticate a missing source declaration, prove the Analysis
laws, establish backend correctness, or establish protocol security. Passing
tests show only that the bounded review instrument reproduces its frozen
findings from this source snapshot.

Surprises and corrections to the brief: the factual owner-repair description
was accurate, including the seven completed displays. What did not follow from
those repairs was migrated-package closure: the imported public-coin carrier
still lacks `fresh_law`, the construction carrier still lacks identity-bearing
challenge rules, and the migrated declaration catalog still lacks the exact
operational-completion hypothesis. Both endpoint profile revisions remain 1
even though all six profile identifiers rotate through the changed source
page. This clone has no local `AGENTS.md` or `.claude/CLAUDE.md`, so the
read-only primary-checkout copies named by the workflow were used. The private
register was not appended because it is outside this clone and read-only to
this lane. No lifecycle count pin moved because this round updates an existing
package rather than adding one.
