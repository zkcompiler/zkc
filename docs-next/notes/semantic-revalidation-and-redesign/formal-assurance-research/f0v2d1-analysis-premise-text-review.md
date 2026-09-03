# Analysis Named-Premise Owner-Text Review

> **State:** `Negative/F0V2D1-N-ANALYSIS-PREMISE-TEXT-NOT-CLOSED`
> for the exact owner-text range `7a63432..177cbaa`
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

## Handoff

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
