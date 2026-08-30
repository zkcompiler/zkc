# Relations

> **Document kind:** Domain index
> **Document state:** Active target-domain index
> **Provisional owner:** `relations`
> **Authority:** None during the transition. Current relation semantics remain
> governed by the [Relations specification](../../docs/spec/relations.md).
> **Closure interpretation:** This index routes the current selected target. It
> does not assert semantic freeze, implementation conformance, protocol-family
> support, or normative cutover. The
> [v0 Semantic Design Program](../project/v0-design-program.md#14-progress-and-change-control)
> owns the live gate.

## Purpose

`relations/` owns mathematical relation meaning and the checked bridges from
that meaning to exact PIR facts. It keeps five questions separate:

1. what relation is defined;
2. what typed public, private, Oracle, and phased inputs it expects;
3. whether one exact confidential assignment satisfies one exact semantic
   model;
4. whether selected Protocol, Plan, artifact, or run occurrences correspond to
   selected relation occurrences; and
5. whether one relation transformation preserves satisfaction in a stated
   direction.

Admission of a definition, Interface, instance, or binding answers none of the
later questions automatically.

## Owned semantic subjects

- `RelationDefinition`, its admitted definition-language declaration, and
  exact typed payload;
- `RelationInterface`, with four ordered and non-collapsible roles:
  `PublicInstance`, `PrivateWitness`, `OracleStatement`, and `PhaseInput`;
- `RelationInstance`, containing only public-instance values, public Oracle
  bindings, and phase values;
- fresh owner-local private-witness and Oracle-material assignments;
- `RelationSemanticModel` and its identity-bearing deterministic satisfaction
  command machine;
- `RelationTransform` and separately checked directional refinement;
- exactly three value-representation bridges: total equivalence, injective
  embedding, and directional lossy projection;
- relation artifact profiles, expectation-free observations, typed comparison,
  grounding equations, and commitment grounding; and
- the closed correspondence-question algebra, including separate public run
  facts and causal confidential initial logical-Oracle material agreement, and
  its checked results.

The exact namespace is one 23-entry semantic-subject catalog. It is disjoint
from the 14-entry module declaration-contract catalog; neither prose nor an
executable fixture can add a kind or move one between the two. The literal
semantic catalog and still-open profile-preimage boundary are in
[Relation Model, Section 2.1](relation-model.md#21-k1-identity-language-profile-and-values),
and the declaration catalog is in
[Section 2.4](relation-model.md#24-closed-declaration-contract-catalog).
The 14 declarations are module-owned grammar that the final Relations semantic
law source must commit; the profile-local `declaration_catalogs` field is
exactly empty. The bounded executable independently enumerates all 14 kinds,
but its placeholder law bytes neither publish nor authenticate their complete
dispatch grammar.

Semantic proposition identity is separate from validation basis. Certificates,
assumption evidence, exhaustive-check controls, evaluator charging contracts,
request limits, and replay inputs do not enter a proposition or bridge identity.
A checked result binds the exact proposition and the exact validation request.

## Protocol and Plan dependency cut

The two attachment paths are deliberately independent:

| Subject | Reads | Does not read |
|---|---|---|
| `ProtocolRelationBinding` | one exact `ProtocolId`, relation Interfaces, typed PIR Statement/challenge/Oracle/claim/reduction occurrences | external `ProtocolInterface`, `ProverPlan`, secret assignments |
| `PlanWitnessBinding` | one PIR-owned source-ID-free `PlanWitnessSurfaceId`, one `RelationInterfaceId`, typed witness occurrences | `ProverPlanId`, Plan-local nodes, private source maps, Protocol correspondence |

An external `ProtocolInterface` is an additional operand only for questions
about decoded external presentation. It is not a prerequisite for structural
Protocol/relation correspondence. A checked aggregate may combine independently
checked bindings without becoming a new semantic owner.

Equal values at different occurrences never alias. Coverage, injectivity,
whole-surface agreement, and mapped-edge agreement are separate questions.

## Satisfaction

The admitted satisfaction-evaluator declaration commits to exact role types,
model program, state type, and Foundation `start`/per-Oracle `resume`
algorithms. The
Relations owner runs the closed command machine and alone holds restricted
Oracle lookup capabilities. Portable algorithms receive neither Oracle material
nor a capability.

`CheckRelationSatisfaction` is Affirmative only when that machine reaches
`Decide(true)` and Negative only at `Decide(false)` for the exact model,
instance, confidential occurrences, assumptions, and lookup trace. Missing
support or material, authority refusal, malformed input, deterministic limit
exhaustion, and checker disagreement retain distinct qualified outcomes. The
result establishes no Protocol acceptance or cryptographic property.

## Values, artifacts, and grounding

A value bridge relates representations only. Relation refinement, commitment
construction, and a PIR reduction are different subjects with different laws.
Lossy projection carries an exact collision relation and exact use coordinates;
the current target closes occurrence-premise and count consumption only for
the run-grounded relation-instance seam. Structural Plan and artifact mappings
acquire no implicit live-source or quantitative claim. Analysis, not Relations,
owns any quantitative security price.

Artifact interpretation is optional and expectation-free. `Unread` differs
from `Observed([])`. The interpreter consumes one exact format-derived byte
type and returns a closed, typed, bounded field record. A later comparison owns
expected agreement. Grounding equations are finite acyclic typed DAGs over
exact relation, artifact, and PIR sources; commitment grounding names the exact
construction and equation position but proves no binding, hiding, extraction,
or opening theorem.

A PIR commitment-opening verifier profile supplies only public claim and check
coordinates. It does not assert that a private polynomial or Oracle material
produced the commitment, that the asserted answer is the source evaluation, or
that a producer algorithm is correct. Add an exact evaluation-correspondence or
material-grounding relation only when a named consumer needs that proposition;
do not infer it from successful verifier execution.

Public run grounding consumes only a PIR-issued public occurrence view produced
by a live causal execution or an affirmative exact replay. Initial logical-
Oracle material agreement is separate: it consumes one matching Relations
`OracleMaterialAssignment` and one PIR-issued, causal-only, purpose-bound
confidential view of the exact whole carrier. Exact same-type equality is the
only affirmative law. A raw trace, equal reconstructed value, caller-built
tuple, stored result ID, carrier digest, or replay-qualified source cannot mint
that authority. Neither secret body nor a secret-derived identifier enters a
durable Relations subject or result.

Lossy-source authority now has one closed Relations specialization of the Foundation
envelope. Public `RelationInstance` fields and durable
`RelationArtifactObservation` fields use inert portable bindings keyed by their
exact subject IDs; a `PrivateWitnessAssignment` field is owner-local because
the assignment is a fresh nonserializable occurrence. All three additionally
bind the exact typed field, consumer, purpose, no-policy declaration, closure,
and fresh identical-bearer requirement. Equal values and reconstructed
envelopes grant no authority. This is a semantic target decision, not a claim
that the full lossy lane has executable or protocol-family evidence.

## Outcomes and authority

A well-formed completed disagreement is Negative. `Unsupported`,
`MissingDependency`, `CannotAnswer`, `KindMismatch`, `Refused`, `Malformed`,
`DeterministicLimitExceeded`, and `CheckerFailure` are not Negative.
`MissingDependency` is an absent exact named durable preimage after its typed
coordinate forms; `CannotAnswer` is a supported formed operation unable to
obtain a required premise, live read, or authority. Only a completed result
creates a fresh process-local checked capability; portable IDs and reports are
inert. The five selected source families have exact bodies in
[Protocol Correspondence, Section 4.3](protocol-correspondence.md#43-exact-relations-source-authority-subjects).
There is no open family or generic checked-result source binding; exporting a
new family requires a Relations profile/law revision.

Relations has no OIR dependency in this target. Future verifier-to-relation
descent remains unavailable until OIR defines and admits its exact source
result.

## Does not own

- relation-source languages or source-to-definition compilation;
- witness generation, storage, secrecy policy, or endpoint supply;
- Protocol transcript, challenge, claim-flow, or acceptance semantics;
- soundness, knowledge, completeness, zero knowledge, theorem applicability,
  or quantitative security loss;
- OIR projection, endpoint execution, deployment, or realization; or
- broad compatibility with an external relation ecosystem.

## Consumers

- `pir/` supplies admitted Protocol subjects, typed owner views, and the narrow
  `PlanWitnessSurface`;
- `analysis/` may consume exact checked relation, refinement, bridge-use,
  commitment, and run facts without redefining them;
- `compiler/` may require those facts as independently owned prerequisites;
- future `oir/` and Realization may consume public/private roles only through
  their own admitted contracts; and
- `evidence/` records exact adapter and checker observations without upgrading
  their claim scope.

## Target documents

- [Relation Model](relation-model.md) — definitions, four-role Interfaces,
  instances, confidential satisfaction, transforms, bridges, split bindings,
  artifacts, and grounding
- [Protocol Correspondence](protocol-correspondence.md) — closed question
  grammar, one derived read manifest, checked operations, outcomes, public run
  grounding, and causal confidential initial-Oracle agreement
- [Protocol Interfaces and Prover Plans](../pir/interfaces-and-plans.md) — PIR-
  owned external presentation, strategy recipes, `PlanRealizes`, and
  `PlanWitnessSurface`
- [Interactive Core and Causal Execution](../pir/interactive-core.md) — PIR-
  owned occurrence, execution, replay, and public and confidential run-view
  sources

The selected project architecture pages remain historical rationale. These
durable domain pages own the current target definitions. Current `docs/`
remains normative until explicit consolidation and cutover.

## Remaining gates

- The exact 23/14 catalogs and six source-authority body schemas are selected,
  but the complete six-field `SemanticLanguageProfileBody`, exact semantic-
  law-source bytes, and independently reconstructible
  `RelationsProfileId` remain unpublished. No persistent-ID or semantic-freeze
  claim follows from the catalog closure alone.
- The instance/artifact portable and private-witness owner-local source laws
  are now specified. Executable correspondence for those constructors, native
  protocol pressure, cold replay, and negative authority tests remain evidence
  obligations.

- The bounded Analysis target selects games, theorem-applicability rules, and
  quantitative contracts that consume these exact sources without restating
  them. Broader property families and concrete theorem discharge remain open.
- The bounded OIR projection uses OIR-specific purpose views and a separate
  projection identity; `PlanWitnessSurface` remains Relations-specific and
  grants no OIR authority. Full OIR syntax and protocol-family coverage remain
  open.
- One exact three-fold, scalar-terminal classical FRI control supplies bounded
  executable pressure for Oracle publications, twelve logical opening
  coordinates, construction maps, and a scalar terminal residual. The target
  Relations path now distinguishes public-bound and logical Oracle edges and
  requires causal, purpose-bound, whole-carrier authority for initial-Oracle
  material agreement. Its bounded executable evidence and explicit nonclaims
  are tracked by the
  [native FRI/IOR validation package](../../evaluation/native-fri-ior/README.md).
  General FRI/IOR correspondence, opening security, proximity, and outer-
  relation inference remain open, as does native Nova/folding pressure for
  relation-changing reductions.
- The integrated Schnorr witness exercises bounded deduplication and joined
  read closure for one relation/Plan grounding path. It does not exercise the
  full bridge-law portfolio or general relation execution. Broader portfolio
  pressure, independent freeze review, normative encodings, implementation
  correspondence, and migration remain open.
