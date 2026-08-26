# Relations

> **Document kind:** Domain index
> **Document state:** Active target-domain index
> **Provisional owner:** `relations`
> **Authority:** None during the transition. Current relation semantics remain
> governed by the [Relations specification](../../docs/spec/relations.md).
> **Closure interpretation:** This index routes the selected K3-B target. It
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
- the closed correspondence-question algebra and its checked results.

Semantic proposition identity is separate from validation basis. Certificates,
assumption evidence, exhaustive-check controls, evaluator charging contracts,
request limits, and replay inputs do not enter a proposition or bridge identity.
A checked result binds the exact proposition and the exact validation request.

## Protocol and Plan dependency cut

The two attachment paths are deliberately independent:

| Subject | Reads | Does not read |
|---|---|---|
| `ProtocolRelationBinding` | one exact `ProtocolId`, relation Interfaces, typed K2 Statement/challenge/Oracle/claim/reduction occurrences | external `ProtocolInterface`, `ProverPlan`, secret assignments |
| `PlanWitnessBinding` | one PIR-owned source-ID-free `PlanWitnessSurfaceId`, one `RelationInterfaceId`, typed witness occurrences | `ProverPlanId`, Plan-local nodes, private source maps, Protocol correspondence |

An external `ProtocolInterface` is an additional operand only for questions
about decoded external presentation. It is not a prerequisite for structural
Protocol/relation correspondence. A checked aggregate may combine independently
checked bindings without becoming a new semantic owner.

Equal values at different occurrences never alias. Coverage, injectivity,
whole-surface agreement, and mapped-edge agreement are separate questions.

## Satisfaction

The admitted satisfaction-evaluator declaration commits to exact role types,
model program, state type, and K1 `start`/per-Oracle `resume` algorithms. The
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
construction, and a K2 reduction are different subjects with different laws.
Lossy projection carries an exact collision relation and exact use coordinates;
K3-B closes occurrence-premise and count consumption only for the run-grounded
relation-instance seam. Structural Plan and artifact mappings acquire no
implicit live-source or quantitative claim. Analysis, not Relations, owns any
quantitative security price.

Artifact interpretation is optional and expectation-free. `Unread` differs
from `Observed([])`. The interpreter consumes one exact format-derived byte
type and returns a closed, typed, bounded field record. A later comparison owns
expected agreement. Grounding equations are finite acyclic typed DAGs over
exact relation, artifact, and PIR sources; commitment grounding names the exact
construction and equation position but proves no binding, hiding, extraction,
or opening theorem.

Run grounding consumes only a PIR-issued public occurrence view produced by a
live causal execution or an affirmative exact replay. A raw record, equal value,
caller-built tuple, or stored result ID cannot mint that view.

## Outcomes and authority

A well-formed completed disagreement is Negative. `Unsupported`,
`CannotAnswer`, `Refused`, `Malformed`, `DeterministicLimitExceeded`, and
`CheckerFailure` are not Negative. Only a completed result creates a fresh
process-local checked capability; portable IDs and reports are inert.

Relations has no OIR dependency in K3-B. Future verifier-to-relation descent
remains unavailable until OIR defines and admits its exact source result.

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
  grammar, one derived read manifest, checked operations, outcomes, and run
  grounding
- [Protocol Interfaces and Prover Plans](../pir/interfaces-and-plans.md) — PIR-
  owned external presentation, strategy recipes, `PlanRealizes`, and
  `PlanWitnessSurface`
- [Interactive Core and Causal Execution](../pir/interactive-core.md) — K2-
  owned occurrence, execution, replay, and public run-view sources

The selected project architecture pages remain historical rationale. These
durable domain pages own the current K3-B target definitions. Current `docs/`
remains normative until explicit consolidation and cutover.

## Remaining gates

- K3-C must define the Analysis games, theorem-applicability rules, and
  quantitative loss that consume these exact sources.
- K3-D must define any OIR-specific purpose view and projection identity effect;
  `PlanWitnessSurface` is Relations-specific and grants no OIR authority.
- Native P02 FRI/IOR and P09 Nova/folding remain executable portfolio pressure
  for commitment/opening and relation-changing reduction paths.
- K3-E still owns integrated deduplication and freeze review; later stages own
  normative encodings, implementation correspondence, and migration.
