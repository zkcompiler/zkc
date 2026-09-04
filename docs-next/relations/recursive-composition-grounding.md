# Recursive-Composition Grounding

> **Document kind:** Target semantic specification
> **Document state:** Active target extension; semantic source published
> **Provisional owner:** `relations`
> **Authority:** None during transition. Current normative relation semantics
> remain under [`docs/spec/relations.md`](../../docs/spec/relations.md).

<!-- zkc-profile-source:relations-recursive-grounding-semantics:start -->

## 1. Purpose and boundary

This page owns two narrow Relations propositions needed by recursive,
accumulation, and folding consumers:

1. every recursion-facing relation-instance occurrence is either checked
   strictly or bound through an exact finite digest path to a strictly checked
   occurrence; and
2. a CycleFold companion instance is strict, value-bound, and folded inside
   the same primary step.

It does not define recursion, an accumulator, a folding scheme, a recursive
proof, an induction theorem, or a second execution semantics. PIR still owns
each run and direct causal handoff. Analysis owns cryptographic interpretation
and every many-step theorem.

This page imports the existing typed `GroundingEquation`,
`GroundingInvocation`, `CheckedGroundingEvaluation`, `GroundingOutputCoordinate`,
`RelationInstance`, `RelationRunView`, and exact source-authority laws from
[Relation Model](relation-model.md). It imports generated run and Plan-recipe
authority from PIR without redefining either.

## 2. Recursion-facing binding coverage

### 2.1 Identified schema

One new Relations semantic subject fixes the complete role graph before any
runtime occurrence exists:

~~~text
RecursionCoverageInstanceSlotDecl = {
  interface_id: RelationInterfaceId
}

RecursionCoverageInstanceSlotRef =
  canonical ordinal in `instance_slots`

CoverageGroundingUse = {
  equation_id: GroundingEquationId,
  instance_slot_map:
    ExactInjectiveMap<
      GroundingInstanceSlotRef,
      RecursionCoverageInstanceSlotRef>
}

StrictInstanceDischarge = {
  instance_slot: RecursionCoverageInstanceSlotRef,
  grounding_use: CoverageGroundingUse,
  truth_output: GroundingOutputCoordinate<Bool>
}

DigestBindingDischarge = {
  child_slot: RecursionCoverageInstanceSlotRef,
  parent_slot: RecursionCoverageInstanceSlotRef,
  grounding_use: CoverageGroundingUse,
  binding_equality_ordinal: Natural,
  digest_algorithm_coordinates:
    CanonicalNonEmptySortedUniqueSeq<PortableAlgorithmRef>
}

RecursionInstanceDischarge =
    Strict(StrictInstanceDischarge)
  | DigestBound(DigestBindingDischarge)

RecursionBindingCoverageSchemaBody = {
  used_modules: CanonicalSortedUniqueSeq<SemanticModuleId>,
  instance_slots: CanonicalNonEmptySeq<RecursionCoverageInstanceSlotDecl>,
  discharges:
    ExactMap<RecursionCoverageInstanceSlotRef,RecursionInstanceDischarge>
}

RecursionBindingCoverageSchemaId =
  RelationsId<"relations.recursion-binding-coverage-schema">(
    B,RecursionBindingCoverageSchemaBody)

RecursionBindingCoverageQuestionCoordinate = {
  schema_id: RecursionBindingCoverageSchemaId
}
~~~

The discharge-map key set equals every and only `instance_slots`. A `Strict`
entry's key equals `instance_slot`. A `DigestBound` entry's key equals
`child_slot`; its parent differs and is in range. Every non-strict slot has
exactly one parent, the resulting directed graph is acyclic, and every path
ends at one strict slot. Therefore an omitted imported instance, a second
parent, a self edge, a cycle, and a disconnected component refuse schema
formation.

Every `CoverageGroundingUse` authenticates its exact admitted equation. Its
map covers every and only that equation's instance slots and preserves each
declared `RelationInterfaceId`. The same coverage slot may be read by multiple
equations, but one equation slot cannot be mapped twice. A strict
`truth_output` names the same equation and has the exact Foundation value type
`Bool`. A digest
discharge names an in-range equality whose two dependency cones read the exact
mapped child and parent slots. Its algorithm-coordinate set is owner-derived
from every digest-producing step in those two cones; a caller cannot omit,
add, or reorder an algorithm.

`used_modules` is the exact direct module union of the slot Interfaces,
grounding equations, output type, and digest algorithms. The schema contains
no relation instance, run, secret, result, capability, theorem, hash-security
claim, or own ID.

The one-field question coordinate is a canonical Relations law coordinate,
not another semantic subject. It selects the complete schema rather than a
caller-authored subset of roles or discharges. The checked result below retains
that exact coordinate so another owner can ask about the complete coverage
proposition without identifying the live occurrence.

### 2.2 Occurrence-local invocation

~~~text
RecursionBindingCoverageInvocation = {
  schema_id: RecursionBindingCoverageSchemaId,
  instances:
    ExactMap<RecursionCoverageInstanceSlotRef,RelationInstance>,
  grounding_invocations:
    ExactMap<GroundingEquationId,GroundingInvocation>
}

CheckedRecursionBindingCoverage =
  owner-local nonserializable association of {
    question_coordinate: RecursionBindingCoverageQuestionCoordinate,
    schema_id: RecursionBindingCoverageSchemaId,
    invocation: exact RecursionBindingCoverageInvocation,
    grounding_results:
      ExactMap<GroundingEquationId,CheckedGroundingEvaluation>,
    strict_truth_reads:
      ExactMap<RecursionCoverageInstanceSlotRef,CanonicalValue<Bool=true>>,
    paths_to_strict_discharge:
      ExactMap<RecursionCoverageInstanceSlotRef,
               NonEmptyCanonicalSeq<RecursionCoverageInstanceSlotRef>>,
    digest_binding_coordinates:
      CanonicalSortedUniqueSeq<{
        equation_id: GroundingEquationId,
        equality_ordinal: Natural,
        digest_algorithm_coordinates:
          CanonicalNonEmptySortedUniqueSeq<PortableAlgorithmRef>
      }>,
    exact source objects, generations, and fresh capabilities
  }

CheckRecursionBindingCoverage(
  exact admitted RecursionBindingCoverageSchema,
  exact RecursionBindingCoverageInvocation,
  every exact admitted GroundingEquation,
  every exact affirmative CheckedGroundingEvaluation and fresh capability,
  every exact instance, source binding, and fresh capability)
  -> Qualified<Affirmative({
       result: CheckedRecursionBindingCoverage,
       capability: CheckedRecursionBindingCoverageCapability
     })>
   | Negative | Unsupported | MissingDependency | CannotAnswer | KindMismatch
   | Refused | Malformed | DeterministicLimitExceeded | CheckerFailure
~~~

The invocation's instance key set is exact. Each instance Interface equals its
slot declaration. Every grounding invocation supplies that same instance
object at every mapped operand slot, and the corresponding source authority
binds that exact occurrence. Equal IDs, equal values, a replayed instance, or
a reconstructed authority cannot substitute.

For a strict discharge, Relations reads the exact `truth_output` through the
affirmative grounding capability and requires `true`. For a digest discharge,
the named equality is present in the exact affirmative grounding result. All
other equality clauses of every used grounding equation must also be
affirmative: a caller cannot select one true clause from an otherwise negative
equation. Missing, extra, duplicated, or wrong-generation grounding inputs
refuse.

An affirmative result establishes only complete occurrence linkage under the
written equations. A false strict output or false grounding equality is
Negative. An unbound role, malformed graph, owner mismatch, wrong occurrence,
or inexact invocation is `Malformed` or `Refused` according to whether
formation or authority failed. Missing a formed exact dependency is
`MissingDependency`; unavailable live reads are `CannotAnswer`.

The result has no semantic ID, portable body, or cold reconstruction. A finite
consumer may retain its exact digest-binding coordinates as inputs to an
Analysis question. Relations does not interpret those algorithms as collision
resistant, binding, random-oracle, or secure.

The exact cross-owner source operation is:

~~~text
IssueRecursionBindingCoverageResultSource(
  exact affirmative CheckedRecursionBindingCoverage result,
  identical live CheckedRecursionBindingCoverageCapability result_capability,
  exact consumer: RelationsDownstreamCoordinate,
  exact purpose: RelationsDownstreamCoordinate)
  -> RelationsFieldSourceIssueOutcome<OwnerLocalSourceAuthorityBinding>
~~~

It derives family `"recursion-binding-coverage-result"`, source
`RecursionBindingCoverageResultSource(result.question_coordinate)`, manifest
`CompleteRecursionBindingCoverageResult`, and the exact Relations role,
payload, no-policy, requirement, and closure subjects. Its Foundation local
coordinate is the identical result object. The fresh source capability retains
the original result capability and exact consumer, purpose, schema, process
generation, and lifetime. A partial role/path projection, copied result,
reconstructed envelope, different schema, or stale bearer refuses. The export
therefore carries the complete affirmative finite occurrence check and no
claim about digest binding or induction.

## 3. Finite recurrence remains one-step

`CheckedRecursionBindingCoverage` may be conjoined with one exact
`CheckedCausalPlanStepRecurrence` only when both retain the same two run
objects, the same relation-instance objects in their named roles, and matching
fresh source authorities. The conjunction is owner-local and nonidentified.

A finite sequence of such conjunctions may be checked for exact adjacency:
the target run and carried instance object of edge `i` are the source run and
carried instance object of edge `i+1`, and no one-use handoff capability is
reused. The finite chain result is also nonidentified and nonserializable. It
establishes adjacency only for those occurrences. It cannot form an Analysis
family, theorem schema, theorem applicability result, or induction judgment.

## 4. CycleFold same-step entry condition

CycleFold's companion curve-operation instance is not a second continuation
step. A complete CycleFold elaboration must satisfy:

~~~text
CycleFoldSameStepGroundingQuestionCoordinate = {
  primary_protocol_id: ProtocolId,
  companion_interface_id: RelationInterfaceId,
  companion_grounding_equation_id: GroundingEquationId,
  primary_values: {
    rho: ProtocolValueCoordinate,
    C1: ProtocolValueCoordinate,
    C2: ProtocolValueCoordinate,
    C_prime: ProtocolValueCoordinate
  },
  companion_values: {
    rho: RelationPublicRef,
    C1: RelationPublicRef,
    C2: RelationPublicRef,
    C_prime: RelationPublicRef
  },
  strict_truth_output: GroundingOutputCoordinate<Bool>,
  companion_fold_effect: exact PIR Plan effect coordinate,
  primary_step_terminal: exact PIR terminal coordinate
}

CycleFoldSameStepGroundingRequest = {
  question_coordinate: CycleFoldSameStepGroundingQuestionCoordinate,
  primary_run: exact causal RelationRunView,
  companion_instance: exact RelationInstance,
  companion_grounding_invocation: GroundingInvocation
}

CheckCycleFoldSameStepGrounding(
  exact request,
  exact affirmative CheckedGroundingEvaluation and fresh capability,
  exact causal primary-run and Plan-recipe/effect views and fresh capabilities)
  -> Qualified<Affirmative({
       result: CheckedCycleFoldSameStepGrounding,
       capability: CheckedCycleFoldSameStepGroundingCapability
     })>
   | Negative | Unsupported | MissingDependency | CannotAnswer | KindMismatch
   | Refused | Malformed | DeterministicLimitExceeded | CheckerFailure
~~~

The coordinate is a canonical Relations law coordinate rather than a new
semantic subject. It contains only authenticated static subjects and typed
references; it has no run, instance, value, result, capability, or own ID. The
request's run Protocol and companion Interface must equal the coordinate.

The equation reads the exact primary run and companion instance. It contains
four same-type equalities, in the written order, for `(rho,C1,C2,C_prime)` and
its strict output evaluates to `true`. The companion instance is created by an
effect in that same generated Plan step. The Plan dependency graph places the
companion-fold effect after creation and all five checks, and places the effect
before the reached accepted terminal. Every object and capability is exact.
The affirmative result and capability retain the exact question coordinate,
request, grounding result, run, instance, effect ordering, and source
authorities used by the check.

A companion supplied only as an accepted-terminal output, a relation instance
from another run, a relaxed or false strictness output, one wrong public-I/O
value, or a fold effect after terminal is not affirmative. A two-run encoding
is unsupported unless a distinct exact Relations law proves an equivalent
same-step ordering and all value bindings.

This operation is a protocol-specific entry condition for a future complete
CycleFold witness. It does not add a generic satellite-protocol primitive or
claim CycleFold correctness.

The matching cross-owner source operation is:

~~~text
IssueCycleFoldSameStepGroundingResultSource(
  exact affirmative CheckedCycleFoldSameStepGrounding result,
  identical live CheckedCycleFoldSameStepGroundingCapability result_capability,
  exact consumer: RelationsDownstreamCoordinate,
  exact purpose: RelationsDownstreamCoordinate)
  -> RelationsFieldSourceIssueOutcome<OwnerLocalSourceAuthorityBinding>
~~~

It derives family `"cyclefold-same-step-grounding-result"`, the exact result
question coordinate, `CompleteCycleFoldSameStepGroundingResult`, and the same
closed Relations role, payload, no-policy, requirement, and closure chain as
the other source families. The owner-local coordinate is the identical result
object and the fresh source capability retains the original result capability.
Another step, equation, companion Interface, consumer, purpose, process
generation, partial result view, copied result, or stale bearer refuses. This
does not make the CycleFold condition portable or establish its protocol
theorem.

## 5. Portable re-admission is not causal recurrence

Transported accumulator or witness material may later be decoded and admitted
as a fresh ordinary PIR input. A receiver may run an exact decider or verify a
proof and use that Analysis result as a premise. Neither operation recreates
the source run object, the consumed one-use handoff capability, or a
`CheckedCausalPlanStepRecurrence` result. Relations therefore refuses a causal
join whose target occurrence was created by byte transport rather than the
exact PIR handoff operation.

## 6. Nonclaims

Nothing on this page establishes relation satisfaction, fold preservation,
accumulator validity, a decider theorem, collision resistance, completeness,
soundness, knowledge extraction, non-malleability, IVC/NIVC/PCD, arbitrary-
party continuation, or implementation support. Those conclusions require
their own exact Analysis families, theorem sources, assumptions, and evidence.

<!-- zkc-profile-source:relations-recursive-grounding-semantics:end -->
