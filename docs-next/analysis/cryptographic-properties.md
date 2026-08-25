# Cryptographic property families

> **Document kind:** Target semantic specification
> **Document state:** Active non-normative target
> **Target status:** Stage 4A durable promotion
> **Provisional owner:** `analysis`
> **Authority:** This document specifies the selected target for `docs-next/`.
> It is non-normative until explicit consolidation and cutover. The current
> specifications under [`docs/`](../../docs/README.md) remain authoritative.
> This document states schemas and boundaries; it establishes no theorem,
> security property, implementation support, migration feasibility, or
> consumer assurance.

> **K1 transition notice — 2026-08-26:** Identity, value, algorithm, and
> evaluation notation below predates
> [Executable Semantic Foundations](../foundation/executable-foundations.md).
> K3 must bind each theorem-applicability input to exact K1 identities and the
> K2 Protocol/Fiat--Shamir model before any family here is integrated.

## 1. Scope and family architecture

This document defines the target Analysis shape for completeness, soundness,
knowledge, and zero-knowledge families. It also defines the Analysis-owned
Fiat--Shamir theorem-applicability seam.

Every family uses the category, identity, basis, qualification, negative, and
authority rules of the [Analysis semantic model](analysis-model.md). The
admitted Fresh and Fiat--Shamir Protocols, transcript construction, and
`CheckedFSConstruction` come from
[Fiat--Shamir and Core composition](../pir/fiat-shamir-and-composition.md).
Relation truth, when an experiment reads it, comes only from the
Relations-owned satisfaction operation described in
[Semantic relation families](semantic-relations.md#8-relations-owned-relationsatisfies).

Every operation below executes through the complete occurrence-local
`AnalysisCheckingInvocation`: exact authenticated request and family policy,
all typed admitted-subject/view and checked-result source bindings, the total
source-policy closure, separately supplied fresh source and checker
capabilities, and the exact named consumer and typed purpose. Signatures may
elide this envelope for readability; no operation may read an ambient value,
policy, binding, or authority.

The architecture is federated rather than one universal security predicate:

~~~text
family-owned exact experiment
  + family-owned conclusion and refutation schema
  + exact model, occurrences, resources, and hypotheses
  + one admitted semantic and validation basis
  -> exact qualified property judgment
~~~

Shared infrastructure supplies typed occurrence coordinates, experiment
components, quantitative sorts, hypothesis algebra, proof-lane contracts, and
replay discipline. It does not erase the irreducible distinctions among
families.

## 2. Exact experiment envelope

### 2.1 Family-selected coordinates

A cryptographic family profile selects every coordinate its experiment reads
from this typed envelope:

- admitted Protocol, Core, Interface, Plan, construction, composition, setup,
  SRS/CRS, commitment, and occurrence subjects;
- exact relation definition, instance, public assignment, private-witness
  occurrence reference, and Relations-owned satisfaction fact requirement when
  relation truth is read;
- security parameter, instance size, field, group, and algebraic regime;
- statement and auxiliary-input distribution;
- honest prover, malicious prover, verifier, adversary, observer, extractor,
  and simulator interfaces;
- classical or quantum state, initialization, advice, and uniformity;
- oracle topology, programming rights, access order, namespace, query and move
  limits, and response correlation;
- classical, ROM, ideal-permutation, QROM, CRS/SRS, or another exact model;
- randomness ownership, independence, sharing, derivation, and substitution;
- abort, retry, rejection, failure, conditioning, and termination semantics;
- exact time, expected-time, query, move, round, communication, and memory
  resources; and
- single, sequential, parallel, interleaved, concurrent, or multi-session
  scheduling.

When the semantic experiment itself names a Relations-owned private-witness
occurrence, its question and every later identity whose own preimage names that
local coordinate use the [confidential owner-local handle
lane](analysis-model.md#confidential-owner-local-handle-lane). When an otherwise
public experiment reads an owner-private satisfaction record only as concrete
proof support, its public question, goal, proposition, semantic basis, and
validation basis remain portable; taint begins at the support instantiation and
propagates only through later preimages that name its local handle. Every
actually affected family result has no public digest, is usable only by the
exact owner-authorized same-process consumer, and has no persistence or exact
cold replay.

This envelope is a vocabulary, not a universal struct. A family omits an
irrelevant coordinate rather than supplying `None` or a default. Every field
that changes experiment meaning has its schema and interpretation fixed by
`FamilySemanticProfileId`; its concrete selected value enters the model
instantiation or `AnalysisQuestionId` as the family contract specifies. A
proof-specific encoding or checker dependency belongs to the basis instead. A
live satisfaction capability never enters profile, model, question, or
proposition identity; it is supplied separately to the checking invocation
against the exact fact requirement and private occurrence coordinate.

### 2.2 Model and occurrence identity

`ModelInstantiationId` binds the exact admitted model, experiment regime, and
all model parameters. Labels such as `ROM`, `QROM`, `concurrent`, or
`adaptive` are not sufficient identities. The model closes the oracle,
state, scheduling, abort, termination, observation, and resource conventions
needed to interpret the property.

A static Protocol occurrence and a runtime invocation occurrence are
different subjects. An occurrence-sensitive question names the exact owner of
the occurrence graph and every map from Protocol events, rounds, statements,
challenges, transcript prefixes, or relation values into that graph. Stage 3
Protocol identity alone does not create a runtime-occurrence subject.

One experiment run, benchmark, or trace cannot be generalized to a family
property without an exact Evidence-derived rule whose sampling model and
uncertainty support that proposition. Likewise, a theorem over an abstract
model cannot establish a concrete Protocol property until subject, model,
statement, occurrence, and parameter correspondence are checked in the
required implication direction.

### 2.3 Exact hypothesis boundary

Hardness assumptions, unproved theorems, termination restrictions, extractor
requirements, oracle restrictions, losslessness, and assumed correspondence
propositions remain in the exact `AnalysisHypothesisContext`. Model
coordinates are not removable hypotheses. Checker correctness, proof-kernel
soundness, encoding adequacy, and runtime correctness are residual trust, not
logical premises.

Every inference canonically unions inherited hypotheses and may discharge a
hypothesis only through an exact checked family rule. A property record never
silently relabels an assumption as an established premise or as trust
metadata.

## 3. Family profiles

### 3.1 Completeness

The completeness family closes:

~~~text
exact admitted Protocol and occurrence subjects
exact relation and valid public/private pair operands
exact Relations-owned satisfaction fact requirement and private witness
  occurrence reference when the selected profile reads relation truth
honest prover and verifier algorithms or models
honest randomness and setup distribution
accepted or output event
failure, abort, retry, and termination semantics
exact probability or error conclusion
~~~

Completeness is separate from soundness. Its negative, when the basis is
complete, identifies an exact valid input/occurrence or positive failure mass
that violates the claimed completeness proposition. An unavailable witness,
failed honest-run search, or missing satisfaction authority is not that
negative.

### 3.2 Plain soundness

Plain soundness binds:

~~~text
false-language or invalid-instance event
malicious prover/adversary class
verifier, setup, oracle, and scheduling model
acceptance or output-language event
resource regime and exact soundness error
~~~

The definition of false language is an explicit model or relation proposition,
not the absence of a supplied witness. An affirmative soundness judgment is
conditional on its exact assumptions, adversary class, model, resource bound,
and error expression. It does not imply knowledge extraction.

### 3.3 Knowledge soundness

Knowledge soundness additionally closes:

- the exact relation and occurrence operands;
- extractor interface and access to adversary state, transcript, oracle, and
  rewinding or restoration operations;
- straight-line, rewinding, expected-time, or quantum extraction mode;
- accepting-run conditioning and adversary failure treatment;
- witness map and exact satisfaction requirement;
- extraction time, success, failure, and knowledge error; and
- the relation among adversary acceptance, extracted witness validity, and
  extractor failure.

Knowledge soundness is not plain soundness with an optional extractor field.
Different extractor access or conditioning yields a different family profile
or model. A candidate witness that fails Relations-owned satisfaction is not a
proof that no valid extractor exists.

### 3.4 Special soundness

Special soundness binds an exact accepting transcript-tree shape, the common
prefix and state relation, challenge-diversity coordinates, the extractor and
witness map, and information-theoretic or computational failure. The number,
distribution, independence, and namespace of challenges are semantic inputs.

A special-soundness result does not generically imply round-by-round knowledge,
state-restoration knowledge, or Fiat--Shamir soundness. Each implication needs
an exact theorem, model map, side conditions, and loss.

### 3.5 Round-by-round soundness and knowledge

Round-by-round soundness defines a family-owned doomed-state predicate over
exact partial-transcript and state occurrences, a challenge occurrence for
each transition, and an exact per-round error or transition relation.

Round-by-round knowledge separately defines a knowledge-state predicate,
round extractor, witness-flow relation, state exposure, and per-round
extraction errors. Similar round coordinates do not make the two predicates or
results interchangeable.

The state predicate, transcript prefix, challenge namespace, abort treatment,
and composition schedule are part of experiment meaning. A theorem using a
different notion needs checked directional adequacy; a name match is
insufficient.

### 3.6 State-restoration soundness and knowledge

State-restoration soundness closes a restoration game with:

- the doomed-state or false-language event;
- exact stored-prefix and mutable-state semantics;
- salt and challenge namespace;
- oracle programming, move, and query budgets;
- static or adaptive adversary behavior;
- restricted or full restoration access; and
- exact error, abort, and termination treatment.

State-restoration knowledge replaces or extends the win condition with an
exact extraction game, extractor access and mode, witness-flow and
satisfaction relation, restoration semantics, failure probability, and time
profile.

Restricted/full, static/adaptive, classical/quantum, and soundness/knowledge
variants are separate profiles. No weakening or strengthening relation is
implicit.

### 3.7 Zero knowledge

Zero knowledge binds two exact experiments:

~~~text
RealExperiment(
  Protocol, relation/statement/witness occurrence, honest prover,
  verifier or observer, setup, oracle, schedule, auxiliary input)

SimulatedExperiment(
  exact simulator interface and resources,
  simulated setup/transcript/oracle operations,
  same exact observer-facing coordinates)
~~~

The family declares the comparison notion and direction: perfect identity,
statistical distance, or computational indistinguishability. It also closes
auxiliary input, adaptivity, verifier class, oracle programming, abort and
failure mass, session composition, state sharing, and simulator runtime.

Honest-verifier ZK does not imply malicious-verifier ZK. Single-theorem does
not imply adaptive, multi-theorem, parallel, interleaved, or concurrent ZK.
ROM does not imply QROM. A simulator that works under one exact state or oracle
interface establishes nothing for another without a typed theorem.

A future family may be exactly representable while every evaluation basis is
`Unsupported`. Representability is not property truth or implementation
support.

## 4. Typed quantitative algebra

### 4.1 Exact sorts

The common substrate is a multi-sorted exact expression language. Its
representative sorts include:

~~~text
Probability
StatisticalDistance
ComputationalAdvantage
ExtractionFailure
KnowledgeError
ExtractionSuccess
QueryCount
MoveCount
RoundCount
RunningTime
ExpectedRunningTime
ByteCount
CommunicationCount
FieldSize
Degree
SecurityParameter
AsymptoticFunction
CostObservation
~~~

Family profiles admit only dimensionally meaningful operators. There is no
implicit conversion between probability, advantage, distance, time, count,
or asymptotic functions. A concrete value and an asymptotic function remain
different sorts until an explicit checked lift relates them.

### 4.2 Expressions and loss ledgers

The closed library may contain exact rational arithmetic, sums, products,
`1 - product(1 - epsilon_i)`, maxima, minima, powers, binomial coefficients,
substitution, reindexing, expectation, and explicit concrete-to-asymptotic
lifts. Every operator declares its input sorts, output sort, totality domain,
and side conditions.

Every derivation retains a quantitative-transform ledger containing:

- source expressions and portable proposition IDs or exact owner-local handles;
- exact substitutions and parameter maps;
- side-condition propositions and checked support;
- abort, failure, conditioning, and union/composition losses; and
- the exact output expression.

Unsupported symbolic forms are `Unsupported`; they are never approximated or
rounded silently. A changed bound changes `AnalysisGoalId` and
`AnalysisPropositionId` in the portable lane, or their exact local handles in a
private-occurrence-derived lane.

## 5. Cross-notion implications

No implication follows from family names. In particular:

- completeness and soundness are independent tracks;
- plain soundness does not imply knowledge soundness;
- standard soundness does not imply round-by-round or state-restoration
  soundness;
- special soundness does not generically imply round-by-round knowledge;
- knowledge in one extractor model does not imply knowledge in another;
- a ROM result does not imply its QROM analogue;
- a single-session result does not imply parallel or concurrent security; and
- structural equality, relation correspondence, or a valid Fiat--Shamir
  construction does not imply a cryptographic property.

Every conversion is a typed theorem or rule instance. Its semantic basis names
the exact source proposition schemas and polarities, target family and
proposition, model/subject/occurrence maps, side conditions, hypotheses, and
quantitative transformer. Its validation basis separately names how that rule
was checked.

## 6. Fiat--Shamir theorem applicability

### 6.1 Three separate contracts

Fiat--Shamir reasoning remains factored:

~~~text
CheckedFSConstruction
  // PIR-owned structural construction result from Stage 3

CheckedFSTheoremInstance<T>
  // Analysis-owned theorem/model applicability result

PropertyTransport<T, SourcePremiseSchemas, PTarget>
  // Analysis-owned derivation of one exact target property
~~~

The first result transports no cryptographic property. The second exposes
typed property ports but asserts no source property and derives no target
property. Only the third operation, specified in
[Transport, composition, and replay](transport-composition-and-replay.md),
combines exact source judgments with one exact port and target proposition.

If the durable operation name `FSCompile` is retained, it denotes only theorem
applicability. The names `FS-valid`, unqualified
`CheckedFSTheoremInstantiation`, and unqualified `FSCompileCapability` are not
aliases because they invite construction, validity, or preservation
inferences.

### 6.2 Applicability operation

~~~text
CheckFSTheoremApplicability<T>(
  admitted Fresh Protocol,
  admitted Fiat--Shamir Protocol,
  admitted transcript construction,
  affirmative CheckedFSConstruction,
  exact theorem schema T,
  exact established theorem capability
    or explicitly admitted assumed-theorem proposition,
  exact source and target semantic model instantiations,
  for every theorem, subject, model, transcript, codec, oracle, occurrence,
    and parameter correspondence:
      affirmative established correspondence capability
        or explicitly admitted assumed-correspondence proposition,
  global hypotheses and quantitative parameters)
  -> AnalysisAttemptOutcome<FSTheoremApplicability<T>>
~~~

The affirmative live capability is:

~~~text
EstablishedFSTheoremInstance<
  T, AssuranceClass, FamilyOperationPolicyId,
  ExactSourceOperationPolicyDependencyClosure,
  NamedConsumer, OperationPurpose,
  ExactJudgmentBinding,
  ExactCheckedResultAuthorityBinding<Analysis, FSTheoremApplicability<T>>>
~~~

This is a specialization of the common `EstablishedAnalysisJudgment` contract,
not a policy- or origin-erased capability. Its durable semantic record is
`CheckedFSTheoremInstance<T>` only in the portable untainted lane. If a theorem,
correspondence, or other concrete input is local and the instance preimage names
it, the instance and its result use local handles. The exact portable
instance identity binds:

~~~text
FSTheoremInstanceId = H(
  "zkc/fs-theorem-instance",
  exact Stage 3 Fresh, Fiat--Shamir, construction, and checked-map operands,
  exact theorem schema,
  source and target ModelInstantiationIds,
  every correspondence PropositionId and direction,
  parameter substitution,
  global residual HypothesisContextId,
  every assumed theorem or correspondence PropositionId,
  exact property-port schemas exposed by T)
~~~

The semantic basis and validation basis that establish the instance retain
their own identities. Every assumed theorem or correspondence proposition is
canonically unioned into the theorem-instance hypothesis context. It cannot
satisfy a premise requiring an established affirmative capability.

### 6.3 Correspondence completeness

Applicability checks every theorem-read coordinate, including when relevant:

- message and statement/session binding;
- transcript prefix and event/round occurrence maps;
- framing, codec, rate, capacity, salt, and domain separation;
- challenge derivation, decoding, bias, and namespace;
- source and target relation, witness, and accepted-output maps;
- oracle model, programming rights, query and move limits;
- adversary and extractor interfaces;
- adaptivity, auxiliary input, abort, retry, and failure behavior;
- termination and expected-time premises; and
- exact quantitative parameter substitution.

Semantic correspondence cannot hide in validation metadata. A correspondence
is an exact conditional Analysis proposition with its own question, goal,
hypotheses, direction, maps, loss, basis, and checked support. If a checked
one-way implication suffices, literal equality is unnecessary; the direction
is still mandatory.

No applicable theorem, unsupported ROM/QROM regime, missing view, or
incomplete correspondence yields `Unsupported` or `CannotAnswer`. It does not
make the admitted target malformed and does not establish a negative target
property. An assumed theorem lane is permitted only when the exact unresolved
theorem proposition remains in the result hypotheses.

### 6.4 Property transport ports

An affirmative theorem instance exposes zero or more attenuated live ports:

~~~text
PropertyTransportPort<T, SourcePremiseSchemas, TargetFamily> {
  exact theorem-instance portable ID or local handle according to its own
    semantic preimage,
  exact source theorem-instance ExactJudgmentBinding with per-coordinate
    portable IDs or local handles,
  exact source theorem-instance ExactCheckedResultAuthorityBinding,
  exact_source_assurance_class,
  exact_source_residual_trust_closure_id,
  exact_source_family_operation_policy_id,
  exact_source_operation_policy_dependency_closure,
  exact_source_named_consumer_and_typed_OperationPurpose,
  exact_tuple_of_source_family_proposition_schemas_and_polarities,
  target_family_and_semantic_regime,
  extra_hypothesis_and_side_condition_schemas,
  subject_model_occurrence_and_parameter_map_schemas,
  exact_quantitative_transformer
}
~~~

A different source-premise tuple, target family, target semantic regime, map,
side condition, or quantitative transformer requires a different port. The
port is live authority only for its exact theorem-instance proposition,
hypotheses, judgment record, basis qualification, assurance class, residual-
trust closure, source `FamilyOperationPolicyId`, complete transitive source-
operation-policy closure, exact named consumer, typed `OperationPurpose`,
complete `ExactCheckedResultAuthorityBinding` and its inert
`OwnerCapabilityRequirement`, and exact derivation/support/semantic/validation
binding. Attenuation preserves every one of those coordinates; the port cannot
be serialized or widened. Use under a target request additionally requires the
target policy and every source-owner policy to permit the exact transport
consumer and purpose.

The displayed mixed references follow the common per-coordinate identity rule.
Private support may make only the support, derivation, judgment, concrete port,
and result local while a public theorem-instance semantic ID, proposition,
semantic basis, or validation basis remains portable. If the theorem-instance
semantic preimage itself contains a local proposition, occurrence, theorem, or
map handle, its own coordinate is local as well. No backward taint is inferred
from support choice.

## 7. Direct target analysis

Fiat--Shamir transport is never mandatory. Once the target Protocol and every
question-specific operand are independently admitted, a target property may
be checked directly through any basis lane admitted by that property's family:

~~~text
admitted target Protocol
  + exact target property question and proposition
  + target-owned views and semantic model
  + direct/internal/external/certificate basis
  -> exact target property judgment
~~~

Direct analysis and transported analysis may establish the same
`AnalysisPropositionId` through different semantic bases, validation bases,
derivations, assurance classes, and residual trust. Proposition equality does
not collapse those qualifications. A consumer may require either basis shape
or accept both explicitly.

Disagreement among qualified bases is not resolved by overwriting one record.
It is an exact conflict requiring investigation of premises, model and subject
correspondence, theorem direction, checker contracts, and trust roots. The
common Analysis layer does not choose a preferred theorem or assurance lane
without an explicit relying policy.

## 8. Selected nonclaims

This specification does not establish:

- correctness of any property definition, theorem, reduction, extractor,
  simulator, correspondence, quantitative loss, checker, or proof system;
- truth of any hardness, termination, losslessness, model, or correspondence
  hypothesis;
- relation satisfaction from a relation definition, instance, witness-shaped
  value, or correspondence result alone;
- a property-negative result from failed proof search, solver `unknown`, an
  invalid certificate, a failed coupling, or missing theorem applicability;
- any property from `CheckedFSConstruction` or
  `CheckedFSTheoremInstance<T>` alone;
- transfer between soundness, knowledge, completeness, zero knowledge,
  classical, ROM, QROM, or concurrency regimes without an exact checked rule;
- persistence of a live property or theorem-instance capability; or
- implementation support, security assurance, endpoint feasibility, release
  readiness, or acceptance of residual trust by a consumer.
