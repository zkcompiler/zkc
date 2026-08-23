# Protocol semantic model

> **Document kind:** Target semantic specification
> **Document state:** Active non-normative target
> **Target status:** Stage 3.5 durable promotion
> **Provisional owner:** `pir`
> **Authority:** This document specifies the selected target for `docs-next/`.
> It is non-normative until explicit consolidation and cutover. The current
> specifications under [`docs/`](../../docs/README.md) remain authoritative.
> This document makes no implementation, compatibility, or migration claim.

## 1. Scope and architectural position

This document defines the complete v0 Protocol semantic subject: a finite
`InteractiveCore` plus exactly one interpretation of its public challenges.
It fixes the closed semantic vocabulary, occurrence and reference discipline,
admission predicates, operational trace meaning, identity algebra, and
authority topology.

~~~text
InteractiveCore + ChallengeInterpretation = Protocol

Protocol
  <-> one physically canonical MLIR PIR graph
  +-> separately identified ProtocolInterface
  +-> separately identified ProverPlan
  +-> purpose-specific immutable consumer views
~~~

Protocol meaning is language-independent. The unique physical v0 carrier is
the closed MLIR graph specified by [Canonical PIR](canonical-pir.md); this
semantic algebra is not a second interchange format. Interface and Plan are
separate dependent subjects specified by
[Protocol interfaces and prover plans](interfaces-and-plans.md). Relation,
Analysis, Compiler, and OIR owners receive only the narrow views defined here
and in the [Protocol IR architecture](../project/protocol-ir-architecture.md).

The words “exact,” “total,” and “canonical” are semantic requirements:

- every meaning-bearing choice is explicit and finite;
- every reference is typed and occurrence-exact;
- every map claimed total contains every and only member of its named domain;
- every sequence order is semantic unless a field is explicitly a set;
- unknown constructors, dependency kinds, regimes, or references fail closed;
  and
- IDs, bytes, signatures, provenance, and producer reports never substitute
  for authenticated and admitted process-local authority.

## 2. Semantic universes and references

### 2.1 Subject boundary

The Protocol family contains exactly these semantic roots:

~~~text
InteractiveCore
TranscriptConstruction
Protocol
~~~

The following are dependent satellite subjects, not fields of `Protocol`:

~~~text
ProtocolInterface
ProverPlan
RelationDefinitionRef
RelationInterface
RelationInstance
RelationBinding
RelationArtifactProfile
RelationAdapterContract
RelationArtifactObservation
CoreCompositionSpec
~~~

Checked relations such as `PlanRealizes`, relation correspondence,
Fresh-to-Fiat--Shamir construction, and Core composition have their own
process-local result capabilities. A relation result never becomes a field of
Protocol merely because it mentions a `ProtocolId`.

Private witness assignments are occurrence-local confidential values. They
are not mandatory globally content-addressed subjects and their bytes do not
enter a Protocol identity.

### 2.2 Typed regimes and closed algorithms

`ProtocolSemanticRegime` fixes the meaning needed to encode, authenticate, and
admit `InteractiveCore`, `TranscriptConstruction`, and `Protocol`. A semantic
regime is not an MLIR bytecode version, package version, checker build, policy,
or deployment profile. A meaning change under unchanged fields requires a new
regime and therefore a new identity.

Every codec, encoder, decoder, framing rule, sampler, or pure function stored
in semantic data is a closed value:

~~~text
CanonicalAlgorithmSpec<K> =
    ClosedFiniteTerm(kind = K, typed syntax, declared totality evidence)
  | ContentAddressedContractRef(
      kind = K,
      contract_regime_id,
      regime_qualified_content_id,
      exact ABI,
      direct_dependency_ids)
~~~

A referenced contract is admitted only with its exact authenticated preimage
and dependency closure. Live executable implementations and checker
capabilities are operation inputs, never semantic fields or identity
preimages.

`TranscriptConstruction` uses the exact `ProtocolSemanticRegime`; it does not
introduce an independent semantic regime. Reusable transcript algorithms are
typed dependency IDs inside that construction.

### 2.3 Local, Core, and Protocol-scoped references

Before a root identity exists, candidates use typed positional references:

~~~text
LocalRef(kind, canonical_ordinal)
~~~

After authentication, an intrinsic Core occurrence has the durable form:

~~~text
CoreRef<K> = (CoreId, K, canonical_ordinal)
~~~

`K` is one of `dependency`, `role`, `port`, `value`, `object`, `randomness`,
`event`, `challenge`, `claim`, `reduction`, `check`, `failure`, `terminal`,
`endpoint_obligation`, `prover_obligation`, or
`prover_obligation_failure`. Kinds are never interchangeable when ordinals
coincide.

Facts whose meaning depends on Fresh versus Fiat--Shamir interpretation use:

~~~text
ProtocolScopedRef<K> = (ProtocolId, CoreRef<K>)
~~~

Fresh and FS Protocols may share a `CoreRef` but never a
`ProtocolScopedRef`. Runtime occurrences additionally need their exact
invocation or trace identity; this specification does not turn a runtime event
into a durable semantic subject.

Composition uses local child slots before its spec identity exists and
`ChildOccurrenceRef = (CoreCompositionSpecId, child_slot)` afterward. Reusing
one `CoreId` in two slots creates two occurrences, not two Core identities.
PIR owns the exact composition transaction specified by
[Fiat--Shamir and Core composition](fiat-shamir-and-composition.md). The
[transition and bridge architecture](../project/transition-and-bridge-architecture.md)
owns the shared construction, authority, outcome, persistence, and replay
constraints that transaction follows.

### 2.4 Canonical semantic encoding

For regime `R`, `CanonicalEncode_R(T)` is injective and structural:

- sums carry domain-separated variant tags;
- products encode fields in declared order;
- sequences carry lengths and ordered elements;
- sets and maps use canonical encoded-key order and reject duplicate keys;
- optional values carry explicit absent or present tags;
- references include their subject family and typed key; and
- scalar domains use their regime-owned unique mathematical encoding.

Printer spelling, MLIR bytecode, host layout, map iteration order, source
position, pointers, and process identity never enter this encoding. Satellite
subjects may have lossless transport profiles, but transport cannot add
semantic fields or create a second representation of Protocol.

## 3. `InteractiveCore`

### 3.1 Complete root

~~~text
InteractiveCore = {
  dependencies: CanonicalMap<DependencyRef, DependencyDecl>,
  roles:        CanonicalSeq<RoleDecl>,
  ports:        CanonicalSeq<PortDecl>,
  values:       CanonicalSeq<ValueNode>,
  objects:      CanonicalSeq<ObjectDecl>,
  randomness:   CanonicalSeq<RandomnessDecl>,
  challenges:   CanonicalSeq<ChallengeDecl>,
  events:       CanonicalSeq<EventDecl>,
  causal_edges: CanonicalSet<(EventRef, EventRef)>,
  schedule:     Permutation<EventRef>,
  claims:       CanonicalSeq<ClaimDecl>,
  reductions:   CanonicalSeq<ReductionDecl>,
  checks:       CanonicalSeq<CheckDecl>,
  failures:     CanonicalSeq<FailureDecl>,
  terminals:    CanonicalSeq<TerminalDecl>,
  endpoint_obligations: CanonicalSeq<EndpointObligation>,
  prover_obligations:   CanonicalSeq<ProverObligation>,
  prover_obligation_failures:
    CanonicalSeq<ProverObligationFailureDecl>
}
~~~

Every canonical sequence order is semantic. Authoring order is not reused as
an implicit order.

### 3.2 Dependency closure

The v0 dependency-kind sum is closed:

~~~text
DependencyKind =
    ValueDomainContract
  | PureFunctionContract
  | ProtocolObjectContract
  | DistributionContract
  | JointDistributionContract
  | WireCodecContract
  | ApplicationChannelContract
  | CheckContract
  | ClaimContract
  | ReductionContract
  | EndpointObligationContract
  | ProverObligationContract
~~~

Each `DependencyDecl` contains its kind, semantic regime, content identity,
direct dependency identities, and exact Core-facing ABI. The direct manifest
is identity-bearing. Admission consumes its authenticated least reachable
closure and rejects missing, extra, wrong-kind, wrong-regime, or wrong-ABI
preimages. Core never performs ambient registry lookup. Relation, artifact,
source, theorem, and deployment references are not Core dependency kinds.

Adding a dependency kind requires a new Protocol semantic regime.

### 3.3 Roles, knowledge, and ports

~~~text
RoleClass = Prover | Verifier | PublicEnvironment

RoleDecl = (canonical role ordinal, RoleClass)
~~~

An admitted Core has exactly one Prover, exactly one Verifier, and at most one
PublicEnvironment. The environment is required if any public randomness,
port, or event refers to it. It supplies explicit public inputs, context, and
abstract public coins; it is not an ambient oracle.

~~~text
AllRoles =
  {the unique Prover, the unique Verifier}
  union {the unique PublicEnvironment when present}
~~~

Knowledge evolves only through the closed rules below:

1. public input occurrences and constants are initially known to all roles;
   private input occurrences are known only to their exact owner;
2. private randomness and prover-obligation outputs are initially known only
   to Prover after successful pre-action preparation;
3. check results are initially known only to Verifier; check-false and
   explicit-abort facts are initially Verifier-known, while challenge-sampling
   failure facts are also known to the resolving PublicEnvironment;
4. pure results are known exactly by roles that know every operand and the
   authenticated contract;
5. an occurring `ObservePublicValue` publishes its input to all roles;
6. an occurring `Message` transfers its payload from sender to receiver; and
7. successful public challenges and terminal public outputs become known to
   all roles.

Protected transcript, check, artifact, claim, or failure observation is not an
implicit knowledge transfer. `EmitArtifact` does not publish its input.

~~~text
PortDecl = {
  role: RoleRef,
  direction: Input | Output,
  visibility: Public | PrivateToRole,
  value_domain: ValueDomainContractRef,
  multiplicity: ExactlyOne | FixedCount(n),
  semantic_purpose: Statement | Witness | Context | ProtocolValue,
  binding: InputSource | OutputValues(CanonicalSeq<ValueRef>)
}

PortOccurrenceRef = (PortRef, occurrence_ordinal)
InputPortOccurrenceRef =
  PortOccurrenceRef restricted to direction Input
~~~

`FixedCount(n)` requires positive canonical `n`; occurrence ordinals are the
exact range. An input has `InputSource`. An output names exactly one
same-domain value per occurrence in ordinal order. An output port is only a
declarative grouping: it creates no value, effect occurrence, exposure,
availability, or knowledge transfer. External names, containers, and actual
exposure belong to Interface and OIR. `PortValue` can reference input
occurrences only.

### 3.4 Values, guards, availability, and objects

`ValueNode` is a closed, topologically ordered pure DAG:

~~~text
ValueNode =
    PortValue(PortOccurrenceRef)
  | CanonicalConstant(ValueDomainContractRef, value)
  | PrivateRandomnessValue(RandomnessRef)
  | ChallengeValue(ChallengeRef)
  | ProverObligationOutput(ProverObligationRef, output_ordinal)
  | CheckResult(CheckRef)
  | FailureStatusValue(FailureRef)
  | FailureOccurred(FailureRef)
  | Tuple(CanonicalSeq<ValueRef>)
  | Project(ValueRef, field_ordinal)
  | InjectVariant(SumValueDomainContractRef, variant_ordinal, ValueRef)
  | Apply(PureFunctionContractRef, CanonicalSeq<ValueRef>)
  | GuardDecision(CanonicalGuardFormula)
  | GuardedMerge(
      NonEmptyCanonicalSeq<(GuardValueRef, ValueRef)>,
      ExhaustiveOneHot)
~~~

There is no generic event-output origin. A future value-producing effect needs
a named constructor and a new Protocol semantic regime.

Path conditions have one finite canonical representation:

~~~text
GuardAtom =
    BooleanAtom(BooleanValueRef)
  | FiniteValueEquals(ValueRef, CanonicalSemanticValue)

CanonicalGuardFormula =
  CanonicalReducedOrderedDecisionDiagram<GuardAtom>

GuardValueRef =
  ValueRef whose origin is GuardDecision(CanonicalGuardFormula)
~~~

`BooleanAtom` references an earlier Boolean value that is not another
`GuardDecision`. Finite equality requires a finite declared domain and a
canonical same-domain value. The regime fixes atom order and one complete
reduced ordered decision-diagram algorithm. Authentication checks physical
normal form directly; implication reduces `A AND NOT B` to false. No SMT
solver, callback, proof search, or unrecorded theory participates. Arbitrary
Boolean `Apply` nodes may be atoms, but distinct atoms are propositionally
independent.

Existence and role knowledge are boundary-indexed derived facts:

~~~text
SemanticBoundary =
    Initial
  | PreAttempt(EventRef)
  | PostPreparation(EventRef)
  | PostResolution(EventRef)

ClaimClosurePoint =
    InitialClosure
  | PostOccurrenceClosure(EventRef)

EmbedClaimClosurePoint(InitialClosure) = Initial
EmbedClaimClosurePoint(PostOccurrenceClosure(e)) = PostResolution(e)

DerivedAvailabilityAtom =
    ValueGuardAtom(GuardAtom)
  | ProverPreparationSucceededAtom(ProverObligationRef)
  | RandomnessProducedAtom(RandomnessRef)

DerivedAvailabilityFormula =
  CanonicalReducedOrderedDecisionDiagram<DerivedAvailabilityAtom>

ExistsAt(ValueOrObjectRef, SemanticBoundary)
  -> DerivedAvailabilityFormula

KnowsAt(RoleRef, ValueOrObjectRef, SemanticBoundary)
  -> DerivedAvailabilityFormula

AvailableAt(role, ref, boundary) =
  ExistsAt(ref, boundary) AND KnowsAt(role, ref, boundary)
~~~

The two operational atoms are derived occurrence outcomes and cannot appear in
Protocol guards. One total fold over the value/object DAG and schedule
computes availability. It introduces inputs and constants initially; closes
pure values and objects when operands exist; introduces private samples and
prover outputs only after successful preparation; introduces challenge,
check, and failure origins only at their exact resolution boundaries; and then
applies only the knowledge transfers listed in Section 3.3.

For a guarded merge:

~~~text
MergeReady(role, boundary) =
  AND_i AvailableAt(role, g_i, boundary)

MergeSelected(role, boundary) =
  OR_i (ValueOf(g_i) AND AvailableAt(role, v_i, boundary))

AvailableAt(role, merge, boundary) =
  MergeReady(role, boundary) AND MergeSelected(role, boundary)

ExistsAt(merge, boundary) =
  (AND_i ExistsAt(g_i, boundary))
  AND (OR_i (ValueOf(g_i) AND ExistsAt(v_i, boundary)))
~~~

Admission proves pairwise-exclusive branch guards, one common branch value
domain, and availability of the selected branch on every use path. A merge may
be partial outside those paths; it has no caller-selected `when` field.
`InjectVariant` is the structural injection into one closed sum domain and
must use the exact payload domain for its variant.

Every use has an exact phase. Guards are known at `PreAttempt`; prover-basis
inputs are available there; action inputs are available to their actor at
`PostPreparation`; terminal payload and check inputs use their exact
action/resolution boundary; reduction side inputs use existence at the
embedded claim-closure point. Admission proves the use condition implies the
corresponding derived availability formula.

~~~text
ObjectObservationClass = Transcript | Wire | Check | Artifact | Claim

ObjectDecl = {
  contract: ProtocolObjectContractRef,
  constructor_inputs: CanonicalSeq<ValueOrObjectRef>,
  owner_role: RoleRef,
  visibility: Public | PrivateToRole,
  protected_observations: CanonicalSet<ObjectObservationClass>
}
~~~

An object contract fixes its domain, constructor inputs, total deterministic
construction relation, equality, and encoding. It cannot read ambient
registries, transcript state, clocks, randomness, files, policy, or live
handles. Visibility constrains transfer but does not publish an object.
`protected_observations` is recomputed as the exact union of actual transcript,
wire, check, artifact, and claim uses. Private objects cannot be observed by a
role outside their owner.

### 3.5 Randomness and correlation

~~~text
RandomnessDecl = {
  owner: RoleRef,
  purpose: PublicChallenge(ChallengeRef)
         | PrivateProverSample(ProverObligationRef),
  distribution: DistributionContractRef,
  correlation: IndependentFresh
             | JointMember(JointDistributionContractRef,
                           CoreJointRandomnessGroupRef,
                           index),
  available_before: EventRef,
  on_sampling_failure: VerifierVisibleFailure(FailureRef)
                     | ProverCannotProduce(ProverObligationFailureRef)
}

CoreJointRandomnessGroupRef =
  dense canonical ordinal allocated by the least RandomnessRef in each group
~~~

Public-challenge randomness is owned by the unique PublicEnvironment; private
sampling is owned by Prover and names the exact obligation that consumes it.
For a public challenge, `available_before` is its linked `FreshChallenge`
event and failure maps to its linked verifier-visible failure. For private
randomness, it is the obligation source event and failure maps to the exact
`PrivateSamplingFailed` cause.

Each `IndependentFresh` declaration is one distinct sample. A distribution
contract fixes value domain, probability law, support, and the closed
one-attempt result:

~~~text
SingleSamplingStep() =
    Produced(value in exact declared support)
  | SamplingFailed
~~~

The failure variant is present only when the contract permits failure.

A joint contract fixes member domains, joint law, marginals, and ordered
conditional steps:

~~~text
JointSamplingStep(i, prior successful components) =
    Produced(component_i)
  | SamplingFailedAt(i)
~~~

One group has one owner, one purpose class, dense collision-free indices, a
single contract, exact marginals, schedule-ordered exposure, and one
noncircular base guard. The first failed member closes that group execution.
For public members, later member guards additionally exclude every earlier
failure; for private members, an earlier failure already ends the Core as
`ProverDidNotProduce`. Consumers require successful production of the exact
member. Public and private randomness never share a group.

Replay witnesses validate one closed transition; they do not prove that an
external sampler followed the declared law. Private randomness remains an
abstract prover obligation under both Fresh and FS interpretations. A Plan may
select an implementation but cannot replace its distribution or correlation.

Every public challenge and public-randomness declaration are in a one-to-one
backlink. `public_coin_index` is the challenge's rank among scheduled
`FreshChallenge` events; correlation is defined only by the randomness
declaration, never by this index.

### 3.6 Seven typed effect occurrences

The v0 effect vocabulary has exactly seven event kinds in one common envelope:

~~~text
EventKind =
    ObservePublicValue(value)
  | Message(from, to, channel, payload, WireCodecContractRef)
  | FreshChallenge(ChallengeRef)
  | InvokeCheck(CheckRef)
  | RaiseFailure(FailureRef)
  | EmitArtifact(object_or_value)
  | ReachTerminal(TerminalRef)

EventDecl = {
  kind: EventKind,
  actor: RoleRef,
  inputs: CanonicalSeq<ValueOrObjectRef>,
  protected_observations: CanonicalSet<EventObservationClass>,
  activation_guard: GuardValueRef,
  obligation_basis: EventObligationBasis
}

EventObligationBasis = {
  endpoint_contracts: EventEndpointContractBasis,
  prover_construction: Optional<ProverConstructionBasis>
}

EventEndpointContractBasis =
    ObservePublicValueContracts(
      observe: EndpointObligationContractRef)
  | MessageContracts(
      send: EndpointObligationContractRef,
      receive: EndpointObligationContractRef)
  | FreshChallengeContracts(
      resolve: EndpointObligationContractRef)
  | InvokeCheckContracts(
      invoke: EndpointObligationContractRef)
  | RaiseFailureContracts(
      signal: EndpointObligationContractRef)
  | EmitArtifactContracts(
      emit: EndpointObligationContractRef)
  | ReachTerminalContracts(
      reach: EndpointObligationContractRef)

ProverConstructionBasis = {
  contract: ProverObligationContractRef,
  inputs: CanonicalSeq<ValueOrObjectRef>,
  output_domains: NonEmptyCanonicalSeq<ValueDomainContractRef>,
  private_randomness: CanonicalSeq<RandomnessRef>
}
~~~

The envelope fields are constrained by exact per-kind equations:

| Kind | `inputs` | Protected observations | Actor |
|---|---|---|---|
| `ObservePublicValue(v)` | `[v]` | `{PublicValue}` | declared observer |
| `Message(..., payload, ...)` | `[payload]` | `{Wire}` or `{Wire, Transcript}` | exact sender |
| `FreshChallenge(c)` | `[]` | `{Transcript, PublicValue}` | PublicEnvironment |
| `InvokeCheck(k)` | `k.values` | `{Check}` | Verifier |
| `RaiseFailure(f)` | `[]` | `{Failure}` | Verifier |
| `EmitArtifact(x)` | `[x]` | `{Artifact}` | declared emitter |
| `ReachTerminal(t)` | `t.public_outputs` | `{Terminal}` | Verifier |

Missing, extra, reordered, or kind-incompatible inputs and observations reject.
The message observation choice is identity-bearing. Claims use their own
protected occurrence rules.

~~~text
MessageChannel =
    Proof
  | PublicVerifierMessage
  | ApplicationChannel(ApplicationChannelContractRef)
~~~

Proof travels Prover to Verifier; public verifier messages travel Verifier to
Prover. An application-channel dependency fixes exact roles, transcript
policy, payload domain, and endpoint-contract families. Direction is never
inferred from schedule position.

The endpoint-basis variant must match the event kind exactly. An optional
`ProverConstructionBasis` is legal only on a Prover-acted Observe, Message, or
Emit event. Its outputs are exactly the `ProverObligationOutput` nodes for
that obligation, in ordinal and domain order, and every listed private sample
points back to the same obligation.

An occurring Prover event has two phases. It resolves its guard, samples the
declared private randomness in order, and binds all obligation outputs; only
then does it check kind inputs and perform the action. Same-event outputs are
legal only at this successful `PostPreparation`. The first failed sample or
binding condition selects one exact `ProverDidNotProduce` cause and suppresses
the action.

The Core is finite and acyclic. `causal_edges` is acyclic; `schedule` is its
total extension. Guards read only earlier available atoms. Execution scans
that schedule, skips inactive occurrences, and stops at the first terminal or
prover nonproduction. The final scheduled occurrence is a canonical-true
fallback terminal.

~~~text
EventAttempted(e) =
  activation_guard(e) AND ExecutionStillLiveBefore(e)

ExecutionStillLiveBefore(e) =
  no earlier scheduled active event has selected a terminal
  AND no earlier attempted prover obligation has selected
      ProverDidNotProduce

EventActionOccurs(e) =
  EventAttempted(e) AND ProverPreparationSucceeded(e)

ProverPreparationSucceeded(e) =
  true when e has no ProverConstructionBasis
  OR successful binding of e's exact ProverConstructionBasis

EventActionOccurrenceRef = EventActionOccurrence(EventRef)
~~~

Terminal selection includes either an earlier action-occurring
`ReachTerminal` or an earlier resolved failure with a `Terminate` effect.
Successful basis binding means every declared private-randomness attempt and
every required output binding completed under the exact transaction and
precedence rules in Section 3.11. A failed preparation selects that
obligation's one exact `ProverDidNotProduce` cause and the event action does
not occur.

Challenge resolution occurs on attempt. Success publishes the challenge;
failure applies its exact linked failure effect and cannot suppress the
transition that caused it. Under FS, this occurrence executes the exact
`DeriveChallenge` transcript action, including its state update on a failed
derivation. Other event inputs, endpoint actions, and protected observations
occur exactly when `EventActionOccurs`. `RaiseFailure` is the only
explicit-abort source. There are no loops, recursion, dynamic event allocation,
or unbounded message families.

~~~text
EventObservationClass =
    Transcript | Wire | PublicValue | Check | Artifact | Failure | Terminal

ProtectedObservationClass = EventObservationClass | Claim
~~~

Unknown observation classes fail closed.

### 3.7 Challenges

~~~text
ChallengeDecl = {
  output: ValueRef,
  randomness: RandomnessRef,
  public_coin_index: ordinal,
  rejection_or_abort: FailureRef,
  transcript_event_prefix_template:
    CanonicalSeq<EventActionOccurrenceRef>
}
~~~

Each challenge owns exactly one `ChallengeValue`, public randomness
declaration, scheduled `FreshChallenge` event, failure, and public-coin rank.
The prefix template is every prior potentially action-occurring
transcript-participating event in total schedule order, not a selected causal
subset. At runtime it becomes the active ordered subsequence. The template is
Core semantics and does not depend on a particular FS construction.

### 3.8 Claims, reductions, and checks

~~~text
ClaimDecl = {
  contract: ClaimContractRef,
  parameters: CanonicalSeq<ValueOrObjectRef>,
  producer: InputPortOccurrenceRef | EventRef | ReductionRef,
  disposition: Linear | Persistent
}

ReductionDecl = {
  contract: ReductionContractRef,
  inputs: CanonicalSeq<ClaimRef>,
  outputs: CanonicalSeq<ClaimRef>,
  side_inputs: CanonicalSeq<ValueOrObjectRef>
}

CheckDecl = {
  contract: CheckContractRef,
  values: CanonicalSeq<ValueOrObjectRef>,
  claims: CanonicalSeq<ClaimRef>,
  on_false: FailureRef,
  invocation_event: EventRef
}
~~~

Claims are actorless typed resources. Their parameters and reduction side
inputs require semantic existence but do not transfer role knowledge. A value
that an `InvokeCheck` must inspect also appears in `CheckDecl.values` and must
be available to Verifier.

Their only operational occurrences are derived from the event schedule:

~~~text
ClaimConsumerOccurrenceRef =
    ReductionClaimInput(ReductionRef, input_ordinal)
  | CheckClaimInput(CheckRef, input_ordinal)

ClaimProduced(c) =
    Initially
      if c.producer is an input occurrence and every parameter exists
  | AfterEvent(e)
      if c.producer = e, EventActionOccurs(e), execution remains live,
      and every parameter exists after resolution
  | AtReduction(r)
      if c.producer = r and ReductionFires(r)

ReductionEnabled(r, closure_point) =
  r has not fired
  AND every input claim is live
  AND every side input and output-claim parameter exists at the embedded
      claim-closure boundary

ReductionFires(r) =
  r is the least canonical ReductionRef enabled at the current closure step
~~~

Claim execution is a deterministic derived closure, not a second free
schedule. Initial input claims are created first. After each event that leaves
execution live, action-dependent claims are created and reductions saturate by
repeatedly firing the least enabled `ReductionRef`. Each reduction fires at
most once, atomically consumes linear inputs, retains persistent inputs, and
creates outputs in canonical order. No post-terminal saturation occurs.

An occurring check consumes its live linear claim inputs before resolving its
Boolean result and failure effect. Every linear claim has exactly one
syntactic consumer and must reach it before every terminal reachable from its
production path; no terminal state may retain a live linear claim. Persistent
claims may have finitely many consumers. Admission recomputes production,
guarded liveness, use, contract routing, reduction order, and terminal closure.

The occurrence transaction first resolves the event guard and occurrence-total
Booleans, then consumes check claims when the action occurs, resolves the
action and failure effect, and commits any selected terminal immediately. Only
if execution remains live does it create `AfterEvent` claims and run the next
saturation. Inactive events create no event-produced claim, but their resolved
false facts can enable a reduction. Event-produced claims cannot be consumed
by the same event.

A claim occurrence is a protected `Claim` observation, not proof of claim
truth, relation satisfaction, or any security property.

### 3.9 Failures and terminals

~~~text
FailureSourceRef =
    CheckFalse(CheckRef, InvokeCheckEventRef)
  | ChallengeSampling(ChallengeRef, FreshChallengeEventRef, RandomnessRef)
  | ExplicitAbort(RaiseFailureEventRef)

FailureClass =
    MalformedProtocolInput
  | CheckRejected
  | ChallengeSamplingFailed
  | ExplicitProtocolAbort

FailureDecl = {
  source: FailureSourceRef,
  class: FailureClass,
  effect: Terminate(TerminalRef) | ContinueWithStatus(ValueRef),
  observations: CanonicalSet<Failure | Terminal>
}

FailureStatusToken = {
  failure: FailureRef,
  class: FailureClass
}

TerminalResult = Accept | Reject | Abort

TerminatingResultForFailureClass = {
  MalformedProtocolInput -> Reject,
  CheckRejected -> Reject,
  ChallengeSamplingFailed -> Abort,
  ExplicitProtocolAbort -> Abort
}

TerminalDecl = {
  result: TerminalResult,
  public_outputs: CanonicalSeq<ValueRef>
}

TerminalSelectionOccurrence =
    ReachTerminalSelection(EventRef, TerminalRef)
  | TerminatingFailureSelection(FailureRef, TerminalRef)

TerminalPayload(selection) =
  TerminalDecl(selection.terminal).public_outputs
~~~

The terminating result is fixed by failure class:

| Failure class | Result |
|---|---|
| `MalformedProtocolInput` | `Reject` |
| `CheckRejected` | `Reject` |
| `ChallengeSamplingFailed` | `Abort` |
| `ExplicitProtocolAbort` | `Abort` |

Each failure has one exact source and every source names one exact failure.
Check-false failures have only the first two classes; challenge failure has
`ChallengeSamplingFailed`; explicit abort has `ExplicitProtocolAbort` and must
terminate. A continuing failure exposes only its fixed occurrence-local
`FailureStatusToken` and observes `{Failure}`. A terminating failure observes
exactly `{Failure, Terminal}` and cannot select `Accept` directly. A later
explicit compound decision may recover after a continuing failure.

`FailureOccurred(f)` is a total Boolean after the source resolves, including
an inactive source. `FailureStatusValue(f)` exists only on the true continuing
branch. Wire visibility requires an explicit later `Message`; no failure has
an implicit wire payload.

Every terminal selection must make its full ordered public-output tuple
available and known to Verifier on that exact path. A `ReachTerminal` carries
the tuple as its inputs. A terminating failure may use the just-resolved check
or failure fact, but not an unproduced challenge, a continuing-only status,
later event, or inactive branch. Selection publishes the complete tuple to all
roles.

External container decoding failures and pre-Protocol refusal are
Interface-owned, not members of this failure sum.

### 3.10 Endpoint and prover obligations

~~~text
EndpointObligation = {
  owner_role: RoleRef,
  source_event: EventRef,
  contract: EndpointObligationContractRef,
  inputs: CanonicalSeq<ValueOrObjectRef>,
  action: Send | Receive | ObservePublicValue | EmitArtifact
        | ResolvePublicChallenge | InvokeVerifierCheck | SignalFailure
        | ReachTerminal,
  failure_surface: CanonicalSet<FailureRef>
}

ProverObligation = {
  source_event: EventRef,
  contract: ProverObligationContractRef,
  inputs: CanonicalSeq<ValueOrObjectRef>,
  output_domains: CanonicalSeq<ValueDomainContractRef>,
  private_randomness: CanonicalSeq<RandomnessRef>,
  failure_map:
    TotalMap<ProverObligationFailureCause, ProverObligationFailureRef>
}

ProverObligationFailureCause =
    MissingOutput(output_ordinal)
  | DuplicateOutput(output_ordinal)
  | EarlyOutput(output_ordinal)
  | UnexpectedOutput(output_ordinal)
  | PrivateSamplingFailed(RandomnessRef)

ProverObligationFailureDecl = {
  obligation: ProverObligationRef,
  cause: ProverObligationFailureCause
}
~~~

Endpoint obligations are recomputed exactly:

~~~text
ObservePublicValue:
  one (actor, ObservePublicValue, {}, observe contract)

Message:
  one (from, Send, {}, send contract)
  one (to, Receive, {}, receive contract)

FreshChallenge:
  one (PublicEnvironment, ResolvePublicChallenge,
       {linked sampling failure}, resolve contract)

InvokeCheck:
  one (Verifier, InvokeVerifierCheck,
       {check.on_false}, invoke contract)

RaiseFailure:
  one (Verifier, SignalFailure, {that failure}, signal contract)

EmitArtifact:
  one (actor, EmitArtifact, {}, emit contract)

ReachTerminal:
  one (Verifier, ReachTerminal, {}, reach contract)
~~~

The tuple order is `(owner_role, action, failure_surface, contract)`; each row
also carries the current event as `source_event` and the event's exact
recomputed input sequence. No other endpoint obligation is derived. If and
only if a Prover construction basis is present, one prover obligation is
derived with its exact contract, inputs, output domains, and randomness. Its
failure map is the total product of four binding causes per output ordinal and
one private-sampling cause per randomness member. Backlinks and the explicit
failure declaration family must equal this recomputation.

Endpoint obligations originate no values. Prover outputs exist only through
`ProverObligationOutput`. Prover nonproduction is neither a verifier-visible
failure nor a terminal.

### 3.11 Invocation grammar and execution

~~~text
PublicInputPortOccurrenceRef =
  InputPortOccurrenceRef restricted to Public

PrivateInputPortOccurrenceRef =
  InputPortOccurrenceRef restricted to PrivateToRole

CoreInvocationInputs = {
  public_inputs:
    TotalMap<PublicInputPortOccurrenceRef, CanonicalSemanticValue>,
  private_inputs:
    TotalMap<PrivateInputPortOccurrenceRef, RoleSecretInputValue>
}

RoleSecretInputValue = {
  owner: RoleRef,
  domain: ValueDomainContractRef,
  value: CanonicalSemanticValue
}

ProverBindingBoundary = BeforeFirstEvent | PreAction(EventRef)

TypedProverOutputValue = {
  domain: ValueDomainContractRef,
  value: CanonicalSemanticValue
}

ProverBindingRecord = {
  boundary: ProverBindingBoundary,
  obligation: ProverObligationRef,
  output_ordinal: CanonicalOrdinal,
  output: TypedProverOutputValue
}

ProverTrace = CanonicalSeq<ProverBindingRecord>

TypedRandomnessValue = {
  domain: ValueDomainContractRef,
  value: CanonicalSemanticValue
}

RandomnessAttemptOutcome =
    Produced(TypedRandomnessValue)
  | IndependentSamplingFailed
  | JointSamplingFailedAt(CanonicalOrdinal)

RandomnessAttemptRecord = {
  randomness: RandomnessRef,
  source_event: EventRef,
  outcome: RandomnessAttemptOutcome
}

RandomnessReplay = CanonicalSeq<RandomnessAttemptRecord>
~~~

Input maps cover every and only matching input-port occurrence with exact
domains and private owners. Traces are nondecreasing by boundary rank and
randomness records by the unique potential-attempt order. Unknown references,
wrong domains, noncanonical order, illegal failure tags, missing records, and
extra records are malformed invocation inputs and mint no Core outcome.

Replay outcomes must satisfy the exact authenticated single or joint sampling
transition, not merely domain membership. Fresh public challenges consume
replay records; FS challenges are derived deterministically. Private Core
randomness consumes replay records in both interpretations.

At an attempted Prover obligation, binding causes have this exact precedence:

1. the first pre-source record selects `EarlyOutput`;
2. the first record at an inactive source selects `UnexpectedOutput`;
3. the first repeated ordinal selects `DuplicateOutput`;
4. the first failed private sample selects `PrivateSamplingFailed`;
5. the least missing output ordinal selects `MissingOutput`; and
6. otherwise all outputs bind in ordinal order and the action may occur.

A post-source record selects `UnexpectedOutput` when reached. The first cause
ends execution as one `ProverDidNotProduce`; residual records cannot replace
that result, but make Protocol acceptance false.

~~~text
CoreState = {
  schedule_cursor,
  canonical values and objects,
  per-role knowledge,
  live claim resources,
  claim production/consumption occurrence sequence,
  active transcript occurrence sequence,
  wire occurrence sequence,
  check results,
  resolved failure booleans and available status tokens,
  observed artifacts,
  optional terminal
}

CoreExecutionOutcome =
    Terminal(TerminalRef, final_state)
  | ProverDidNotProduce(ProverObligationFailureRef, partial_state)

CoreExecutionRecord = {
  outcome: CoreExecutionOutcome,
  consumed_prover_record_count: CanonicalOrdinal
}

ExactProtocolExecutionCapabilities = {
  core_dependencies:
    ExactMap<DependencyRef, ProtocolDependencyExecutionCapability>,
  transcript_algorithms:
    None
    | ExactMap<TypedTranscriptAlgorithmDependencyRef,
               TranscriptAlgorithmExecutionCapability>
}

Step(
  InteractiveCore,
  CoreState,
  EventRef,
  exact Prover records at this boundary,
  exact next randomness replay records)
  -> CoreState | CoreExecutionOutcome

ExecuteProtocol(
  AdmittedProtocol,
  CoreInvocationInputs,
  ProverTrace,
  RandomnessReplay,
  ExactProtocolExecutionCapabilities,
  exact ExactAdmittedSubjectAuthorityBinding for the Protocol and exact
    ExactSourceAuthorityBinding for every authority-bearing dependency view,
    with separately supplied fresh capabilities)
  -> Qualified<CoreExecutionRecord,
               exact ExactCheckedResultAuthorityBinding<PIR, CoreExecution>>
~~~

Execution validates all statically decidable input, trace, replay, and
capability facts first. It then scans the schedule, resolves guards, performs
pre-action binding, executes exactly the seven closed actions, records
protected occurrences at their specified phases, and stops on the first
terminal or prover nonproduction. A dynamic replay mismatch discards the
provisional state and returns `Malformed`, not a semantic outcome.

Before completion, execution matches every source binding to its separately
supplied fresh capability, reauthenticates the exact family-indexed PIR
capability contract and ABI, and freshly validates every explicit no-policy
contract or transitive bound source policy for the named execution purpose.
Either closed `CoreExecutionOutcome` creates one exact checked-result binding
under `PirCapabilityContractId<CoreExecution>` and the live qualified
capability retains it. The binding contains the exact invocation, trace,
randomness replay, execution dependency basis, outcome record, total source-
policy closure, and inert `OwnerCapabilityRequirement`. Malformed, refused,
unsupported, cannot-answer, or checker-failure outcomes create neither result
coordinate nor qualified capability.

The Core execution-capability map contains every and only content-addressed
dependency actually evaluated, matched by kind, regime, content ID, ABI, and
direct edges. Closed finite terms use the regime evaluator. Fresh has no
transcript capability map; FS has exactly its admitted construction algorithm
closure. Missing or mismatched authority is `Refused`; operational execution
failure is `CheckerFailure`.

`AcceptProtocol` holds exactly when execution returns an `Accept` terminal,
all supplied Prover records were consumed, every occurring check followed its
declared false effect, and every claim-resource rule holds. `Reject` and
`Abort` are semantic terminal outcomes, not checker failures. A continuing
check failure may feed a later compound decision; a terminating one cannot
accept.

Protocol execution deliberately does not consume statement-container bytes,
proof-container bytes, endpoint calls, or runtime suppliers. Interface and a
later OIR/Realization bridge own the mapping from decoded external occurrences
and supplier results into this exact invocation grammar. Interface
preservation alone is not a complete runtime-invocation claim.

The operational relation above defines Protocol behavior. Probabilistic and
cryptographic denotations interpret its explicit distributions, traces, and
assumptions; they do not replace it.

### 3.12 Core admission

`CoreAdmissible_R(C)` is the conjunction of:

~~~text
closed dependency kinds and authenticated least dependency closure
exactly one Prover, exactly one Verifier, and zero or one PublicEnvironment
typed roles, ports, values, objects, events, claims, reductions, and checks
all local references in bounds and of the declared kind
acyclic value/object, claim, and causal graphs
schedule is a total permutation extending every causal edge
canonical reduced guards and directly recomputable implication
role-knowledge and path-availability closure
canonical-true residual fallback terminal
private and public distribution/correlation closure
challenge backlinks, prefixes, ranks, distributions, and failures
message direction, channel, role, wire-codec, and observation consistency
claim production, linearity, routing, reduction order, and terminal closure
failure-source/effect/class and terminal-payload totality
protected-observation classification completeness
endpoint- and prover-obligation recomputation equality
prover-obligation-failure recomputation and reference closure
no unresolved choice, symbol, external policy, or ambient semantic read
~~~

This is structural and semantic admission of a Core. It establishes neither
relation satisfaction nor a cryptographic property.

## 4. Protocol, identity, and authority

### 4.1 Challenge interpretation

~~~text
ChallengeInterpretation =
    FreshPublicCoins
  | FiatShamir(TranscriptConstructionId)

Protocol = {
  core: InteractiveCore,
  challenge_interpretation: ChallengeInterpretation
}
~~~

Fresh interprets each public challenge through its declared distribution. FS
interprets the same Core occurrence through one exact admitted transcript
construction. They are distinct Protocols over one Core.

The exact construction schema, transcript-action semantics, occurrence and
prefix maps, abort map, context closure, and construction/composition
transactions are specified by
[Fiat--Shamir and Core composition](fiat-shamir-and-composition.md). This
document fixes the Protocol-facing seam and does not duplicate that dependent
subject as a second Core vocabulary.

In v0, only the construction's `SqueezeAndSampleRule` may fail during Protocol
execution, and its failure is exactly the linked challenge failure selected by
the construction's total abort map. Initialization, typed context binding,
framing, and absorbed-atom codecs are total and infallible over admitted
domains. External byte-decoding errors occur before Protocol execution. Any
additional runtime transcript failure requires a new occurrence-exact Core
source or a new regime.

### 4.2 Identity algebra

~~~text
CoreId = H(
  "zkc/core",
  ProtocolSemanticRegimeId,
  CanonicalEncode(InteractiveCore))

TranscriptConstructionId = H(
  "zkc/transcript-construction",
  ProtocolSemanticRegimeId,
  CoreId,
  CanonicalEncode(TranscriptConstruction))

ProtocolId = H(
  "zkc/protocol",
  ProtocolSemanticRegimeId,
  CoreId,
  FreshPublicCoins)

ProtocolId = H(
  "zkc/protocol",
  ProtocolSemanticRegimeId,
  CoreId,
  FiatShamir,
  TranscriptConstructionId)
~~~

FS initialization binds `CoreId`, `TranscriptConstructionId`, and exact
application/session context, not `ProtocolId`, avoiding an identity cycle. A
construction contains `BindConstructionSelfId`; authentication computes its ID
first and execution interprets that instruction with the computed value.

`CoreId` identifies the exact bounded normal form, not an observational
equivalence class. Behaviorally equivalent but differently encoded Cores may
have different IDs and require a separate observer-indexed equivalence
judgment.

### 4.3 Protocol admission

`ProtocolAdmissible(P)` requires:

- `CoreAdmissible(P.core)` under the exact Protocol regime;
- a known interpretation tag;
- for Fresh, every challenge supported by its exact distribution;
- for FS, an authenticated and admitted construction over the same `CoreId`
  with complete occurrence/prefix maps, total abort map, exact closed context,
  and structurally closed framing and derivation algorithms; and
- exact `CoreId`, `TranscriptConstructionId` when present, and `ProtocolId`
  recomputation.

Admission does not require an `FSCompile` theorem. An FS Protocol can be
meaningful and admitted without establishing Fiat--Shamir security.

Physical canonicality and dependency authentication precede this predicate;
their exact operation is specified by [Canonical PIR](canonical-pir.md).

### 4.4 Authority topology

The common lifecycle is:

~~~text
raw carrier
  -> physical and dependency authentication
  -> immutable AuthenticatedCanonicalProtocolCandidate
  -> Protocol admission
  -> opaque immutable process-local AdmittedProtocol
~~~

`CoreId` is a semantic subidentity, not a second official artifact. Core
authentication and admission are subchecks inside Protocol admission.
Successful Core sub-admission mints a transaction-scoped
`CoreAdmissionWitness`; it cannot leave the transaction, serialize, or assert a
challenge interpretation. After Protocol admission, `AdmittedCoreView` is an
attenuated immutable view minted only from that exact `AdmittedProtocol`; it
cannot widen back to Protocol authority.

Cold standalone FS admission is acyclic:

~~~text
authenticate Core
  -> check CoreAdmissible and mint scoped CoreAdmissionWitness
  -> authenticate and admit TranscriptConstruction against that witness
  -> check FS Protocol admission
  -> mint AdmittedProtocol
  -> discard CoreAdmissionWitness
~~~

A composed construction requires exact reconstructed composition authority,
not a serialized old result. A newly composed Core gains no official
persistence or consumer authority until paired with an interpretation and
authenticated and admitted as a new Protocol.

`AdmittedProtocol` is required by `ExecuteProtocol`; a raw value or ID is not
enough. It retains exact authenticated dependency views and, for FS, the
admitted construction and algorithm dependencies. Execution attenuates these
views for the operation and cannot widen or serialize them.

After process, FFI, mutation, reopen, or serialization boundaries, all live
capabilities are lost. Reuse requires reauthentication and readmission.

## 5. Narrow views and outcomes

### 5.1 Purpose-specific immutable views

No consumer receives a universal fact root:

| Consumer | PIR-owned source view | Additional exact inputs | Consumer-owned result |
|---|---|---|---|
| Relations | ports, objects, claims/checks/terminals, obligations, occurrences | Interface, relation interface, binding, question, checked artifact comparison or grounding when requested | correspondence |
| Analysis | events, schedule, challenges, checks, claims, failures, maps | question, model, assumptions, and only when named by the family rule: Interface, Plan, admitted TranscriptConstruction, affirmative CheckedFSConstruction, admitted CoreCompositionSpec, or affirmative CheckedCoreComposition | qualified judgment |
| Compiler | admitted predecessor facts and declared transformation surface | proposal candidate, exact bridge-owner checked transition result, and policy-declared Analysis, peer-owner, Evidence, or later-owner inputs | Compiler-owned candidate/domain/assessment/decision results; transition truth remains bridge-owner authority |
| OIR | events, ports, obligations, failures, occurrences | Interface, role, tagged Plan basis | OIR and projection relation |

Each view has an adequacy predicate proving it contains every source fact its
named consumer question may read. It is derived from an admitted subject and
has no independent identity unless a named durable cross-process consumer
requires one.

### 5.2 Qualified outcomes

Owner operations distinguish these semantic classes when applicable:

~~~text
Affirmative
Negative(reason, retained_facts)
Unsupported(exact unsupported construct or question)
CannotAnswer(missing named semantic input or basis)
Refused(missing authority or prohibited invocation)
Malformed(exact input framing or structural defect)
CheckerFailure(operational failure with no semantic conclusion)
~~~

Direct total predicates ordinarily return affirmative or negative. Absence of
support or input never becomes a negative semantic judgment. For A/N relation
families, only a completed affirmative or negative result mints a question-
scoped checked capability. An owner may instead define another explicitly
closed qualified-outcome algebra, such as `CoreExecutionOutcome`; each of its
completed variants may mint only the exactly corresponding checked capability.
`Unsupported`, `CannotAnswer`, `Refused`, `Malformed`, and `CheckerFailure`
mint none in every family.

### 5.3 Checker placement

Direct recomputation owns semantic IDs, dependency closure, canonical guard
form, Core admission, obligation equality, challenge prefixes, and the
structural parts of dependent-subject admission. A proposal plus independent
validator is appropriate only when a producer searches but the complete
predicate is executable. Theorem- or model-backed judgments own
Fiat--Shamir security, property transport, semantic equivalence/refinement,
relation satisfaction, completeness, and cryptographic claims.

There is no universal checker registry. Each operation receives the exact
identity-matched capabilities for its owned relation kind and regime.

## 6. Nonclaims and residual obligations

Admission of this model does not by itself establish:

- implementation conformance or faithful representation by current code;
- relation truth, satisfiability, witness validity, or committed-object
  grounding;
- soundness, knowledge soundness, completeness, zero knowledge, or
  Fiat--Shamir security;
- compiler preservation, optimality, or target selection;
- Interface preservation, Plan realization, OIR projection correctness, or
  endpoint support unless their separately owned relations are checked;
- prover termination, cost, performance, or supplier correctness;
- correctness of an external sampler beyond one replay transition;
- formal-model adequacy or proof-assistant verification;
- artifact provenance, independent review, or production readiness; or
- compatibility with any earlier or later semantic regime.

The [Relations domain](../relations/README.md), dependent
[interfaces and plans](interfaces-and-plans.md), and later Analysis, Compiler,
and OIR specifications own those conclusions. This specification provides the
closed subject against which they can be stated without collapsing their
authority into Protocol admission.
