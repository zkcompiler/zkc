# Candidate C integrated target semantic model

> **Document kind:** Temporary integrated design
> **Document state:** Stage 3.4 convergence candidate; validation and final
> selection pending
> **Authority:** None. This document neither changes the current specification
> nor authorizes implementation, migration, or a cryptographic claim.
> **Scope:** The complete Stage 3 semantic surface at clean-room design
> resolution. Later Analysis, Compiler, OIR, Realization, and Evidence schemas
> remain out of scope.
> **Disposition:** After scenario and convergence review, promote accepted
> sections into durable PIR and Relations owners and record absorption.

## 1. Architectural thesis

The candidate is a **small semantic kernel with typed satellites**:

```text
language-independent InteractiveCore algebra
  + one ChallengeInterpretation
  = Protocol
        <-> one physically canonical, closed MLIR PIR graph

Protocol
  +--> ProtocolInterface[ProtocolId]
  +--> ProverPlan[ProtocolId]
  +--> RelationBinding[ProtocolInterfaceId, RelationInterfaceId]
  +--> FSConstruction[source ProtocolId, target ProtocolId]
  `--> CoreComposition[child occurrences, target CoreId]
```

Only `InteractiveCore` and `Protocol` are denoted by canonical PIR. Interface,
Plan, relation subjects, artifact observations, construction results, and
checked relations are separate semantic objects with their own owners,
regimes, identities where justified, admission predicates, and authority.

The semantic algebra is independent of MLIR so that meaning can be interpreted
by specifications, formal models, and independent checkers. Canonical PIR is
still the only v0 production representation of that algebra. This is not a
second carrier-neutral interchange format.

## 2. Semantic universes and reference discipline

### 2.1 Closed subject families

Stage 3 defines these subject families:

```text
InteractiveCore
TranscriptConstruction
Protocol
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
```

It defines these capability-neutral producer outputs:

```text
NormalizationAudit<ProtocolAuthoring | RelationAuthoring>
CanonicalRelationCandidateBundle
```

It defines these checked result families:

```text
PlanRealizes
RelationArtifactAgreesWithInterface
CommittedObjectGrounding
RelationCorrespondsAtInterface
RelationInstanceCorrespondsAtInterface
FSConstruction
CoreComposition
```

Every checked relation has a distinct opaque process-local completed-result
capability. The names used below are:

```text
CheckedPlanRealizes
CheckedArtifactInterfaceComparison
CheckedCommittedObjectGrounding
CheckedRelationCorrespondenceJudgment
CheckedInstanceCorrespondenceJudgment
CheckedFSConstruction
CheckedCoreComposition
```

`Qualified<CheckedX>` returns `CheckedX` only for a completed affirmative or
negative semantic outcome. The capability retains the exact operands,
question, regime, field-factored result, checker identity, and dependency/read
closure. `Unsupported`, `CannotAnswer`, `Refused`, `Malformed`, and
`CheckerFailure` mint no checked capability. A serialized result record is not
that capability and cannot be widened to another question.

It exports signatures, not implementations or conclusions, for:

```text
RelationSatisfies
FSCompile
PropertyTransport
ProjectionCorrect
LocalOirValid
```

Private witness assignments are occurrence-local confidential values. They are
not mandatory global content-addressed subjects, because public identities over
secret bytes can leak equality or invite unsafe persistence.

### 2.2 Typed semantic regimes

Every subject family has a typed regime. A regime fixes exactly the meanings
needed to authenticate and admit that family:

```text
ProtocolSemanticRegime
InterfaceSemanticRegime
PlanSemanticRegime
PlanRealizesRegime
RelationDefinitionRegime        // externally owned
RelationInterfaceRegime
RelationInstanceRegime
RelationBindingRegime
RelationArtifactProfileRegime
RelationAdapterRegime
RelationArtifactObservationRegime
CorrespondenceRegime
FSConstructionRegime
CompositionRegime
```

A regime is not a tool version, MLIR bytecode version, package version, policy,
or checker build. Changing meaning while preserving carrier fields requires a
new semantic regime and therefore a new semantic identity.

`TranscriptConstruction` is interpreted by the exact
`ProtocolSemanticRegime`, as selected in Stage 1, rather than introducing an
independent construction regime. Reusable hash, duplex, framing, and sampling
profiles remain exact semantic dependency IDs inside the construction.

### 2.3 Local and global references

Before a root identity exists, a candidate uses typed positional local
references:

```text
LocalRef(kind, canonical_ordinal)
```

After authentication, a durable occurrence reference is:

```text
CoreRef<K> = (CoreId, K, canonical_ordinal)
```

where `K` is one of `role`, `port`, `value`, `object`, `randomness`, `event`,
`challenge`, `claim`, `reduction`, `check`, `failure`, `terminal`,
`endpoint_obligation`, `prover_obligation`, `prover_obligation_failure`, or
`dependency`. Kinds are not interchangeable even when ordinals match.

`CoreRef<K>` is used only for facts intrinsic to the Core. Any result or map
whose meaning depends on Fresh versus FS interpretation uses:

```text
ProtocolScopedRef<K> = (ProtocolId, CoreRef<K>)
```

Fresh and FS Protocols may share the inner Core reference but never the scoped
reference. A later runtime occurrence additionally requires its exact trace or
invocation occurrence identity; Stage 3 does not mint that runtime subject.

A composition candidate first uses a non-global local child slot:

```text
LocalChildOccurrenceRef = child_slot
LocalChildInnerRef<K> = (child_slot, child CoreRef<K>)
```

Only after composition-spec authentication is the durable occurrence tag
formed:

```text
ChildOccurrenceRef = (CoreCompositionSpecId, child_slot)
ChildInnerRef<K> = (ChildOccurrenceRef, child CoreRef<K>)
```

The canonical spec preimage contains only local child-slot references, so its
identity is acyclic. Two uses of the same `CoreId` remain distinct without
inventing two child semantic identities.

### 2.4 Canonical semantic encoding

For each regime `R`, `CanonicalEncode_R(T)` is an injective typed encoding of
the semantic value `T`. The preimage is defined structurally:

- every sum carries a domain-separated variant tag;
- every product encodes fields in its declared order;
- every sequence carries its length and ordered elements;
- every set or map is sorted by the canonical encoded key and rejects duplicate
  keys;
- every optional value has an explicit absent or present tag;
- every reference includes its subject family and typed local or global key;
- integers and field-like scalars use their regime-owned unique mathematical
  encoding; and
- strings are permitted only in subject families that own human-facing names
  and use a regime-owned Unicode and length encoding.

No printer spelling, MLIR bytecode, host object layout, map iteration order,
source position, local pointer, or process identifier enters a semantic
preimage. The later normative identity specification selects the hash function
and concrete byte grammar while preserving this exact structural tuple and
injectivity requirement.

Every field below whose name denotes a codec, encoder, decoder, framing rule,
sampler, or pure function is canonical data, never an ambient executable value:

```text
CanonicalAlgorithmSpec<K> =
    ClosedFiniteTerm(kind = K, typed syntax, declared totality evidence)
  | ContentAddressedContractRef(kind = K, contract_regime_id,
                                regime_qualified_content_id, exact ABI,
                                direct_dependency_ids)
```

`LosslessContainerCodec`, `TotalSemanticEncoder`,
`TotalTaggedSemanticDecoder`, `InjectiveFramingContract`, and
`InjectiveTypedCodec` are aliases for the corresponding kind of this closed
sum. A reference is admitted only with its exact authenticated preimage under
the named contract regime and dependency closure; every direct dependency ID
is likewise typed and regime-qualified. Live implementations and checker
capabilities remain
outside every semantic preimage. Thus identity commits to a finite schema or
content-addressed contract, not to host-language function equality.

The Fiat--Shamir algorithm-bearing names used below are closed aliases of the
same sum:

```text
DomainSeparatedInitialization =
  CanonicalAlgorithmSpec<TranscriptInitialization>
InitializationAction =
  CanonicalAlgorithmSpec<InitializeFromTypedContextValue>
SqueezeAndSampleRule =
  CanonicalAlgorithmSpec<TranscriptConditionalChallengeSample>

CanonicalStaticContext = {
  language_id: RegimeQualifiedContentId,
  argument_system_id: RegimeQualifiedContentId,
  application_domain_id: RegimeQualifiedContentId,
  static_parameters:
    CanonicalMap<RegimeQualifiedFieldId, CanonicalStaticScalarOrSequence>
}

RegimeQualifiedFieldId = (ContractRegimeId, RegimeQualifiedContentId)
CanonicalStaticScalar =
    Boolean | UnsignedInteger | FiniteByteString | RegimeQualifiedContentId
CanonicalStaticScalarOrSequence =
    CanonicalStaticScalar | CanonicalSeq<CanonicalStaticScalar>
```

Their exact ABIs include input/output semantic domains, state transition,
domain-separation and framing tags, total/typed failure sum, and direct
dependency closure. A squeeze rule for joint member `i` additionally accepts
exactly the successful components `0..i-1` and returns either its component or
`SamplingFailedAt(i)` under the named joint contract. Static context values are
finite tagged scalars or finite sequences under the regime encoding; they
contain no callbacks, registry keys, ambient strings, clocks, or runtime port
values.

The Protocol family's unique physically canonical v0 carrier is the MLIR PIR
graph in Section 5. Other Stage 3 subjects are finite canonical algebraic
values under this encoding, not alternate Protocol carriers. An owner may
accept one or more transport profiles only when each has a total tagged,
lossless decode into that exact value; transport bytes and profile revisions do
not enter the semantic ID unless the subject explicitly owns byte language.
Authentication of a satellite therefore means transport/profile validation
when applicable, exact value reconstruction, dependency authentication, and
identity recomputation. A later choice of JSON, MLIR, binary, or API spelling
cannot add semantic fields or create a second Protocol model.

## 3. `InteractiveCore`

### 3.1 Complete root

```text
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
```

Canonical sequence order is semantic except where the field definition says it
is a set and supplies a unique sort key. Authoring order is never reused as an
implicit semantic order.

### 3.2 Dependencies

The v0 dependency-kind sum is closed:

```text
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
```

Each `DependencyDecl` contains its kind, semantic regime, content identity,
direct dependency identities, and the exact protocol-facing ABI used by the
Core. A Core cites meaning through this ABI; it never asks a registry to
discover an operation by a string name.

The direct manifest is identity-bearing. Admission consumes the least
reachable graph of authenticated dependency preimages. Opaque relation,
artifact, source, theorem, or deployment references are not dependency kinds
and acquire no authority through Core admission.

Adding a canonical dependency kind requires a new Protocol semantic regime.
Unknown kinds fail closed.

### 3.3 Roles and ports

A `RoleDecl` gives one canonical role ordinal and a closed role class:

```text
RoleClass = Prover | Verifier | PublicEnvironment
```

The v0 Protocol is two-party public coin. Admission requires exactly one
`Prover` role, exactly one `Verifier` role, and at most one
`PublicEnvironment` role. If any port, public-randomness declaration, or event
names the public environment, that unique role must exist. No other role is
admitted. `PublicEnvironment` supplies fixed public inputs, explicit context,
and abstract public coins but does not become an ambient oracle.

Execution maintains an explicit role-knowledge state over the closed set of
declared roles. `AllRoles` means the unique Prover, the unique Verifier, and
the optional PublicEnvironment when it exists. Knowledge evolves only by the
following rules:

1. a `Public` input-port occurrence is initially available to `AllRoles`; a
   `PrivateToRole` occurrence is initially available only to its port owner;
2. a canonical constant is available to `AllRoles`; a private-randomness
   value is available only to its owner after its successful sampling step;
3. a prover-obligation output is initially available only to the Prover in
   the pre-action binding phase of its active source event; a check result is
   initially available only to the Verifier when its source resolves; a
   check-false or explicit-abort failure result is initially available only to
   the Verifier, while a public-challenge sampling failure result is initially
   available to both the Verifier and the exact `PublicEnvironment` resolver;
4. a pure constructor or function result is available to exactly each role
   that knows every input and the named pure contract;
5. an active `ObservePublicValue(v)` requires its actor to know `v` at the
   action phase and then makes `v` available to `AllRoles`;
6. an active `Message` requires its sender to know the payload at the action
   phase and adds the
   payload to the receiver's knowledge; and
7. a successfully resolved public challenge and the public outputs of an
   active terminal become available to `AllRoles`.

An output port creates no value, operational occurrence, observation,
exposure boundary, or intra-Core knowledge transfer. It is only a declarative
typed grouping for an Interface or later OIR boundary. Its visibility is a
constraint that a later exposure operation must respect; by itself it neither
asserts that an execution exposes the value nor that any role receives it.
A Core role does not learn a value merely because an output port names it.
Public values that must become known during Protocol execution use
an explicit `ObservePublicValue`, `Message`, successful public challenge, or
terminal public output. `EmitArtifact` does not publish its input, and
protected transcript, check, artifact, claim, or failure observation is not an
implicit knowledge transfer. Admission checks every event input against the acting
role's exact path-sensitive knowledge at the action phase defined below.
The optional PublicEnvironment follows the same public-knowledge rules, but
it may act only where the closed event-kind rules permit; it is not an ambient
oracle or privileged reader. Role knowledge is recomputed from canonical
ports, value origins, events, and guards rather than copied into an
authority-bearing cache.

A `PortDecl` contains:

```text
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
```

`ExactlyOne` has cardinality one and `FixedCount(n)` requires canonical
positive `n`; the occurrence ordinals are exactly `0..cardinality-1`. An input
has exactly `InputSource`; an output has exactly one same-domain
`OutputValues` entry per occurrence, in ordinal order. Because Core defines no
output-exposure occurrence, no path-availability proposition is inferred from
that grouping. Interface may attach a lossless external representation, but
Stage 4B must name an exact OIR exposure boundary and prove availability before
the value can be externally obtained. `PortValue` may reference input-port
occurrences only. Port names and occurrences are canonical ordinals.
Application names and containers belong to Interface. Private witness ports
declare requirements; no witness bytes enter Core identity.

### 3.4 Pure values and protocol objects

`ValueNode` is a closed pure DAG:

```text
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
```

The only admissible path-condition representation is finite and canonical:

```text
GuardAtom =
    BooleanAtom(BooleanValueRef)
  | FiniteValueEquals(ValueRef, CanonicalSemanticValue)

CanonicalGuardFormula =
  CanonicalReducedOrderedDecisionDiagram<GuardAtom>

GuardValueRef =
  ValueRef whose origin is exactly GuardDecision(CanonicalGuardFormula)
```

`BooleanAtom` may reference only an earlier Boolean value whose origin is not
another `GuardDecision`. `FiniteValueEquals` requires a finite declared value
domain and a canonical same-domain value. Atom order is the lexicographic
canonical encoding of the tagged atom and its occurrence-exact references.
The Protocol semantic regime fixes one complete reduced ordered decision
diagram algorithm: physical normalization, reduction, Boolean operations,
satisfiability, equality, and implication. Authentication directly verifies
the ordered reduced form. Equality is canonical-form equality, and
`A implies B` is checked by reducing `A AND NOT B` to false. No SMT solver,
host callback, proof search, or unrecorded semantic theory participates.

An arbitrary Boolean-returning `Apply` may be used as a `BooleanAtom`, but the
guard checker treats distinct atoms as propositionally independent. This is a
deliberately conservative rule: it may refuse a semantically valid implication
that would require function-specific reasoning, but it cannot manufacture one.
A future regime may add a typed, identity-bearing theory certificate; v0 does
not. Every stored activation guard, merge branch, composition suppression
equation, and terminal route guard must be a `GuardValueRef`. Derived
availability is not a hidden stored guard; it is the total transfer function
below. A guard value is available to a role only when all of its atom operands
are available to that role.

The Protocol regime defines one closed boundary-indexed availability algebra:

```text
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
```

The two operational atom kinds are occurrence-exact outcomes from the closed
execution relation, not author-selectable guard atoms. Protocol guards cannot
reference them. The availability checker orders their tagged encodings after
ordinary `GuardAtom`s, constrains them by the declared preparation and
randomness transitions, and uses the same reduced ordered decision-diagram
algorithm for direct equality and implication. Thus availability checking is
finite and canonical without adding fields to the Protocol identity.

The transfer is one total fold over the value/object DAG and event schedule:

1. at `Initial`, every input-port value exists; public inputs are known to
   `AllRoles` and private inputs only to their exact owner. Canonical constants
   exist and are known to `AllRoles`;
2. tuples, projections, injections, and pure applications exist when every
   operand exists, and a role knows the result exactly when it knows every
   operand and the authenticated pure contract. An object follows the same
   rule subject to its owner and visibility restriction;
3. a private-randomness value and a prover-obligation output exist at the
   successful `PostPreparation` of their exact source event and are initially
   known only to Prover;
4. a challenge value exists at `PostResolution` exactly on the linked
   `RandomnessProduced` branch and is then known to `AllRoles`; a check result
   exists at its action-occurring `PostResolution` and is initially known only
   to Verifier;
5. `FailureOccurred(f)` exists with a total Boolean value after its unique
   source occurrence resolves, including an inactive source. For
   `ChallengeSampling` it is initially known to Verifier and the exact
   `PublicEnvironment` resolver; for `CheckFalse` or `ExplicitAbort` it is
   initially known only to Verifier. `FailureStatusValue(f)` exists only on
   the true continuing-failure branch and follows the same source-indexed
   knowledge rule; and
6. after each phase, topological pure/object closure runs and the exact
   `ObservePublicValue`, `Message`, public-challenge, and terminal-output transfer
   rules of Section 3.3 update `KnowsAt`. No other operation transfers
   knowledge.

For `GuardDecision`, existence and role knowledge are the conjunction of the
corresponding facts for all atom operands. For
`GuardedMerge([(g_i, v_i)])`, define:

```text
MergeReady(role, boundary) =
  AND_i AvailableAt(role, g_i, boundary)

MergeSelected(role, boundary) =
  OR_i (ValueOf(g_i) AND AvailableAt(role, v_i, boundary))

AvailableAt(role, merge, boundary) =
  MergeReady(role, boundary) AND MergeSelected(role, boundary)

ExistsAt(merge, boundary) =
  (AND_i ExistsAt(g_i, boundary))
  AND (OR_i (ValueOf(g_i) AND ExistsAt(v_i, boundary)))
```

Admission proves the branch guards pairwise exclusive. Their canonical
disjunction is the merge's exact derived availability condition; no separate
or caller-selected `when` field exists. A use-site condition must imply this
disjunction and the corresponding role-specific `AvailableAt` formula. Thus a
merge may be partial outside the paths on which it is used, while exactly one
available branch is selected on every use path.

Every use has one fixed boundary and implication check: an event actor must
know its activation-guard operands at `PreAttempt`; a prover construction must
know its basis inputs there; kind-specific event inputs must be available to
the actor at `PostPreparation`; a check's claim values and a terminal
selector's payload use their exact action/resolution boundary; and reduction
side inputs use `ExistsAt` at `EmbedClaimClosurePoint` of their exact
`ClaimClosurePoint`. Same-event prover outputs
are legal only at their own successful `PostPreparation`. For every use,
admission directly proves that the use's derived occurrence condition implies
the required `ExistsAt` or `AvailableAt` formula. Unknown boundaries or origin
forms fail closed.

Pure value dependencies point backward in canonical topological order.
`PrivateRandomnessValue`, `ChallengeValue`, `ProverObligationOutput`,
`CheckResult`, `FailureStatusValue`, and
`FailureOccurred` are typed origin bindings to
separately declared occurrences. Private randomness becomes available at its
declared sampling point; a challenge value becomes available only after its
active `FreshChallenge` event is interpreted; a prover-obligation output becomes
available only after the active obligation is bound exactly once by the prover
trace; a check result becomes available only after its active `InvokeCheck`;
and a failure status becomes available only after that failure occurs with
`ContinueWithStatus` and must be the exact value named by the effect.
`FailureOccurred` is a total Boolean available after the unique source
occurrence resolves, whether or not the failure occurred.
Admission rejects a mismatched origin kind, output ordinal,
domain, activation relation, or use before availability. Pure functions are
total over their declared domains or expose a typed result sum; they cannot
read transcript state, undeclared randomness, registries, files, clocks, or
policies.

`InjectVariant(sum, i, v)` is the canonical injection into one closed sum
domain. Admission requires `i` in range and `v` to have exactly the declared
payload domain of variant `i`; the result has exactly `sum`. It is structural,
injective, and has no user-selected implementation.

`GuardedMerge` is the sole phi-like value form. Admission additionally proves
that all branch values have one domain and that each selected-branch condition
implies the corresponding value's existence. At runtime all branch guards
needed by a use resolve, exactly one is true, and only that selected branch
value must be available; unselected values need not be produced. This
preserves a total value DAG while allowing bounded branches to feed a later
compound decision.

`ObjectDecl` is closed rather than an open host object:

```text
ObjectObservationClass = Transcript | Wire | Check | Artifact | Claim

ObjectDecl = {
  contract: ProtocolObjectContractRef,
  constructor_inputs: CanonicalSeq<ValueOrObjectRef>,
  owner_role: RoleRef,
  visibility: Public | PrivateToRole,
  protected_observations: CanonicalSet<ObjectObservationClass>
}
```

The named dependency ABI fixes the semantic object domain, exact constructor
input domains, total deterministic construction relation, and canonical
equality/encoding operations exposed to Core. It cannot read a registry,
transcript, clock, randomness, file, policy, or live implementation handle.
Construction becomes available to a role exactly when that role knows every
constructor input and the contract; `PrivateToRole` restricts that set to
`owner_role`, while `Public` permits transfer but does not itself publish the
object. A public object initially known only to Prover therefore still needs a
`Message` to become known to Verifier. A private object cannot be sent,
transcript-absorbed, artifact-emitted, or used as a check value by a role
outside its owner. A claim parameter or reduction side input follows the
separate global-resource rule in Section 3.8 and does not transfer object
knowledge to any role.

`protected_observations` is recomputed as the exact union of actual direct or
structurally contained object uses: a transcript atom contributes
`Transcript`, a message payload `Wire`, a check input `Check`, an emitted
artifact `Artifact`, and either a claim parameter or a reduction side input
contributes `Claim`. Each reduction-side use cites that reduction's exact
contract ABI and is available under the reduction-firing rule. Every other use
must likewise cite its matching event, claim, codec, or contract ABI and
satisfy its kind-specific role-knowledge or semantic-availability rule;
missing or extra classes reject. No object is an ambient pointer, and
serialization material is not object identity unless the object contract says
so. Commitments, polynomial claims, openings, and similar objects can thus be
represented without making Relations interpret their mathematical truth
during Protocol admission.

### 3.5 Randomness and correlation

All randomness required by the abstract protocol is explicit:

```text
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
```

`FreshPublicCoins` applies only to public-challenge randomness. Private prover
randomness remains an abstract prover obligation under both Fresh and FS
interpretations. Its declared distribution and correlation are Core semantics
because later completeness or zero-knowledge questions may read them, even
though Stage 3 proves neither property.

A public-challenge declaration is owned by the unique `PublicEnvironment`
role, which must therefore exist whenever the Core declares a challenge. A
private-prover sample is owned by the unique `Prover` and must name the exact
prover obligation that consumes it. Admission rejects every other owner/purpose
combination.

Availability is occurrence-exact. For `PublicChallenge(c)`,
`available_before` is that challenge's linked `FreshChallenge(c)` event and
`on_sampling_failure` is its linked verifier-visible sampling failure. For
`PrivateProverSample(o)`, `available_before` is exactly
`ProverObligation(o).source_event` and `on_sampling_failure` is exactly the
obligation failure `PrivateSamplingFailed(this randomness)`. An independent
sample is attempted immediately before that active event is bound; an inactive
event performs no attempt. Joint members advance at those same exact points
under the group equations below. No unrelated event, implicit pre-sampling, or
ambient activation guard can determine randomness timing.

Correlation closure is global and exact. Core group ordinals are exactly
`0..group_count-1`, ordered by each group's least member `RandomnessRef`; no
string or author label enters identity. Every `JointMember(contract, group,
index)` in one group names the same authenticated joint contract; indices are
the collision-free canonical range for exactly that group's members, and each
member's declared distribution equals the contract's checked marginal at its
index. A group is homogeneous: every member has the same owner and purpose
class, so public-challenge and private-prover randomness cannot share a joint
group.

The protocol-facing ABI of each `DistributionContract` fixes its canonical
value domain, probability law, exact support, and closed one-attempt outcome
relation:

```text
SingleSamplingStep() =
    Produced(value in exact declared support)
  | SamplingFailed       // present only when the contract permits failure
```

Successful Fresh executions are interpreted by the declared law. Admission
can authenticate that finite contract and execution can check whether one
replayed outcome belongs to its transition relation; neither check proves
that an external sampler followed the law.

The protocol-facing ABI of a `JointDistributionContract` is not merely a joint
law. It fixes the finite member-domain sequence, the joint distribution, every
marginal, and one ordered conditional sampling transition per member index:

```text
JointSamplingStep(i, prior successful components) =
    Produced(component_i)
  | SamplingFailedAt(i)
```

Successful steps compose to exactly the declared joint distribution. A step
can report only its own tagged failure, and the first failure closes that group
execution, so one attempt can never activate several verifier failures or
several prover-nonproduction causes. The member index is also the exposure
rank: members' `available_before` events are strictly ordered by the Core
schedule in index order. Each group has one base activation guard available
before its first member, defined as the exact activation guard of the index-0
source event rather than as an extra field or ambient predicate. For public
challenges, the effective event guard at
index `i` is exactly that base guard conjoined with the negation of every
earlier member's `FailureOccurred`; for private samples, each source event uses
the base guard because an earlier private-sampling failure already ends the
trace as `ProverDidNotProduce`. When the effective guard is true, execution
advances the group at that member's availability point; success reveals only
that component, while failure selects exactly that member's
`on_sampling_failure`. Every consumer of a public component has a guard
implying that component's effective guard and successful production. A
continuing public failure therefore suppresses all later group members and
consumers; a private failure yields its one named nonproduction outcome
immediately. When the base guard is false, no group step occurs. These rules
make partial activation, hidden failure suppression, late resolution, and
ambiguous multi-failure interpretations inadmissible.

Every `IndependentFresh` declaration is a distinct sample occurrence. Fresh
execution therefore performs one independent step per such `RandomnessRef`
and one ordered joint experiment per exact group; equality of types or
ordinals never shares a sample.

Every public `ChallengeDecl` and public-challenge `RandomnessDecl` are in an
exact one-to-one backlink relation. `public_coin_index` is the challenge's
zero-based rank among `FreshChallenge` events in the total Core schedule, so
the indices form one collision-free canonical range. The index selects trace
order only; independence or joint correlation comes exclusively from the
randomness declaration and checked joint contract.

A Plan may choose an algorithm for satisfying a randomness obligation but may
not replace its distribution or correlation contract. Unknown or implicit
random sources are admission failures. `ProverObligationFailureRef` is a
Core-owned abstract failure to produce a trace, not a Plan or Realization
failure type and not a verifier terminal.

### 3.6 Effect occurrences

The closed v0 event kind and its common occurrence envelope are:

```text
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
    ObservePublicValueContracts(observe: EndpointObligationContractRef)
  | MessageContracts(send: EndpointObligationContractRef,
                     receive: EndpointObligationContractRef)
  | FreshChallengeContracts(resolve: EndpointObligationContractRef)
  | InvokeCheckContracts(invoke: EndpointObligationContractRef)
  | RaiseFailureContracts(signal: EndpointObligationContractRef)
  | EmitArtifactContracts(emit: EndpointObligationContractRef)
  | ReachTerminalContracts(reach: EndpointObligationContractRef)

ProverConstructionBasis = {
  contract: ProverObligationContractRef,
  inputs: CanonicalSeq<ValueOrObjectRef>,
  output_domains: NonEmptyCanonicalSeq<ValueDomainContractRef>,
  private_randomness: CanonicalSeq<RandomnessRef>
}
```

```text
MessageChannel =
    Proof
  | PublicVerifierMessage
  | ApplicationChannel(ApplicationChannelContractRef)
```

`Proof` requires `from = Prover` and `to = Verifier`;
`PublicVerifierMessage` requires `from = Verifier` and `to = Prover`.
`ApplicationChannel(ref)` cites one exact Core dependency whose ABI fixes the
channel's semantic purpose, permitted sender and receiver role classes,
whether transcript observation is permitted or required, and compatible
payload-domain and endpoint-contract families. Two application channels are
distinct through their regime-qualified contract references; no string,
singleton ambient channel, or undeclared label aliases them. The event's
`from`, `to`, codec, protected observations, and send/receive endpoint basis
must match that ABI exactly.

One message occurrence is the shared semantic
fact from which prover-send and verifier-receive endpoint obligations are
derived; direction is never inferred from schedule position. The kind fixes
the actor constraints and the exact source information from which endpoint and
prover obligations are derived. No v0 event kind creates an otherwise
unaccounted ordinary value: pure computations use `Apply`, fresh challenges
use `ChallengeValue`, checks use `CheckResult`, and prover-produced values use
`ProverObligationOutput`. A future value-producing effect requires a named
event constructor and new Protocol regime.

The common `inputs` and protected-observation set are not free metadata. They
are recomputed exactly from the kind:

```text
ObservePublicValue(v): inputs = [v], observations = {PublicValue}
Message(..., payload, ...): inputs = [payload],
  observations = {Wire} or {Wire, Transcript} as explicitly selected
FreshChallenge(c): inputs = [], observations = {Transcript, PublicValue}
InvokeCheck(k): inputs = k.values, observations = {Check}
RaiseFailure(f): inputs = [], observations = {Failure}
EmitArtifact(x): inputs = [x], observations = {Artifact}
ReachTerminal(t): inputs = t.public_outputs, observations = {Terminal}
```

The message choice is identity-bearing and the only optional observation in
this table. Claim observations arise from claim/reduction declarations, and a
failure caused by a check or challenge arises from its exact `FailureDecl`;
neither is smuggled into an event's input or observation set. Admission rejects
missing, extra, reordered, or kind-incompatible inputs and observations.
`Message.actor == from`; `FreshChallenge.actor` is the unique
`PublicEnvironment`; and `InvokeCheck`, `RaiseFailure`, and `ReachTerminal`
are verifier actions. `ObservePublicValue` and `EmitArtifact` name the role
performing the observation or emission. Admission checks those equalities
rather than deriving an actor from schedule position.

The endpoint-basis variant must match the event kind exactly. Its contract
references are identity-bearing Core inputs, so two same-kind dependencies can
never be selected by an ambient registry or by mnemonic. `prover_construction`
is present only on a Prover-acted `ObservePublicValue`, `Message`, or
`EmitArtifact` occurrence. Its inputs are available before the event; its
outputs are exactly all `ProverObligationOutput` origins for that obligation,
in ordinal/domain order, and become available for the active event binding.
Every declared private-randomness member points back to that same obligation.
All other event kinds require the field absent. This basis describes the
semantic production requirement, not a Plan algorithm.

Such an active Prover event executes in two exact phases. First, its guard is
resolved without reading any same-event output; every construction-basis input
must already be known to the Prover, its declared private samples advance, and
successful binding adds exactly the obligation outputs to Prover knowledge.
Second, the event-kind input equation is checked against that augmented
knowledge and the Observe, Send, or Emit action occurs. Those exact outputs
are the only same-event origins legal in an event input. Any other current,
later, failed, or inactive origin is unavailable. An event without
`prover_construction` has no pre-action binding phase and all kind inputs must
already be known before the occurrence. This permits a proof message to carry
the output produced for that same message without weakening use-before-origin
checks elsewhere.

The identity-bearing `prover_construction.private_randomness` sequence is the
exact pre-action attempt order. Each `IndependentFresh` entry performs its one
attempt when reached. A joint-member entry advances exactly that member's
ordered conditional step; the global group exposure law requires earlier
members at earlier source events, so one event cannot hide several group steps.
The first failed entry immediately returns its own exact
`ProverObligationFailureRef`, exposes no later sample or obligation output, and
ends the Core trace as `ProverDidNotProduce`. Prior successful private values
exist only in that partial state. Duplicate entries, a member out of group
order, two members of one joint group at one event, or any semantics that can
report several failures from one attempted obligation reject. Only after every
entry succeeds are all construction outputs bound and the action phase entered.

The v0 Core is finite and acyclic: it has no loop, recursion, dynamic event
allocation, or unbounded message family. A guard is one canonical finite
`GuardDecision` over atoms available strictly earlier in the schedule.
Execution scans the total schedule, skips inactive occurrences without wire or
transcript observation, and stops at the first reached terminal. The final
scheduled occurrence is a fallback terminal with the canonical true guard, so every execution
closes even when earlier guards are false. This permits bounded branching
without turning authoring control flow or a host-language interpreter into
Protocol meaning.

For every scheduled event `e`, two operational predicates are defined rather
than declared as fields:

```text
EventAttempted(e) =
  activation_guard(e)
  AND ExecutionStillLiveBefore(e)

ExecutionStillLiveBefore(e) =
  no earlier scheduled active event has selected a terminal
  AND no earlier attempted prover obligation has selected ProverDidNotProduce

EventActionOccurs(e) =
  EventAttempted(e)
  AND ProverPreparationSucceeded(e)

EventActionOccurrenceRef = EventActionOccurrence(EventRef)
```

Selecting a terminal includes an earlier active `ReachTerminal` and any
earlier resolved failure whose effect is `Terminate`; `ProverDidNotProduce` is
the other immediate `CoreExecutionOutcome` and likewise closes the trace. The predicate is
interpreted in the same path-sensitive operational relation that resolves
guards and failures; it is not a free Boolean node or an Interface-side
verifier execution. `ProverPreparationSucceeded` is true when no
`ProverConstructionBasis` exists and otherwise requires successful binding of
that exact basis. A failed private sample or other failed prover construction
selects the exact `ProverDidNotProduce` cause and does not execute its Observe,
Message, or Emit action.

Public challenge resolution is not pre-action preparation. A
`FreshChallenge` resolution transition executes whenever
`EventActionOccurs(e)`—which for that kind equals `EventAttempted(e)`—and
returns exactly `Produced(challenge value)` or its linked failure variant:
`SamplingFailed` for `IndependentFresh`, and `SamplingFailedAt(i)` for joint
member `i`. In an FS interpretation the `DeriveChallenge`
transcript action is the corresponding deterministic derivation transition,
including its exact state update on a failed derivation attempt; failure cannot suppress the transition that caused
it. The Transcript observation and resolve endpoint action therefore occur on
the attempt, while the PublicValue observation and challenge-value knowledge
occur only on `Produced`. A failed attempt then applies its exact
verifier-visible failure effect; if that effect continues, later challenge
prefixes include the failed derivation transition.

For other kinds, event-kind inputs, endpoint action, and event-kind protected
observations exist if and only if `EventActionOccurs(e)`. Prover-preparation
failures retain their own exact nonproduction observations and obligations
from the attempt. Thus a locally true guard after an earlier terminal is not
even attempted, while an attempted proof event whose construction fails does
not create a proof-message occurrence.

An active `RaiseFailure(f)` is the unique `ExplicitAbort` source for `f`; it
produces no ordinary value and immediately applies `f.effect`. An inactive
failure-source event resolves `FailureOccurred(f)` to false. A resolved
check-false or sampling-failure source resolves it to the exact Boolean
result, and only a true continuing failure produces its fixed status token.
Value and role-knowledge availability checks are path-sensitive: a later use
must be guarded by a condition that implies the origin is available.

Event observation classes and the larger protected semantic-observation
taxonomy are distinct:

```text
EventObservationClass =
    Transcript
  | Wire
  | PublicValue
  | Check
  | Artifact
  | Failure
  | Terminal

ProtectedObservationClass = EventObservationClass | Claim
```

An event may contribute to several event classes. Claims are protected by
`ClaimDecl` production/disposition and `ReductionDecl` consumption rather than
being smuggled into an event observation set. Analyses that quantify over all
protected surfaces use `ProtectedObservationClass`; event admission uses only
`EventObservationClass`. Unknown classes fail closed.

### 3.7 Challenges

Each `FreshChallenge` occurrence owns:

```text
ChallengeDecl = {
  output: ValueRef,
  randomness: RandomnessRef,
  public_coin_index: ordinal,
  rejection_or_abort: FailureRef,
  transcript_event_prefix_template:
    CanonicalSeq<EventActionOccurrenceRef>
}
```

The declared prefix template must equal every prior potentially
action-occurring transcript-participating Core event in total schedule order,
not an informally selected causal subset. It contains only derived
`EventActionOccurrenceRef`s; it
does not depend on an FS construction. On one execution, its concrete Core
prefix is the ordered subsequence of all prior action-occurring
transcript-observed and challenge events. The output must be exactly one
`ChallengeValue(this challenge)`. The referenced randomness declaration must
have purpose `PublicChallenge(this challenge)`; its distribution contract
fixes the semantic sample space and failure behavior, and its correlation
field fixes independence or joint correlation. Neither is implied by a
challenge-looking type.

### 3.8 Claims, reductions, and checks

Claims form a typed resource graph separate from the event schedule:

```text
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
```

A claim is an actorless Protocol-semantic resource, not a role-owned value or
knowledge token. Claim production, liveness, reduction, and consumption use
`ExistsAt` for parameters and side inputs; they do not add those inputs to any
role's `KnowsAt` set. A private value or object may therefore parameterize a
claim without being disclosed. If an `InvokeCheck` contract must inspect that
value or object, it must also appear in `CheckDecl.values`, where the ordinary
Verifier `AvailableAt` rule applies and rejects an undisclosed private input.
Reduction contracts transform only live claim resources plus semantically
existing side inputs and likewise transfer no role knowledge. The protected
`Claim` observation records resource occurrences and typed references, not the
secret semantic values behind them.

Claims do not introduce a second freely scheduled transition system. Their
operational occurrences are the directly derived guarded closure of the event
schedule:

```text
ClaimConsumerOccurrenceRef =
    ReductionClaimInput(ReductionRef, input_ordinal)
  | CheckClaimInput(CheckRef, input_ordinal)

ClaimProduced(c) =
    Initially
      if c.producer is an input-port occurrence and every c.parameter is
      semantically available at the initial boundary
  | AfterEvent(e)
      if c.producer = e, EventActionOccurs(e), ExecutionStillLiveAfter(e),
      and every c.parameter is semantically available after e resolves
  | AtReduction(r)
      if c.producer = r and ReductionFires(r)

ReductionEnabled(r, closure_point: ClaimClosurePoint) =
  r has not fired
  AND every r.input is live at closure_point
  AND every r.side_input and every output-claim parameter is semantically
      available at EmbedClaimClosurePoint(closure_point)

ReductionFires(r) =
  r is the least canonical ReductionRef enabled at the current closure step
```

`ExecutionStillLiveAfter(e)` means that resolving scheduled occurrence `e`
selected neither a terminal nor `ProverDidNotProduce`; the latter ordinarily
prevents the action itself. The occurrence transaction order is exact: evaluate
the guard and resolve every occurrence-total Boolean such as an inactive
failure source; if the action occurs, consume any live linear check claims,
perform and resolve the action and its failure effect; commit a selected
terminal immediately if any; and only when execution remains live create any
action-dependent `AfterEvent` claims and run post-occurrence saturation. An
inactive event creates no event-produced claim, but its resolved false facts
can enable a reduction in that saturation. A terminal-selecting event creates
no `AfterEvent` claims and runs no reduction after the terminal.
Terminal-closure admission inspects the state after the action's claim
consumption and terminal resolution, without a hidden post-terminal closure.

Execution computes one reduction saturation after initial input claims are
created and one after every resolved scheduled event occurrence that leaves execution live.
Saturation repeatedly fires the least enabled reduction until none remains. Each `ReductionRef` can fire
at most once. Firing atomically consumes every linear input, retains every
persistent input, and creates every output claim in canonical output order.
Each output claim has the exact producer backlink to that reduction. This
least-reference tie break is identity-derived and leaves no implementation
choice; acyclicity and one-shot firing make saturation finite.

An action-occurring `InvokeCheck(k)` requires every `k.claims` occurrence to
be live immediately before its action. The action atomically consumes its
linear claim inputs in declared order and retains persistent inputs before its
Boolean result and failure effect resolve. A false guard or failed prover
preparation performs no check and consumes nothing. Event-produced claims are
created only after that event resolves and therefore cannot be consumed by the
same event's check. A challenge event that failed to produce a value likewise
cannot produce a claim whose parameters require that unavailable value.

Every linear claim has exactly one syntactic consumer occurrence in the whole
Core; a persistent claim may have any finite number. Duplicate occurrences in
one consumer count separately and are rejected for a linear claim. Admission
computes the guarded production, liveness, consumption, and reduction-firing
formulas from the canonical event guards and schedule. It requires every
consumer to be live whenever it fires, every produced linear claim to reach
its unique consumer before any terminal reachable from that production path,
no use before production, exact contract/domain routing, and no live linear
claim in a terminal state. Claim production, reduction firing, and check
consumption are `Claim` protected observations in this exact derived order;
they are never transcript, wire, or public observations unless a separate
Core event says so.

Admission therefore verifies exact production, use, linearity, route typing,
acyclicity, and terminal closure by direct recomputation. A claim descriptor
is Protocol structure; creating or consuming it is not a mathematical proof
of the claim, a relation-satisfaction judgment, or a security property.

### 3.9 Failures and terminals

Every verifier-visible failure has one closed, occurrence-exact source, one
declared class, and one explicit control effect:

```text
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
```

For `CheckFalse`, the event must invoke that exact check, the check's
`on_false` must name this failure, and the class is exactly
`MalformedProtocolInput` or `CheckRejected`. Protocol-level malformedness is a
semantic predicate over an already decoded input; container decoding failure
remains Interface-owned. For `ChallengeSampling`, all three references must be
the linked challenge bundle and the class is exactly
`ChallengeSamplingFailed`. For `ExplicitAbort`, the event must be exactly
`RaiseFailure(this failure)` and the class is exactly
`ExplicitProtocolAbort`. Every failure is the target of exactly one such
source, and every false-check, challenge-sampling-failure, and active
`RaiseFailure` occurrence names exactly one failure. Unknown source variants
fail closed.

`ContinueWithStatus` records the failure and makes its unique
`FailureStatusValue(this failure)` available to later guards without
terminating. On occurrence its runtime value is the canonical
`FailureStatusToken { this failure, this class }`; it has no ambient payload
and is unavailable when the failure did not occur. Its observations must contain
exactly `{Failure}`; `Terminate` must contain exactly `{Failure, Terminal}`.
For every `Terminate(t)` effect, `TerminalDecl(t).result` must equal
`TerminatingResultForFailureClass[class]`; a terminating failure can therefore
never select `Accept`. `ExplicitProtocolAbort` is stronger: it must use
`Terminate(t)` and the table forces `t` to be `Abort`, so an event called
`RaiseFailure`/`ExplicitAbort` cannot silently continue. The other three
classes may use `ContinueWithStatus`; a later explicit decision may then
select any terminal justified by its guards and inputs, including recovery to
`Accept`. That is a distinct compound Protocol decision, not acceptance by the
failure transition itself.
A wire-visible failure signal is an explicit guarded `Message` carrying a
typed status value after a continuing failure; neither a failure declaration
nor its source has an implicit wire payload, channel, or codec. This is
ordinary Core semantics, not a composition
exception. A standalone Protocol may therefore express bounded recovery or a
compound decision while retaining the exact failure occurrence. The final
canonical-true fallback terminal still makes every non-prover execution path total.
Each `FailureDecl` has exactly one typed source occurrence. A repeated class is
represented by repeated declarations, so `FailureRef`, `FailureOccurred`, and
`FailureStatusValue` are occurrence-exact rather than ambiguous class labels.

Every terminal selection has the same payload-availability law. For
`ReachTerminalSelection`, the selecting event's exact inputs are already the
terminal's ordered public outputs and its Verifier actor must know them before
the action. For `TerminatingFailureSelection`, the failure transition is
Verifier-resolved after its exact source result is known; admission requires
every ordered terminal output to be semantically available on that failure
path and known to the Verifier at that point. The output may depend on the
just-resolved `CheckResult` or `FailureOccurred` value, but not on an
unproduced challenge, a continuing-only failure-status token, a later event,
or an inactive branch. The transition then publishes exactly that complete
tuple to `AllRoles`. A terminal declaration with multiple selectors must pass
this same path-sensitive check at every selector. These derived payload inputs
do not alter the source event's kind-specific `EventDecl.inputs` and do not
create an implicit `ReachTerminal` event or endpoint obligation.

Interface malformed-input and refusal outcomes that occur before Protocol
meaning are Interface-owned and do not enter this sum.

### 3.10 Endpoint and prover obligations

Each semantic event kind has exact and distinct endpoint- and
prover-obligation constructors. Core carries both complete derived sets
explicitly so later projections can cite stable typed references:

```text
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
```

Endpoint-obligation recomputation uses this exhaustive table; `inputs` is the
event's exact recomputed input sequence in every row:

```text
ObservePublicValue: one (actor, ObservePublicValue, {}, observe contract)
Message:           one (from, Send, {}, send contract)
                 + one (to, Receive, {}, receive contract)
FreshChallenge:    one (PublicEnvironment, ResolvePublicChallenge,
                        {linked sampling failure}, resolve contract)
InvokeCheck:       one (Verifier, InvokeVerifierCheck,
                        {check.on_false}, invoke contract)
RaiseFailure:      one (Verifier, SignalFailure, {that failure}, signal contract)
EmitArtifact:      one (actor, EmitArtifact, {}, emit contract)
ReachTerminal:     one (Verifier, ReachTerminal, {}, reach contract)
```

The tuple order is `(owner_role, action, failure_surface, contract)`; the
source event and inputs are the current event. No other endpoint obligation is
derived. If `prover_construction` is present, exactly one `ProverObligation`
is derived with the current source event and the basis's exact contract,
inputs, output domains, and private-randomness sequence. Its failure map and
the complete `ProverObligationFailureDecl` family are then the canonical total
product of its output ordinals' missing, duplicate, early, and unexpected
causes plus its private-randomness members shown above. If
the basis is absent, no prover obligation is sourced at that event. Admission
also requires every `ProverObligationOutput` and private-randomness backlink to
be in this recomputed family and forbids unused or multiply sourced bases.

`ResolvePublicChallenge` is deliberately interpretation-neutral. A Fresh
Protocol resolves it from the declared public distribution; an FS Protocol
resolves the same Core occurrence through its admitted transcript
construction. Stage 4B may project different local endpoint actions only from
that exact Protocol interpretation. Core therefore does not falsely require a
runtime public-coin sampler after Fiat--Shamir transformation.

Endpoint obligations describe externally observable participation and do not
originate semantic values. Prover obligations describe typed values that a
prover trace must supply; their outputs are referenced only through
`ProverObligationOutput`. For each obligation, its failure map is total over
every required output's missing, duplicate, early-binding, and unexpected
causes and every
named private-randomness sampling failure. The corresponding declarations are
unique by `(obligation, cause)`, and each `RandomnessDecl` points to the exact
matching entry. Unknown output references are malformed trace input rather
than a semantic nonproduction cause. Admission recomputes both obligation
sets and the complete failure family from the event vocabulary and checks
exact equality. These failures describe why a complete prover trace was not
produced; they are not verifier-visible failures or terminals. Producer-side
construction obligations are therefore complete without claiming that a Plan
covers them or that a target can project them.

The complete non-identity-bearing invocation grammar is defined before its
execution rules so `prover trace`, `randomness trace`, and `exact inputs` are
not informal parameters:

```text
PublicInputPortOccurrenceRef =
  InputPortOccurrenceRef restricted to Public

PrivateInputPortOccurrenceRef =
  InputPortOccurrenceRef restricted to PrivateToRole

RoleSecretInputValue = {
  owner: RoleRef,
  domain: ValueDomainContractRef,
  value: CanonicalSemanticValue
}

CoreInvocationInputs = {
  public_inputs:
    TotalMap<PublicInputPortOccurrenceRef, CanonicalSemanticValue>,
  private_inputs:
    TotalMap<PrivateInputPortOccurrenceRef, RoleSecretInputValue>
}

ProverBindingBoundary =
    BeforeFirstEvent
  | PreAction(EventRef)

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
```

The input maps have exactly the domains induced by all input-port occurrences:
one same-domain value per public occurrence and one same-domain secret value
owned by the port's exact role per private occurrence, with no omission,
addition, ordinal alias, or duplicate. `RoleSecretInputValue` is an
invocation-local semantic wrapper: it controls initial role knowledge but has
no serialized form, identity, authentication authority, or ambient lookup.
Public inputs include every declared public `Statement`, `Witness`, `Context`,
or `ProtocolValue` input; the Interface statement codec covers only the
smaller public-`Statement` subset assigned to it.

`ProverTrace` records are nondecreasing by boundary rank, where
`BeforeFirstEvent` precedes every event and `PreAction(e)` has `e`'s exact
schedule rank. Records at the same boundary retain their supplied canonical
sequence order. The referenced obligation and output ordinal must exist, and
the output's declared domain and canonical value must equal the obligation's
domain at that ordinal. Unknown references, out-of-range ordinals,
wrong-domain values, noncanonical boundary order, and records outside this
closed grammar are `Malformed` invocation inputs and mint no Core outcome.

`RandomnessReplay` is a deterministic execution witness, not a randomness
oracle or semantic authority. Its statically visible record ranks must be
nondecreasing in the only possible attempt order: Core schedule order, and
within one prover pre-action the obligation basis order. At execution, its
next record must equal each exact dynamically attempted occurrence. A record must name the exact
`RandomnessRef`, source event, and same-domain canonical value or the exact
correlation-dependent failure tag. `IndependentSamplingFailed` is legal only
for `IndependentFresh`; `JointSamplingFailedAt(i)` is legal only for
`JointMember(..., i)` with that exact index. An independent outcome must be a member of the exact
single-attempt outcome relation exported by its authenticated
`DistributionContract`: a produced value must be in that contract's support,
and `IndependentSamplingFailed` is legal only when the contract declares its
`SamplingFailed` transition.
A joint member's outcome must satisfy the exact indexed conditional transition
of its authenticated joint contract given the prior successful group
components, including whether failure is possible at that index. Domain
membership alone is insufficient. These checks validate one replayed outcome;
they do not prove that an external producer sampled according to the declared
probabilities. A missing, reordered, mismatched, or extra replay record is
`Malformed` and yields no semantic conclusion. In a
probabilistic interpretation the declared distribution contracts generate
this replay. Fresh public challenges consume replay records; FS public
challenges are deterministically derived and checked through the admitted
`TranscriptConstruction`, so only private Core randomness consumes replay
records under FS. No replay value can override an FS derivation.

After this structural validation, prover-binding execution has one
deterministic transaction order. The typed records retain their exact supplied
order and boundary. Execution applies these rules:

1. before an obligation's source event, the first binding record for it in
   trace order immediately selects `EarlyOutput(that ordinal)`;
2. at the source boundary, compute `EventAttempted` first; if it is false, the
   first record for that obligation at this boundary selects
   `UnexpectedOutput(that ordinal)`;
3. if the source is attempted, inspect all records positioned at that event
   in trace order, and the first record repeating an already seen ordinal
   selects `DuplicateOutput(that ordinal)`;
4. if the binding shape is duplicate-free, attempt private randomness in the
   identity-bearing basis order and select the first
   `PrivateSamplingFailed(that randomness)`;
5. after all samples succeed, scan required output ordinals in increasing
   order and select `MissingOutput(the least absent ordinal)`; and
6. only if no rule selected a cause, bind every output once in ordinal order
   and enter the event action phase.

A record for an obligation whose source boundary has already closed selects
`UnexpectedOutput` when its later boundary is reached. A source event not
attempted because its guard is false consumes no successful binding. A record
for it is therefore early, unexpected at the source boundary, unexpected at a
later reached boundary, or an unconsumed residual if execution already stopped.
The first selected nonproduction cause ends Core execution, so a duplicate,
sample failure, and several missing outputs can never produce competing
`CoreExecutionOutcome`s. Records remaining after that outcome or after a
terminal do not replace the already selected outcome, but they are residual
records and make `AcceptProtocol` false. This precedence is Core semantics and
is recomputed from the trace plus obligation declaration; it is not a Plan,
endpoint, or implementation policy.

### 3.11 Operational trace meaning

For one structurally valid `CoreInvocationInputs`, `ProverTrace`, and
`RandomnessReplay`, Core execution is the finite transition relation:

```text
CoreState = {
  schedule_cursor,
  canonical values and objects,
  per-role knowledge,
  live claim resources,
  claim production/consumption occurrence sequence,
  active transcript occurrence sequence,
  wire occurrence sequence,
  check results,
  resolved failure-occurrence booleans and available failure-status tokens,
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

Step(Core, state, EventRef,
     exact records at this event's boundary,
     exact next randomness replay records)
  -> next state | CoreExecutionOutcome

ExecuteProtocol(
  AdmittedProtocol,
  CoreInvocationInputs,
  ProverTrace,
  RandomnessReplay,
  ExactProtocolExecutionCapabilities)
  -> Qualified<CoreExecutionRecord>
```

`ExecuteProtocol` first performs every input, trace, and replay check that is
independent of dynamic guards. During execution it checks the next replay
record at each actual attempt and rejects missing, mismatched, or residual
records as `Malformed`, discarding any provisional Core state rather than
minting a semantic outcome from an invalid witness.
The Core capability map contains every and only content-addressed dependency
actually evaluated by this execution—pure/object, distribution, check,
claim/reduction, codec/channel, or obligation contracts as applicable—and each
entry matches the admitted dependency view's exact kind, regime, content ID,
ABI, and direct edges. Closed finite terms use the evaluator fixed by the
semantic regime and require no map entry. Fresh requires
`transcript_algorithms = None`; FS requires every and only content-addressed
initialization, framing, atom-codec, and squeeze dependency retained by its
admitted construction. Missing, extra, or mismatched execution authority is
`Refused`; an operational implementation failure is `CheckerFailure` and
mints no Core outcome. Capabilities are neither identity-bearing nor retained,
and any conforming capability must realize the same admitted deterministic
transition relation over the explicit replay.
Starting from the two exact input maps, execution scans the total potential-event
schedule. It evaluates each canonical guard from earlier state, computes
`EventAttempted`, performs any Prover pre-action binding, and then performs the
closed event action exactly when `EventActionOccurs`. It records each
observation at the kind-specific attempt, action, or success point and stops at
the first terminal or `ProverDidNotProduce`. The residual final terminal guard
makes every still-live non-prover path total. A public-coin resolution attempt
always performs its exact Fresh sampling or FS derivation transition; failure follows its
declared effect, which either terminates or records a status and continues,
while only success publishes the challenge value. Failure to supply,
duplicatively or prematurely bind, or privately sample an attempted prover
obligation yields the distinct Core-owned `ProverDidNotProduce` outcome rather
than inventing a verifier terminal. Every action-occurring prover obligation
is bound exactly once; duplicate, unexpected, missing, or early bindings are the same
nonproduction class. An event with a false attempt predicate has no message,
transcript, check, artifact, terminal, endpoint obligation, or prover
obligation occurrence; an attempted preparation or challenge failure has only
the exact observations and obligations assigned to that failure path.

`AcceptProtocol(admitted_protocol, inputs, prover_trace, randomness_replay,
exact_protocol_execution_capabilities)` holds
exactly when `ExecuteProtocol` returns a record whose outcome is an `Accept`
terminal, whose consumed prover-record count equals the complete supplied
`ProverTrace`, and
whose execution follows every active check's declared false effect and
satisfies every claim-resource rule. A
false check with `Terminate` cannot later accept; a false check with
`ContinueWithStatus` may participate in an explicit later compound decision.
`Reject` and `Abort` are first-class terminal outcomes, not checker failures.
Under an FS interpretation, the
public challenge values are produced by the admitted construction over the
active transcript prefix rather than supplied as fresh samples; every other
Core transition is unchanged.

This Core predicate deliberately does not consume statement-container bytes,
proof-container bytes, endpoint calls, or runtime suppliers. A
`ProtocolInterface` can decode the public-`Statement` assignment subset and
the payload occurrences of proof-channel messages, but it does not invent the
remaining `CoreInvocationInputs`, decompose arbitrary message payloads into
prover-obligation outputs, choose private inputs, or construct a randomness
replay. The Stage 4B OIR/Realization bridge must map authenticated endpoint
inputs, decoded message occurrences, and explicit supplier results to this
closed invocation grammar and prove their agreement. Until that bridge exists,
Interface preservation is a typed correspondence claim rather than a complete
runtime invocation claim.

The admitted Protocol capability is a required execution input, not a raw
`Protocol` value or `ProtocolId`. Its retained authenticated dependency views
supply the Fresh distribution-transition contracts. For FS it additionally
retains the exact admitted `TranscriptConstruction` and its algorithm
dependencies required to interpret `DeriveChallenge`; the ID stored in the
canonical PIR graph is insufficient execution authority. Execution attenuates
these views for the duration of the operation but cannot widen or serialize
them.

This operational relation defines Protocol behavior. A later probabilistic or
cryptographic denotation interprets its explicit distributions, traces, and
assumptions; it does not replace the Core meaning.

### 3.12 Core admission predicate

`CoreAdmissible_R(C)` is the conjunction of:

```text
closed dependency kinds and authenticated least dependency closure
exactly one Prover, exactly one Verifier, and zero or one PublicEnvironment
typed roles, ports, values, objects, events, claims, reductions, and checks
all local references in bounds and of the declared kind
value/object and claim graphs acyclic
causal graph acyclic
schedule is a total permutation and extends every causal edge
canonical reduced guard forms, directly recomputable equality/implication,
role-knowledge and path-availability closure, and residual fallback terminal
private and public randomness distribution/correlation closure
challenge prefix and distribution closure
message direction, channel, role, and wire-codec consistency
claim production, linearity, routing, and terminal closure
check/failure-source/failure-effect/terminal and terminal-payload totality
protected-observation classification completeness
endpoint- and prover-obligation recomputation equality
prover-obligation-failure recomputation and reference closure
no unresolved choice, symbol, external policy, or ambient semantic read
```

This is structural and semantic admission of the Protocol subject. It proves
neither relation satisfaction nor any cryptographic property.

## 4. Protocol and identity

### 4.1 Challenge interpretation

```text
ChallengeInterpretation =
    FreshPublicCoins
  | FiatShamir(TranscriptConstructionId)

Protocol = {
  core: InteractiveCore,
  challenge_interpretation: ChallengeInterpretation
}
```

`FreshPublicCoins` interprets every Core challenge through its declared public
distribution. `FiatShamir` interprets the same challenge occurrences through
one exact transcript construction. The two are different Protocols over the
same Core.

Every challenge exposes one Core-owned interpretation-failure continuation.
In v0, only its `SqueezeAndSampleRule` may fail at Protocol execution time, and
its closed failure sum is exactly the linked sampling/rejection failure mapped
by `abort_map`. Transcript initialization, session-context initialization,
framing, and every absorbed-atom codec are required to be total and infallible
over their already admitted typed semantic domains. Malformed external byte
decoding occurs before Protocol execution at Interface or a later wrapper and
cannot become an ambient transcript failure. If a construction needs another
runtime failure, it is not a construction over this Core; a future regime must
add an occurrence-exact transcript-failure source, or the changed behavior
requires a different Core and `CoreId`. If the permitted challenge failure has
a continuing effect, no later guard may read an unavailable challenge value.

### 4.2 Identity algebra

```text
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

or

ProtocolId = H(
  "zkc/protocol",
  ProtocolSemanticRegimeId,
  CoreId,
  FiatShamir,
  TranscriptConstructionId)
```

The FS initialization binds `CoreId`, `TranscriptConstructionId`, and exact
application/session context, not `ProtocolId`; this avoids a circular
construction in which the construction is needed to compute the Protocol ID
that initializes the construction. The construction body stores the closed
instruction `BindConstructionSelfId`, not a literal copy of its unknown ID.
Authentication first computes `TranscriptConstructionId` from the canonical
body, and execution interprets that instruction using the computed value. Thus
the identity preimage itself is not self-referential.

### 4.3 Protocol admission

`ProtocolAdmissible(P)` requires:

- `CoreAdmissible(P.core)` under the exact Protocol regime;
- a known challenge-interpretation tag;
- for Fresh, every challenge is supported by its exact distribution;
- for FS, an authenticated and admitted construction whose scoped `CoreId`
  equals the Core, whose occurrence and prefix domains are complete, and whose
  framing and deterministic derivation contracts structurally close; and
- exact identity recomputation.

Admission does not require an `FSCompile` theorem basis. Thus a constructed FS
Protocol remains meaningful and admitted even when no security theorem is
available.

### 4.4 Core authority topology

`CoreId` is a semantic subidentity, not a second official v0 artifact family.
The canonical carrier has one Protocol root containing one Core body and one
challenge interpretation. Core authentication and `CoreAdmissible` are
subchecks of Protocol authentication/admission. Successful Core sub-admission
mints a transaction-scoped `CoreAdmissionWitness` used only to close
dependencies required for the enclosing Protocol admission. It is not an
official artifact, cannot leave the admission transaction, and asserts no
challenge interpretation. After full Protocol admission, an
`AdmittedCoreView` is an attenuated immutable view minted from the exact
`AdmittedProtocol`; it likewise cannot be deserialized, widened back into
Protocol authority, or used to assert a challenge interpretation.

Cold admission of a standalone FS carrier is therefore acyclic:

```text
authenticate Core
  -> check CoreAdmissible and mint scoped CoreAdmissionWitness
  -> authenticate/admit TranscriptConstruction against that witness
  -> check FS Protocol admission
  -> mint AdmittedProtocol
  -> discard the transaction witness
```

A construction whose context is `Composed` cannot use that standalone path.
Its cold admission reruns the exact composition spec and child views, checks
the reconstructed Core against the persisted canonical candidate, mints a new
transaction-scoped formation authority, and follows
`ReplayAndAdmitComposedProtocol` in Section 10.2. A serialized
`CoreComposition` result record is never treated as the live
`CheckedCoreComposition` capability needed to
bootstrap this path.

Composition consumes these admitted Core views. A newly composed Core is not
officially persistent or consumer-authoritative until it is paired with a
Fresh or exact FS interpretation and the resulting Protocol is independently
authenticated and admitted. This avoids duplicate Core/Protocol roots while
retaining the Core factorization required by FS and composition.

`CoreId` identifies the exact bounded-normal-form Core encoding. It is not a
quotient over all behaviorally equivalent protocols. Two differently encoded
but observationally equivalent Cores may have different IDs and may later be
related by an observer-indexed `CoreEq` or `TraceEq` judgment.

## 5. Canonical PIR

### 5.1 Exact carrier profile

Canonical PIR is one MLIR operation graph with exactly one `pir.protocol`
root. The v0 semantic operation allowlist is:

```text
pir.protocol
pir.core
pir.dependency
pir.role
pir.port
pir.value
pir.object
pir.randomness
pir.event
pir.challenge
pir.claim
pir.reduction
pir.check
pir.failure
pir.terminal
pir.endpoint_obligation
pir.prover_obligation
pir.prover_obligation_failure
```

Only an explicit minimal allowlist of builtin scalar, array, dictionary, and
type primitives may appear. Locations are absent. No other dialect operation,
unknown attribute, symbol name,
source location, comment, author label, cache, analysis result, Interface,
Plan, relation material, proof, or provenance is legal.

For an FS Protocol the root stores only the exact
`TranscriptConstructionId`. The construction is a separate satellite subject;
its canonical preimage is supplied in the named admission dependency bundle
and authenticated under its own regime. It is never nested as a
`pir.transcript_construction` operation in the Protocol graph. Therefore
`Lower_R` and `Read_R` remain a bijection over exactly Protocol semantics,
while whole-Protocol admission closes the external construction dependency.

The root regions and operation groups occur in the field order of Sections 3
and 4. Every group has one block. Positional references use canonical ordinals;
there are no semantic SSA names or symbol-table lookups. All defaults are
explicit. All unordered maps use canonical semantic-key order. The root
contains the claimed regime and IDs, which authentication recomputes.

### 5.2 Bijection

For regime `R`, the bijection domain contains only physically canonical graphs
whose claimed regime and IDs equal direct recomputation:

```text
Lower_R : Protocol -> IdConsistentCanonicalPirGraph_R
Read_R  : IdConsistentCanonicalPirGraph_R -> Protocol

Read_R(Lower_R(P)) = P
Lower_R(Read_R(G)) = G modulo CarrierTrivia
```

A raw graph with a wrong claimed regime, `CoreId`, or `ProtocolId` may be
structurally parseable, but it is outside this domain. An internal
`ReadUnchecked` used during diagnostics has no round-trip or semantic-authority
law. Authentication establishes ID consistency before exposing `Read_R` or an
authenticated candidate.

The complete `CarrierTrivia` relation contains only:

```text
MLIR in-memory operation identity
SSA alpha-renaming when a builtin carrier requires names
```

Textual spelling, bytecode encoding, attribute insertion order, omitted
defaults, alternative symbol names, and arbitrary metadata are not additional
canonical forms. They are either transport variation outside the graph or
authentication failures.

### 5.3 Authentication versus admission

The complete external authentication input is explicit:

```text
CanonicalTranscriptConstructionCandidate =
  unauthoritative canonical algebraic value of TranscriptConstruction

ExactTranscriptConstructionCandidateAndDependencyPreimages = {
  candidate: CanonicalTranscriptConstructionCandidate,
  algorithm_dependencies:
    ExactTranscriptAlgorithmDependencyPreimageBundle
}

ExactProtocolDependencyPreimageBundle = {
  core_dependencies:
    ExactMap<DependencyRef, AuthenticatedDependencyPreimageInput>,
  transcript_construction:
    None
    | ExactTranscriptConstructionCandidateAndDependencyPreimages
}

ExactCoreDependencyAuthenticationCapabilities =
  ExactMap<DependencyRef,
           DependencyAuthenticationCapability restricted to the exact
           kind, regime, content identity, ABI, and direct-edge declaration>

ExactProtocolDependencyAuthenticationCapabilities = {
  core: ExactCoreDependencyAuthenticationCapabilities,
  transcript:
    None | ExactTranscriptDependencyAuthenticationCapabilities
}

AuthenticateCanonicalPir_R(
  raw,
  ExactProtocolDependencyPreimageBundle,
  ExactProtocolDependencyAuthenticationCapabilities)
  -> AuthenticatedCanonicalProtocolCandidate
```

Fresh requires `transcript_construction = None`; FS requires exactly one
candidate whose recomputed ID equals the root's
`TranscriptConstructionId`. The Core map must contain every and only member of
the candidate Core's least dependency closure. Checker implementations and
process capabilities needed to authenticate a preimage are the exact third
operation input, not fields of this bundle or semantic identity; every typed
capability must match the subject/dependency identity it checks. Fresh requires
`transcript = None` in the capability record; FS requires exactly the matching
transcript-dependency capability set. The Core capability map has exactly the
same keys as `core_dependencies`, and the transcript capability set has
exactly the construction closure's keys. Missing, extra, wrong-kind,
wrong-regime, or wrong-identity authority is refused.

`AuthenticateCanonicalPir_R` performs, in order:

1. transport decoding and MLIR structural parsing;
2. exact root count and closed allowlist checking;
3. physical field, block, operation, reference, default, and ordering checks;
4. `ReadUnchecked_R` into a candidate semantic object with no authority or
   round-trip law;
5. authentication of every named Core dependency preimage from the explicit
   bundle and verification of the declared least dependency closure; for FS,
   separate authentication of the supplied construction preimage and its
   dependencies to the exact referenced construction ID; and
6. recomputation of `CoreId` and `ProtocolId`, including the exact referenced
   `TranscriptConstructionId` in the latter preimage; then
7. establishment of the `IdConsistentCanonicalPirGraph_R` predicate and only
   then exposure of `Read_R` and the authenticated candidate.

Success yields an immutable authenticated candidate, not admission authority.

For FS admission, the separately supplied construction preimage is
authenticated to the referenced `TranscriptConstructionId` and admitted in the
acyclic transaction described in Section 4.4. Canonical PIR authentication
does not pretend that an ID alone authenticates that dependency.

```text
ExactProtocolAdmissionCheckerCapabilities = {
  core: ExactCoreAdmissionCheckerCapabilities,
  transcript:
    None | ExactTranscriptLawCheckerCapabilities
}

AdmitProtocol(
  AuthenticatedCanonicalProtocolCandidate,
  retained exact Protocol dependency views,
  CompositionContextAuthority,
  ExactProtocolAdmissionCheckerCapabilities)
  -> AdmittedProtocol
```

`AdmitProtocol` runs Core admission and mints a transaction-scoped
`CoreAdmissionWitness` internally. For FS it then invokes
`AdmitTranscriptConstruction` using the retained authenticated construction
and algorithm dependency views, that witness, the exact context authority,
and the required identity-matched transcript law checker. Fresh requires
`transcript = None`; FS requires exactly the matching capability. Missing,
extra, or wrong-construction checker capabilities are refused. It then runs
`ProtocolAdmissible` and discards the witness. Fresh and a
standalone FS construction require `NoCompositionContext`; a composed FS
construction requires the matching scoped-formation or checked-composition
authority described below. Success mints an opaque process-local
`AdmittedProtocol` capability. The capability has no serialized form and no
independent semantic identity.

### 5.4 Information-loss ledger

| Authoring distinction | Before erasure | Canonical destination |
|---|---|---|
| partial or unspecified order | schedule-selection and ambiguity checks | one total `schedule` |
| macros, modules, synthesis requests | elaboration and termination checks | elaborated Core nodes only |
| human and source names | duplicate and binding checks | Interface candidate, source map, or erased diagnostics |
| implicit defaults | default-selection check | explicit canonical field |
| imported symbols | exact resolution-closure check | typed dependency ID and ABI |
| relation descriptions | binding classification | separate Relations candidates or opaque Core declarations |
| prover construction routes | semantic-change classification | separate Plan candidate or Protocol behavior |
| source locations and provenance | diagnostic/provenance capture | nonsemantic side output |
| order proved observer-inert | proof/check before erasure | canonical semantic-key order |
| protected effect or observation | never erased | explicit event, edge, codec, failure, or terminal field |

The normalizer may emit several separately typed outputs. Success of one output
does not authenticate or admit another.

Normalization may identify only a finite, regime-declared authoring quotient.
Every refusal-sensitive distinction is checked before its erasure. Admission
of a directly supplied canonical graph establishes only the canonical subject;
it cannot retroactively establish source-language well-formedness, provenance,
macro-expansion, or information-preservation claims about an absent authoring
input.

The mandatory front-end boundary is:

```text
NormalizeAuthoring(
  AuthoringUnit,
  exact resolved read-closure snapshot,
  AuthoringNormalizerContract,
  ProtocolSemanticRegime)
  -> Qualified<
       CanonicalProtocolCandidate,
       InterfaceCandidate*,
       ProverPlanCandidate*,
       NormalizationAudit<ProtocolAuthoring>>
```

The normalizer contract names one authoring language/profile, its finite
declared syntax quotient, every pre-erasure validation rule, the complete
mapping into canonical Core constructs, and its exact immutable dependencies.
`NormalizationAudit` records each source distinction as retained in Protocol,
extracted to a typed satellite/side output, proved quotient-neutral under the
declared authoring contract, or rejected before erasure. Unknown distinctions
and protected-observer changes are refused.

The operation is deterministic over its named inputs but remains an
unauthoritative producer. It neither authenticates nor admits any output. Two
authoring inputs may yield the same candidate only through the declared finite
quotient and identical resolved semantics. This contract lets P1 test the
information-loss frontier without standardizing one universal authoring IR.

## 6. `ProtocolInterface`

### 6.1 Complete subject

```text
ProtocolInterface = {
  protocol_id: ProtocolId,
  algorithm_dependencies:
    CanonicalMap<InterfaceAlgorithmDependencyRef,
                 InterfaceAlgorithmDependencyDecl>,
  external_ports: CanonicalSeq<ExternalPort>,
  role_entries: CanonicalMap<ExternalEntryName, RoleRef>,
  proof_trace_binding: GuardedProofTraceBinding,
  statement_binding: LosslessStatementBinding,
  external_outcomes: CanonicalSeq<InterfaceOutcome>,
  application_bindings: CanonicalSeq<ApplicationBinding>
}

ExternalPort = {
  name: ExternalEntryName,
  direction: Input | Output,
  external_domain: CanonicalExternalValueDomain,
  protocol_port: PortRef,
  representation:
      StatementContainerMember
    | IndependentValueCodec(LosslessContainerCodec)
}

InterfaceOutcome = {
  terminal: TerminalRef,
  external_tag: CanonicalOutcomeTag,
  payload_binding: CanonicalSeq<ValueRef>,
  payload_codec: LosslessContainerCodec
}

ApplicationBinding = {
  application_role: CanonicalApplicationRole,
  target: ExternalPortRef | EventRef | InterfaceOutcomeRef
}

InterfaceAlgorithmDependencyKind =
    LosslessContainerCodecContract
  | SemanticEncoderContract
  | TaggedSemanticDecoderContract

InterfaceAlgorithmDependencyDecl = {
  kind: InterfaceAlgorithmDependencyKind,
  contract_regime_id: InterfaceAlgorithmContractRegimeId,
  content_id: RegimeQualifiedInterfaceAlgorithmContractId,
  direct_dependencies: CanonicalSeq<InterfaceAlgorithmDependencyRef>,
  interface_facing_abi: ExactInterfaceAlgorithmAbi
}
```

The dependency map is identity-bearing. Every
`ContentAddressedContractRef` reachable from an Interface codec, encoder, or
decoder matches exactly one declaration of the same kind, regime-qualified
content ID, direct dependency IDs, and ABI; every `ClosedFiniteTerm` has no
external entry. The map is exactly the least reachable closure of those direct
references. Duplicate aliases, an unused entry, an undeclared transitive read,
or a same-digest regime/kind/ABI mismatch reject.

The statement binding is not a placeholder for implementation policy:

```text
ProtocolPublicStatementOccurrenceRef =
  InputPortOccurrenceRef restricted to a port whose visibility is Public and
  whose semantic_purpose is Statement

ProtocolPublicAssignment<P: ProtocolId> = {
  protocol_id: P,
  values:
    TotalMap<ProtocolPublicStatementOccurrenceRef in P,
             CanonicalSemanticValue in the exact referenced port domain>
}

CanonicalPublicAssignmentDomain(P: ProtocolId) =
  the canonical dependent-map domain of every and only
  ProtocolPublicAssignment<P>

LosslessStatementBinding = {
  external_domain: CanonicalExternalStatementDomain,
  protocol_domain: CanonicalPublicAssignmentDomain(protocol_id),
  shape:
      OneToOne(StatementExternalOccurrenceRef)
    | FixedProduct(TotalCanonicalStatementFieldMap)
    | FixedSequence(TotalCanonicalStatementPositionMap),
  encode: TotalSemanticEncoder,
  decode: TotalTaggedSemanticDecoder
}

StatementExternalOccurrenceRef =
  (ExternalPortRef restricted to StatementContainerMember,
   occurrence_ordinal)

TotalCanonicalStatementFieldMap =
  Bijection<CanonicalExternalStatementFieldRef,
            StatementExternalOccurrenceRef>

TotalCanonicalStatementPositionMap =
  Bijection<CanonicalExternalStatementPosition,
            StatementExternalOccurrenceRef>

decode(encode(x)) = Decoded(x)
encode is injective over protocol_domain
every Decoded external statement yields exactly one protocol assignment
```

The assignment map contains one value for every and only public input port
occurrence of the dependent Protocol whose purpose is `Statement`. Each value
is canonical under that occurrence's exact domain. Missing, extra,
wrong-Protocol, wrong-occurrence, or wrong-domain entries are outside
`CanonicalPublicAssignmentDomain`; container decoding cannot manufacture a
partial assignment.

The closed shape sum fixes how external positions and Protocol ports are
partitioned; no unspecified “declared partition” law remains. The binding's
typed `encode` and `decode` are the sole identity-bearing
statement-container byte language: `encode` maps its exact Protocol assignment
domain through the declared external shape to bytes, while `decode` is total
over all byte strings and reconstructs that exact assignment or a tagged
non-success. There is no second outer statement codec that can vary
independently.

Every and only external port that maps to a public input Protocol port with
semantic purpose `Statement` uses `StatementContainerMember`; it carries no
independent value codec. Expanding multiplicities yields the exact
`StatementExternalOccurrenceRef` range, and the selected shape is a total
bijection over that range. Each external field/position domain equals the
mapped external port domain, which in turn is losslessly equivalent to the
exact Protocol occurrence domain under the one statement encoder/decoder.
Every other external port uses `IndependentValueCodec`, whose direct
round-trip law is checked separately. Thus statement shape, external ports,
and byte language are one connected description rather than competing codecs.

Proof binding ranges over exactly the potential `Message` occurrences whose
channel is `Proof`, not every Core event:

```text
ProofEventOccurrencePredicateRef =
  EventActionOccurrence(ProofChannelMessageEventRef)

GuardedProofTraceBinding = {
  potential_positions:
    Bijection<ExternalProofPosition, ProofChannelMessageEventRef>,
  position_presence:
    TotalMap<ExternalProofPosition,
      AlwaysOccurs(ProofEventOccurrencePredicateRef)
      | OmittedWhenNotOccurs(ProofEventOccurrencePredicateRef)
      | ExplicitNonOccurrenceTag(ProofEventOccurrencePredicateRef,
                                 CanonicalTag)>,
  active_order: ExactScheduleSubsequence,
  encode_active_trace: TotalSemanticEncoder,
  decode_bytes: TotalTaggedSemanticDecoder
}
```

`ProofEventOccurrencePredicateRef` is a restricted
`EventActionOccurrenceRef` with no
independent predicate body, identity, or capability: it denotes exactly the
named event's `EventActionOccurs` predicate. Admission proves that the
potential-position bijection covers every and only
proof-channel message event, each presence condition equals the event's Core
`EventActionOccurs` predicate, `AlwaysOccurs` is used only when that predicate is
true on every admitted execution, omission is unambiguous or explicitly
tagged, and every realized external trace preserves exact Core schedule order.
The decoder reconstructs a guarded potential-position trace; Protocol
execution later checks which subsequence is realized, so Interface decoding
does not execute the verifier. Thus bounded guarded Protocols need not pretend
that every potential proof occurrence is present merely because its local
activation guard is true.

`encode_active_trace` and `decode_bytes` are likewise the sole
identity-bearing proof-container byte language and are exact inverses on the
guarded semantic trace domain under the tagged-decoder laws below. There is no
independent outer proof codec or unrecorded composition step.

External names are Interface semantics and enter Interface identity. Container
codecs may change packaging only under these exact laws. The semantic encoder
is total over every value or trace in the Protocol domain. The byte decoder is
total as a tagged function over all byte strings:

```text
Decode(bytes) = Decoded(semantic_value_or_trace)
              | Malformed(exact structural reason)

Decode(Encode(x)) = Decoded(x)
Encode is injective over the semantic domain
Decoded bytes reconstruct exactly one canonical semantic value or trace
```

This does not mean every byte string is accepted. Different Interfaces may
have different external byte languages while preserving the same Protocol
semantic trace language. Interface decoding occurs outside the Protocol
transcript boundary: it must not reorder canonical proof occurrences before
transcript interpretation, change canonical message bytes, select transcript
framing, or affect challenge derivation.

Codec decoding is pure and has no caller-authority, feature-availability, or
environment input. Such conditions therefore cannot produce a decoder
refusal. Explicit invocation capabilities, unavailable runtime features,
value-range restrictions, authorization policy, semantic defaults, and
application acceptance rules remain Stage 4B OIR/Realization or wrapper
concerns. If one changes Protocol acceptance, it requires a wrapper/new
Protocol rather than an Interface decoder branch.

An application binding gives a typed external role to an exact Protocol port
or occurrence. A relation-specific interpretation remains a Relations-owned
`RelationBinding`; an Interface cannot assert correspondence by naming a role.
Every external port preserves direction, domain, and multiplicity. An
`IndependentValueCodec` round-trips its one mapped Protocol port directly; a
`StatementContainerMember` is encoded only through the one connected
statement binding above. Every occurrence of every public Protocol input port
whose purpose is `Statement` occurs exactly once in that statement binding,
with no ordinal alias or omission; every potential proof message occurs exactly once in the
guarded proof binding. `external_outcomes` is a total bijection over Core
terminal declarations: one entry per `TerminalRef`, no duplicates, and tags
injective across terminals. Its payload binding is exactly that terminal's
ordered `public_outputs`, and the codec round-trips the complete typed tuple.
A complete Protocol execution therefore selects exactly one external terminal
tag and payload. A terminating failure is represented through the terminal
named by its effect; a continuing failure remains a nonfinal Protocol
observation and cannot acquire a second Interface outcome tag. Distinct
failure or reach causes that callers must distinguish require distinct Core
terminals. `ProverDidNotProduce` is a producer-trace outcome, not an Interface
terminal; malformed decoding remains the separate pre-Protocol codec outcome
above. Application roles are closed labels under the
Interface regime and grant no authority or policy.

For an external output port, this mapping fixes only the typed value grouping
and lossless external representation. It does not create a Core occurrence or
claim that the value is available on any execution path. Terminal payloads
have the exact exposure semantics of `external_outcomes`; every other external
output requires Stage 4B to bind an OIR exposure occurrence and discharge the
corresponding `AvailableAt` and visibility obligations.

### 6.2 Identity and admission

```text
ProtocolInterfaceId = H(
  "zkc/protocol-interface",
  InterfaceSemanticRegimeId,
  ProtocolId,
  CanonicalEncode(ProtocolInterface))
```

Interface authentication recomputes physical form, dependency IDs, and the
dependent identity. Its external authority inputs are explicit:

```text
ExactInterfaceDependencyPreimageBundle =
  ExactMap<InterfaceAlgorithmDependencyRef,
           AuthenticatedInterfaceAlgorithmDependencyPreimage>

AuthenticateProtocolInterface(
  raw candidate,
  ExactInterfaceDependencyPreimageBundle,
  ExactInterfaceDependencyAuthenticationCapabilities)
  -> AuthenticatedProtocolInterfaceCandidate

AdmitProtocolInterface(
  AuthenticatedProtocolInterfaceCandidate,
  exact AdmittedProtocol view,
  retained exact Interface dependency views,
  ExactInterfaceLawCheckerCapabilities)
  -> AdmittedProtocolInterface
```

Authentication validates the closed physical form, authenticates every and
only preimage in the declared least dependency closure, checks its exact ABI
and edges, and recomputes `ProtocolInterfaceId`. The authenticated candidate
retains attenuated immutable dependency views; serialized IDs and live checker
implementations grant no authority. Interface admission consumes those views,
the exact admitted Protocol view, and only identity-matched law-checker
capabilities. It proves:

- every referenced port, role, event, check, failure, and terminal exists;
- maps are total over their declared external domains and injective wherever
  lossless recovery requires it;
- statement and proof decoding preserve canonical semantic values and event
  occurrences;
- container failures are classified before Protocol acceptance;
- no restriction, semantic default, transcript-visible rewrite, challenge
  change, check change, or accepted-language change occurs; and
- application bindings are well typed but make no relation claim.

If any preservation clause fails, the candidate is not an Interface. It must
be modeled as an external policy, a checked adapter into the Interface domain,
or a wrapper/new Protocol whose identity contains the changed behavior.

## 7. `ProverPlan`

### 7.1 Complete bounded subject

```text
ProverPlan = {
  protocol_id: ProtocolId,
  private_inputs: CanonicalSeq<PlanInput>,
  construction_nodes: CanonicalSeq<ConstructionNode>,
  holes: CanonicalSeq<TypedHole>,
  private_dependencies:
    CanonicalMap<PlanDependencyRef, PlanDependencyDecl>,
  supplier_requirements: CanonicalSeq<SupplierRequirement>,
  obligation_routes:
    CanonicalMap<ProverObligationRef, ObligationRoute>
}

PlanDependencyKind = ProverConstructionContract | SupplierContract

PlanDependencyDecl = {
  kind: PlanDependencyKind,
  contract_regime_id: PlanContractRegimeId,
  content_id: RegimeQualifiedPlanContractId,
  direct_dependencies: CanonicalSeq<PlanDependencyRef>,
  plan_facing_abi: ExactPlanContractAbi
}

PlanInput = {
  domain: ValueDomainContractRef,
  source:
      ProtocolPrivatePortOccurrence(PortOccurrenceRef)
    | ExternalSecret
}

PlanValueRef =
    ProtocolAvailableValueRef
  | PlanInputRef
  | ConstructionOutputRef
  | HoleOutputRef

PlanOperandRef =
    PlanValueRef
  | ProtocolAvailableObjectRef

ProtocolAvailableValueRef =
  ProtocolValue(ProtocolScopedRef<value> restricted to any value origin except
                `PortValue` of a private Prover input occurrence or
                `PrivateRandomnessValue` of a private-randomness occurrence)

ProtocolAvailableObjectRef =
  ProtocolObject(ProtocolScopedRef<object>)

ConstructionOutputRef = (ConstructionNodeRef, output_ordinal)
HoleOutputRef = (TypedHoleRef, output_ordinal)

PlanPrivateRandomnessRef =
  ProtocolScopedRef<randomness> restricted to RandomnessDecl entries whose
  purpose is PrivateProverSample

PrivateProtocolPlanInputRef =
  PlanInputRef restricted to a `PlanInput` whose source is
  `ProtocolPrivatePortOccurrence`

PlanBasisInputBinding =
    ProtocolAvailableValueRef
  | ProtocolAvailableObjectRef
  | PrivateProtocolPlanInputRef

ConstructionNode = {
  contract: ProverConstructionContractRef,
  inputs: CanonicalSeq<PlanOperandRef>,
  output_domains: CanonicalSeq<ValueDomainContractRef>,
  private_effect:
      PurePrivate
    | UsesProtocolRandomness(CanonicalSeq<PlanPrivateRandomnessRef>)
    | RequiresSuppliers(CanonicalSeq<SupplierRequirementRef>)
}

TypedHole = {
  contract: ProverConstructionContractRef,
  inputs: CanonicalSeq<PlanOperandRef>,
  output_domains: CanonicalSeq<ValueDomainContractRef>
}

SupplierRequirement = {
  target: PlanInputRef | TypedHoleRef | PlanPrivateRandomnessRef,
  contract: SupplierContractRef,
  multiplicity: ExactlyOne | FixedCount(n)
}

ObligationRoute = {
  producer: ConstructionNodeRef | TypedHoleRef,
  basis_input_map:
    TotalMap<ProverObligationInputOrdinal, PlanBasisInputBinding>,
  output_map:
    Bijection<ProverObligationOutputOrdinal, ProducerOutputOrdinal>
}

PlanSemanticClass =
    ProjectionRelevant
  | RealizationOnly
  | ExternalSupplyRequirement
```

Construction nodes form a pure or explicitly effect-typed private DAG.
Algorithms, parallelism, buffering, caching, and supplier selection may vary
only below already-fixed Protocol behavior.

Every `PlanOperandRef` is a closed typed reference. A
`ProtocolAvailableValueRef` or `ProtocolAvailableObjectRef` may name only a
same-kind operand available to the Prover at every derived route deadline; the object
variant preserves its exact Core object domain, owner, and visibility and
cannot be reinterpreted as a value. Every `PlanPrivateRandomnessRef` carries the Plan's exact
`ProtocolId` plus the occurrence-exact Core randomness reference.
`UsesProtocolRandomness` may name only private randomness already owned by the
routed obligation; it does not create or correlate a source. Its ordered
randomness references are the node contract's exact typed private-effect
inputs, distinct from the ordinary `inputs`, and must equal that contract
ABI's private-randomness input sequence in length, order, domains, and
purposes. A hole has no private-effect input channel. A hole's ordered
`inputs` are exact earlier `PlanOperandRef`s whose
domains equal its construction contract ABI; a hole is not an unbound
input-domain assertion. Supplier requirements are declarations, not live providers. Admission
checks node and hole input/output ordinals, contract domains, topological availability,
and that every referenced contract preimage is in the least closed
`private_dependencies` graph. `ProverConstructionContractRef` and
`SupplierContractRef` are typed `PlanDependencyRef`s of exactly their matching
kinds; Core dependency declarations cannot be reinterpreted as Plan contracts.

A private Prover input-port value has exactly one Plan ingress: the unique
`PlanInputRef` whose source is that `ProtocolPrivatePortOccurrence`.
`ProtocolAvailableValueRef` categorically excludes that origin on every node,
hole, and transitive operand edge, not only inside `basis_input_map`. A producer
therefore cannot cite both spellings or obtain the runtime secret without its
declared Plan input.

A Core `PrivateRandomnessValue(r)` likewise has exactly one direct Plan
ingress: `r` in one `UsesProtocolRandomness` effect sequence. The value-origin
form is categorically excluded from `ProtocolAvailableValueRef` on every node,
hole, basis binding, and transitive operand edge. Core values *derived from*
private randomness remain ordinary Core-declared values and may be cited when
their exact availability law holds; the raw sample itself may reach the Plan
only through the typed effect channel. Admission rejects any direct or
transitive Plan spelling that would bypass that channel or disguise the raw
sample as an ordinary operand.

`PlanInput`, holes, private dependencies, and supplier requirements are
semantic descriptors and typed requirements only. Runtime secret values,
supplier handles, process-local capabilities, mutable provider state, and
credentials never enter `CanonicalEncode(ProverPlan)` or `ProverPlanId`; they
are occurrence-local inputs resolved only when a Plan is executed.

Plan timing and private-randomness ownership are derived, never supplied by an
undefined route point. Let `DownstreamObligationRoutes(x)` be the exact
nonempty set of obligation-map keys whose routed producer transitively depends
on node or hole `x` through `PlanOperandRef` edges. Admission rejects a node or
hole with an empty set. For each Protocol value/object operand read by `x` and
each `o` in that set, it directly proves

```text
EventAttempted(source_event(o))
  implies AvailableAt(Prover, operand, PreAttempt(source_event(o)))
```

under the Core's exact path formulas. This checks every deadline separately,
including mutually exclusive routes; textual node order or the earliest
unconditional event is not a timing surrogate.

For `UsesProtocolRandomness(rs)`, every `r` has exactly one owning Core prover
obligation through its recomputed randomness/backlink family,
`DownstreamObligationRoutes(node)` is exactly that singleton owner, and `r`
appears in exactly one Plan node's private-effect sequence. That node is
evaluated after `r`'s exact successful private-sampling step and before the
owner obligation's outputs are bound. Reuse must flow through the node's
ordinary outputs; a second private-effect occurrence would ambiguously imply a
second consumption and rejects. Thus a random source cannot drift to another
route merely because domains or suppliers match.

### 7.2 Identity, admission, and `PlanRealizes`

```text
ProverPlanId = H(
  "zkc/prover-plan",
  PlanSemanticRegimeId,
  ProtocolId,
  CanonicalEncode(ProverPlan))
```

The authority path is explicit:

```text
ExactPlanDependencyPreimageBundle =
  ExactMap<PlanDependencyRef, AuthenticatedPlanDependencyPreimage>

AuthenticateProverPlan(
  raw candidate,
  ExactPlanDependencyPreimageBundle,
  ExactPlanDependencyAuthenticationCapabilities)
  -> AuthenticatedProverPlanCandidate

AdmitProverPlan(
  AuthenticatedProverPlanCandidate,
  exact AdmittedProtocol plan-typing view,
  retained exact Plan dependency views,
  ExactPlanLawCheckerCapabilities)
  -> AdmittedPlan
```

Authentication validates closed physical form, authenticates every and only
preimage in the identity-bearing least `private_dependencies` closure, checks
kind/regime/ABI/edge equality, and recomputes `ProverPlanId`. The candidate
retains attenuated immutable dependency views. Admission checks same exact
`ProtocolId`, referenced Protocol occurrence existence and domain at the
derived route deadlines, local references, DAG acyclicity, contract typing, hole
contracts, supplier requirement form, route form, and identity using only the
exact Protocol view, retained dependency views, and identity-matched checker
capabilities. Serialized IDs, dependency declarations, and checker code grant
no authority.

Plan admission does not check total obligation coverage, conclude that the
Plan realizes the Protocol, or classify fields against an OIR schema that does
not yet exist.

```text
PlanRealizes(AdmittedProtocol, AdmittedPlan, PlanRealizesRegime)
  -> Qualified<CheckedPlanRealizes>
```

This separate relation checks:

```text
same exact ProtocolId
every `ProtocolPrivatePortOccurrence` names one in-range input occurrence whose
  port is owned by Prover, has visibility `PrivateToRole`, and has exactly the
  PlanInput domain; every such Protocol occurrence is covered once, and two
  PlanInputs cannot alias it (reuse cites the one `PlanInputRef`)
every `ExternalSecret` uses its enclosing `PlanInputRef` as the collision-free
  Plan-local requirement identity and cannot masquerade as a Protocol port
  occurrence
every prover obligation has exactly one total route to its exact typed output
every route's `basis_input_map` contains every and only obligation input
  ordinal. A Core operand that is exactly `PortValue(o)` for a private Prover
  input must map to the unique `PrivateProtocolPlanInputRef` whose source is
  `ProtocolPrivatePortOccurrence(o)`; every other operand maps to the
  same-kind exact `ProtocolAvailableValueRef` or
  `ProtocolAvailableObjectRef`. Each binding is a transitive dependency of
  the routed producer and preserves occurrence and domain. An
  `ExternalSecret` Plan input cannot satisfy a Core basis ordinal
for every routed obligation `o`, let `RouteRandomnessIngresses(o)` be the
  canonical sequence of all `PlanPrivateRandomnessRef`s in
  `UsesProtocolRandomness` effects in the routed producer's transitive
  dependency subgraph, ordered by canonical construction-node ordinal and then
  by effect-input ordinal. This sequence equals `o.private_randomness`
  exactly. Thus every required source has one and only one owner-matched typed
  effect ingress, no unrelated source enters the route, and the Core basis
  order is preserved; a hole or `PurePrivate` node cannot stand in for a
  required sample
every route input is available from Protocol values or objects, Plan inputs, earlier
  construction nodes, or an explicit typed hole/supplier requirement
outputs match the obligation contract and domain
the Plan grammar contains no reference or constructor that can create,
  replace, reorder, retype, or delete Core events, messages, randomness,
  transcript actions, checks, failures, terminals, identities, or accepted
  language; routes may bind only exact ProverObligationOutput references
all Plan reads are in the declared closure
```

Affirmative `PlanRealizes` proves structural obligation coverage only. It does
not prove the values correct or distributionally faithful, witness validity,
provider correctness, honest-prover completeness, termination, cost,
performance, acceptance, or successful proof production. Those claims require
later realization, completeness, or property judgments over explicit models.

### 7.3 Placement constraints exported to Stage 4B

`PlanSemanticClass` is an exported classification vocabulary and rule, not a
self-asserted Plan field and not part of Plan admission. Stage 4B must compute
and check the classification against its exact projection/OIR semantics; a
Plan producer cannot grant a field permission to be read at one layer.

A Plan field is `ProjectionRelevant` exactly when substituting it while fixing
Protocol and Interface can change canonical prover OIR event/value dependency
structure, OIR-local inputs, or OIR-local failure/control structure without
changing verifier-visible Protocol semantics. If any such field is read,
prover projection consumes `InterfaceAndPlan` and the resulting OIR identity
commits to the full exact `ProverPlanId`.

A field is `RealizationOnly` when it selects an algorithm, schedule, buffer,
resource, implementation, or supplier below an already fixed OIR obligation.
It cannot be read by projection.

An `ExternalSupplyRequirement` declares a typed need but does not decide where
its live provider is resolved. Stage 4B must classify whether the requirement
changes OIR's explicit input contract or is satisfied below OIR. It may not be
read ambiently at both layers.

The Stage 4B reader must report its exact Plan field read set, classification,
and an adequacy check. Verifier projection never consumes Plan.

## 8. Relations ontology

### 8.1 Subject separation

```text
RelationDefinitionRef = {
  owner_regime: RelationDefinitionRegimeId,
  definition_id: RelationDefinitionId
}

RelationDependencyKind =
    RelationValueDomainContract
  | RelationObjectDomainContract

RelationDependencyDecl = {
  kind: RelationDependencyKind,
  contract_regime_id: RelationContractRegimeId,
  content_id: RegimeQualifiedRelationContractId,
  direct_dependencies: CanonicalSeq<RelationDependencyRef>,
  relation_facing_abi: ExactRelationContractAbi
}

RelationPort = {
  value_domain: RelationValueDomainContractRef,
  multiplicity: ExactlyOne | FixedCount(n)
}

RelationPublicValueRef =
  (RelationPublicPortRef, occurrence_ordinal)

RelationWitnessValueRef =
  (RelationWitnessPortRef, occurrence_ordinal)

CommittedObjectRole = {
  semantic_object_domain: RelationObjectDomainContractRef,
  commitment_value_domain: RelationValueDomainContractRef,
  material_value_domain: RelationValueDomainContractRef,
  multiplicity: ExactlyOne | FixedCount(n)
}

RelationCommittedObjectRef =
  (CommittedObjectRoleRef, occurrence_ordinal)

RelationResultRole = {
  output_domain: RelationValueDomainContractRef,
  accepted_values: NonEmptyCanonicalSet<CanonicalSemanticValue>
}

RelationInterface = {
  definition: RelationDefinitionRef,
  dependencies:
    CanonicalMap<RelationDependencyRef, RelationDependencyDecl>,
  public_ports: CanonicalSeq<RelationPort>,
  witness_ports: CanonicalSeq<RelationPort>,
  committed_objects: CanonicalSeq<CommittedObjectRole>,
  accepted_result: RelationResultRole
}

RelationInstance = {
  interface_id: RelationInterfaceId,
  public_values:
    TotalMap<RelationPublicValueRef, CanonicalSemanticValue>
}

PrivateWitnessAssignment = {
  instance_id: RelationInstanceId,
  interface_id: RelationInterfaceId,
  local_occurrence: UnlinkableLocalRef,
  private_values:
    TotalSecretMap<RelationWitnessValueRef, SecretValueCapability>
}

RelationArtifactProfile = {
  byte_language: ExactByteLanguageContractRef,
  byte_identity_domain: ExactRawBytes,
  fact_schema: ClosedRelationArtifactFactSchema,
  structural_limits: CanonicalArtifactLimits,
  malformed_reason_schema: ClosedMalformedReasonSchema
}

RelationAdapterContract = {
  profile_id: RelationArtifactProfileId,
  interpreter_dependency: ExactDeterministicInterpreterContractRef,
  emitted_fact_schema: ClosedRelationArtifactFactSchema,
  unread_field_schema: ClosedUnreadFieldSchema,
  outcome_schema: Completed | Malformed | Unsupported | Refused
}

RelationAdapterRef = {
  profile_id: RelationArtifactProfileId,
  adapter_id: RelationAdapterId,
  adapter_regime_id: RelationAdapterRegimeId
}

ExactByteLanguageContractRef =
  TypedRelationArtifactProfileDependencyRef restricted to the exact
  byte-language contract kind

ExactDeterministicInterpreterContractRef =
  TypedRelationAdapterDependencyRef restricted to the exact deterministic
  interpreter contract kind
```

The relation definition is owned externally. Its content identity and regime
are cited opaquely unless an explicitly selected adapter can authenticate that
definition language. zkc admission of an interface proves only its exact
declared contract, not the truth, satisfiability, or faithful formalization of
the external predicate.

Every multiplicity expands to the collision-free occurrence range used by the
three occurrence-reference constructors above; `FixedCount(n)` requires
canonical positive `n`. Public and witness sequences provide role by
position, so a port cannot be reclassified through a reference. Each accepted
result value is canonical under `output_domain`, and the set is nonempty and
duplicate-free. A committed-object occurrence names separately the semantic
object domain, commitment-value domain, and canonical material domain; equality
of any two domains is never inferred from a shared encoding.

The dependency map is identity-bearing. Its direct references are exactly the
domain contracts used by ports, committed-object roles, and the result role;
its full contents are exactly the least reachable dependency closure under
`direct_dependencies`. Equal unqualified digests under different regimes or
ABIs do not alias. Authentication consumes exact preimages for this closure;
no ambient registry, mnemonic, loaded backend, or live checker can satisfy a
relation dependency.

### 8.2 Identity algebra

```text
RelationInterfaceId = H(
  "zkc/relation-interface",
  RelationInterfaceRegimeId,
  RelationDefinitionRef,
  CanonicalEncode(RelationInterface))

RelationInstanceId = H(
  "zkc/relation-instance",
  RelationInstanceRegimeId,
  RelationInterfaceId,
  CanonicalEncode(public_values))

RelationArtifactProfileId = H(
  "zkc/relation-artifact-profile",
  RelationArtifactProfileRegimeId,
  CanonicalEncode(RelationArtifactProfile))

RelationAdapterId = H(
  "zkc/relation-adapter",
  RelationAdapterRegimeId,
  RelationArtifactProfileId,
  CanonicalEncode(RelationAdapterContract))
```

`RelationDefinitionId` is computed by its owning regime, not synthesized from
an interface description. Private witness assignment has no mandatory durable
content ID.

### 8.3 Relation-interface and instance admission

```text
ExactRelationDependencyPreimageBundle =
  ExactMap<RelationDependencyRef,
           AuthenticatedRelationDependencyPreimageInput>

ExactRelationDependencyAuthenticationCapabilities =
  ExactMap<RelationDependencyRef,
           RelationDependencyAuthenticationCapability restricted to the
           exact kind, regime, content identity, ABI, and direct edges>

AuthenticateRelationInterface(
  raw candidate,
  ExactRelationDependencyPreimageBundle,
  ExactRelationDependencyAuthenticationCapabilities)
  -> AuthenticatedRelationInterfaceCandidate

AdmitRelationInterface(
  AuthenticatedRelationInterfaceCandidate,
  retained exact relation dependency views,
  ExactRelationInterfaceLawCheckerCapabilities)
  -> AdmittedRelationInterface

AuthenticateRelationInstance(
  raw candidate,
  exact AdmittedRelationInterface identity-and-domain view)
  -> AuthenticatedRelationInstanceCandidate

AdmitRelationInstance(
  AuthenticatedRelationInstanceCandidate,
  exact AdmittedRelationInterface,
  ExactRelationInstanceLawCheckerCapabilities)
  -> AdmittedRelationInstance

ExactRelationArtifactProfileDependencyBundle =
  ExactMap<TypedRelationArtifactProfileDependencyRef,
           AuthenticatedRelationArtifactProfileDependencyPreimage>

TypedRelationArtifactProfileDependencyRef =
  exact profile dependency reference retaining kind, contract regime,
  content ID, exact ABI, and direct dependency IDs

AuthenticateRelationArtifactProfile(
  raw candidate,
  ExactRelationArtifactProfileDependencyBundle,
  ExactRelationArtifactProfileDependencyAuthenticationCapabilities)
  -> AuthenticatedRelationArtifactProfileCandidate

AdmitRelationArtifactProfile(
  AuthenticatedRelationArtifactProfileCandidate,
  retained exact profile dependency views,
  ExactRelationArtifactProfileLawCheckerCapabilities)
  -> AdmittedRelationArtifactProfile

ExactRelationAdapterDependencyBundle =
  ExactMap<TypedRelationAdapterDependencyRef,
           AuthenticatedRelationAdapterDependencyPreimage>

TypedRelationAdapterDependencyRef =
  exact byte-language or deterministic-interpreter dependency reference
  retaining kind, contract regime, content ID, exact ABI, and direct
  dependency IDs

AuthenticateRelationAdapter(
  raw candidate,
  exact AdmittedRelationArtifactProfile identity view,
  ExactRelationAdapterDependencyBundle,
  ExactRelationAdapterDependencyAuthenticationCapabilities)
  -> AuthenticatedRelationAdapterCandidate

AdmitRelationAdapter(
  AuthenticatedRelationAdapterCandidate,
  exact AdmittedRelationArtifactProfile,
  retained exact adapter dependency views,
  ExactRelationAdapterInterpreterAndLawCheckerCapabilities)
  -> AdmittedRelationAdapter
```

Authentication checks closed physical form, definition-reference syntax,
every occurrence range, exact direct references, the least reachable
regime-qualified dependency closure, and identity recomputation. Admission
reruns semantic domain/ABI compatibility, committed-object role separation,
canonical accepted-result values, and all totality rules, then retains the
exact authenticated dependency bundle in the immutable admitted capability.
The two operations reject a missing preimage, an extra declared dependency,
an undeclared transitive read, or a same-digest regime/ABI mismatch.
The authentication capability map has exactly the preimage bundle's key set;
each capability is kind-, regime-, identity-, ABI-, and direct-edge-matched.
Authentication retains attenuated immutable views of every and only member of
that closure. Admission consumes those retained views rather than accepting a
second nominal dependency bundle; authentication capabilities are not
retained as semantic authority.

Relation-instance authentication and admission use the explicit operations
above and require one and only one canonical same-domain value for every
`RelationPublicValueRef`. Private witness assignment is occurrence-local and
contains one live secret capability for every `RelationWitnessValueRef`; it is
not serializable, authenticated as a semantic artifact, or inspected by
interface admission.

The two typed artifact dependency refs retain the full dependency kind,
contract regime, content ID, exact ABI, and direct dependency IDs; each bundle
is the exact least reachable closure and is retained only as attenuated
immutable views. Artifact-profile authentication and admission check the exact byte language,
raw-byte identity domain, closed fact and malformed-reason schemas, limits, and
identity without loading a relation or Protocol. Adapter authentication
recomputes its profile-dependent identity. Adapter admission consumes the
exact admitted profile plus the named executable dependency/checker capability
and checks deterministic, total tagged interpretation over the profile domain,
fact-schema closure, refusal closure, and absence of ambient reads. The live
checker capability never enters either semantic preimage.

Neither admission loads Protocol, Interface, artifact bytes, or a witness.
Neither establishes `RelationSatisfies(instance, witness)`.

### 8.4 Relation authoring ingress

Relation source languages enter through an explicit unauthoritative
normalization/refusal boundary, independently of artifact interpretation:

```text
NormalizeRelationAuthoring(
  RelationAuthoringUnit,
  ExactResolvedRelationReadClosureSnapshot,
  RelationAuthoringNormalizerContract,
  RelationSemanticRegimeSet)
  -> Qualified<CanonicalRelationCandidateBundle,
               NormalizationAudit<RelationAuthoring>>

CanonicalRelationCandidateBundle = {
  interface: RelationInterfaceCandidate,
  instances: CanonicalSeq<RelationInstanceCandidate>,
  bindings: CanonicalSeq<RelationBindingCandidate>
}
```

The normalizer contract names one finite authoring language/profile, its
finite syntax quotient, every resolution and pre-erasure check, the complete
mapping into the canonical relation algebra, exact supported semantic regimes,
and immutable dependencies. The resolved-read snapshot is complete and
content-addressed; imports, environment lookups, registries, clocks, and
caller policy outside it are forbidden. The audit classifies every authoring
distinction as retained in a candidate, extracted to a typed nonsemantic side
output, proved neutral under the finite declared quotient, or rejected before
erasure. Unknown constructs, unresolved reads, unsupported relation roles,
and unclassified loss are refusals.

The operation is deterministic over those named inputs but authenticates and
admits nothing. Each emitted candidate independently follows its ordinary
authentication and admission lifecycle with exact dependency preimages.
Direct construction of a canonical candidate remains legal as a low-level
ingress, but carries no source-language, resolution, preservation, or
provenance claim. A `RelationArtifactObservation` cannot substitute for this
boundary: it records selected backend-artifact facts, not the semantics of a
relation authoring unit.

### 8.5 Relation binding

```text
ProtocolPublicBindingTarget =
  ProtocolPublicAssignmentOccurrence(ProtocolPublicStatementOccurrenceRef)

ProtocolWitnessBindingTarget =
    ProtocolPrivatePortValue(PortOccurrenceRef)
  | ProtocolProverObligationOutput(ProverObligationRef, output_ordinal)

RelationToProtocolValueBridge = {
  relation_domain: RelationValueDomainContractRef,
  protocol_domain: ValueDomainContractRef,
  to_protocol:
    CanonicalAlgorithmSpec<RelationValueToProtocolCanonicalValue>,
  to_relation:
    CanonicalAlgorithmSpec<ProtocolValueToRelationCanonicalValue>
}

RelationPublicPortBinding = {
  target: ProtocolPublicBindingTarget,
  value_bridge: RelationToProtocolValueBridge
}

RelationWitnessPortBinding = {
  target: ProtocolWitnessBindingTarget,
  value_bridge: RelationToProtocolValueBridge
}

ProtocolResultBinding =
    ClaimPresence(ClaimRef)
  | CheckTrue(CheckRef)
  | AcceptingTerminals(NonEmptyCanonicalSet<TerminalRef>)

ProtocolInterfaceObjectPosition =
    ProofMessageObject(ExternalProofPosition, EventInputOrdinal)
  | ApplicationEventObject(ApplicationBindingRef, EventInputOrdinal)

ArtifactGroundingDependency =
    NoArtifactDependency
  | FromArtifactFact(RelationAdapterRef, TypedArtifactFactSelector)

CommittedObjectGroundingEntry = {
  protocol_object: ObjectRef,
  semantic_object_derivation:
    CanonicalAlgorithmSpec<ProtocolObjectToRelationSemanticObject>,
  commitment_value_derivation:
    CanonicalAlgorithmSpec<RelationObjectToCommitmentValue>,
  material_encoding:
    CanonicalAlgorithmSpec<RelationObjectToCanonicalMaterial>,
  interface_position: Optional<ProtocolInterfaceObjectPosition>,
  artifact_dependency: ArtifactGroundingDependency
}

CommittedObjectGroundingMap =
  TotalMap<RelationCommittedObjectRef, CommittedObjectGroundingEntry>

RelationBinding = {
  protocol_interface_id: ProtocolInterfaceId,
  relation_interface_id: RelationInterfaceId,
  public_port_map:
    TotalMap<RelationPublicValueRef, RelationPublicPortBinding>,
  witness_port_map:
    TotalMap<RelationWitnessValueRef, RelationWitnessPortBinding>,
  committed_object_grounding: CommittedObjectGroundingMap,
  result_binding: ProtocolResultBinding
}
```

`RelationBindingId` commits to its own regime, both dependent IDs, and
canonical content. Every value bridge is a total canonical bijection between
its exact independently owned relation and Protocol domains:

```text
to_relation(to_protocol(r)) = r
to_protocol(to_relation(p)) = p
```

The two algorithm ABIs carry those exact source and target domain contracts;
an identity bridge is legal only when the regime-qualified domain contract is
literally shared. Byte equality, equal cardinality, or a mnemonic never
establishes cross-domain equality.

A public port target must be an occurrence of a
public input port whose semantic purpose is `Statement`, and that exact
occurrence must appear once in the dependent Interface's
`CanonicalPublicAssignmentDomain`. No challenge, prover-produced value,
terminal output, merely public observation, or post-statement computation can
enter this constructor: value-level correspondence consumes decoded statement
assignments and does not execute the Protocol. A derived public relation value
therefore requires an explicit future derivation constructor or its own
statement occurrence rather than an arbitrary `ValueRef`. Its bridge's
relation domain equals the exact source relation port domain and its Protocol
domain equals the target occurrence domain. A witness-port target must be a
private Prover input occurrence or one exact output ordinal of a named Prover
obligation, with the same exact bridge-domain equations.

Targets are injective within each public or witness map: two distinct relation
occurrences cannot alias one Protocol occurrence or obligation output. Binding
admission does not require the map image to exhaust every Protocol statement,
private input, or obligation output; exact cross-subject cardinality and image
equality are questions for the requested `PublicPorts` or `WitnessPorts`
correspondence clause. This preserves a well-formed proposal on which that
later check can return a meaningful negative result.

The committed-object map is total over relation object occurrences and each
entry is identity-bearing binding content. Its three closed algorithm specs
name exact domain/codomain ABIs: Protocol object contract to relation semantic
object domain, relation semantic object to commitment-value domain, and
relation semantic object to canonical material domain. Binding authentication
consumes every referenced algorithm preimage and direct dependency; admission
checks only ABI closure, the exact Protocol object reference, occurrence
totality, and position/ref shape. It does not assert that the derivations are
mathematically faithful or that an artifact contains their result.

An optional Interface position is occurrence-exact. A proof position must map
through `GuardedProofTraceBinding` to a proof-message event whose named input
ordinal is exactly this object; an application position must map through the
named `ApplicationBinding` to an event whose named input ordinal is exactly
this object. No external name, ordinal coincidence, or untyped event link can
stand in for that chain. `FromArtifactFact` assigns one exact adapter and fact
selector to this object occurrence; `NoArtifactDependency` forbids a grounding
checker from reading artifact facts for it. There is no unassigned global
adapter list.

`ClaimPresence` names one exact produced claim, `CheckTrue` names one exact
invoked Boolean check, and every member of `AcceptingTerminals` is a distinct
Core terminal whose result is `Accept`. The later correspondence checker—not
binding admission—can check only this occurrence/domain binding shape. It does
not establish that the externally owned relation result lies in
`accepted_values` exactly when the named Protocol condition holds, nor that a
terminal subset is exhaustive for relation acceptance. Such a behavioral
equivalence requires an exact result-semantics model/adapter plus a separately
checked relation-owned capability; Stage 3 defines neither. Binding
admission checks reference existence, occurrence totality, uniqueness where a
binding injectivity is required, bridge/domain correctness, exact Interface exposure, and
grounding-dependency closure only. It remains a proposal for semantic correspondence.

```text
RelationBindingId = H(
  "zkc/relation-binding",
  RelationBindingRegimeId,
  ProtocolInterfaceId,
  RelationInterfaceId,
  CanonicalEncode(RelationBinding))
```

Binding authority follows an explicit dependent-subject lifecycle:

```text
ExactRelationBindingAlgorithmDependencyBundle =
  ExactMap<TypedRelationBindingAlgorithmDependencyRef,
           AuthenticatedRelationBindingAlgorithmDependencyPreimage>

TypedRelationBindingAlgorithmDependencyRef =
  ContentAddressedContractRef restricted to a value-bridge or
  committed-object algorithm kind, retaining its contract regime,
  content ID, exact ABI, and direct dependency IDs

AuthenticateRelationBinding(
  raw candidate,
  ExactRelationBindingAlgorithmDependencyBundle,
  ExactRelationBindingDependencyAuthenticationCapabilities)
  -> AuthenticatedRelationBindingCandidate

AdmitRelationBinding(
  AuthenticatedRelationBindingCandidate,
  exact AdmittedProtocol binding view,
  exact AdmittedProtocolInterface,
  exact AdmittedRelationInterface,
  retained exact binding-algorithm dependency views,
  exact admitted adapter views required by `FromArtifactFact`,
  ExactRelationBindingLawCheckerCapabilities)
  -> AdmittedRelationBinding
```

The dependency bundle contains every and only preimage in the least closure of
all public/witness value-bridge and committed-object algorithm specs. The
authenticated candidate retains attenuated immutable views; optional adapter
IDs remain identity-bearing selectors but only the separately supplied exact
admitted views grant use authority. Admission verifies the two value-bridge
round trips and exact domain ABIs in addition to the occurrence, grounding,
and reference-shape laws. The admitted capability establishes only
binding-shape and dependency closure; the separately checked correspondence
result owns every semantic agreement or disagreement. Missing, extra,
mismatched, or same-digest cross-regime dependencies are refused, and no live
capability enters identity.

This separate subject permits several relation interpretations of one
Interface and avoids making relation-specific maps part of Protocol or
Interface identity.

### 8.6 Artifact interpretation and comparison

Artifact-byte identity binds exact content, not a transport envelope or a
caller-supplied digest:

```text
RelationArtifactByteId = H(
  "zkc/relation-artifact-bytes",
  RelationArtifactProfileId,
  CanonicalEncode(ExactRawBytes))

InterpretRelationArtifact(
  ExactRawBytes,
  AdmittedRelationArtifactProfile,
  AdmittedRelationAdapter,
  ExactRelationAdapterInterpreterExecutionCapabilities)
  -> Qualified<RelationArtifactObservationCandidate>

RelationArtifactObservationContent = {
  artifact_byte_id: RelationArtifactByteId,
  profile_id: RelationArtifactProfileId,
  adapter_ref: RelationAdapterRef,
  observed_facts: CanonicalSet<TypedArtifactFact>,
  unread_fields: CanonicalSet<TypedArtifactFieldRef>
}

RelationArtifactObservation = RelationArtifactObservationContent
RelationArtifactObservationCandidate = RelationArtifactObservationContent

RelationArtifactObservationId = H(
  "zkc/relation-artifact-observation",
  RelationArtifactObservationRegimeId,
  RelationArtifactByteId,
  RelationArtifactProfileId,
  RelationAdapterRef,
  CanonicalEncode(observed_facts, unread_fields))

AuthenticateRelationArtifactObservation(
  raw observation candidate,
  ExactRawBytes,
  exact AdmittedRelationArtifactProfile identity view,
  exact AdmittedRelationAdapter identity view)
  -> AuthenticatedRelationArtifactObservationCandidate

AdmitRelationArtifactObservation(
  AuthenticatedRelationArtifactObservationCandidate,
  ExactRawBytes,
  exact AdmittedRelationArtifactProfile,
  exact AdmittedRelationAdapter,
  ExactRelationAdapterInterpreterExecutionCapabilities)
  -> AdmittedRelationArtifactObservation
```

Interpretation reads no expected relation or Protocol and executes only
through the supplied capability whose interpreter identity exactly matches the
admitted adapter; the capability is neither ambient nor retained in the
candidate. Only `Completed` forms
an observation candidate. The candidate and subject aliases have exactly the
same closed content record; only successful authentication/admission changes
lifecycle authority, never fields or identity preimage. `Malformed`, `Unsupported`, `Refused`, and
`CheckerFailure` are distinct qualified operation outcomes and mint no
observation identity. The explicit authentication operation checks closed
physical form, exact raw-byte/profile/adapter scope, fact and unread-field
schemas, and identity recomputation. Admission consumes those same exact live
inputs, reruns the interpreter through the identity-matched execution
capability, requires byte-for-byte/fact-for-fact equality with the candidate,
and mints the process-local admitted observation capability. A transport checksum may
protect delivery but never enters artifact-byte, observation, relation, or
Protocol identity.

Comparison is a separate checked operation:

```text
ArtifactComparisonQuestion =
  NonEmptyCanonicalSet<RelationInterfaceFieldRef>

RelationArtifactAgreesWithInterface(
  AdmittedRelationArtifactObservation,
  AdmittedRelationInterface,
  ArtifactComparisonQuestion,
  CorrespondenceRegime)
  -> Qualified<CheckedArtifactInterfaceComparison>
```

An affirmative result records agreement for every requested field; a negative
result records exact conflicts while retaining unaffected agreements.
`CannotAnswer` covers requested facts that the adapter did not emit.
Interpretation failure is not disagreement, and an observation alone asserts
no relation correspondence. Named independent consumers justify the durable
observation: Relations checkers can replay artifact/interface comparisons in
another process, and Stage 6 Evidence may ingest the observation and its later
checked comparison. Serialized observations carry no live authority and must
be reauthenticated and rechecked at each consumer boundary.

### 8.7 Committed-object grounding

Committed-object grounding is checked before it can be used as a
correspondence clause:

```text
ConditionalArtifactObservationMap =
  CanonicalMap<RelationCommittedObjectRef,
               AdmittedRelationArtifactObservation>

GroundCommittedObjects(
  admitted Protocol object-declaration view,
  admitted ProtocolInterface,
  admitted RelationInterface,
  admitted RelationBinding,
  exact admitted grounding-algorithm dependency views attenuated from the
    binding,
  ExactGroundingAlgorithmExecutionCapabilities,
  ConditionalArtifactObservationMap,
  CorrespondenceRegime)
  -> Qualified<CheckedCommittedObjectGrounding>
```

The conditional observation map has exactly one entry for each and only each
grounding entry whose `artifact_dependency` is `FromArtifactFact`; the
observation must retain the identical admitted adapter/profile, exact raw-byte
identity, and selected typed fact. A missing or mismatched required observation
is `CannotAnswer`; an observation for `NoArtifactDependency` is an undeclared
read and is refused. The checker evaluates only the identity-bearing grounding
entry equations and their exact dependency ABIs using only identity-matched
execution capabilities. The retained views and live capabilities do not enter
the grounding subjects' semantic identities. The checker cannot choose a
codec, adapter, fact, or Interface position at invocation time.

An affirmative result binds each `RelationCommittedObjectRef` to its entry's
exact `CoreRef<object>`, semantic domain, commitment-value derivation,
canonical material encoding, optional exact Interface position, and assigned
artifact derivation when declared. Protocol objects outside the map need not be
covered. Multiple relation committed-object occurrences may name one Protocol
object when their independently checked domains and derivations agree; no
inverse injectivity is inferred unless a later question explicitly requests
and checks it. A negative result names the conflicting
equation and retains unaffected agreements. An unassigned adapter proposal,
reader capability, material digest, or instance-wiring map cannot assert
grounding. Grounding changes neither Protocol nor relation identity and proves
neither derivation faithfulness beyond the checked contract equations, opening
knowledge, nor witness satisfaction.

### 8.8 Exact Protocol-at-Interface correspondence

```text
CorrespondenceBaseClause =
    PublicPorts
  | WitnessPorts
  | ResultBindingReferenceShape
  | CommittedObjectGrounding

CorrespondenceQuestion = {
  base_clauses: CanonicalSet<CorrespondenceBaseClause>,
  artifact_question: Optional<ArtifactComparisonQuestion>
}

base_clauses is nonempty OR artifact_question is present

RelationCorrespondsAtInterface(
  AdmittedProtocol,
  AdmittedProtocolInterface,
  AdmittedRelationInterface,
  AdmittedRelationBinding,
  CorrespondenceQuestion,
  Optional<CheckedArtifactInterfaceComparison>,
  Optional<CheckedCommittedObjectGrounding>,
  CorrespondenceRegime)
  -> Qualified<CheckedRelationCorrespondenceJudgment>
```

The exact question determines both the authority requested and the fields the
result may claim. The checker consumes owner-defined narrow views and, for each
requested clause, compares:

1. exact source identities and regimes;
2. public port cardinalities, values/positions, exact admitted cross-domain
   bridge ABIs and round trips, and lossless Interface decoding;
3. witness port roles, domain bridges, and abstract prover obligations without
   inspecting witness values;
4. the exact checked committed-object grounding capability rather than raw
   adapter assertions;
5. the exact constructor/reference well-formedness of the named
   claim/check/Accept-terminal result binding, while separately retaining the
   already admitted relation result-role declaration;
6. the exact checked artifact/interface agreement rather than an observation
   or parsed fact by itself; and
7. closure of every adapter and dependency read.

If `CommittedObjectGrounding` is in `base_clauses`, an exact checked grounding result
over the same subjects and regime is mandatory: an affirmative result supports
the clause, while a negative result makes the clause negative and preserves
unaffected grounding facts. If `artifact_question = Some(q)`, an exact
checked artifact/interface comparison over the identical subjects, regime,
and nested `ArtifactComparisonQuestion q` is mandatory under the same rule.
Agreement on a subset or different field set cannot be widened. A raw
value or merely admitted observation cannot substitute. If a clause is not
requested, the result makes no claim about it. If it is requested and the
required checked capability is absent or mismatched, the outcome is
`CannotAnswer`, not a smaller affirmative judgment. The two optional operation
inputs must be absent when their corresponding grounding or artifact field is
not requested; an extra capability is an undeclared read and is refused. The result records one
field-factored outcome per requested base clause and one artifact field outcome
when `artifact_question` is present, and commits to the exact question. An
affirmative judgment has agreement for every requested field. A negative
judgment names every refuted field and preserves unaffected agreements.
`Unsupported`, `CannotAnswer`, `Refused`, `Malformed`, and `CheckerFailure` are
not negative correspondence.

Correspondence does not establish relation definition truth, public-instance
truth, witness possession, witness satisfaction, Protocol admission,
completeness, soundness, knowledge, zero knowledge, or endpoint realization.
In particular, `ResultBindingReferenceShape` has one directly recomputable
meaning: `ClaimPresence` names one in-range produced claim; `CheckTrue` names
one in-range invoked Boolean check; or `AcceptingTerminals` is a nonempty,
duplicate-free set of in-range terminals whose static result is `Accept`.
The admitted relation result role is retained as a subject fact, but this
clause performs no comparison between its `output_domain` or
`accepted_values` and the Protocol constructor. An affirmative result is only
this typed reference-shape fact. It does not say that relation acceptance and
Protocol acceptance coincide. That stronger statement remains unavailable
until a later owner supplies an exact relation-result semantics and a checked
capability connecting it to the named Protocol condition.

For an exact public assignment, a second value-level relation remains
distinct:

```text
RelationInstanceCorrespondsAtInterface(
  affirmative CheckedRelationCorrespondenceJudgment
    whose exact CorrespondenceQuestion.base_clauses contains PublicPorts,
  AdmittedProtocolInterface,
  AdmittedRelationBinding,
  AdmittedRelationInstance,
  ProtocolPublicAssignment<the exact dependent ProtocolId>,
  exact admitted value-bridge dependency views attenuated from the binding,
  ExactRelationValueBridgeExecutionCapabilities,
  CorrespondenceRegime)
  -> Qualified<CheckedInstanceCorrespondenceJudgment>
```

`ProtocolPublicAssignment<P>` is the pure semantic result of successful
Interface statement decoding, not an invocation, deployment, or capability.
The supplied value must inhabit the exact admitted Interface's
`CanonicalPublicAssignmentDomain(P)`; partial, extra-key, wrong-Protocol, and
wrong-domain maps are malformed inputs. The checker
requires exact identity agreement among the structural judgment, admitted
Interface, admitted binding, and relation instance; the structural capability
retains the admitted Protocol and relation-interface views. It then applies
the admitted binding's exact `to_protocol` value bridge to each
relation-instance value and compares that canonical Protocol value with the
one reconstructed by the Interface statement binding for the mapped public
port. Each execution capability must match that bridge's exact typed identity
and ABI in the attenuated admitted dependency views; a binding law checker is
not retained as executable authority and no ambient implementation is read.
No raw-byte or unqualified-value equality is used. An affirmative judgment whose question omitted `PublicPorts`
cannot be widened for this purpose. The checker does not inspect a witness or
execute the verifier. This keeps reusable interface correspondence separate
from one instance occurrence.

### 8.9 Satisfaction boundary

Stage 3 exports only the signature:

```text
RelationSatisfies(
  RelationDefinitionRef,
  AdmittedRelationInstance,
  PrivateWitnessAssignment,
  exact semantic model and assumptions)
  -> later-owned qualified judgment
```

No Stage 3 admission or correspondence result may be substituted for it.

## 9. Fresh-to-Fiat--Shamir construction

### 9.1 Transcript construction subject

```text
TranscriptConstruction = {
  core_id: CoreId,
  initialization: DomainSeparatedInitialization,
  application_domain: CanonicalStaticContext,
  session_context_map:
    TotalMap<ContextPortOccurrenceRef, InitializationAction>,
  framing: InjectiveFramingContract,
  event_actions: TotalMap<EventRef, TranscriptAction>,
  challenge_prefixes:
    TotalMap<ChallengeRef, CanonicalSeq<EventActionOccurrenceRef>>,
  abort_map: TotalMap<ChallengeRef, FailureRef>,
  composition_context: ExactCompositionContext
}

ExactCompositionContext =
    Standalone
  | Composed(
      CoreCompositionSpecId,
      CanonicalSeq<ChildOccurrenceRef>,
      CanonicalMap<ContextPortOccurrenceRef, InitializationAction>)

ContextPortOccurrenceRef =
  PortOccurrenceRef restricted to Public Input Context ports

TranscriptAction =
    Absorb(NonEmptyCanonicalSeq<TypedTranscriptAtom>)
  | DeriveChallenge(ChallengeRef, SqueezeAndSampleRule)
  | NoTranscriptAction

TypedTranscriptAtom = {
  source: ExactEventInputOccurrenceRef,
  semantic_type: ExactValueOrObjectDomainRef,
  codec: InjectiveTypedCodec
}

ExactEventInputOccurrenceRef = {
  event: EventRef,
  input_ordinal: ordinal
}
```

Initialization binds the construction suite, Core ID, message/type framing,
language/argument-system identifier, and exact static application domain.
Per-instance session context enters only through every exact occurrence of
public Core context input ports and the identity-bearing
`session_context_map`. The map is total over those occurrences, ordered first
by port ordinal and then occurrence ordinal, and each action consumes exactly
that occurrence's typed context value; runtime values do not create one
Protocol identity per invocation. Human labels or ambient caller strings are
insufficient. Every Core event has exactly one action. A non-challenge event
classified `Transcript` has one nonempty `Absorb` when its
`EventActionOccurs` predicate is true; a `FreshChallenge` event has exactly one
matching `DeriveChallenge` when its action occurs; every
other event has `NoTranscriptAction` and may not claim a transcript
observation. Thus a challenge is never ambiguously both absorbed and squeezed.
Each absorbed atom names an exact in-range position of that same event's
recomputed `EventDecl.inputs`; the atom sequence covers every and only input
position exactly once in canonical input order, and `semantic_type` equals the
referenced value or object's exact domain.
There is no event-output source kind: v0 event results are separately declared
values and occurrence bindings, so transcript material must enter through the
event's closed input sequence.

The initialization and framing contracts, every `InitializationAction`, and
every `TypedTranscriptAtom.codec` have total infallible ABIs on these exact
admitted inputs. Their canonical algorithm specifications may contain
structural validation evidence, but their Protocol-facing result type has no
failure variant. `DeriveChallenge` is the sole fallible transcript transition;
its `SqueezeAndSampleRule` returns exactly its produced value or the one
challenge-indexed sampling-failure variant. This makes the transcript fold a
total operation with one occurrence-exact Core continuation for every possible
runtime non-success.

The concrete transcript state is the fold of the initialization actions and
then all action-occurring non-no-op event actions in total Core schedule order.
A challenge prefix is exactly every prior potentially action-occurring absorb
or derive action in that order, with derived action-occurrence predicates
retained; at runtime it is exactly the action-occurring subsequence. It is not
a caller-selected causal subset. The stored
`challenge_prefixes` must equal the exact action-wise image of the Core
`transcript_event_prefix_template` under `event_actions`, after excluding
no-op actions. This equality is directly recomputed.

`abort_map` is total over exact challenge occurrences and each value equals
that challenge declaration's linked `ChallengeSampling` failure. There is no
construction-only verifier failure. `ExactCompositionContext` is a closed sum:
`Standalone` binds no composition history, while `Composed` binds one exact
authenticated composition-spec identity, its ordered durable child
occurrences, and every public target context port used by initialization. It
cannot read private ports or infer a current composition from ambient state.
For `Composed`, the child-occurrence sequence equals the authenticated spec's
ordered slots exactly, and the stored context map equals
`session_context_map`; it is a domain-separation commitment to that same map,
not a second mapping policy. `Standalone` requires no composition-owned
context entry.

For every public `JointMember` group, the member `DeriveChallenge` actions are
checked together, not as unrelated per-challenge samplers. They cite the same
authenticated joint contract, cover its complete index range in Core exposure
order, and use the Core's exact base/effective guards. Rule `i` has the exact
earlier successful component domains as inputs and can return only a value in
the member's declared domain or `SamplingFailedAt(i)`; `abort_map[i]` is that
member's unique linked failure, and the Core guard equations suppress every
later action and consumer after the first continuing failure. The rules carry
the Core joint-contract reference as their identity-bearing *intended ideal
draw contract*, so a later theorem has an exact statement to prove.

These are algorithm, type, order, guard, and failure-surface checks. They do
not prove that deterministic transcript derivation induces the referenced
joint distribution, its marginals, or independence. That conclusion depends
on an explicit transcript/hash model and theorem and belongs exclusively to
`FSCompile` or a property-specific transport judgment. Fresh and
Fiat--Shamir interpretations therefore share an exact structural group-level
success/failure and availability surface; distributional correspondence is a
later conditional claim. A construction without this exact structural group
realization is unavailable for that Core rather than silently treating
correlated challenges as independent.

TranscriptConstruction authentication recomputes its regime-qualified ID and
authenticates codec, framing, sampler, and suite dependency preimages. Its
standalone authority path, also reused inside canonical-PIR and composition
transactions, is:

```text
ExactTranscriptAlgorithmDependencyPreimageBundle =
  ExactMap<TypedTranscriptAlgorithmDependencyRef,
           AuthenticatedTranscriptAlgorithmDependencyPreimage>

TypedTranscriptAlgorithmDependencyRef =
  ContentAddressedContractRef restricted to initialization, framing,
  atom-codec, or squeeze-rule kind, retaining its contract regime,
  content ID, exact ABI, and direct dependency IDs

AuthenticateTranscriptConstruction(
  CanonicalTranscriptConstructionCandidate,
  ExactTranscriptAlgorithmDependencyPreimageBundle,
  ExactTranscriptDependencyAuthenticationCapabilities)
  -> AuthenticatedTranscriptConstructionCandidate
```

The map contains every and only preimage in the least dependency closure of
all content-addressed initialization, framing, atom-codec, and squeeze rules
named by the candidate. Authentication checks kind, regime, ABI, direct-edge,
and identity equality and retains attenuated immutable dependency views.
Closed finite terms require no map entry; extra, missing, same-digest
cross-regime, or undeclared transitive inputs reject. The canonical-PIR FS
bundle in Section 5.3 supplies this exact candidate, bundle, and capability
set rather than invoking a separate ambient path.

Admission has the exact authority signature:

```text
CompositionContextAuthority =
    NoCompositionContext
  | ScopedCompositionFormationAuthority
  | affirmative CheckedCoreComposition

AdmitTranscriptConstruction(
  AuthenticatedTranscriptConstructionCandidate,
  CoreAdmissionWitness | AdmittedCoreView,
  CompositionContextAuthority,
  retained exact transcript algorithm dependency views,
  ExactTranscriptLawCheckerCapabilities)
  -> AdmittedTranscriptConstruction
```

`Standalone` requires `NoCompositionContext`. `Composed` rejects that variant:
during target formation it requires the transaction-scoped authority minted by
`ConstructAndSubadmitCore` from the exact admitted composition spec, target
Core witness, target `CoreId`, and invocation token; after formation it requires the checked
affirmative `CheckedCoreComposition` capability, which retains the exact spec and target Core
view. In either case admission directly checks the stored spec ID, ordered
child occurrences, target Core ID, and context map. A serialized spec ID or
unverified child list grants no composition-context authority.

Admission then checks exact Core scope, total
guarded event/challenge domains, injective framing, codec round trips, sampling
output domains, exact action/prefix equality, conditional-input and group-order
shape, intended independent/joint contract references, failure mapping, and
absence of ambient state. It additionally checks that initialization,
context initialization, framing, and absorb codecs have no Protocol-facing
failure case and that each squeeze failure is mapped to exactly its linked Core
failure. It neither checks nor concludes an induced
distribution or correlation equation. It mints only an
`AdmittedTranscriptConstruction` capability retaining attenuated immutable
views of the exact context authority and algorithm dependency closure; law
checker implementations are not retained as semantic authority. It does not
construct a target or establish a theorem.

### 9.2 Construction contract

```text
ConstructFS(
  admitted fresh Protocol,
  admitted TranscriptConstruction)
  -> FS target candidate
     + FSConstructionMaps

FSConstructionMaps = {
  source_protocol_id: ProtocolId,
  target_protocol_id: ProtocolId,
  shared_core_id: CoreId,
  interpretation_change:
    FreshToFiatShamir(TranscriptConstructionId),
  events:
    TotalMap<SourceProtocolScopedEventRef,
             TargetProtocolScopedEventRef>,
  challenges:
    TotalMap<SourceProtocolScopedChallengeRef,
             TargetProtocolScopedChallengeRef>,
  prefixes:
    TotalMap<SourceProtocolScopedChallengeRef,
             FSTargetPrefixDescriptor>
}

FinalizeFSConstruction(
  admitted fresh Protocol,
  admitted FS Protocol,
  admitted TranscriptConstruction,
  FSConstructionMaps,
  FSConstructionRegime)
  -> Qualified<CheckedFSConstruction>

SourceProtocolScopedEventRef =
  ProtocolScopedRef<event> under source_protocol_id
TargetProtocolScopedEventRef =
  ProtocolScopedRef<event> under target_protocol_id
SourceProtocolScopedChallengeRef =
  ProtocolScopedRef<challenge> under source_protocol_id
TargetProtocolScopedChallengeRef =
  ProtocolScopedRef<challenge> under target_protocol_id

ExactActionOccurringSubsequence =
  deterministic ordered filtering by EventActionOccurs

FSTargetPrefixDescriptor = {
  target_challenge: TargetProtocolScopedChallengeRef,
  potential_core_prefix: CanonicalSeq<EventActionOccurrenceRef>,
  transcript_action_prefix:
    CanonicalSeq<EventActionOccurrenceRef>,
  runtime_projection: ExactActionOccurringSubsequence
}
```

The target uses the same intrinsic Core; Fresh challenges are interpreted by
the exact construction. Both admitted Protocols must have `shared_core_id`
literally as their `CoreId`.
The event and challenge maps are total bijections over every Core event and
challenge and preserve the exact inner `CoreRef`; their different source and
target
`ProtocolScopedRef<K>` values even when their inner `CoreRef<K>` values match,
so later theorem consumers do not infer interpretation or occurrence alignment
from equal ordinals.

The prefix map sends every source challenge occurrence to that mapped target
challenge, its exact ordered target action-occurrence template, the exact
non-no-op action-wise image under the admitted construction, and on execution
the exact action-occurring subsequence and framing actions used to derive it.
The two potential sequences must be the directly recomputed Core and
construction views of the same occurrences. The constructor is
deterministic and directly recomputable. The target is then physically
authenticated and admitted independently. Only after both subjects are
admitted does `FinalizeFSConstruction` directly recompute every identity,
interpretation, event, challenge, and prefix equation and mint the checked
result capability.

### 9.3 Later theorem seam

```text
FSCompile(
  admitted fresh Protocol,
  admitted FS Protocol,
  affirmative CheckedFSConstruction,
  semantic model identity,
  theorem/rule identity,
  explicit assumptions and quantitative parameters)
  -> Analysis-owned qualified judgment
```

`FSCompile` is unavailable rather than false when no theorem/rule or semantic
model applies. Each `PropertyTransport` additionally names the source property
judgment, exact FS result, property-specific rule, assumptions, losses, and
target conclusion. There is no global `FS-valid` capability.

## 10. Semantic Core composition

### 10.1 Composition specification

```text
CoreCompositionSpec = {
  target_protocol_regime_id: ProtocolSemanticRegimeId,
  children: CanonicalSeq<CoreId>,
  face_maps: CanonicalSeq<LocalTypedFaceMap>,
  ordinary_origin_maps: OrdinaryOriginMaps,
  terminal_origin_map:
    TotalMap<LocalChildInnerTerminalRef, TerminalOriginDisposition>,
  locally_added: CanonicalSet<LocalTargetCoreRef>,
  causal_seams: CanonicalSet<
    (LocalChildInnerEventRef, LocalChildInnerEventRef)>,
  locally_added_causal_edges:
    CanonicalSet<(LocalTargetEventRef, LocalTargetEventRef)>,
  interleaving: Permutation<LocalTargetEventRef>,
  challenge_policy:
    TotalMap<LocalChildChallengeBundleRef, ChallengePolicy>,
  private_randomness_policy:
    TotalMap<LocalChildPrivateRandomnessBundleRef, PrivateRandomnessPolicy>,
  failure_policy:
    TotalMap<LocalChildFailureOccurrenceRef, FailurePolicy>,
  reach_exit_policy:
    TotalMap<LocalChildInnerReachTerminalEventRef, ReachExitPolicy>,
  terminal_combiner: TotalTerminalCombiner,
  target_fragment: LocalTargetCoreFragment
}

LocalTypedFaceMap = {
  child_slot: LocalChildOccurrenceRef,
  ports: TotalMap<LocalChildInnerPortRef, LocalPortBinding>
}

OrdinaryOriginMaps = {
  values:
    TotalMap<LocalChildInnerOrdinaryValueRef, LocalTargetValueRef>,
  objects: TotalMap<LocalChildInnerObjectRef, LocalTargetObjectRef>,
  events:
    TotalMap<LocalChildInnerOrdinaryEventRef, LocalTargetEventRef>,
  claims: TotalMap<LocalChildInnerClaimRef, LocalTargetClaimRef>,
  reductions:
    TotalMap<LocalChildInnerReductionRef, LocalTargetReductionRef>,
  checks: TotalMap<LocalChildInnerCheckRef, LocalTargetCheckRef>
}

LocalTargetCoreRef =
    LocalTargetDependencyRef | LocalTargetRoleRef | LocalTargetPortRef
  | LocalTargetValueRef | LocalTargetObjectRef | LocalTargetRandomnessRef
  | LocalTargetChallengeRef | LocalTargetEventRef | LocalTargetClaimRef
  | LocalTargetReductionRef | LocalTargetCheckRef | LocalTargetFailureRef
  | LocalTargetTerminalRef | LocalTargetEndpointObligationRef
  | LocalTargetProverObligationRef
  | LocalTargetProverObligationFailureRef

LocalTargetValueDomainContractRef =
  LocalTargetDependencyRef restricted to ValueDomainContract
LocalTargetSumValueDomainContractRef =
  LocalTargetDependencyRef restricted to a ValueDomainContract whose ABI is
  the named closed sum
LocalTargetPureFunctionContractRef =
  LocalTargetDependencyRef restricted to PureFunctionContract
LocalTargetDistributionContractRef =
  LocalTargetDependencyRef restricted to DistributionContract
LocalTargetJointDistributionContractRef =
  LocalTargetDependencyRef restricted to JointDistributionContract

TerminalOriginDisposition = {
  mapped_target: Optional<LocalTargetTerminalRef>,
  captured_sources: CanonicalSet<
      LocalChildFailureOccurrenceRef
    | LocalChildInnerReachTerminalEventRef>,
  removed_sources: CanonicalSet<LocalChildFailureOccurrenceRef>
}

LocalPortBinding =
    ExternalInput(LocalTargetInputPortRef)
  | InternalInputs(CanonicalSeq<LocalTargetValueRef>)
  | ExternalOutput(LocalTargetOutputPortRef,
                   CanonicalSeq<LocalTargetValueRef>)
  | InternalOutputs(CanonicalSeq<LocalTargetValueRef>)

LocalChildChallengeBundleRef = {
  challenge: LocalChildInnerChallengeRef,
  event: LocalChildInnerFreshChallengeEventRef,
  value: LocalChildInnerChallengeValueRef,
  randomness: LocalChildInnerPublicRandomnessRef,
  sampling_endpoint_obligations:
    CanonicalSet<LocalChildInnerEndpointObligationRef>,
  sampling_failure: LocalChildFailureOccurrenceRef,
  public_coin_index: ordinal,
  correlation: ExactChildCorrelationDecl
}

LocalTargetFreshChallengeBundle = {
  challenge: LocalTargetChallengeRef,
  event: LocalTargetFreshChallengeEventRef,
  value: LocalTargetChallengeValueRef,
  randomness: LocalTargetPublicRandomnessRef,
  sampling_endpoint_obligations:
    CanonicalSet<LocalTargetEndpointObligationRef>,
  sampling_failure: LocalTargetFailureRef,
  public_coin_index: ordinal,
  correlation: ExactTargetCorrelationDecl
}

ChallengeSubstitutionDisposition = {
  value: LocalTargetValueRef,
  observation_event: LocalTargetObservePublicValueEventRef,
  removed_randomness: NoTargetRandomness,
  removed_sampling_endpoint_obligations: NoTargetSamplingObligations,
  removed_sampling_failure: NotApplicableAfterSubstitution,
  removed_public_coin_index: NoTargetPublicCoinIndex,
  correlation_effect: DeterministicFromNamedSources | ExternalPublicInput
}

CompositionChallengeGroupRef =
  dense canonical ordinal allocated by the least
  LocalChildChallengeBundleRef in each challenge-policy group

DerivedChallengeSources =
  NonEmptyCanonicalSeq<LocalChildChallengeBundleRef>

ChallengePolicy =
    IndependentChallenge(LocalTargetFreshChallengeBundle)
  | JointChallengeMember(CompositionChallengeGroupRef,
                         LocalTargetFreshChallengeBundle)
  | SharedChallenge(CompositionChallengeGroupRef,
                    LocalTargetFreshChallengeBundle)
  | DerivedChallenge(DerivedChallengeSources, LocalTargetPureFunctionContractRef,
                     ChallengeSubstitutionDisposition)
  | ImportedChallenge(LocalTargetContextPortRef,
                      LocalTargetEndpointObligationRef,
                      ChallengeSubstitutionDisposition)

PrivateRandomnessPolicy =
    PreserveIndependent(LocalTargetPrivateRandomnessBundle)
  | JointPrivateMember(CompositionPrivateRandomnessGroupRef,
                       LocalTargetJointDistributionContractRef,
                       LocalTargetPrivateRandomnessBundle)
  | DerivedPrivateValue(DerivedPrivateRandomnessSources,
                        LocalTargetPureFunctionContractRef,
                        PrivateRandomnessSubstitutionDisposition)
  | ExternalPrivateSupply(LocalTargetPrivatePortRef,
                          LocalTargetProverObligationRef,
                          PrivateRandomnessSubstitutionDisposition)

LocalChildPrivateRandomnessBundleRef = {
  randomness: LocalChildInnerPrivateRandomnessRef,
  value: LocalChildInnerPrivateRandomnessValueRef,
  owner_obligation: LocalChildInnerProverObligationRef,
  sampling_failure: LocalChildInnerProverObligationFailureRef
}

CompositionPrivateRandomnessGroupRef =
  dense canonical ordinal allocated by the least
  LocalChildPrivateRandomnessBundleRef in each private-policy group

DerivedPrivateRandomnessSources =
  NonEmptyCanonicalSeq<LocalChildPrivateRandomnessBundleRef>

LocalTargetPrivateRandomnessBundle = {
  randomness: LocalTargetPrivateRandomnessRef,
  value: LocalTargetPrivateRandomnessValueRef,
  owner_obligation: LocalTargetProverObligationRef,
  sampling_failure: LocalTargetProverObligationFailureRef,
  distribution: LocalTargetDistributionContractRef,
  correlation: ExactTargetCorrelationDecl
}

PrivateRandomnessSubstitutionDisposition = {
  value: LocalTargetValueRef,
  remove_owner_private_randomness_entry: Required,
  remove_private_sampling_failure: Required,
  owner_event_basis_rewrite: ProverConstructionBasisRewrite,
  distribution_effect: DeterministicFromNamedSources | ExternalPrivateInput
}

ProverConstructionBasisRewrite = {
  target_event: LocalTargetEventRef,
  replacement_basis: LocalTargetProverConstructionBasis,
  substituted_input_ordinal: ordinal
}

LocalTargetProverConstructionBasis =
  ProverConstructionBasis<all references in LocalTargetRef namespace>

SuffixSuppression = {
  exit_taken: LocalTargetBooleanValueRef,
  rewritten_guards:
    TotalMap<LocalChildLaterEventRef, LocalTargetGuardValueRef>
}

ExitStatusInjection = {
  raw_status: LocalTargetValueRef,
  sum_domain: LocalTargetSumValueDomainContractRef,
  variant_ordinal: ordinal,
  injected_status: LocalTargetValueRef
}

LocalTargetCapturedFailureExitStatusValueRef = LocalTargetValueRef

FailurePolicy =
    PreserveContinue(LocalTargetFailureRef)
  | PropagateFailure(LocalTargetFailureRef, LocalTargetTerminalRef)
  | CaptureFailure(LocalTargetFailureRef,
                   LocalTargetFailureStatusValueRef,
                   LocalTargetCapturedFailureExitStatusValueRef,
                   ExitStatusInjection,
                   SuffixSuppression)
  | RemovedByChallengeSubstitution(LocalChildChallengeBundleRef)

ReachExitPolicy =
    PropagateReach(LocalTargetReachTerminalEventRef,
                   LocalTargetTerminalRef)
  | CaptureReach(LocalTargetValueRef,
                 LocalTargetObservePublicValueEventRef,
                 ExitStatusInjection,
                 SuffixSuppression)

TotalTerminalCombiner = {
  inputs: CanonicalSeq<CombinerInput>,
  result_function: LocalTargetPureFunctionContractRef,
  result_value: LocalTargetValueRef,
  terminal_result_value_domain: LocalTargetValueDomainContractRef,
  result_domain: NonEmptyCanonicalSet<TerminalResult>,
  finals: TotalMap<ResultIn(result_domain), {
      guard: LocalTargetGuardValueRef | UnguardedFallback,
      public_output_function: LocalTargetPureFunctionContractRef,
      public_output_tuple: LocalTargetValueRef,
      public_output_values: CanonicalSeq<LocalTargetValueRef>,
      terminal: LocalTargetTerminalRef,
      event: LocalTargetReachTerminalEventRef
    }>,
  route_order: Permutation<ResultIn(result_domain)>
}

CombinerInput = {
  child_slot: LocalChildOccurrenceRef,
  merged_status: LocalTargetGuardedMergeValueRef
}

LocalTargetCoreFragment = {
  dependencies: CanonicalSeq<LocalTargetDependencyDecl>,
  roles: CanonicalSeq<LocalTargetRoleDecl>,
  ports: CanonicalSeq<LocalTargetPortDecl>,
  values: CanonicalSeq<LocalTargetValueNode>,
  objects: CanonicalSeq<LocalTargetObjectDecl>,
  randomness: CanonicalSeq<LocalTargetRandomnessDecl>,
  challenges: CanonicalSeq<LocalTargetChallengeDecl>,
  events: CanonicalSeq<LocalTargetEventDecl>,
  causal_edges: CanonicalSet<(LocalTargetEventRef, LocalTargetEventRef)>,
  claims: CanonicalSeq<LocalTargetClaimDecl>,
  reductions: CanonicalSeq<LocalTargetReductionDecl>,
  checks: CanonicalSeq<LocalTargetCheckDecl>,
  failures: CanonicalSeq<LocalTargetFailureDecl>,
  terminals: CanonicalSeq<LocalTargetTerminalDecl>,
  endpoint_obligations: CanonicalSeq<LocalTargetEndpointObligation>,
  prover_obligations: CanonicalSeq<LocalTargetProverObligation>,
  prover_obligation_failures:
    CanonicalSeq<LocalTargetProverObligationFailureDecl>
}
```

Every reference to not-yet-authenticated target content is a typed
`LocalTargetRef`; no global-looking target reference appears in the spec
preimage. The target fragment can declare every Core family that composition
may add. `interleaving` covers every and only target-fragment event exactly
once and becomes the target Core schedule; it is not a child-event list later
deduplicated through maps. Fields cannot be synthesized from ambient defaults.

Every restricted local contract alias above points to exactly one
same-kind declaration in `target_fragment.dependencies`, including its exact
regime, content ID, ABI, and direct edges. A child-origin contract reaches that
local declaration only through the deterministic dependency-origin mapping;
a locally introduced contract is covered by `locally_added`. No bare Core
dependency ref, global ID lookup, or equal-looking ABI can resolve one of
these policy fields.

`ordinary_origin_maps` removes all allocation ambiguity. Its value domain is
exactly every child value except `PortValue`, `PrivateRandomnessValue`,
`ChallengeValue`, `FailureStatusValue`, and `FailureOccurred`, whose origins
are owned respectively by face, randomness/challenge, or failure policies. Its
event domain is exactly every child event except `FreshChallenge` and
`ReachTerminal`, which their policies own. Each ordinary map is total and
injective across all child slots. Value, object, claim, reduction, and check
constructors are exact typed images with every operand/reference mapped
recursively. An ordinary event preserves its kind, actor, inputs,
and observations. Its endpoint-contract basis and prover-construction basis
are exact typed images unless an explicit private-randomness substitution owns
the one field-exact basis rewrite below. Its guard is the exact mapped source
guard unless the one applicable `SuffixSuppression` requires the exact
conjunctive rewrite below. Repeated identical children therefore still name
distinct explicit target ordinals.

Roles are derived uniquely by role class; ports by face maps; dependencies by
the deterministic least reachable closure; randomness and challenges by their bundle policies;
failure-origin values, failures, terminals, and terminal events by failure and
reach policies; and obligations by deterministic recomputation. Every target
declaration is covered exactly once by one of those sources, an ordinary map,
or `locally_added`, and those origin classes are disjoint. `locally_added`
contains every and only declarations with no child or derived-policy origin,
including combiner structure. Because the target fragment's canonical
sequences and these maps are both in the spec preimage, construction and final
map checking never recover origin by shape, pointer identity, or provisional
history.

Local additions cannot create an undeclared exit channel. They contain no
fresh randomness/challenge bundle, check, failure, failure-origin/status value,
`RaiseFailure`, terminal, or `ReachTerminal` except the exact values, terminals,
and reach events generated by `terminal_combiner`. Other locally added pure
values, objects, claims/reductions, ports, or nonterminal events remain legal
when fully closed. A composition that needs a new independent check/failure
protocol supplies it as an admitted child (or a future explicit local-exit
policy) rather than hiding it in the target fragment. Thus propagated child
exits and combiner routes are the complete verifier-terminal surface.

The target causal-edge set is closed independently of declaration origins. It
equals exactly the union of (a) the image of every child causal edge under the
complete event-occurrence maps, (b) every mapped `causal_seams` edge, (c) the
deterministically recomputed face-feed, challenge/private-randomness,
failure/reach-rewrite, suffix-suppression, and terminal-combiner edges, and
(d) `locally_added_causal_edges`. The locally added set is disjoint from the
first three classes, has only declared target-event endpoints, and is the only
place an intentional ordering edge with no derived origin may enter. The union
must be acyclic and `interleaving` must extend it exactly. Missing derived
edges, arbitrary fragment-only edges, and shape-inferred provenance all reject.

Target event guards have one deterministic precedence rule. For ordinary,
independent, derived/imported, failure, and reach origins, the contribution is
the mapped source or declared replacement base guard conjoined with the
negation of every earlier captured exit in that child slot. A one-origin
non-joint event uses that contribution exactly. A `SharedChallenge` is
admitted only when every member contribution after that per-child suppression
is the same exact Boolean value; the one target event uses that value. This
coactivation restriction keeps its many-to-one challenge, failure occurrence,
status, and prefix maps exact rather than inventing per-member projections
from one target failure. Conditional reuse with unequal guards requires an
explicit wrapper/shared-challenge child, not implicit subset semantics.

A target `JointChallengeMember` group is computed in two noncircular phases.
First, each source member contributes a *group base*: for a member of a source
joint group this is the mapped index-zero source-group base, and for an
independent or explicitly regrouped source it is the mapped source event
guard. That base is conjoined with exactly the captured-exit suppressions that
precede that source member's availability point. Every contribution in one
target group must be the same exact Boolean value; this common value is
`B_target`. Preserving one source joint group therefore maps its one source
base exactly, while regrouping is an `IntentionalChange` and is admitted only
when all proposed sources already have an equal explicit coactivation basis.
Second, target member `i` receives exactly
`B_target AND NOT(FailureOccurred(member_0)) ... AND
NOT(FailureOccurred(member_{i-1}))`. No mapped source member-final guard,
member-local suffix suppression, or event policy may be conjoined afterward.
A capture whose placement would make the member base contributions unequal
therefore rejects the composition or must be represented by an explicit
wrapper child. This equation both anchors member zero in mapped source
semantics and preserves the intrinsic joint first-failure law.

A target `JointPrivateMember` group derives `B_target` by the same
per-source-base and pre-group-capture equation. Because the first failed
private step immediately selects `ProverDidNotProduce`, every member's owner
event uses exactly `B_target`; no later-member failure conjunction is needed
and no member-local suppression is legal. If an owner event also has another
mapped origin, that origin's final contribution must equal `B_target`.
Unequal source bases, capture histories, or co-owned event contributions reject
the grouping rather than defining a partial joint experiment.

A locally added event has no child contribution and uses its explicit combiner
or local base equation. All Boolean nodes and dependency edges created by
these calculations are policy-derived and origin-covered. No event policy
writes a second final guard. Accordingly, every later statement that calls an
event an “exact typed image” means exact kind, actor, inputs, observations,
and exact mapped or explicitly rewritten obligation basis plus this one
final-guard equation.

`terminal_origin_map` is total over every terminal declaration in every child
occurrence. For a source terminal, its source-occurrence set is exactly all
child failures whose effect is `Terminate(that terminal)` plus all child
`ReachTerminal(that terminal)` events. `captured_sources` is exactly the subset
handled by `CaptureFailure` or `CaptureReach`; `removed_sources` is exactly the
subset of terminating sampling failures handled by
`RemovedByChallengeSubstitution`; and every remaining source occurrence uses
the matching propagation constructor. Those three subsets and propagation are
disjoint and exhaustive. `mapped_target` is present if and only if the
propagation subset is nonempty. When present, all propagated sources name that
one target terminal, whose result and public outputs are the exact typed image
of the source declaration. Mappings for distinct child terminal occurrences
are injective except when their propagating failures are members of one exact
`SharedChallenge` group; that sole many-to-one case requires identical mapped
results and public outputs and names the group's one target failure terminal.
Mixed capture, removal, and propagation of different occurrences over one
source terminal is explicit and legal, but each occurrence is in exactly one
subset. When `mapped_target` is absent, every source occurrence is captured or
removed; captures retain the complete result/output payload, while removals
are exactly the substitutions that erase the impossible sampling exit. Every
target terminal is covered exactly once either as one `mapped_target` image or
by `locally_added`; the two sets are disjoint, and terminal-combiner finals are
locally added. Thus neither an orphan target terminal nor an undeclared merge
of equal-looking child terminals can pass admission.

There is exactly one `LocalTypedFaceMap` per child slot. Role mapping is not a
policy: each child `Prover`, `Verifier`, and optional `PublicEnvironment` maps
deterministically to the unique target role of the same class. The port map is
total. `ExternalInput` is legal only from a child input to a target input with
identical role class, visibility, value domain, multiplicity, and semantic
purpose. `InternalInputs` must name one same-domain target value per child
occurrence, each available before every mapped use. It is inadmissible for any
child input occurrence named as a `ClaimDecl.producer`: replacing an initial
input occurrence by a value would erase both the producer reference and its
`Initial` timing. Such a case requires an explicit future
claim-producer/timing rewrite, not an inferred event. `ExternalOutput` is legal
only from a child output to a same-domain, same-multiplicity target output whose
declared output sequence is the named target sequence. `InternalOutputs`
names that exact same-domain occurrence sequence. Multiple
child inputs may share one external input only when every equality above is
explicitly satisfied; target outputs have exactly one producer. All internal
feed edges are added to the causal/value graph and must be acyclic. No other
port aliasing, direction reversal, visibility weakening, or face default is
admitted.

These are occurrence-indexed value equations, not only type checks.
`ExternalInput(p)` maps each child `PortValue(child_port, i)` to exactly
`PortValue(p, i)`. `InternalInputs(values)` has exactly the child port
cardinality and substitutes `values[i]` at every same-ordinal child input
occurrence. Likewise, `ExternalOutput(p, values)` and
`InternalOutputs(values)` contain exactly one target value per child output
occurrence and map every child `OutputValues[i]` to `values[i]`; in the
external case target port `p` has the same multiplicity and binds that complete
sequence. Every mapped value has the exact port element domain and required
path availability. No truncation, broadcast, ordinal permutation, or
same-domain but unrelated value satisfies a face.

Dependency and obligation merging are deliberately deterministic and have no
policy fields. After every target constructor and rewrite is fixed, its typed
dependency references are the root set. Target dependencies are exactly the
least reachable authenticated closure of those roots, drawn from the exact
child and locally supplied preimage pool and keyed by `(kind, semantic regime,
content identity, protocol-facing ABI)`. Unused child dependencies are not
historical target semantics. A referenced preimage absent from the pool
rejects; equal content identities with unequal regimes, preimages, or ABIs
reject; unequal regime-qualified identities never merge. Endpoint
obligations, prover obligations, and prover-obligation failures are then
recomputed from the fully constructed target events and randomness and must
equal the target fragment exactly. Child obligation maps are derived from the
checked event, randomness, and source constructors. A face map cannot erase,
invent, or rename an obligation independently.

Each challenge policy owns the entire linked challenge bundle: event, value,
randomness, public-sampling endpoint obligations, sampling failure,
public-coin index, and correlation. Independent and shared cases name a
complete target fresh bundle; joint-member cases name one distinct complete
target fresh bundle per member. The shared case may be many-to-one but must
give that target bundle one exact index and correlation declaration. Every
target fresh challenge bundle is covered by exactly one independent image, one
joint-member image, or one shared group, with sharing the only permitted
many-to-one case.

For every such target bundle, `public_coin_index` is recomputed as that target
`FreshChallenge` event's zero-based rank among all target challenge events in
`interleaving`. The checked composition maps retain each child challenge
occurrence and child index to this exact target occurrence and recomputed
index; shared groups alone may map several child indices to one target index.
This is structural occurrence reindexing, not preservation of an integer
field. Two child index-zero challenges therefore receive distinct target ranks
unless an explicit shared policy maps them to one occurrence.

Challenge-policy group references are the exact dense range ordered by each
group's least canonical policy-map key. Each group is homogeneous: all entries
are `JointChallengeMember` or all are `SharedChallenge`; the variants cannot
reuse one group reference. Private-policy groups use their distinct typed
reference family and the analogous least-key dense allocation. A Core
joint-randomness group, a composition challenge-policy group, and a composition
private-policy group never alias merely because their ordinals match.

For `IndependentChallenge`, the target event/value/randomness/failure and
obligation backlinks are the exact typed image of the child bundle except for
the recomputed occurrence index above, the target
distribution equals the child distribution, and target correlation is
`IndependentFresh`. It is legal only for a child whose source correlation is
`IndependentFresh`; breaking a source joint group by silently relabeling its
members independent is not admitted. The complete target Fresh event,
including its `FreshChallengeContracts` basis, and the recomputed sampling
endpoint obligation are exact typed images.

For each `JointChallengeMember(group_id, bundle)`, all and only policies with
that group ID name distinct target bundles whose correlation declarations are
`JointMember` entries of one exact target joint contract and target group. Their
indices are the complete collision-free range, equal the target exposure order,
and every target marginal equals its mapped child's distribution. Target event
order, the single `B_target` derivation, member effective guards, conditional
sampling step, value and failure
backlinks, kind-exact obligation bases, recomputed endpoint obligations, and
first-failure suppression satisfy the global joint-randomness laws. A source
joint group is structurally preserved only when every one of its
members appears in one target group with the same authenticated contract,
member correspondence, and index order. Combining independent sources,
regrouping source joints, or changing the joint contract is an
`IntentionalChange`; splitting a source joint is possible only through explicit
derived/imported substitution dispositions for the removed members, never via
`IndependentChallenge`.

For each `SharedChallenge(group_id, bundle)`, all and only
members with that group ID name the same target bundle; the target correlation
is `IndependentFresh`, their child sample
domains and distributions equal the target distribution, their source failure
classes/effects and `FreshChallengeContracts` are exact-equal and compatible,
the target event uses that same basis and recomputed sampling obligation, and
their final guard contributions are exact-equal under the coactivation law. The
one target public-coin index is the
declared many-to-one image of every member index. The sharing-policy group—not
the target randomness correlation—contains exactly the declared child members
and one collision-free source-member-to-target-occurrence map. Sharing is an
`IntentionalChange` unless the source model already declared that exact common
sample occurrence.

The single shared target `FreshChallenge` has one explicit position in
`interleaving`. It occurs after the mapped union of every member's causal
predecessors and required transcript-prefix events and before the mapped union
of every member's consumers and causal successors. Its target
challenge-prefix template is recomputed from the complete target schedule;
every member's event, value, challenge, failure, and prefix map names this same
occurrence and the exact corresponding target prefix. Cyclic union constraints
reject the spec. No first-member, last-member, deduplication, or ambient anchor
rule is permitted.

Derived and imported cases instead use a complete substitution disposition.
They produce an exact target value plus `ObservePublicValue` occurrence and
explicitly remove—not silently remap—the fresh randomness, sampling
obligations, sampling failure, and coin index. A derived value is a total pure
term over named source values. An imported value comes from a public-context
port and names an endpoint obligation owned by the unique
`PublicEnvironment`; it is not a prover obligation. The correlation effect is
respectively deterministic or external-public-input. These policies are typed
substitutions, not challenge-occurrence embeddings, and may constitute
`IntentionalChange`.

For `DerivedChallenge(sources, f, d)`, `d.value` is exactly
`Apply(f, the exact mapped source challenge values in the identity-bearing
declared source-sequence order)`.
For `ImportedChallenge(port, obligation, d)`, the port is a public `Context`
input of the unique `PublicEnvironment` with multiplicity `ExactlyOne`, and
`d.value` is exactly `PortValue(port, 0)`. In both cases
`d.observation_event` is exactly
`ObservePublicValue(d.value)`; in the imported case the named
endpoint obligation has that event as source, that public-environment owner,
that value as input, and action `ObservePublicValue`. References in one source
sequence are unique. Each source key resolves through its exact challenge
policy to that policy's target value. The induced graph from every derived
policy key to its source keys is acyclic, rejecting self-reference and
recursive substitution; it is evaluated in dependency-topological order while
preserving each function's declared argument order. All named source values
must be available before the observation. Admission checks these equations
and the four exact removals in the disposition, not only reference kinds. The
replacement event has the kind-exact `ObservePublicValueContracts` basis in
the target fragment, and its one recomputed endpoint obligation uses that
explicit contract; no source sampling contract is silently reused.

The private-randomness map is total over complete child bundles. Preserve and
joint policies name one exact target randomness/value/owner-obligation/failure
bundle per child; a joint group additionally names the one joint distribution
and every index/correlation fact. Derived and external policies remove the
child randomness entry, its exact occurrence in the owner's
`private_randomness` sequence, and the matching
`PrivateSamplingFailed(randomness)` declaration exactly once, and substitute
the named value. Their `owner_event_basis_rewrite.target_event` is the exact
mapped source event; its endpoint-contract basis is unchanged, while its
prover-construction basis is exactly the named replacement. The replacement
preserves every unaffected mapped input and output domain, removes exactly the
declared randomness members, and places each substituted value at its declared
input ordinal under an explicit target construction contract. Multiple
substitutions for one obligation must name one identical replacement basis and
collision-free substitution ordinals. `ExternalPrivateSupply` names a private input plus the exact
target prover obligation that consumes it. Recomputed target obligations and
failures must equal those dispositions; correlation or sampling obligations
cannot survive as stale structure.

`PreserveIndependent` is legal only for a child `IndependentFresh` source; the
target distribution, value/backlinks, owner obligation, and private-sampling
failure are its exact typed image and target correlation remains
`IndependentFresh`. All and only per-child `JointPrivateMember` entries with
one group ID form that target group. Each map entry names exactly one distinct
target bundle for its source key; the repeated joint-contract references are
exact-equal, no target bundle is repeated, and source keys to target member
indices form a bijection. Every target randomness declaration has one distinct
`JointMember(contract, group, index)`, the indices form a bijection with group
members, and the joint contract's checked marginal at each index equals that
child's distribution. Target availability order, the exact noncircular
`B_target`, owner-event guards, ordered conditional steps, and first tagged
`ProverDidNotProduce` outcome satisfy the
global joint-randomness equations. The named target obligation and failure
backlinks are exact for every member. A source joint group is structural only
under the same complete contract/member/index correspondence; combining,
regrouping, or changing it introduces an `IntentionalChange`.

For `DerivedPrivateValue(sources, f, d)`, `d.value` is exactly
`Apply(f, the mapped source private values in the identity-bearing declared
source-sequence order)`. References are unique, each resolves through the
exact policy for that source key, and the induced private-substitution graph is
acyclic and evaluated topologically without reordering a function's inputs. For
`ExternalPrivateSupply(port, obligation, d)`, the port is a private Prover
input with multiplicity `ExactlyOne`, `d.value` is exactly
`PortValue(port, 0)`, and the named target obligation
is the one recomputed from `d.owner_event_basis_rewrite` and consumes that
value at `d.owner_event_basis_rewrite.substituted_input_ordinal`. Source availability, function
domain/codomain, the declared deterministic or external distribution effect,
and every exact removal are checked. Neither constructor may leave a target
randomness declaration or private-sampling-failure backlink for the removed
source. Because the replacement construction contract may differ, each such
rewrite is an `IntentionalChange`; no obligation-preservation claim is inferred
from matching output domains.

`failure_policy` is total over every child verifier-visible failure occurrence;
`reach_exit_policy` is independently total over every child
`ReachTerminal` event occurrence. For an independent, joint-member, or shared
challenge, the
failure policy's target failure reference must equal the target fresh bundle's
`sampling_failure`; its source is exactly the target bundle's linked
`ChallengeSampling` source, and its class, effect, and observations must satisfy
the same constructor law below. A joint member additionally uses its exact
conditional-step failure at that index, and its effective guard and all later
member suppression equal the admitted group equations. Shared
challenge children may map to that one failure only within the declared shared
group. For a derived or imported challenge the corresponding failure policy is
exactly `RemovedByChallengeSubstitution` naming that child bundle. Every other
failure uses exactly one non-removal constructor.

Removal is legal only when the child sampling failure has `Terminate`, so no
available `FailureStatusValue` exists. Every child
`FailureOccurred(sampling_failure)` maps to the canonical target `false`
constant, and admission rejects any reachable status-value use or other branch
that assumes the removed failure can occur. This deterministic value rewrite
is part of the challenge substitution, not an ordinary origin map.

For every nonremoved failure, the target `FailureSourceRef` is exactly the
typed image of the child source under the checked event, check, challenge, and
randomness maps; its backlinks name that same target failure. The target class
is exactly the child class, and every child `FailureOccurred` maps to exactly
the target `FailureOccurred`. `PreserveContinue` is legal only for a child
`ContinueWithStatus` failure and names a target failure with the exact mapped
status effect and observation set; its child `FailureStatusValue` maps to the
target status value. `PropagateFailure` is legal only for a child
terminating failure and names a target failure whose effect is exactly
`Terminate(the mapped named target terminal)` with the exact mapped
observations; that target terminal's result and public outputs are the exact
typed image of the child failure terminal. `CaptureFailure` is legal only for
a child terminating failure and names a target failure whose effect is exactly
`ContinueWithStatus(the named FailureStatusValue of that same target failure)`;
its failure observations are the mapped child set with `Terminal` removed, and
the continuing status remains available. Its captured-exit value is exactly
`Tuple(FailureStatusValue(target failure),
CanonicalConstant(terminal_result_value_domain,
CanonicalTerminalResultValue(child terminal result)), mapped child terminal
public outputs...)` in that order, so capture
does not discard the terminating exit's result or payload before the combiner.
Because target class is preserved and `ExplicitProtocolAbort` is intrinsically
terminating, `CaptureFailure` is inadmissible for that class; an author who
needs a catchable signal must model a different continuing failure rather than
misname it an explicit abort. Capture is recorded as `IntentionalChange`; the other two are structural
preservation only when all these equalities hold.

`PropagateReach` names an event that is exactly
`ReachTerminal(the named target terminal)`: the target `TerminalDecl` has the
exact mapped child result and public outputs, and the complete target event
envelope (actor, inputs, guard, and protected observations) is the exact typed
image of the child reach event, including its `ReachTerminalContracts` basis,
except for an exact required suffix-suppression guard rewrite. `CaptureReach`
is an `IntentionalChange`. Its
status value is the exact canonical tuple of the terminal result and mapped
public outputs; its replacement is exactly a verifier
`ObservePublicValue(status)` event with the mapped and, when applicable,
suffix-rewritten original guard,
available inputs, and protected observations equal to the mapped set with
`Terminal` replaced by `PublicValue`.
The replacement has one explicit kind-exact `ObservePublicValueContracts`
basis and its recomputed endpoint obligation; changing from the source reach
contract is part of the declared intentional capture rather than an inferred
contract conversion.
Its raw status is exactly
`Tuple(CanonicalConstant(terminal_result_value_domain,
CanonicalTerminalResultValue(child terminal result)),
mapped child terminal public outputs...)` in that order. The enclosing sum
variant already identifies the exact child reach occurrence, so no duplicate
ambient occurrence label is placed in the value payload.
Each source occurrence and replacement appears once; an original exit cannot
survive beside its replacement.

v0 capture has one conservative claim-resource admissibility boundary.
`CaptureFailure` or `CaptureReach` is admitted only when direct symbolic
recomputation proves `CaptureClaimQuiescent(child, source)`:

- the source replacement cannot newly satisfy any mapped `AfterEvent` claim
  production that the child terminal-selecting occurrence suppressed;
- the child has no live linear claim at the captured exit;
- every child reduction that has not fired by that exit remains disabled at
  this and every later composite closure point under all mapped, shared, and
  locally added values and claims; and
- no mapped, shared, or locally added target reduction can consume a retained
  claim from that child after the exit.

The checker compares the complete guarded live-claim set and Claim observation
sequence at the child exit with the target prefix, then evaluates every later
target closure point using the target's ordinary claim semantics. If it cannot
prove quiescence, the composition spec is inadmissible; event suffix guards do
not substitute for this check. Persistent claims may remain only when the
proof above makes them inert. This deliberately makes some captures
unavailable in v0. A future regime may add an explicit claim-state freeze or
claim/reduction guard-rewrite disposition, but admission cannot simulate one
ambiently.

Each capture's `ExitStatusInjection.raw_status` is exactly its constructor's
complete captured-failure exit value or raw reach status, and
`injected_status` is exactly
`InjectVariant(sum_domain, variant_ordinal, raw_status)`. All captures for one
child use one exact closed sum domain, distinct declared variants with payload
domains matching their raw statuses, and one injection per raw capture. The
per-child `GuardedMerge` branches are these injected values, never the
heterogeneously typed raw values. Thus every branch has one domain without
erasing whether the source was a failure or a reached terminal.

Every capture carries a total suffix suppression. For `CaptureFailure`,
`exit_taken` is exactly `FailureOccurred(the named target failure)`; for
`CaptureReach`, it is exactly the final mapped guard contribution of the
captured reach event. For every later potential non-joint event origin of the
same child, its rewritten guard contribution is the mapped original or policy
base guard conjoined with the negation of the disjunction of all earlier
captured exits from that child. A one-origin event uses that contribution; a
shared event requires all member contributions equal under the central
coactivation rule. For a target joint group, suppression enters only its
per-source group-base contributions; those contributions must be exact-equal,
and member-final guards are then derived solely from the common base and
earlier member failures. No other guard rewrite is legal.
Every conjunction/disjunction/negation value and dependency edge introduced by
this equation is owned by that capture policy in the origin and causal-edge
partitions; it is neither an ordinary image nor an unaccounted local addition.
Consequently each child path selects exactly one captured status when it exits,
and first-exit behavior cannot leak later event or Claim observations into the
composite trace.

There is exactly one terminal-combiner input for each child slot that has a
captured source on any path that can reach the combiner, and no input for any
other slot. Its `merged_status` is one exhaustive one-hot `GuardedMerge`, and
every captured reach or failure contributes its exact injected status to
exactly one branch. Define a *combiner-reaching path* as a path on which
`ExecutionStillLiveBefore` holds at the first final event in `route_order`.
On every such path, every child slot has completed at exactly one captured
source, every combiner input has selected exactly one branch, and the input set
therefore contains exactly one entry for every child slot. A slot with no
combiner input must instead have a mandatory propagated exit on every path;
that makes every combiner final unreachable. These are checked path formulas,
not an assumption that a missing merge value will be supplied later.

Every target event that resolves a captured or propagated child terminal
source precedes every combiner final in both the recomputed causal-edge set and
`interleaving`; the final events occur in exact `route_order`. Thus all child
completion alternatives have resolved before a final can be attempted. If a
propagated failure or reach selected its target terminal, the operational
`ExecutionStillLiveBefore` conjunct makes every final unattempted. Admission
proves, for each final event, that `EventAttempted(final)` implies (a) no
propagated exit was selected, (b) exactly one captured completion is available
for every child slot, and (c) every `inputs[*].merged_status` is available.
Consequently a final cannot run before a later propagated exit, bypass an
uncompleted child, or read a conditionally absent status.

Admission requires `terminal_result_value_domain` to name an authenticated
finite value-domain contract whose canonical inhabitants are exactly
`CanonicalTerminalResultValue(tag)` for the tags in `result_domain`, with no
other inhabitant. Every captured terminal-result constant uses this same
contract. It also requires
`result_value = Apply(result_function, inputs[*].merged_status)` and requires
the function's codomain to equal `terminal_result_value_domain` and its range
to cover only `result_domain`. For every non-last `route_order` tag, the
final guard is exactly the canonical `GuardDecision` whose sole atom is
`FiniteValueEquals(result_value,
CanonicalTerminalResultValue(tag))`. The last and only
`UnguardedFallback` is materialized as the canonical true guard;
`ExecutionStillLiveBefore` prevents it from being attempted after an earlier
route reaches its terminal. For each route, `public_output_tuple` is exactly
`Apply(public_output_function, inputs[*].merged_status)`, and
`public_output_values` is the
canonical sequence of every `Project(public_output_tuple, i)` with the exact
declared product-domain order. The final terminal has
`TerminalDecl.result == tag` and exactly those public outputs, and the final
event is exactly `ReachTerminal(that terminal)`. Thus routes and their output
payloads are one-hot and exhaustive while `TerminalDecl.result` remains
static.

Spec admission proves every equality above, every captured suffix rewrite,
and exact occurrence coverage. For every execution with a complete active
prover trace and private-sampling supply, the admitted target reaches either an
explicit propagated exit or exactly one combiner route. `ProverDidNotProduce`
remains the separate nonterminal-trace outcome. Capturing any standalone child
exit or changing a failure effect is an intentional semantic change, never a
preservation theorem.

```text
CoreCompositionSpecId = H(
  "zkc/core-composition-spec",
  CompositionRegimeId,
  target_protocol_regime_id,
  CanonicalEncode(children, face_maps, ordinary_origin_maps,
                  terminal_origin_map, locally_added,
                  causal_seams, locally_added_causal_edges, interleaving,
                  challenge_policy, private_randomness_policy,
                  failure_policy, reach_exit_policy,
                  terminal_combiner, target_fragment))
```

`CoreCompositionSpecId` commits to the Composition regime, target Protocol
regime, ordered child Core IDs and occurrence slots, and canonical
specification content. Authentication recomputes that identity and all
dependency references but cannot validate child shape from IDs alone.

```text
ExactCompositionSpecDependencyPreimageBundle =
  ExactMap<LocalTargetDependencyRef,
           AuthenticatedDependencyPreimageInput>

AuthenticateCoreCompositionSpec(
  raw candidate,
  ExactCompositionSpecDependencyPreimageBundle,
  ExactCompositionSpecDependencyAuthenticationCapabilities)
  -> AuthenticatedCoreCompositionSpec

AdmitCoreCompositionSpec(
  AuthenticatedCoreCompositionSpec,
  exact ordered CanonicalSeq<AdmittedCoreView>)
  -> AdmittedCoreCompositionSpec
```

Authentication checks closed physical/local-reference form, authenticates
every and only dependency preimage declared by `target_fragment.dependencies`
under the full local typed key, verifies kind/regime/ID/ABI/direct-edge
equality, recomputes the spec identity, and retains attenuated immutable
dependency views. Child IDs remain data at this point and grant no child-shape
authority.

Admission first computes the target's least required dependency-key closure
from the complete target constructors and declared direct edges. That key set
must equal the authenticated target-fragment dependency bundle exactly. For
each required key, it selects every child view that the admitted origin maps
make reachable at that key and deduplicates those views only when their
authenticated preimages, ABIs, and direct edges are exactly equal. A conflict
among reachable views rejects. If no reachable child view supplies a required
key, the exact authenticated target dependency view retained by spec
authentication is its local supply and the matching dependency ref must be
covered by `locally_added`. Conversely, a locally supplied dependency cannot
claim a key supplied by a reachable child origin. The selected reachable-child
views plus these local views must equal the authenticated target bundle
exactly. Unreachable child dependency history is neither conflict-checked nor
retained as target semantics. Live views and checker capabilities do not enter
the spec ID. The admitted spec retains only the required attenuated immutable
views through target subadmission.
`AdmitCoreCompositionSpec` therefore consumes the exact ordered live
`AdmittedCoreView`s, checks their IDs, and requires every child view's
`ProtocolSemanticRegimeId` to equal `target_protocol_regime_id` exactly.
Stage 3 v0 has no cross-regime composition: such a construction requires a
future explicit semantic-translation subject and checked relation rather than
constructor copying under a different regime. Admission then checks totality
and typing of every
map, the disjoint and exhaustive ordinary/terminal/local origin partition, the
exact causal-edge union, the full local target fragment, interleaving, face,
challenge,
private-randomness, failure, reach-exit, and combiner laws, and closed inputs.
The resulting capability retains the child views and the exact selected target
dependency views. It neither
constructs nor admits the target, and serialized child IDs carry no authority.

### 10.2 Construction and checking

Composition-map realization is a deterministic checked projection, not a
caller-supplied or transaction-carried authority object. Its closed carrier is:

```text
TargetRefInstantiation = {
  dependencies: Bijection<LocalTargetDependencyRef, CoreRef<dependency>>,
  roles: Bijection<LocalTargetRoleRef, CoreRef<role>>,
  ports: Bijection<LocalTargetPortRef, CoreRef<port>>,
  values: Bijection<LocalTargetValueRef, CoreRef<value>>,
  objects: Bijection<LocalTargetObjectRef, CoreRef<object>>,
  randomness: Bijection<LocalTargetRandomnessRef, CoreRef<randomness>>,
  challenges: Bijection<LocalTargetChallengeRef, CoreRef<challenge>>,
  events: Bijection<LocalTargetEventRef, CoreRef<event>>,
  claims: Bijection<LocalTargetClaimRef, CoreRef<claim>>,
  reductions: Bijection<LocalTargetReductionRef, CoreRef<reduction>>,
  checks: Bijection<LocalTargetCheckRef, CoreRef<check>>,
  failures: Bijection<LocalTargetFailureRef, CoreRef<failure>>,
  terminals: Bijection<LocalTargetTerminalRef, CoreRef<terminal>>,
  endpoint_obligations:
    Bijection<LocalTargetEndpointObligationRef,
              CoreRef<endpoint_obligation>>,
  prover_obligations:
    Bijection<LocalTargetProverObligationRef,
              CoreRef<prover_obligation>>,
  prover_obligation_failures:
    Bijection<LocalTargetProverObligationFailureRef,
              CoreRef<prover_obligation_failure>>
}

ResolvedCoreCompositionMaps = {
  composition_spec_id: CoreCompositionSpecId,
  child_occurrences: CanonicalSeq<(ChildOccurrenceRef, CoreId)>,
  target_core_id: CoreId,
  target_refs: TargetRefInstantiation,
  face_maps: ResolveTargetRefs<CanonicalSeq<LocalTypedFaceMap>>,
  ordinary_origin_maps: ResolveTargetRefs<OrdinaryOriginMaps>,
  terminal_origin_map:
    ResolveTargetRefs<TotalMap<LocalChildInnerTerminalRef,
                               TerminalOriginDisposition>>,
  locally_added: ResolveTargetRefs<CanonicalSet<LocalTargetCoreRef>>,
  causal_seams:
    ResolveTargetRefs<CanonicalSet<
      (LocalChildInnerEventRef, LocalChildInnerEventRef)>>,
  locally_added_causal_edges:
    ResolveTargetRefs<CanonicalSet<
      (LocalTargetEventRef, LocalTargetEventRef)>>,
  challenge_policy:
    ResolveTargetRefs<TotalMap<LocalChildChallengeBundleRef,
                               ChallengePolicy>>,
  private_randomness_policy:
    ResolveTargetRefs<TotalMap<LocalChildPrivateRandomnessBundleRef,
                               PrivateRandomnessPolicy>>,
  failure_policy:
    ResolveTargetRefs<TotalMap<LocalChildFailureOccurrenceRef,
                               FailurePolicy>>,
  reach_exit_policy:
    ResolveTargetRefs<TotalMap<LocalChildInnerReachTerminalEventRef,
                               ReachExitPolicy>>,
  terminal_combiner: ResolveTargetRefs<TotalTerminalCombiner>,
  target_interleaving: Permutation<CoreRef<event>>,
  derived_role_origins:
    TotalMap<ChildInnerRef<role>, CoreRef<role>>,
  derived_dependency_origins:
    TotalMap<ChildInnerRef<dependency>, Optional<CoreRef<dependency>>>,
  derived_endpoint_obligation_origins:
    TotalMap<ChildInnerRef<endpoint_obligation>,
             Optional<CoreRef<endpoint_obligation>>>,
  derived_prover_obligation_origins:
    TotalMap<ChildInnerRef<prover_obligation>,
             Optional<CoreRef<prover_obligation>>>,
  derived_prover_obligation_failure_origins:
    TotalMap<ChildInnerRef<prover_obligation_failure>,
             Optional<CoreRef<prover_obligation_failure>>>
}

ResolvedCompositionFieldFamily =
    FaceMap | OrdinaryOrigin | TerminalOrigin | LocalAddition
  | CausalSeam | LocalCausalEdge | ChallengePolicy
  | PrivateRandomnessPolicy | FailurePolicy | ReachExitPolicy
  | TerminalCombiner | TargetInterleaving | DerivedRoleOrigin
  | DerivedDependencyOrigin | DerivedEndpointObligationOrigin
  | DerivedProverObligationOrigin
  | DerivedProverObligationFailureOrigin

CoreCompositionEquationPath =
    SubjectIdentity(CoreCompositionSpecId | ChildOccurrenceRef | CoreId)
  | TargetReference(RefKind, LocalTargetCoreRef)
  | ResolvedField(ResolvedCompositionFieldFamily,
                  CanonicalTypedKeyPath)

CoreCompositionComparisonFact = {
  path: CoreCompositionEquationPath,
  expected: CanonicalTypedValueAt(path),
  actual: Absent | CanonicalTypedValueAt(path)
}

CoreCompositionCheckedPayload =
    Affirmative(ResolvedCoreCompositionMaps)
  | Negative(
      mismatches: NonEmptyCanonicalSet<CoreCompositionComparisonFact>,
      unaffected_agreements: CanonicalSet<CoreCompositionComparisonFact>)
```

`ResolveTargetRefs<T>` is one regime-owned total type-directed operation: it
replaces every `LocalTargetRef<K>` in `T` through the matching member of
`TargetRefInstantiation`, replaces every local child slot by the corresponding
`ChildOccurrenceRef`, and otherwise preserves product order, sum tags, map
keys, sets, ordinals, and literals exactly. It cannot drop, add, rename, or
coerce a reference. Each instantiation member is the unique same-kind
ordinal-preserving bijection between the complete target-fragment family and
the independently admitted target Core family. The five derived-origin maps
are recomputed from the admitted construction equations: `Optional.None`
means exactly an unreachable dependency removed by closure or an obligation
removed by an explicit admitted substitution; it is not a free deletion.

`ResolveCoreCompositionMaps(admitted spec, admitted target Core view)
-> CoreCompositionCheckedPayload` is a pure total comparison over those exact
admitted operands. It directly checks every resolved field and derived origin
against both operands and has no raw-map parameter. Exact agreement returns
the unique map record in the affirmative variant. Any mismatch returns the
negative variant; no partial map record is produced.
The resulting negative `CheckedCoreComposition` capability retains the exact
operands, regime, nonempty typed mismatch facts, and unaffected agreements,
but no `ResolvedCoreCompositionMaps`. An affirmative capability retains the
unique resolved record. Only that affirmative variant can inhabit
`CompositionContextAuthority`; neither payload alone is an admission witness
or composition authority.

The challenge interpretation is an explicit later operation input rather than
a hidden constructor choice:

```text
ConstructAndSubadmitCore(
  AdmittedCoreCompositionSpec,
  ExactCoreAdmissionCheckerCapabilities)
  -> CanonicalCoreCandidate
     + transaction-scoped CoreAdmissionWitness
     + transaction-scoped ScopedCompositionFormationAuthority

FiatShamirFormationInput = {
  candidate: CanonicalTranscriptConstructionCandidate,
  algorithm_dependency_preimages:
    ExactTranscriptAlgorithmDependencyPreimageBundle,
  dependency_authentication_capabilities:
    ExactTranscriptDependencyAuthenticationCapabilities,
  law_checker_capabilities: ExactTranscriptLawCheckerCapabilities,
  formation_authority:
    transaction-scoped ScopedCompositionFormationAuthority
}

ChallengeInterpretationInput =
    FreshPublicCoins
  | FiatShamir(FiatShamirFormationInput)

FormAndAdmitProtocol(
  CanonicalCoreCandidate,
  transaction-scoped CoreAdmissionWitness,
  ChallengeInterpretationInput,
  target_protocol_regime_id)
  -> AdmittedProtocol

FinalizeCoreComposition(
  AdmittedCoreCompositionSpec,
  AdmittedProtocol)
  -> Qualified<CheckedCoreComposition>

ReplayAndAdmitComposedProtocol(
  AuthenticatedCanonicalProtocolCandidate,
  AdmittedCoreCompositionSpec,
  ExactProtocolAdmissionCheckerCapabilities)
  -> Qualified<AdmittedProtocol, CheckedCoreComposition>
```

The Core checker capability supplied to `ConstructAndSubadmitCore` must match
the target Protocol regime and every exact admitted dependency view retained by
the spec. It is used only to evaluate `CoreAdmissible` and mint the
transaction-scoped witness/formation authority; it is not stored in the spec,
target identity, or result. An initial formation caller supplies it directly,
while cold replay forwards the exact `.core` capability described below.
Construction and finalization recheck that the target Protocol and every
retained child Core view are in the spec's exact
`target_protocol_regime_id`; a regime mismatch cannot reach map resolution.

`ScopedCompositionFormationAuthority` is an opaque linear process-local
capability retaining exactly the admitted composition spec, the target
`CoreAdmissionWitness`, the target `CoreId`, and an unforgeable invocation
token for this `ConstructAndSubadmitCore` call. The invocation token is neither
semantic data nor serializable. The authority carries no caller-selected map
bundle; all maps are recomputed by `ResolveCoreCompositionMaps` from the exact
admitted operands.

For the FS branch, the construction cannot already be admitted against a Core
that did not exist. It is authenticated and admitted inside this transaction
against the exact scoped Core witness and the exact formation authority carried
by the `FiatShamir` formation record. The record contains every and only the
inputs to `AuthenticateTranscriptConstruction` and
`AdmitTranscriptConstruction`; candidate, dependency bundle, both capability
sets, Protocol regime, construction identity, target Core, and composition
context must match exactly, and any missing, extra, or mismatched member is
refused. Its authority must have been minted by this same
`ConstructAndSubadmitCore` invocation and must retain the identical admitted
spec, target Core witness, and target `CoreId`; cross-transaction or wrong-spec
authority is refused. It is consumed during construction
admission and discarded if enclosing Protocol admission fails. The Fresh
variant carries no such authority and cannot invoke construction admission.
The Core construction itself is independent of the selected challenge
interpretation; only the explicit `FormAndAdmitProtocol` input chooses Fresh
or FS.

`ReplayAndAdmitComposedProtocol` is the cold-reopen path. It reruns
`ConstructAndSubadmitCore` from the freshly reconstructed admitted composition
spec and its retained ordered child and selected target dependency views,
forwarding the `.core` member of the supplied exact Protocol-admission checker
bundle;
requires the resulting canonical Core body, regime, and `CoreId` to equal the
authenticated persisted Protocol candidate exactly; and only
then uses the explicitly supplied checker capabilities and newly minted scoped
formation authority to admit a composed FS
construction and the enclosing Protocol. Fresh follows the same equality
path and requires the transcript-construction checker component absent. The
capability bundle is typed to the exact Core dependencies and, for FS, the
exact construction/algorithm dependency identities; missing, extra, or
mismatched capabilities are refused and none is retained in semantic identity.
Finally it reruns
`FinalizeCoreComposition`. A serialized composition result, spec ID, child-ID
list, prior scoped witness, or prior checked capability may guide material
selection but grants no authority. This operation reconstructs every live
capability in the new process and breaks the apparent composed-FS bootstrap
cycle.

The operations perform:

1. assign distinct child occurrence tags;
2. validate every face map and reject port/domain/direction aliasing that is
   not explicitly permitted;
3. apply the exact ordinary- and terminal-origin maps, derived role maps, and
   policy-owned local reference maps into the target namespace; no origin is
   recovered by renaming or structural matching;
4. apply the complete challenge and private-randomness policies plus only the
   explicit Core context ports and face data;
5. apply the total failure and reach-exit policies, the central ordinary,
   shared, and joint guard equations, suffix suppression, and the total
   terminal combiner, then close every value, object, event, claim, reduction,
   check, failure, and terminal constructor;
6. now construct the exact mapped, seam, policy-derived, and locally added
   causal-edge union from those closed constructors, prove it acyclic, and
   require the one declared `interleaving` schedule to extend it;
7. only after every target constructor and rewrite is fixed, compute the least
   reachable target dependency closure from exact child and local preimages
   under typed regime/identity/ABI equality, dropping unreachable history and
   never resolving by mnemonic;
8. recompute the complete endpoint obligations, prover obligations, and
   prover-obligation failures from the closed target events and randomness,
   require exact equality with the target fragment, and construct one target
   Core candidate;
9. directly recompute its canonical semantic encoding and `CoreId`, check
   `CoreAdmissible`, and retain the resulting `CoreAdmissionWitness` only
   inside the transaction; mint the matching scoped composition-formation
   authority from that witness, the admitted spec, target `CoreId`, and this
   invocation token;
   this is a subcheck, not authentication of a standalone Core carrier;
10. consume the explicit challenge-interpretation input; for FS, validate its
    `ExactCompositionContext` against the formed Core and exact context-port
    map, require and consume the matching transaction-scoped formation
    authority, and authenticate and admit the construction against the scoped witness;
    then form,
    authenticate, and admit the enclosing target Protocol;
11. attenuate its `AdmittedCoreView`, directly recompute every map against the
    exact spec and admitted child Core views by
    `ResolveCoreCompositionMaps`, and mint the checked
    `CheckedCoreComposition` capability with either the unique affirmative
    resolved maps or the nonempty exact negative mismatch facts; and
12. discard the transaction witness and scoped
    composition-formation authority.

No `CheckedCoreComposition` capability outlives target authority: every
variant retains the exact admitted child Core views and the target's
attenuated `AdmittedCoreView`; only its affirmative variant retains the unique
`ResolvedCoreCompositionMaps` and grants checked composition-context
authority. A
durable result, when a named consumer justifies one, binds the spec ID, child
Core IDs and slots, target Core ID, regimes, checker identity, outcome, and
either affirmative maps or negative mismatch/agreement facts;
after serialization it must be rechecked against newly admitted views.

The map algebra is explicit:

- ordinary child value, object, event, claim, reduction, and check maps are
  injective occurrence embeddings; port/value substitutions and policy-owned
  families use their separately declared exact maps, while obligations and
  obligation failures are deterministically recomputed rather than ordinary
  origins;
- repeated equal child IDs still receive disjoint `ChildOccurrenceRef`s;
- independent challenges map injectively to distinct target challenges;
- a joint-challenge group maps members injectively to distinct ordered target
  challenge bundles under one exact joint contract;
- a shared-challenge group has a declared many-to-one child-to-target map;
- a derived child challenge maps each child occurrence to an exact target
  value term and public-observation occurrence rather than a fresh target
  challenge; a later target FS construction recomputes transcript actions and
  prefixes over that already formed Core rather than consuming a hidden
  substitution template; and
- an imported child challenge maps to an exact external context port, target
  value, public-observation occurrence, and admission obligation, not a target
  challenge occurrence. No child or ambient transcript grants that authority
  implicitly, and no trace or property preservation is inferred from this
  substitution; and
- every child failure occurrence maps through its exact `FailurePolicy`, and
  every child `ReachTerminal` occurrence maps through its exact
  `ReachExitPolicy`: propagated exits terminate immediately, while captured
  reach/failure exits map to typed status occurrences, suppress the same
  child's suffix, and feed one declared total-combiner input; and
- every child private-randomness source maps explicitly to an independent
  target source, a declared joint distribution, a derived private value, or an
  external private supply obligation. Sharing or correlating prover randomness
  is never inferred from common types or suppliers.

Under the admitted child-to-target event relation, including every explicit
substitution, removal, and many-to-one challenge map, the selected target-event
interleaving must be a linear extension of every child schedule, every child
causal edge, and every declared seam. Composition explicitly
closes guards, role knowledge, randomness and correlation, transcript and wire
observations, claims, checks, continuing and terminating failures, exit
propagation, suffix suppression, terminal capture and combination,
dependencies, endpoint obligations, and prover obligations.

`CoreId` commits only to the exact intrinsic bounded-normal-form target
encoding. Arbitrary child tag spelling, elaborator order, and construction
history are removed before target numbering; target occurrences receive
canonical hygienic ordinals. If two composition histories produce that same
encoding, they have the same `CoreId`; their composition specifications and
checked map results remain distinct. If child origin, grouping, or domain
context is observed by the target, it must be an explicit target field and
changes `CoreId`. Behavioral equivalence alone does not imply equal IDs.

### 10.3 Laws and non-laws

Composition has no universal commutativity, associativity, idempotence, or
identity law. A constructor-specific relation may establish one law only under
exact face, schedule, challenge, failure, terminal, and observer premises.
Repeated use of one child is never idempotent by equal `CoreId`.

Authoring `link` may assemble symbols, regions, or proposal graphs and may
produce a `CoreCompositionSpec`. It remains unauthoritative until the full
construction, target authentication/admission, and map checks succeed.

Composition consumes Core views, not the challenge interpretations of child
Protocols. The target independently selects Fresh or an exact FS construction.
Already-FS child status is not inherited, and
`FS(compose(children))` is not assumed equal or related to
`compose(FS(children))`; any such statement needs its own exact construction
maps and later checked relation.

Structural `CoreComposition` proves no cryptographic property. Property
composition and transport belong to Analysis.

## 11. Narrow views and ownership

No consumer receives a universal fact root. PIR owns purpose-specific immutable
views and their adequacy predicates:

| Consumer | Exact source view | Additional identified inputs | Consumer-owned result |
|---|---|---|---|
| Relations | ports, objects, claims/checks/terminals, typed obligations, occurrences | exact Interface, relation interface, binding, question, and checked artifact comparison or grounding when requested | correspondence |
| Analysis | events, schedule, challenges, checks, claims, failures, maps | exact question, model, assumptions, optional Interface/Plan when read | qualified judgment |
| Compiler | admitted predecessor facts and declared transformation surface | exact candidate, relation, objective inputs | checked edge and selection decision |
| OIR | events, ports, obligations, failures, occurrences | exact Interface, role, tagged Plan basis | OIR and projection relation |

An adequacy predicate states that the view contains every source fact a named
consumer question may read. The view is derived from an admitted subject and
does not acquire an independent semantic identity unless a named durable
cross-process consumer requires one.

## 12. Authority and persistence

The common lifecycle for identity-bearing Stage 3 subjects is:

```text
candidate
  -> physical authentication
  -> domain admission
  -> opaque immutable process-local capability
```

Construction and checked-relation lifecycles add independent target admission:

```text
proposal + admitted inputs
  -> construct candidate
  -> authenticate target
  -> admit target
  -> check exact relation
  -> result capability
```

A carrier, semantic ID, digest, serialized marker, provenance record,
signature, or producer report never substitutes for the capability. After a
process, FFI, mutation, reopen, or serialization boundary, a consumer starts
with raw material and recreates authority only by the owning checks.

Official semantic persistence is admission-gated. Workbench caches and
proposal packages must be unmistakably unauthoritative. Durable checked
results are introduced only for a named independent consumer and bind all
subjects, regimes, inputs, checker identity, qualified outcome, and residual
trust; their bytes still carry no live capability.

## 13. Qualified outcomes

Each owner defines its own result type using these distinct semantic classes:

```text
Affirmative
Negative(reason, retained_facts)
Unsupported(exact unsupported construct or question)
CannotAnswer(missing named semantic input or basis)
Refused(missing authority or prohibited invocation)
Malformed(exact input framing or structural defect)
CheckerFailure(operational failure with no semantic conclusion)
```

Not every predicate needs every class. Direct total predicates ordinarily
return affirmative or negative; boundary operations may additionally refuse or
report malformed inputs. Absence of support or inputs never becomes a negative
semantic judgment.

## 14. Direct recomputation and checker placement

Use direct recomputation for:

- semantic identity and dependency closure;
- canonical PIR physical form;
- Core and dependent-subject admission;
- Interface map preservation;
- Plan well-formedness and `PlanRealizes` structural coverage;
- relation binding form and field correspondence;
- FS construction and occurrence/prefix maps; and
- Core composition construction and structural maps.

Use a proposal plus an independent domain validator only when a producer may
search or use heuristics but the complete predicate remains executable. Use a
theorem/model-backed judgment for `FSCompile`, property transport, semantic
equivalence/refinement, satisfaction, completeness, or cryptographic claims.

There is no open universal checker registry. Every checker is selected by its
owned relation kind and exact semantic regime.

## 15. Clean-room non-claims

The selected semantic architecture, if admitted after validation, would not by
itself establish:

- faithful representation by the current implementation;
- relation truth, satisfiability, or witness validity;
- soundness, knowledge, completeness, zero knowledge, or Fiat--Shamir
  security;
- compiler preservation, optimality, or target selection;
- OIR projection correctness or endpoint support;
- prover termination, cost, performance, or supplier correctness;
- formal-model adequacy or proof-assistant verification;
- artifact provenance, independent review, or production readiness; or
- compatibility with a prior or future semantic regime.

Those conclusions require their separately owned subjects and judgments.
