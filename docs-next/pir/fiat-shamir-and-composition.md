# Fiat--Shamir construction and semantic Core composition

> **Document kind:** Target semantic specification
> **Document state:** Active non-normative target
> **Target status:** Stage 3.5 durable promotion
> **Provisional owner:** `pir`
> **Authority:** This document specifies the selected target for `docs-next/`.
> It is not normative until explicit consolidation and cutover. The current
> specifications under [`docs/`](../../docs/README.md) remain authoritative.
> This document makes no implementation, compatibility, or migration claim.

> **K1 transition notice — 2026-08-26:** The algorithm, dependency, value,
> execution-capability, and `H(...)` identity forms retained below are pre-K1
> Stage 3 placeholders. [Executable Semantic Foundations](../foundation/executable-foundations.md)
> owns the exact selected substrate. K2 must refine every semantic algorithm position to an
> exact PIR-owned `PortableAlgorithmRef`, authenticate each supplied candidate
> against its own `DirectPrimitiveRefs`, `DirectModuleRoots`, and
> `RequiredModuleClosure_B`, and define the exact Foundation `ValueType`s used
> by transcript state, codecs, and challenge results. Primitive references stay
> direct; only module imports form a transitive preimage DAG. Strong
> Fiat--Shamir closure is therefore still a K2 obligation.

## 1. Scope and design center

This document defines two PIR-owned structural constructions:

1. a fresh-public-coin Protocol to Fiat--Shamir Protocol construction; and
2. semantic composition of admitted Core views into one new Core and Protocol.

Both use the same non-collapsible lifecycle:

~~~text
admitted source subjects + admitted construction specification
  -> deterministic target candidate
  -> independent target authentication and admission
  -> direct exact source/target relation check
  -> qualified checked-result capability
~~~

Construction never authorizes its output. Target admission never proves the
source/target relation. A checked structural relation never proves a
cryptographic property. The selected
[Protocol IR architecture](../project/protocol-ir-architecture.md) owns this
factorization, while the
[transition and bridge architecture](../project/transition-and-bridge-architecture.md)
owns its shared authority, replay, and outcome constraints. The
[Protocol semantic model](protocol-model.md) owns the Core and Protocol subjects
consumed and constructed here. [Canonical PIR](canonical-pir.md) owns their
carrier, persistence, decoding, and replay representation. The
[PIR domain index](README.md) remains the ownership map.

All normative reads are explicit immutable fields, retained admitted views, or
identity-matched process-local capabilities. Unknown meaning-bearing
constructors, regimes, references, dependency kinds, and algorithms fail
closed. No ambient current Protocol, transcript, resolver, composition,
checker registry, or target is permitted.

## 2. Common authority and result discipline

### 2.1 Regimes, references, canonical encoding, and algorithms

The typed regimes used here are:

~~~text
ProtocolSemanticRegime
FSConstructionRegime
CompositionRegime
~~~

`TranscriptConstruction` deliberately uses the exact Protocol semantic regime;
reusable framing, codec, hash, duplex, and sampler contracts remain typed
dependency identities. A semantic regime is not a tool, carrier, package,
policy, or checker version. A meaning change requires a new typed regime and
therefore a new semantic identity.

Before a root identity exists, candidates use:

~~~text
LocalRef(kind, canonical_ordinal)
~~~

Authenticated intrinsic references and interpretation-qualified references
are:

~~~text
CoreRef<K> = (CoreId, K, canonical_ordinal)
ProtocolScopedRef<K> = (ProtocolId, CoreRef<K>)
~~~

Kinds are not interchangeable. Fresh and FS Protocols may share one inner
Core reference but never the scoped reference.

Composition uses acyclic local child slots before spec authentication:

~~~text
LocalChildOccurrenceRef = child_slot
LocalChildInnerRef<K> = (child_slot, child CoreRef<K>)
~~~

Only afterward are durable occurrence tags formed:

~~~text
ChildOccurrenceRef = (CoreCompositionSpecId, child_slot)
ChildInnerRef<K> = (ChildOccurrenceRef, child CoreRef<K>)
~~~

Two uses of one `CoreId` are distinct child occurrences without creating two
child semantic identities.

For every regime `R`, `CanonicalEncode_R(T)` is injective and structural:
sums carry domain-separated tags; products use declared field order;
sequences carry length and order; maps and sets sort canonical keys and reject
duplicates; optionals carry absent/present tags; references encode subject
family and typed key; and scalars use the regime's unique mathematical
encoding. Printer spelling, MLIR bytecode, host layout, iteration order,
source position, pointer identity, and process identity do not enter the
preimage.

Algorithm-bearing fields are canonical data:

~~~text
CanonicalAlgorithmSpec<K> =
    ClosedFiniteTerm(kind = K, typed syntax, declared totality evidence)
  | ContentAddressedContractRef(
      kind = K,
      contract_regime_id,
      regime_qualified_content_id,
      exact ABI,
      direct_dependency_ids)

DomainSeparatedInitialization =
  CanonicalAlgorithmSpec<TranscriptInitialization>
InitializationAction =
  CanonicalAlgorithmSpec<InitializeFromTypedContextValue>
SqueezeAndSampleRule =
  CanonicalAlgorithmSpec<TranscriptConditionalChallengeSample>
InjectiveFramingContract =
  CanonicalAlgorithmSpec<InjectiveTranscriptFraming>
InjectiveTypedCodec =
  CanonicalAlgorithmSpec<InjectiveTypedTranscriptAtomCodec>

CanonicalStaticContext = {
  language_id: RegimeQualifiedContentId,
  argument_system_id: RegimeQualifiedContentId,
  application_domain_id: RegimeQualifiedContentId,
  static_parameters:
    CanonicalMap<RegimeQualifiedFieldId,
                 CanonicalStaticScalarOrSequence>
}

RegimeQualifiedFieldId =
  (ContractRegimeId, RegimeQualifiedContentId)

CanonicalStaticScalar =
    Boolean
  | UnsignedInteger
  | FiniteByteString
  | RegimeQualifiedContentId

CanonicalStaticScalarOrSequence =
    CanonicalStaticScalar
  | CanonicalSeq<CanonicalStaticScalar>
~~~

`CanonicalStaticContext` contains only regime-qualified language,
argument-system, and application-domain IDs plus a finite canonical map of
tagged Boolean, unsigned-integer, finite-byte-string, or
regime-qualified-content-ID scalars and finite sequences. It contains no
callback, registry key, clock, ambient string, or runtime port value.

Content-addressed algorithms require exact authenticated preimages and the
least typed dependency closure; closed finite terms have no external entry.
Live implementations and checker capabilities are outside semantic identity.
Satellite transport is permitted only through a total tagged lossless decode
to the exact canonical algebraic value.

### 2.2 Authentication, admission, and replay

A content ID, carrier, serialized capability, signature, producer report, or
prior result never grants authority. Each identity-bearing subject follows:

~~~text
candidate
  -> physical and dependency authentication
  -> domain admission
  -> opaque immutable process-local capability
~~~

Construction relations additionally require independently admitted source and
target operands. After serialization, FFI, mutation, reopening, or a process
boundary, replay reconstructs every dependency view and capability and reruns
the owner checks.

Official Protocol and construction-spec persistence is admission-gated.
Workbench caches and proposal packages remain explicitly unauthoritative. A
durable checked result is introduced only for a named independent consumer and
binds the exact subject tuple, regimes, operation inputs, checker identity,
qualified outcome, and residual trust. Its bytes carry no live authority.

Semantic identity and dependency closure, transcript action/prefix maps, FS
construction maps, Core composition construction, and composition maps are
directly recomputed. There is no open universal checker registry; every
checker is selected by its owned relation and exact semantic regime.

### 2.3 Qualified checked results

Owner operations preserve these semantic distinctions where applicable:

~~~text
Affirmative
Negative(reason, retained_facts)
Unsupported(exact unsupported construct or question)
CannotAnswer(missing named semantic input or basis)
Refused(missing authority or prohibited invocation)
Malformed(exact framing or structural defect)
CheckerFailure(operational failure with no semantic conclusion)
~~~

A completed negative is a checked result. Unsupported, missing-input,
refused, malformed, and operational-failure outcomes are not negative truth.

`Qualified<CheckedX>` creates the exact `PirCheckedResultCoordinate<X>` defined
by [Canonical PIR](canonical-pir.md#51-cross-owner-capability-contract-and-inert-bindings)
and mints the distinct opaque process-local checked capability only for a
completed affirmative or negative semantic outcome. The
capability retains exact operands, question, regime, field-factored result,
checker identity, dependency/read closure, and the complete
`ExactCheckedResultAuthorityBinding`, including the authenticated
`OwnerDefinesNoOperationPolicy(PirCapabilityContractId<CheckedX>, exact
capability ABI)` disposition. `Unsupported`, `CannotAnswer`, `Refused`, `Malformed`, and
`CheckerFailure` create neither result coordinate nor checked capability.
Serialized result bytes are not that capability and cannot be
widened to another subject, regime, question, or conclusion.

For `CheckedFSConstruction`, both completed variants retain the exact source,
target, construction, maps-as-checked-operand, regime, and field-factored
result; a negative does not receive the composition-specific A-only map rule.
Neither variant grants theorem or property authority. Core composition has the
stricter A/N payload and authority rule in Section 6.2.

## 3. Transcript construction

### 3.1 Complete subject

~~~text
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
~~~

Initialization binds the construction suite, `CoreId`, type/message framing,
language or argument-system identifier, and exact static application domain.
Per-invocation session context enters only through every public Core
`Context`-input occurrence and the identity-bearing
`session_context_map`. That map is total and ordered by port ordinal, then
occurrence ordinal. Runtime values do not create a new Protocol identity.
Labels and ambient caller strings are insufficient domain separation.

### 3.2 Exact action and failure surface

Every Core event has one and only one action:

- a non-challenge event with `Transcript` protected observation has one
  nonempty `Absorb` when `EventActionOccurs`;
- a `FreshChallenge` event has one matching `DeriveChallenge` when its action
  occurs; and
- every other event has `NoTranscriptAction` and cannot claim a transcript
  observation.

Each absorbed atom names an in-range input occurrence of the same event.
Atoms cover every and only input ordinal once, in canonical input order, and
each semantic type equals the referenced value or object's exact domain.
There is no event-output transcript source. Value-producing effects use
separately declared values and bindings, so transcript material enters through
the closed event-input sequence.

Initialization, framing, context initialization, and absorb-codec algorithms
have total infallible Protocol-facing ABIs on admitted inputs.
`DeriveChallenge` is the sole fallible transcript transition. Its rule returns
either the exact challenge value or the challenge-indexed sampling failure.
`abort_map` is total over challenge occurrences and maps each challenge to its
one linked `ChallengeSampling` failure. There is no construction-only verifier
failure.

For a public `JointMember` group, all member derivations cite one exact joint
contract and cover its complete index range in Core exposure order. Member
`i` consumes the exact earlier successful component domains and yields only
its declared value or `SamplingFailedAt(i)`. Core base/effective guards and
first-failure suppression remain exact. The joint contract is the
identity-bearing intended draw contract, not a theorem that the deterministic
transcript realizes the distribution.

### 3.3 Prefix semantics

The transcript state is the fold of initialization actions followed by every
action-occurring non-no-op event action in total Core schedule order.

A challenge prefix is exactly every prior potentially action-occurring absorb
or derive action, retaining its derived action-occurrence predicate. Runtime
uses the exact action-occurring subsequence. The stored map satisfies:

~~~text
challenge_prefixes[c] =
  exact non-no-op action-wise image of
  core.transcript_event_prefix_template[c]
  under event_actions
~~~

It is not a caller-selected causal subset, and local activation is not a
substitute for `EventActionOccurs`.

### 3.4 Standalone and composed contexts

`ExactCompositionContext` is a closed sum.

`Standalone` has no composition history and requires
`NoCompositionContext` authority. `Composed` binds:

- one exact authenticated `CoreCompositionSpecId`;
- the spec's exact ordered durable child occurrences; and
- the same total public target-context map used by
  `session_context_map`.

It cannot read private ports or infer composition history from ambient state.
The child sequence and context map are checked exactly. In target formation,
`Composed` requires transaction-scoped formation authority. After formation,
it requires an affirmative checked Core-composition capability over the exact
spec and target Core view.

### 3.5 Identity, authentication, and admission

The construction is scoped to one exact Core and shares the Protocol semantic
regime:

~~~text
TranscriptConstructionId = H(
  "zkc/transcript-construction",
  ProtocolSemanticRegimeId,
  CoreId,
  CanonicalEncode(TranscriptConstruction))

ExactTranscriptAlgorithmDependencyPreimageBundle =
  ExactMap<TypedTranscriptAlgorithmDependencyRef,
           AuthenticatedTranscriptAlgorithmDependencyPreimage>

TypedTranscriptAlgorithmDependencyRef =
  ContentAddressedContractRef restricted to initialization, framing,
  atom-codec, or squeeze-rule kind, retaining contract regime,
  content ID, exact ABI, and direct dependency IDs

AuthenticateTranscriptConstruction(
  CanonicalTranscriptConstructionCandidate,
  ExactTranscriptAlgorithmDependencyPreimageBundle,
  ExactTranscriptDependencyAuthenticationCapabilities)
  -> AuthenticatedTranscriptConstructionCandidate

CompositionContextAuthority =
    NoCompositionContext
  | ScopedCompositionFormationAuthority
  | affirmative CheckedCoreComposition

AdmitTranscriptConstruction(
  AuthenticatedTranscriptConstructionCandidate,
  CoreAdmissionWitness | AdmittedCoreView,
  CompositionContextAuthority,
  retained exact transcript algorithm dependency views,
  exact complete ExactSourceAuthorityBinding ledger for every authority-bearing
    admitted Core view, checked Core-composition context, and retained
    dependency view, with separately supplied fresh capabilities,
  ExactTranscriptLawCheckerCapabilities)
  -> (exact ExactAdmittedSubjectAuthorityBinding<PIR,
         TranscriptConstruction>,
      fresh AdmittedTranscriptConstruction)
~~~

The dependency bundle contains every and only preimage in the least closure of
content-addressed initialization, framing, codec, and squeeze rules. Exact
kind, regime, identity, ABI, and direct edges are checked. Closed finite terms
need no entry; extra, missing, same-digest cross-regime, and undeclared
transitive inputs reject.

Admission checks exact Core scope, total guarded event/challenge domains,
framing injectivity, codec round trips, sampler domains, exact action/prefix
equality, conditional and joint-group structure, failure mapping, context
authority, and absence of ambient state. It retains attenuated immutable views
of the exact dependency and context authority. It does not construct a
Protocol or prove a distributional theorem.

Before successful admission, PIR matches every ledger entry to its separately
supplied fresh capability, reauthenticates the exact family capability contract
and ABI, and freshly validates every bound policy or explicit no-policy
disposition for the named transcript-construction-admission purpose. The
transaction-local `CoreAdmissionWitness` and
`ScopedCompositionFormationAuthority` branches have no cross-owner source
binding, but must match the exact current admission/formation invocation and
cannot escape it. The admitted-subject binding and fresh construction
capability retain the canonical total transitive source-operation-policy
closure and every inert `OwnerCapabilityRequirement`, but no transitive live
authority.

### 3.6 Protocol identity and acyclic FS admission

~~~text
ChallengeInterpretation =
    FreshPublicCoins
  | FiatShamir(TranscriptConstructionId)

Protocol = {
  core: InteractiveCore,
  challenge_interpretation: ChallengeInterpretation
}

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
~~~

FS initialization binds `CoreId`, the computed
`TranscriptConstructionId`, and exact application/session context, never
`ProtocolId`. The canonical construction body stores the closed
`BindConstructionSelfId` instruction rather than a literal self ID.
Authentication first computes the construction ID; execution interprets the
instruction with that value. The identity preimage is therefore acyclic.

Canonical PIR has one Protocol root and stores only the exact
`TranscriptConstructionId` for FS. The construction is a separate satellite
candidate supplied with its exact dependency preimages and authenticated under
the Protocol regime. It is not nested as another PIR operation or alternate
Protocol carrier.

~~~text
ExactTranscriptConstructionCandidateAndDependencyPreimages = {
  candidate: CanonicalTranscriptConstructionCandidate,
  algorithm_dependencies:
    ExactTranscriptAlgorithmDependencyPreimageBundle
}

ExactProtocolDependencyPreimageBundle = {
  core_dependencies:
    ExactMap<DependencyRef, AuthenticatedDependencyPreimageInput>,
  transcript_construction:
    None | ExactTranscriptConstructionCandidateAndDependencyPreimages
}

ExactProtocolDependencyAuthenticationCapabilities = {
  core: ExactCoreDependencyAuthenticationCapabilities,
  transcript:
    None | ExactTranscriptDependencyAuthenticationCapabilities
}

AuthenticateCanonicalPir_R(
  raw canonical PIR,
  ExactProtocolDependencyPreimageBundle,
  ExactProtocolDependencyAuthenticationCapabilities)
  -> AuthenticatedCanonicalProtocolCandidate
~~~

Authentication parses and checks the physically canonical carrier, obtains an
authority-neutral semantic candidate, authenticates every and only Core
dependency and the FS satellite when present, recomputes Core and Protocol
identities, and only then exposes the authenticated candidate. An unchecked
parse has no semantic or round-trip authority.

Cold standalone FS admission is:

~~~text
authenticate canonical Core and Protocol carrier
  -> check CoreAdmissible
  -> mint transaction-scoped CoreAdmissionWitness
  -> authenticate and admit the referenced TranscriptConstruction
     against that witness and NoCompositionContext
  -> check ProtocolAdmissible and exact ProtocolId
  -> mint AdmittedProtocol
  -> discard CoreAdmissionWitness
~~~

The external Protocol dependency bundle contains every and only Core
dependency preimage and, for FS, exactly one construction candidate plus its
algorithm-dependency preimages. Its authentication-capability record has the
same exact keys. Fresh requires both transcript entries absent. FS requires
both present and identity-matched.

Protocol admission consumes retained exact dependency views,
`CompositionContextAuthority`, and:

~~~text
ExactProtocolAdmissionCheckerCapabilities = {
  core: ExactCoreAdmissionCheckerCapabilities,
  transcript:
    None | ExactTranscriptLawCheckerCapabilities
}

AdmitProtocol(
  AuthenticatedCanonicalProtocolCandidate,
  retained exact Protocol dependency views,
  exact ExactSourceAuthorityBinding for every authority-bearing admitted or
    dependency view, with separately supplied fresh capabilities,
  CompositionContextAuthority,
  ExactProtocolAdmissionCheckerCapabilities)
  -> ProtocolAdmissionAttemptOutcome
~~~

This is the exact canonical operation from
[Canonical PIR](canonical-pir.md#52-separate-checker-authority), not a second
FS-local admission variant or a success-only projection. Before either
completed outcome it matches every source binding to its separately supplied
fresh capability, validates every source-policy disposition for the named
admission purpose, and constructs the canonical total transitive source-policy
closure.

Fresh requires `transcript = None`. FS requires the exact matching law
capability and invokes `AdmitTranscriptConstruction` with the scoped Core
witness. Missing, extra, wrong-kind, wrong-regime, or wrong-identity
dependencies or capabilities are refused. Protocol admission does not require
an `FSCompile` theorem. A `Composed` construction cannot use this standalone
path; it uses the exact formation and replay transaction in Section 7.

`ProtocolAdmissible` rechecks `CoreAdmissible`, the closed interpretation tag,
Fresh support for every declared challenge distribution or FS scope and
complete action/prefix domains, framing and deterministic derivation closure,
and exact identity. Only `CompletedAdmitted` returns an `AdmittedProtocol`,
which is the only official Protocol authority. `CompletedNonAdmission` instead
returns only its exact checked negative under the canonical result-binding
contract. The Core witness is transaction-local and destroyed.

## 4. Fresh-to-Fiat--Shamir construction

### 4.1 Candidate, maps, and final check

~~~text
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
  transcript_action_prefix: CanonicalSeq<EventActionOccurrenceRef>,
  runtime_projection: ExactActionOccurringSubsequence
}

FinalizeFSConstruction(
  admitted fresh Protocol,
  admitted FS Protocol,
  admitted TranscriptConstruction,
  FSConstructionMaps,
  exact ExactAdmittedSubjectAuthorityBinding for every admitted operand and
    view, with separately supplied fresh capabilities,
  FSConstructionRegime)
  -> Qualified<CheckedFSConstruction,
               exact ExactCheckedResultAuthorityBinding<PIR, FSConstruction>>
~~~

The construction has three authority stages:

1. `ConstructFS` deterministically emits an unauthoritative target candidate
   and exact proposed maps.
2. The target is physically authenticated and admitted independently under
   its exact Protocol regime and dependency closure.
3. `FinalizeFSConstruction` consumes both admitted Protocols, the admitted
   construction, maps, and relation regime; it directly recomputes every
   identity, interpretation, event, challenge, and prefix equation before
   minting the checked-result capability.

Before completion it matches every admitted operand/view capability to its
exact source binding, reauthenticates each `PirCapabilityContractId` and ABI,
and freshly validates every explicit no-policy contract and transitive bound
source policy for the named FS-finalization purpose. The resulting checked-
result binding retains the canonical total transitive source-policy closure and
the exact `OwnerCapabilityRequirement`; the capability retains that identical
binding.

The source and target share the literal same `CoreId`. Event and challenge maps
are total bijections over the complete Core families and preserve inner
`CoreRef` values. Their source- and target-qualified references remain
distinct; equal inner ordinals do not authorize interpretation alignment.

Each prefix descriptor binds the mapped target challenge, exact potential Core
action-occurrence template, exact non-no-op action image, and exact runtime
action-occurring projection. The maps are directly recomputable. Construction
success, target admission, and the checked relation remain separate.

### 4.2 Property seam

~~~text
FSCompile(
  admitted fresh Protocol,
  admitted FS Protocol,
  admitted TranscriptConstruction,
  affirmative CheckedFSConstruction,
  exact admitted-subject/result authority binding for every consumed operand,
    with separately supplied fresh matching owner capabilities,
  semantic model identity,
  theorem/rule identity,
  explicit assumptions and quantitative parameters)
  -> Analysis-owned qualified judgment
~~~

`FSCompile` is unavailable rather than false when no semantic model or
theorem applies. Property transport additionally names the exact source
property judgment, FS result, property-specific rule, assumptions, losses,
and target conclusion. There is no global `FS-valid` capability. Structural
construction proves no random-oracle, sponge, distributional, independence,
soundness, knowledge, completeness, or zero-knowledge claim.
The affirmative checked construction result retains the transcript subject's
exact binding but cannot replace the separately supplied fresh transcript-
admission authority required by the Analysis checking occurrence.

## 5. Semantic Core composition specification

### 5.1 Complete identity-bearing root

All target references in the preimage are typed local references. Global
target Core references are minted only after the target is formed and
admitted.

~~~text
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
  values: TotalMap<LocalChildInnerOrdinaryValueRef, LocalTargetValueRef>,
  objects: TotalMap<LocalChildInnerObjectRef, LocalTargetObjectRef>,
  events: TotalMap<LocalChildInnerOrdinaryEventRef, LocalTargetEventRef>,
  claims: TotalMap<LocalChildInnerClaimRef, LocalTargetClaimRef>,
  reductions:
    TotalMap<LocalChildInnerReductionRef, LocalTargetReductionRef>,
  checks: TotalMap<LocalChildInnerCheckRef, LocalTargetCheckRef>
}

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
~~~

Restricted local contract references resolve only through matching declarations in
`target_fragment.dependencies` with exact kind, regime, content ID, ABI, and
direct edges.

### 5.2 Challenge and private-randomness policies

Each child challenge policy key denotes the complete linked challenge bundle:
challenge, `FreshChallenge` event, value, public randomness, sampling endpoint
obligations, sampling failure, coin index, and correlation.

~~~text
ChallengePolicy =
    IndependentChallenge(LocalTargetFreshChallengeBundle)
  | JointChallengeMember(CompositionChallengeGroupRef,
                         LocalTargetFreshChallengeBundle)
  | SharedChallenge(CompositionChallengeGroupRef,
                    LocalTargetFreshChallengeBundle)
  | DerivedChallenge(
      DerivedChallengeSources,
      LocalTargetPureFunctionContractRef,
      ChallengeSubstitutionDisposition)
  | ImportedChallenge(
      LocalTargetContextPortRef,
      LocalTargetEndpointObligationRef,
      ChallengeSubstitutionDisposition)

ChallengeSubstitutionDisposition = {
  value: LocalTargetValueRef,
  observation_event: LocalTargetObservePublicValueEventRef,
  removed_randomness: NoTargetRandomness,
  removed_sampling_endpoint_obligations: NoTargetSamplingObligations,
  removed_sampling_failure: NotApplicableAfterSubstitution,
  removed_public_coin_index: NoTargetPublicCoinIndex,
  correlation_effect: DeterministicFromNamedSources | ExternalPublicInput
}

PrivateRandomnessPolicy =
    PreserveIndependent(LocalTargetPrivateRandomnessBundle)
  | JointPrivateMember(
      CompositionPrivateRandomnessGroupRef,
      LocalTargetJointDistributionContractRef,
      LocalTargetPrivateRandomnessBundle)
  | DerivedPrivateValue(
      DerivedPrivateRandomnessSources,
      LocalTargetPureFunctionContractRef,
      PrivateRandomnessSubstitutionDisposition)
  | ExternalPrivateSupply(
      LocalTargetPrivatePortRef,
      LocalTargetProverObligationRef,
      PrivateRandomnessSubstitutionDisposition)

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

DerivedChallengeSources =
  NonEmptyCanonicalSeq<LocalChildChallengeBundleRef>

CompositionChallengeGroupRef =
  dense canonical ordinal allocated by the least
  LocalChildChallengeBundleRef in each challenge-policy group

LocalChildPrivateRandomnessBundleRef = {
  randomness: LocalChildInnerPrivateRandomnessRef,
  value: LocalChildInnerPrivateRandomnessValueRef,
  owner_obligation: LocalChildInnerProverObligationRef,
  sampling_failure: LocalChildInnerProverObligationFailureRef
}

LocalTargetPrivateRandomnessBundle = {
  randomness: LocalTargetPrivateRandomnessRef,
  value: LocalTargetPrivateRandomnessValueRef,
  owner_obligation: LocalTargetProverObligationRef,
  sampling_failure: LocalTargetProverObligationFailureRef,
  distribution: LocalTargetDistributionContractRef,
  correlation: ExactTargetCorrelationDecl
}

DerivedPrivateRandomnessSources =
  NonEmptyCanonicalSeq<LocalChildPrivateRandomnessBundleRef>

CompositionPrivateRandomnessGroupRef =
  dense canonical ordinal allocated by the least
  LocalChildPrivateRandomnessBundleRef in each private-policy group
~~~

Challenge- and private-policy group references are dense canonical ordinals
allocated by each group's least policy-map key. Challenge joint and shared
groups are homogeneous and cannot share a group reference. Private groups use
a distinct typed reference family.

The challenge-policy map is total over complete child bundles. Every target
fresh challenge bundle is covered exactly once by one independent image, one
joint-member image, or one shared group; sharing is the sole permitted
many-to-one case. For every target bundle:

~~~text
public_coin_index =
  zero-based rank of its FreshChallenge event
  among all target challenge events in interleaving
~~~

Checked composition maps retain each child challenge occurrence and child
index to that exact target occurrence and recomputed index. Only a declared
shared group may map several child occurrences and indices to one target
occurrence and index.

Independent challenge preservation is legal only for an
`IndependentFresh` source. Its target distribution equals the child
distribution, its target correlation is `IndependentFresh`, and its complete
event/value/randomness/failure/obligation bundle is the exact typed image
apart from the recomputed coin index. Joint groups preserve complete collision-free
member ranges, marginal contracts, exposure order, common base guard, ordered
conditional steps, and first-failure suppression. For each
`JointChallengeMember(group_id, bundle)`, all and only policies with that group
ID name distinct target bundles. Their correlation declarations are
`JointMember` entries of one exact authenticated target joint contract and one
exact target group; their member indices form the complete collision-free
range and equal target exposure order; and every target marginal equals its
mapped child's distribution. Target event order, the single target base-guard
derivation, member effective guards, conditional sampling steps, value and
failure backlinks, kind-exact obligation bases, recomputed endpoint
obligations, and first-failure suppression satisfy the global joint-randomness
laws. Every preserved independent or joint-member target event carries the
exact typed-image `FreshChallengeContracts` basis.

A source joint group is structurally preserved only if all of its members
appear in one target group with the same authenticated contract, exact member
correspondence, and index order. Combining independent sources, regrouping
source joints, or changing the joint contract is `IntentionalChange`. A source
joint may be split only by explicit derived or imported substitutions for the
removed members, never by `IndependentChallenge`.

A shared challenge maps all declared members to one exact target fresh bundle.
Their domains, distributions, failure classes/effects, obligation bases, and
post-suppression coactivation guards are exact-equal. The target distribution
equals every member distribution and its target correlation is
`IndependentFresh`. The one target event is
after all mapped member predecessors and required prefix events and before all
mapped consumers and successors. Cycles reject. Sharing is
`IntentionalChange` unless the source already declared that same sample
occurrence. Its target event carries the one exact-equal
`FreshChallengeContracts` basis and recomputed sampling obligation.

The shared target event has one explicit position in the complete target
`interleaving`. Its challenge-prefix template is recomputed from that complete
target schedule. Every member's event, value, challenge, failure, and prefix
map names the same target occurrence and the exact corresponding target
prefix. No first-member, last-member, deduplication, or ambient-anchor rule may
choose the occurrence or prefix.

Derived and imported challenges are substitutions, not target
`ChallengeRef`s. They explicitly remove randomness, sampling obligations,
sampling failure, and coin index. Derived values are exact pure applications
over the identity-bearing ordered source sequence. Imported values are exact
`PortValue(port, 0)` values from a public `Context` input owned by
the unique `PublicEnvironment`; the port has multiplicity `ExactlyOne`. The
import names the exact recomputed endpoint obligation whose source is the
observation event, whose owner is that PublicEnvironment, whose input is that
value, and whose action is `ObservePublicValue`. Both substitutions create
exactly `ObservePublicValue(disposition.value)` with the kind-exact
`ObservePublicValueContracts` basis. Every named source value is available
before that event. Derived equations are exactly:

~~~text
disposition.value =
  Apply(function,
        mapped source challenge values in declared source-sequence order)
~~~

Source references are unique; each resolves through its own policy's target
value. The dependency graph is acyclic and topologically evaluated without
reordering function arguments. Function domains and codomain match exactly.
Admission checks the four explicit removal fields, not only their reference
kinds. No occurrence or property preservation is inferred.

Private preservation and joint grouping obey analogous complete bundle,
contract, marginal, guard, owner-obligation, and failure-backlink equations.
The private-policy map is total over every complete child private-randomness
bundle. `PreserveIndependent` is legal only for `IndependentFresh`, produces
one exact typed-image target randomness/value/owner/failure bundle per child,
preserves the distribution, and sets target correlation to
`IndependentFresh`.

All and only `JointPrivateMember` entries for one group name distinct target
bundles and one exact-equal authenticated joint contract. Source keys map
bijectively to the complete target member-index range; no target bundle
repeats. Every target member has `JointMember(contract, group, index)`
correlation, its checked marginal equals the child distribution, and its
availability, common base guard, ordered conditional step, owner-obligation
and private-sampling-failure backlinks satisfy the Core joint laws. Preserving
a source joint group requires complete contract/member/index correspondence;
combining, regrouping, or changing it is `IntentionalChange`.

Derived or externally supplied private values remove the source randomness,
its owner-basis occurrence, and matching
`PrivateSamplingFailed(randomness)` declaration exactly once. The declared
prover-construction basis rewrite preserves all unaffected fields and inserts
the substitute at the exact ordinal. Their exact equations are:

~~~text
DerivedPrivateValue:
  disposition.value =
    Apply(function,
          mapped source private values in declared source-sequence order)

ExternalPrivateSupply:
  disposition.value = PortValue(private_port, 0)
~~~

Derived source references are unique, resolve through their exact source
policies, and form an acyclic graph evaluated topologically without argument
reordering. The pure function's domains and codomain, source availability, and
declared deterministic distribution effect are exact.

External supply uses a `PrivateToRole` Prover input of multiplicity
`ExactlyOne`. Its named target obligation is the one recomputed from the basis
rewrite and consumes the value at `substituted_input_ordinal`. The external
distribution effect is explicit. If one obligation has multiple
substitutions, every entry names one identical replacement basis and
collision-free substitution ordinals. The endpoint-contract basis, unaffected
construction inputs, outputs, domains, and all non-replaced fields remain exact
typed images. These rewrites are `IntentionalChange` and cannot imply
distributional fidelity.

### 5.3 Failure, reach, capture, and terminal policy

~~~text
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
  | CaptureFailure(
      LocalTargetFailureRef,
      LocalTargetFailureStatusValueRef,
      LocalTargetCapturedFailureExitStatusValueRef,
      ExitStatusInjection,
      SuffixSuppression)
  | RemovedByChallengeSubstitution(LocalChildChallengeBundleRef)

ReachExitPolicy =
    PropagateReach(LocalTargetReachTerminalEventRef,
                   LocalTargetTerminalRef)
  | CaptureReach(
      LocalTargetValueRef,
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
~~~

`failure_policy` is total over every verifier-visible child failure occurrence.
`reach_exit_policy` is separately total over every child
`ReachTerminal` occurrence.

For every nonremoved failure, its target `FailureSourceRef` is the exact typed
image of the child source under the checked event, check, challenge, and
randomness maps. Every source backlink names that same target failure. The
target failure class equals the child class, and each child
`FailureOccurred(source_failure)` maps to exactly
`FailureOccurred(target_failure)`. For challenge bundles, the failure-policy
target is the policy bundle's linked sampling failure; joint members use the
exact conditional step at their index, and shared members may converge only
inside the declared shared group.

- `PreserveContinue` preserves a continuing failure, its exact status value,
  class, source, and observations. Its effect is exactly
  `ContinueWithStatus(FailureStatusValue(target failure))`, and the child
  status value maps to that exact target value.
- `PropagateFailure` preserves a terminating failure and routes it to the
  terminal named by `Terminate(mapped terminal)` with exact result, outputs,
  and observations.
- `CaptureFailure` converts a terminating non-explicit-abort failure to the
  same-class named continuing failure. Its observations are the mapped child
  observations with `Terminal` removed, its effect is exactly
  `ContinueWithStatus` of its own named status value, and its complete captured
  status is
  `Tuple(FailureStatusValue(target failure),
  CanonicalConstant(terminal_result_value_domain,
  CanonicalTerminalResultValue(child terminal result)),
  mapped child terminal public outputs...)`.
- `RemovedByChallengeSubstitution` is legal only for the terminating sampling
  failure of a derived/imported challenge. It maps
  `FailureOccurred` to canonical false and permits no reachable status use.
- `PropagateReach` preserves the exact target reach event, terminal, event
  envelope, result, and outputs.
- `CaptureReach` creates the exact public observation of
  `Tuple(CanonicalConstant(terminal_result_value_domain,
  CanonicalTerminalResultValue(child terminal result)),
  mapped child terminal public outputs...)` and removes the original terminal
  exit.

`PropagateReach` preserves the complete event envelope, including actor,
inputs, mapped or suffix-rewritten guard, protected observations, and the
kind-exact `ReachTerminalContracts` basis. `CaptureReach` uses the verifier as
actor; preserves the available mapped inputs and guard; replaces the
`Terminal` observation with `PublicValue`; uses
`ObservePublicValue(status)` with the exact
`ObservePublicValueContracts` basis; and carries the one recomputed endpoint
obligation for that event. The enclosing sum variant identifies the child
reach occurrence, so the raw tuple contains no duplicate occurrence label.

Failure class and terminal-result compatibility is exact. Whenever a
verifier-visible failure uses `Terminate(t)`, `MalformedProtocolInput` and
`CheckRejected` require `t.result = Reject`, while `ChallengeSamplingFailed`
and `ExplicitProtocolAbort` require `t.result = Abort`.
`ExplicitProtocolAbort` must terminate and cannot be captured.
Private-sampling failure is not a verifier-visible `FailureDecl` and selects no
terminal; it produces the separate Core-owned
`ProverDidNotProduce(ProverObligationFailureRef, partial_state)` outcome.

Capture is admitted only when direct symbolic recomputation proves
`CaptureClaimQuiescent`: no newly enabled mapped production, no live linear
claim at the exit, no later-enabled child reduction, and no target reduction
that can consume retained child claims. If this cannot be proved, capture is
unavailable. The checker compares the complete guarded live-claim set and
`Claim` observation sequence at the child exit with the target prefix, then
evaluates every later target closure point under ordinary target claim
semantics. Suffix guards do not substitute for this proof.

Each captured raw status is injected with `InjectVariant` into one exact
per-child closed sum domain. Variants are distinct and payload-correct. One
exhaustive one-hot `GuardedMerge` consumes the injected values; a branch
requires all guards and only the selected branch value. Every capture supplies
total suffix suppression: later source-event guard contributions conjoin the
negation of every earlier captured exit. Joint groups receive suppression only
in their common base contributions and then derive member-final guards through
their intrinsic first-failure law.

For each capture:

~~~text
ExitStatusInjection.raw_status = the constructor's complete raw status
ExitStatusInjection.injected_status =
  InjectVariant(sum_domain, variant_ordinal, raw_status)
~~~

For `CaptureFailure`, `SuffixSuppression.exit_taken` is exactly
`FailureOccurred(the named target failure)`. For `CaptureReach` it is exactly
the captured reach event's final mapped guard contribution. The
`rewritten_guards` map is total over every later potential event origin of that
child. All Boolean nodes and causal edges introduced by suppression are owned
by that policy; no second guard rewrite is legal.

There is exactly one combiner input for each child slot with a captured source
on a path that can reach the combiner, and no input for any other slot. Every
combiner-reaching path has exactly one captured completion for each child slot
and one available merged status per input. A slot without a combiner input
must have a mandatory propagated exit on every path, making combiner finals
unreachable. Propagated exits immediately make all finals unattempted.

Every event resolving a captured or propagated child terminal precedes every
combiner final in both the exact causal-edge set and `interleaving`; finals
occur in `route_order`. For each final, admission proves:

~~~text
EventAttempted(final) implies
  no propagated exit was selected
  and every child slot has exactly one captured completion
  and every combiner merged_status input is available
~~~

`terminal_result_value_domain` is a finite authenticated domain containing
exactly canonical values for `result_domain`. `result_function` has that exact
codomain and its range contains only those result-domain tags. The combiner
satisfies:

~~~text
result_value =
  Apply(result_function, inputs[*].merged_status)

for each non-last route tag t:
  guard =
    GuardDecision(
      FiniteValueEquals(
        result_value,
        CanonicalTerminalResultValue(t)))

the last route:
  guard = canonical true UnguardedFallback

public_output_tuple =
  Apply(public_output_function, inputs[*].merged_status)

public_output_values =
  every Project(public_output_tuple, i) in product-domain order
~~~

Each final terminal has the route's static result and exact projected public
outputs, and its event is exactly `ReachTerminal(terminal)`. Route order,
`ExecutionStillLiveBefore`, and prior-terminal behavior make finals one-hot,
exhaustive, and ordered.

For every execution with a complete active prover trace and private-sampling
supply, the admitted target reaches either one explicit propagated exit or
exactly one combiner route. `ProverDidNotProduce` remains the separate
nonterminal producer-trace outcome.

### 5.4 Complete local target fragment and origin closure

~~~text
LocalTargetCoreFragment = {
  dependencies: CanonicalSeq<LocalTargetDependencyDecl>,
  roles: CanonicalSeq<LocalTargetRoleDecl>,
  ports: CanonicalSeq<LocalTargetPortDecl>,
  values: CanonicalSeq<LocalTargetValueNode>,
  objects: CanonicalSeq<LocalTargetObjectDecl>,
  randomness: CanonicalSeq<LocalTargetRandomnessDecl>,
  challenges: CanonicalSeq<LocalTargetChallengeDecl>,
  events: CanonicalSeq<LocalTargetEventDecl>,
  causal_edges:
    CanonicalSet<(LocalTargetEventRef, LocalTargetEventRef)>,
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
~~~

`interleaving` is a permutation of every and only target-fragment event and is
the target Core schedule. It is not a child list later deduplicated through
maps.

Origin classes are disjoint and exhaustive:

- roles are derived uniquely by role class;
- ports come from the one total face map per child slot;
- ordinary values, objects, events, claims, reductions, and checks come from
  injective typed ordinary-origin maps;
- challenge and private-randomness bundles come from their policies;
- failures, failure-origin values, terminals, and reach events come from
  failure/reach policy;
- endpoint/prover obligations and prover-obligation failures are
  deterministically recomputed; and
- `locally_added` contains every and only declaration with no child or
  policy-derived origin, including combiner structure.

The ordinary value map excludes port, private-randomness, challenge,
failure-status, and failure-occurrence origins. The ordinary event map excludes
`FreshChallenge` and `ReachTerminal`. Ordinary constructors are exact recursive
typed images except for the declared private-basis and suffix-guard rewrites.
Repeated equal children still use distinct target ordinals.

Local additions cannot create an undeclared exit channel. Outside exact
terminal-combiner structure, they cannot introduce fresh
randomness/challenges, checks, failures, failure-origin/status values,
`RaiseFailure`, terminals, or `ReachTerminal`. A new independent exit protocol
must be an admitted child or a future explicit local-exit policy.

### 5.5 Face, dependency, obligation, schedule, and guard laws

There is one `LocalTypedFaceMap` per child slot, total over its ports. Roles map
deterministically to the unique target role of the same class.

- `ExternalInput` preserves direction, role class, visibility, domain,
  multiplicity, purpose, and every port-value occurrence.
- `InternalInputs` gives one same-domain available target value per child
  occurrence and cannot replace a claim-producing initial input.
- `ExternalOutput` preserves direction, domain, multiplicity, and the complete
  exact target output sequence.
- `InternalOutputs` names that same-domain complete occurrence sequence.

No truncation, broadcast, ordinal permutation, direction reversal, visibility
weakening, or implicit face default is allowed. Internal feeds become explicit
acyclic value/causal edges.

After every constructor and rewrite is fixed, target dependencies are exactly
the least reachable authenticated closure of their typed roots, keyed by kind,
semantic regime, content identity, Protocol-facing ABI, and exact preimage
edges. Unused child dependency history is not target semantics. Missing
preimages or conflicting reachable views reject. Locally supplied dependencies
are disjoint from reachable child supplies.

Endpoint obligations, prover obligations, and prover-obligation failures are
recomputed from the completed target events and randomness and must equal the
target fragment. No face or policy may erase, invent, or rename them
independently.

Target causal edges equal exactly:

1. every child edge under the complete event-occurrence maps;
2. every mapped explicit `causal_seams` edge;
3. every deterministic face-feed, challenge/private-randomness,
   failure/reach-rewrite, suffix-suppression, and combiner edge; and
4. `locally_added_causal_edges`, disjoint from the first three.

The union is acyclic and `interleaving` extends it exactly.

Final event guards have one owner:

- ordinary and substitution origins use the mapped or declared base guard plus
  exact per-child capture suppression;
- shared challenges require identical post-suppression member
  contributions;
- a public joint group derives one noncircular common base and then member
  `i` uses that base conjoined only with the negation of earlier member
  failures;
- a private joint group uses its common base for every owner event because
  private nonproduction terminates the producer trace; and
- local events use their explicit local or combiner equation.

No policy writes a second final guard.

For each public joint group, a source member contributes its mapped
index-zero source-group base when it already belongs to a source joint group,
or its mapped source-event guard otherwise. That value is conjoined with
exactly the capture suppressions preceding the member's availability point.
All contributions must be equal:

~~~text
B_target = the one exact common contribution

target_member_guard(i) =
  B_target
  AND NOT(FailureOccurred(target_member_failure(0)))
  ...
  AND NOT(FailureOccurred(target_member_failure(i - 1)))
~~~

No source member-final guard or later suppression is added. Private joint
groups derive the same common base, and every member owner event uses exactly
`B_target` because the first failed private step immediately yields
`ProverDidNotProduce`. Unequal bases, capture histories, or co-owned event
contributions reject.

### 5.6 Terminal origin partition

`terminal_origin_map` is total over every terminal in every child occurrence.
For one child terminal, its source-occurrence set is every terminating failure
and every `ReachTerminal` occurrence naming it. Captured, removed, and
propagated occurrences are disjoint and exhaustive.

`mapped_target` is present exactly when propagation is nonempty. Its result and
public outputs are the exact typed source image. Distinct terminal occurrences
map injectively except for compatible failures in one exact shared-challenge
group. If propagation is empty, every source occurrence is captured or is the
explicitly removed sampling failure; captured payloads remain complete. Every
target terminal is covered exactly once by a mapped image or
`locally_added`, never both.

### 5.7 Specification identity, authentication, and admission

~~~text
CoreCompositionSpecId = H(
  "zkc/core-composition-spec",
  CompositionRegimeId,
  target_protocol_regime_id,
  CanonicalEncode(
    children,
    face_maps,
    ordinary_origin_maps,
    terminal_origin_map,
    locally_added,
    causal_seams,
    locally_added_causal_edges,
    interleaving,
    challenge_policy,
    private_randomness_policy,
    failure_policy,
    reach_exit_policy,
    terminal_combiner,
    target_fragment))

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
  exact ordered CanonicalSeq<AdmittedCoreView>,
  exact complete ExactSourceAuthorityBinding ledger for every admitted child
    Core view and authority-bearing retained target dependency view, with
    separately supplied fresh capabilities)
  -> (exact ExactAdmittedSubjectAuthorityBinding<PIR, CoreCompositionSpec>,
      fresh AdmittedCoreCompositionSpec)
~~~

Authentication checks the closed local-reference carrier, authenticates every
and only target-fragment dependency preimage, verifies the complete typed key,
and recomputes the identity. Child IDs remain data and grant no shape
authority.

Admission consumes exact ordered live child Core views. Their IDs and
`ProtocolSemanticRegimeId` must match the spec exactly. v0 composition is
same-regime only. Cross-regime composition requires a future explicit
translation subject and checked relation.

Admission computes the target-required reachable dependency closure, reconciles
exact-equal reachable child views, supplies missing required keys only through
disjoint authenticated local additions, and discards unreachable child
history. It then checks every total map, local fragment, disjoint/exhaustive
origin class, causal union, interleaving, face, policy, capture, and combiner
law. The admitted spec retains ordered child views and exact selected target
dependency views. It does not construct or admit a target.

Before successful admission, PIR matches every ledger entry to its separately
supplied fresh capability, reauthenticates the exact family capability contract
and ABI, and freshly validates every bound policy or explicit no-policy
disposition for the named composition-spec-admission purpose. The exported
`ExactAdmittedSubjectAuthorityBinding<PIR, CoreCompositionSpec>` and fresh
`AdmittedCoreCompositionSpec` capability retain the canonical total transitive
source-operation-policy closure and every inert `OwnerCapabilityRequirement`,
but no transitive live authority.

## 6. Composition maps and checked result

### 6.1 Exact map carrier

~~~text
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
~~~

`ResolveTargetRefs<T>` is one total type-directed operation. It replaces each
local target reference through the same-kind ordinal-preserving bijection and
each local child slot with its global `ChildOccurrenceRef`; it preserves
product order, sum tags, map keys, sets, ordinals, and literals exactly.
Derived optional origins are `None` only for unreachable dependencies or
obligations removed by an explicit admitted substitution.

### 6.2 Affirmative and negative checked payloads

~~~text
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
~~~

~~~text
ResolveCoreCompositionMaps(
  admitted spec,
  admitted target Core view)
  -> CoreCompositionCheckedPayload
~~~

Resolution is a pure total comparison with no caller-supplied map parameter.
Exact agreement returns the unique map record. Any mismatch returns a nonempty
typed mismatch set and unaffected agreements, with no partial map record.

Both completed variants retain exact admitted operands and the relation regime.
Only the affirmative variant retains `ResolvedCoreCompositionMaps` and grants
composition-context authority. The negative variant grants no target-map or
composition-context authority. Neither payload is a Core or Protocol admission
witness.

## 7. Three-phase target formation and replay

### 7.1 Operations

~~~text
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
  AdmittedProtocol,
  exact ExactAdmittedSubjectAuthorityBinding for every admitted operand and
    view, with separately supplied fresh capabilities)
  -> Qualified<CheckedCoreComposition,
               exact ExactCheckedResultAuthorityBinding<PIR, CoreComposition>>

ReplayAndAdmitComposedProtocol(
  AuthenticatedCanonicalProtocolCandidate,
  AdmittedCoreCompositionSpec,
  exact complete ExactSourceAuthorityBinding ledger for the admitted
    composition spec, every authority-bearing admitted child or retained target
    dependency view required by replay, and every authority-bearing retained
    Protocol dependency view, with separately supplied fresh capabilities,
  ExactProtocolAdmissionCheckerCapabilities)
  -> Qualified<AdmittedProtocol,
               CheckedCoreComposition,
               exact ExactAdmittedSubjectAuthorityBinding<PIR, Protocol>,
               exact ExactCheckedResultAuthorityBinding<PIR,
                 CoreComposition>>
~~~

The authority phases are exact:

1. **Construct and subadmit Core.** Deterministically instantiate local target
   references, apply faces, policies, guards, causal edges, dependency closure,
   and recomputed obligations. Recompute canonical Core encoding and `CoreId`,
   check `CoreAdmissible`, and mint a transaction-only witness plus formation
   authority.
2. **Form and admit Protocol.** Consume the exact witness and explicit
   challenge interpretation. Fresh carries no composition-context authority.
   FS carries every candidate, dependency, authentication, law-checker, and
   same-invocation formation input needed to authenticate and admit its
   construction against that not-yet-published target Core. Then independently
   authenticate and admit the enclosing Protocol.
3. **Finalize composition.** Attenuate the admitted target Core view, directly
   recompute all maps against the admitted spec and children, and mint the
   affirmative or negative checked capability. Discard the transaction witness
   and scoped formation authority.

Finalization matches every admitted operand and attenuated view capability to
its exact source binding and freshly validates every explicit no-policy
contract or transitive bound source policy for the named composition purpose.
The completed result creates the exact `PirCheckedResultCoordinate` and total
source-policy closure; the live capability retains its complete inert binding.

Before replay or either completed output, the operation matches every ledger
entry to its separately supplied fresh capability, reauthenticates the exact
owner capability contract and ABI, and freshly validates every bound-policy or
explicit no-policy disposition for the named replay-and-admission purpose. It
constructs the canonical total transitive source-operation-policy closure.
The admitted-Protocol binding retains the complete Protocol-admission source
closure; the checked-composition binding retains the complete spec, child,
target, and finalization source closure. Each fresh output capability retains
its identical inert binding and every required `OwnerCapabilityRequirement`,
but no transitive live authority.

`ScopedCompositionFormationAuthority` is opaque, linear, process-local, and
bound to the exact admitted spec, Core witness, target `CoreId`, and one
unforgeable invocation token. It contains no caller-selected map. The FS
formation record must match the same invocation, spec, witness, Core, regime,
construction identity, context, dependency preimages, and capability sets.
Cross-transaction, missing, extra, or mismatched material is refused. If
Protocol admission fails, the authority is discarded.

The Core candidate is independent of Fresh versus FS selection. Only the
explicit `ChallengeInterpretationInput` chooses the target interpretation.

### 7.2 Deterministic construction order

The transaction performs these steps in order:

1. assign distinct child occurrence tags;
2. validate every face and exact port equation;
3. apply ordinary/terminal origins, derived roles, and policy-owned maps;
4. apply complete challenge and private-randomness policies;
5. apply total failure and reach policy, guard equations, suffix suppression,
   and terminal combiner, then close all target constructors;
6. construct the exact derived and locally added causal-edge union, prove
   acyclicity, and require `interleaving` to extend it;
7. compute the target-required least dependency closure, dropping unreachable
   child history and resolving only exact typed keys;
8. recompute every endpoint obligation, prover obligation, and
   prover-obligation failure and require exact fragment equality;
9. construct, canonically encode, and subadmit the target Core;
10. consume the explicit challenge interpretation, admitting a composed
    transcript construction inside the same transaction when FS is selected,
    then authenticate and admit the target Protocol;
11. recompute the complete composition maps and mint the exact A/N checked
    result; and
12. destroy transaction-only authority.

### 7.3 Cold replay

`ReplayAndAdmitComposedProtocol`:

- revalidates the freshly admitted composition spec, ordered child views, and
  selected target dependency views against their exact bindings and fresh
  capabilities;
- reruns Core construction and subadmission using the exact Core member of the
  Protocol-admission checker capability bundle;
- requires the reconstructed Core body, regime, and ID to equal the
  authenticated persisted Protocol candidate;
- for FS, recreates and consumes the same-invocation formation authority and
  exact transcript dependency/law capability inputs;
- independently admits the enclosing Protocol; and
- reruns `FinalizeCoreComposition`.

Fresh requires the transcript-construction checker component to be absent.
The exact checker bundle is typed to the Core dependencies and, for FS, to the
construction and algorithm dependencies. Missing, extra, or mismatched
capabilities are refused.

Exact cold replay exists only when every identity-bearing source binding and
both recreated output coordinates are portable and all authenticated owner
contracts permit the named replay and retention. If any required source or
output coordinate is owner-local, serialized material cannot recreate or
compare it: an authorized same-owner, same-generation invocation must instead
perform a new local reconstruction with fresh capabilities and newly allocated
local coordinates. That invocation is a new result, not exact cold replay, and
no portable result identity may include or erase an owner-local coordinate.

A serialized result, spec ID, child-ID list, prior witness, or previous
checked capability may guide material selection but grants no authority. A
durable checked result is permitted only for a named consumer and binds exact
spec, child slots/IDs, target Core ID, regimes, checker identity, qualified
outcome, residual trust, and either affirmative maps or negative facts. It
must be rechecked against newly admitted views after serialization.

## 8. Structural laws, identity effects, and non-laws

The map algebra has these exact properties:

- ordinary value, object, event, claim, reduction, and check maps are injective
  occurrence embeddings;
- port substitutions and policy-owned families use their declared exact maps;
- obligations and obligation failures are recomputed, not mapped by an
  arbitrary origin policy;
- repeated equal child IDs have distinct `ChildOccurrenceRef` values;
- independent challenges map injectively;
- joint members map injectively and in order under one exact joint contract;
- shared groups use only their declared many-to-one map;
- derived/imported challenges map to values and public-observation events, not
  target challenge occurrences;
- every failure and reach occurrence follows its exact total policy; and
- each private source maps explicitly to preserved independent, joint,
  derived, or external supply structure.

The target interleaving is a linear extension of every mapped child schedule,
child causal edge, declared seam, and deterministic policy edge. Composition
closes guards, role knowledge, public/private randomness and correlation,
transcript/wire observations, claims, checks, failures, exit behavior, suffix
suppression, terminals, dependencies, and obligations.

`CoreId` commits only to the exact intrinsic canonical target encoding.
Different construction histories can yield the same Core ID while retaining
different spec IDs and checked map results. Behavioral equivalence alone does
not imply equal IDs. Any child origin, grouping, or context observed by target
semantics must be explicit and changes Core identity.

Composition has no universal commutativity, associativity, idempotence, or
identity law. Repeating one child is not idempotent merely because its Core ID
is equal. A constructor-specific law requires exact face, schedule, challenge,
failure, terminal, and observer premises.

Authoring `link` may propose graphs or a composition specification. It remains
unauthoritative until full spec admission, target formation/admission, and map
checking complete.

Composition consumes child Core views, not child challenge interpretations.
The target independently selects Fresh or one exact FS construction. It does
not inherit “already FS” status. Neither
`FS(compose(children)) = compose(FS(children))` nor any related statement is
assumed; it requires its own exact maps and checked relation.

## 9. Explicit nonclaims

Transcript-construction admission, `CheckedFSConstruction`, composition-spec
admission, target Protocol admission, and `CheckedCoreComposition` establish
only their named structural results. They do not establish:

- relation truth, satisfaction, or witness validity;
- induced random-oracle, sponge, hash, joint-distribution, marginal, or
  independence semantics;
- Fiat--Shamir security, soundness, knowledge, completeness, or zero
  knowledge;
- semantic equivalence, refinement, or property preservation across
  composition or FS;
- compiler legality, optimality, or target selection;
- OIR validity, projection correctness, endpoint support, concrete
  realization, or successful execution;
- implementation correspondence, formal-model adequacy, proof-assistant
  verification, artifact provenance, independent review, or production
  readiness; or
- compatibility with another semantic regime.

`FSCompile`, property transport, equivalence/refinement, property composition,
and cryptographic conclusions belong to Analysis and require explicit models,
rules, assumptions, quantitative loss, and exact source judgments.
