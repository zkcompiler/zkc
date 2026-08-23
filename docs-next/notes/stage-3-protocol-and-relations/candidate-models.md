# Stage 3 equal-resolution candidate models

> **Document kind:** Temporary architecture candidate portfolio
> **Document state:** Stage 3.3 candidate instantiation complete; convergence
> input, not a decision
> **Authority:** None. This page does not define v0 semantics, admit a subject,
> or authorize implementation or migration.
> **Scope:** Complete Protocol, canonical PIR, Interface, Plan, Relations,
> Fiat--Shamir, composition, identity, authority, and checking centers.
> **Parity basis:** Frozen target SHA-256
> `107255938efa6af7802030b93bdbc9dcb4d5535335866cffa304df33083a7f5b`.
> **Disposition:** Promote the selected model and durable rejected-alternative
> rationale, retain reversal triggers, then delete this page before cutover.

## 1. Comparison discipline

Candidate C, D, and the admitted output of E inherit every fixed Stage 1 and
Stage 2 decision. Candidate A is the required current-preserving control and
therefore deliberately tests reopening the physical-canonicality decision;
Candidate B tests a bundle reopening. Neither control is gate-eligible unless
its exact inherited decision is formally reopened. No candidate can win by
collapsing subjects, moving semantic authority into MLIR, serializing a live
capability, inventing a universal transition runtime, or turning a structural
relation into a property theorem.

They are instantiated at one resolution. Each candidate specifies:

- its semantic center and physical canonicality;
- subject and identity boundaries;
- Protocol Interface and Prover Plan treatment;
- Relations ingress and correspondence;
- Fresh-to-Fiat--Shamir construction;
- semantic composition;
- authentication, admission, checking, and authority;
- extension behavior and expected failure modes; and
- capabilities it uniquely enables or makes expensive.

The portfolio intentionally includes a current-preserving reopening control,
an alignment/completion reopening control, two structural redesigns, and one
capability-expanding full-stack direction. E elaborates to a C-shaped admitted
subject, so it is a materially different authoring architecture but not an
independent admitted semantic center. Passing current cases is necessary but
cannot select a candidate by itself. Equal-resolution scenario and outcome
results are recorded separately rather than implied by the prose length here.

## 2. Frozen common comparison subject

This portfolio compares candidate architectures against the frozen Stage 3
target snapshot, not against the earlier draft vocabulary. All five candidates
must instantiate the following exact subject families:

```text
identity-bearing subjects
  = InteractiveCore
  + TranscriptConstruction
  + Protocol
  + ProtocolInterface
  + ProverPlan
  + RelationDefinitionRef
  + RelationInterface
  + RelationInstance
  + RelationBinding
  + RelationArtifactProfile
  + RelationAdapterContract
  + RelationArtifactObservation
  + CoreCompositionSpec

capability-neutral producer outputs
  = NormalizationAudit<ProtocolAuthoring | RelationAuthoring>
  + CanonicalRelationCandidateBundle

checked relations
  = PlanRealizes
  + RelationArtifactAgreesWithInterface
  + CommittedObjectGrounding
  + RelationCorrespondsAtInterface
  + RelationInstanceCorrespondsAtInterface
  + FSConstruction
  + CoreComposition

later-owner signatures only
  = RelationSatisfies
  + FSCompile
  + PropertyTransport
  + ProjectionCorrect
  + LocalOirValid
```

Every checked relation has its own opaque completed-result capability:
`CheckedPlanRealizes`, `CheckedArtifactInterfaceComparison`,
`CheckedCommittedObjectGrounding`, `CheckedRelationCorrespondenceJudgment`,
`CheckedInstanceCorrespondenceJudgment`, `CheckedFSConstruction`, or
`CheckedCoreComposition`. Only a completed affirmative or negative semantic
outcome mints the matching capability. The capability retains the exact
operands, question, regime, checker identity, read/dependency closure, and
field-factored result. Serialization never preserves live authority.

Every candidate also keeps all dependent IDs distinct: `CoreId`,
`TranscriptConstructionId`, `ProtocolId`, `ProtocolInterfaceId`,
`ProverPlanId`, `RelationDefinitionId`, `RelationInterfaceId`,
`RelationInstanceId`, `RelationArtifactProfileId`, `RelationAdapterId`,
`RelationBindingId`, `RelationArtifactByteId`,
`RelationArtifactObservationId`, and `CoreCompositionSpecId`. A private
witness assignment is an unlinkable occurrence-local confidential capability,
not a mandatory public content-addressed subject.

## 3. Frozen laws and equal-resolution axes

The tables for A--E below use the same contract. A row is complete only when it
states where the exact structure lives, what enters identity, which owner
authenticates and admits it, what live capability is required or produced, and
what a cold consumer must replay. The common frozen law surface is recorded
here so repeated candidate prose cannot weaken or silently rename it.

### 3.1 Identity, reference, and carrier contract

- Every subject and checked relation has its typed semantic regime.
  `TranscriptConstruction` deliberately uses the exact
  `ProtocolSemanticRegime`; a meaning change requires a regime/identity change.
- Candidate-local `LocalRef`s become typed `CoreRef<K>` only after Core identity
  exists. Interpretation-dependent maps use `ProtocolScopedRef<K>`. Composition
  uses `LocalChildOccurrenceRef` and `LocalTargetRef` in the spec preimage and
  forms durable `ChildOccurrenceRef` only after spec authentication.
- `CanonicalEncode_R` is injective and structural. Every semantic algorithm is
  a `CanonicalAlgorithmSpec`: either a closed finite typed term with declared
  totality evidence or a contract-regime-qualified content-addressed reference
  with exact ABI and direct dependency IDs. Live code, registries, callbacks,
  checker builds, transport digests, and process identities are excluded.
- Except for Candidate A's deliberate reopening control, Protocol has one
  physically canonical MLIR PIR graph carrier with one `pir.protocol` root and
  the exact closed operation allowlist. `Lower_R` and `Read_R` are bijective
  modulo only in-memory operation identity and required SSA alpha-renaming.
  `CoreId` is a Protocol subidentity and never a second official artifact root.
- Canonical-PIR authentication follows the exact order: structural transport
  checks -> diagnostic `ReadUnchecked_R` with no authority or round-trip law ->
  authentication of `ExactProtocolDependencyPreimageBundle` using the exact
  `ExactCoreDependencyAuthenticationCapabilities` and
  `ExactProtocolDependencyAuthenticationCapabilities` Fresh/FS record ->
  Core/construction/Protocol ID recomputation -> establishment of
  `IdConsistentCanonicalPirGraph_R` -> exposure of authoritative `Read_R`.
  Protocol admission separately consumes retained dependency views,
  `CompositionContextAuthority`, and the exact Fresh/FS-keyed
  `ExactProtocolAdmissionCheckerCapabilities`.

### 3.2 Exact Core and execution contract

`InteractiveCore` contains exact canonical families for dependencies, roles,
ports, values, objects, randomness, challenges, events, causal edges, a total
event permutation, claims, reductions, checks, failures, terminals, endpoint
obligations, prover obligations, and prover-obligation failures.

- `PortDecl` is occurrence-indexed with `ExactlyOne | FixedCount(n)` and binds
  an input to `InputSource` or an output to
  `OutputValues(CanonicalSeq<ValueRef>)`. `PortValue` names only an input
  `PortOccurrenceRef`. An output declaration groups values but creates no
  occurrence, exposure, path-availability fact, or intra-Core knowledge
  transfer.
- `ValueNode` is the exact fourteen-form closed sum:
  `PortValue`, `CanonicalConstant`, `PrivateRandomnessValue`,
  `ChallengeValue`, `ProverObligationOutput`, `CheckResult`,
  `FailureStatusValue`, `FailureOccurred`, `Tuple`, `Project`,
  `InjectVariant`, `Apply`, `GuardDecision`, and `GuardedMerge`.
  `GuardDecision` contains the canonical finite reduced ordered decision
  diagram over `BooleanAtom` and finite-value-equality atoms. Every stored
  activation, merge, suppression, and terminal-route guard is a
  `GuardValueRef`; equality and implication are direct canonical ROBDD
  operations. `GuardedMerge` is one-hot and only its selected branch must be
  available.
- `ObjectDecl` is a closed contract/inputs/owner/visibility/protected-use
  record. Boundary-indexed `ExistsAt`, `KnowsAt`, and `AvailableAt` are
  deterministically derived; there is no ambient knowledge. Claims are global
  actorless resources with least-reference saturation, exact linearity and
  terminal closure; they transfer no role knowledge.
- Roles are exactly one Prover, one Verifier, and at most one required
  PublicEnvironment. `EventKind` is the exact seven-form sum
  `ObservePublicValue | Message | FreshChallenge | InvokeCheck |
  RaiseFailure | EmitArtifact | ReachTerminal`. Every `EventDecl` has
  `{kind, actor, inputs, protected_observations, activation_guard,
  obligation_basis}`. `EventObligationBasis` has the kind-exact
  `EventEndpointContractBasis` and an optional `ProverConstructionBasis` only
  for a Prover-acted observe, message, or emit event. Inputs, observations,
  actors, endpoint contracts, and optional construction basis are recomputed
  exactly from the event kind. `MessageChannel` is the closed
  `Proof | PublicVerifierMessage | ApplicationChannel(contract)` sum.
- Execution distinguishes `EventAttempted`, `EventActionOccurs`, and
  `EventActionOccurrenceRef`. A Prover event resolves its guard, exact private
  sampling, and same-event output binding in a preparation phase before the
  action. A challenge transition occurs on attempt; only success publishes its
  value. The last scheduled event is a canonical-true fallback terminal.
- Randomness records exact owner, public-challenge or private-prover purpose,
  distribution, independent or joint correlation, occurrence timing, and
  exact failure. Joint groups have collision-free indices, exact marginals,
  one noncircular base guard, ordered conditional steps, and first-failure
  semantics. Fresh and FS change only public-challenge interpretation.
- `FailureSourceRef` is exactly `CheckFalse | ChallengeSampling |
  ExplicitAbort`. Failure class and source backlinks are exact.
  `ContinueWithStatus` produces only the canonical occurrence-indexed status
  token. Terminating results are fixed:
  `MalformedProtocolInput`/`CheckRejected -> Reject` and
  `ChallengeSamplingFailed`/`ExplicitProtocolAbort -> Abort`; no terminating
  failure can accept, and `ExplicitProtocolAbort` must terminate.
- Endpoint obligations and prover obligations are distinct complete derived
  sets. The prover cause family is exactly `MissingOutput`,
  `DuplicateOutput`, `EarlyOutput`, `UnexpectedOutput`, and
  `PrivateSamplingFailed`; execution uses the frozen deterministic precedence.
  `CoreInvocationInputs`, `ProverTrace`, and `RandomnessReplay` are closed
  explicit inputs. Replay validates exact independent or conditional joint
  transition membership and witnesses an allowed outcome, never stochastic
  generation.
- `ExecuteProtocol` additionally consumes the identity- and ABI-matched
  `ExactProtocolExecutionCapabilities` bundle and returns a qualified
  `CoreExecutionRecord` whose semantic outcome is only `Terminal` or
  `ProverDidNotProduce`. `AcceptProtocol` separately requires an Accept
  terminal and complete trace/replay/resource consumption.

### 3.3 Exact Interface contract

`ProtocolInterface` contains its Protocol ID, an identity-bearing least
algorithm-dependency closure, external ports, role entries, proof and statement
bindings, terminal outcomes, and application bindings.

- An external port uses `StatementContainerMember` exactly for public input
  Statement occurrences and `IndependentValueCodec` otherwise. The one
  statement encoder/decoder owns the byte language and yields a dependent
  `ProtocolPublicAssignment<P>`: a total no-extra same-domain map over every
  and only `ProtocolPublicStatementOccurrenceRef` of that Protocol.
- `GuardedProofTraceBinding` covers every and only Proof-channel messages.
  Presence is `AlwaysOccurs`, `OmittedWhenNotOccurs`, or
  `ExplicitNonOccurrenceTag` over the exact restricted
  `ProofEventOccurrencePredicateRef = EventActionOccurrence(event)`, not an
  activation guard. Decoding reconstructs a guarded potential trace without
  executing the verifier; realized positions preserve schedule order.
- Encoders are total and injective; tagged decoders are total over bytes and
  return only `Decoded` or exact `Malformed`. Pure decoding has no refusal or
  ambient policy branch. Every `InterfaceOutcome` corresponds bijectively to
  exactly one `TerminalRef`; its payload is exactly that terminal's ordered
  public outputs. Continuing failures and `ProverDidNotProduce` have no
  Interface outcome tag.
- Output-port binding still grants no Core exposure. Terminal output exposure
  is exact; every other external output needs a later OIR occurrence and
  availability proof.
- `AuthenticateProtocolInterface` consumes the exact dependency preimages and
  authentication capabilities. `AdmitProtocolInterface` consumes retained
  views, the exact admitted Protocol view, and identity-matched law-checker
  capabilities. Neither ID nor codec bytes grant admission.

### 3.4 Exact Plan contract

`ProverPlan` contains private inputs, construction nodes, typed holes, the
least private dependency closure, supplier requirements, and proposed
obligation routes. Coverage belongs only to the separate `PlanRealizes` check.

- `PlanOperandRef` distinguishes Protocol values, Protocol objects, Plan
  inputs, node outputs, and hole outputs. A private Prover port occurrence has
  one ingress through `ProtocolPrivatePortOccurrence`; raw private
  `PortValue` is excluded everywhere else. A raw Core
  `PrivateRandomnessValue` is likewise excluded from
  `ProtocolAvailableValueRef`; its only ingress is an exact
  `UsesProtocolRandomness(CanonicalSeq<PlanPrivateRandomnessRef>)` effect.
- `PlanBasisInputBinding` may use the unique private-port Plan input or exact
  available Protocol value/object, never `ExternalSecret`. Derived route
  deadlines check every transitive Protocol operand at `PreAttempt`.
  Randomness has singleton owner-route/node consumption and
  `RouteRandomnessIngresses(o) == o.private_randomness` in exact Core basis
  order, with no extra ingress and no hole or `PurePrivate` substitute.
- Authentication and admission close dependencies, typing, occurrence scope,
  DAGs, deadlines, holes, and suppliers but not obligation coverage.
  `PlanRealizes` checks exact private-port and obligation coverage, basis and
  output maps, randomness routes, confinement, and declared reads. It proves
  no value correctness, distributional fidelity, witness fact, provider
  behavior, termination, completeness, cost, or proof production.
- `PlanSemanticClass` is later computed by Stage 4B; no Plan field can assert
  its own placement.

### 3.5 Exact Relations contract

Relations keeps definition reference, interface, instance, local private
witness, binding, artifact profile, adapter, observation, grounding, and both
correspondence judgments separate.

- `RelationInterface` has occurrence-indexed public/witness ports, committed
  object occurrences, a structural accepted-result declaration, and its exact
  least typed dependency closure. Relation authoring normalization yields only
  a `CanonicalRelationCandidateBundle` plus a typed audit; every output follows
  ordinary independent authentication/admission.
- `RelationBinding` contains total public/witness occurrence maps with exact
  bidirectional identity-bearing value-domain bridges, a relation-occurrence-
  total committed-object grounding map, and one closed result-binding
  constructor. Public targets are only the dependent Interface statement
  occurrences; witness targets are private Prover input occurrences or exact
  prover-obligation outputs. `AcceptingTerminals` may contain only static
  Accept terminals.
- Artifact profile, adapter, byte interpretation, observation authentication,
  artifact/interface comparison, binding, grounding, and correspondence each
  have their own typed dependency, execution-capability, authentication, and
  admission boundary. Only completed interpretation yields an observation;
  only the exact checked comparison may answer an artifact question.
- `CorrespondenceQuestion` has four base clauses only:
  `PublicPorts`, `WitnessPorts`, `ResultBindingReferenceShape`, and
  `CommittedObjectGrounding`, plus a separate optional
  `artifact_question`. The base set may be empty only when that optional
  question is present. `ResultBindingReferenceShape` checks only the exact
  claim/check/Accept-terminal constructor and reference shape; it makes no
  relation-result behavioral equivalence claim.
- Grounding is total over relation committed-object occurrences, not Protocol
  objects. It permits several relation occurrences to name one Protocol object
  when their independently checked domains/derivations agree; it asserts no
  inverse injectivity or Protocol-object exhaustivity. Artifact observations
  are supplied exactly where each binding entry requests one.
- Value-level instance correspondence consumes an affirmative structural
  capability containing `PublicPorts`, exact admitted bridge views and
  identity-matched execution capabilities, and the exact dependent
  `ProtocolPublicAssignment<P>` before applying `to_protocol`.

### 3.6 Exact Fiat--Shamir contract

`TranscriptConstruction` contains Core ID, total initialization and public
context-occurrence initialization, injective framing, one action per event,
one `EventActionOccurrenceRef` prefix per challenge, total `abort_map`, and
`Standalone | Composed(spec, ordered child occurrences, exact context map)`.
Every Absorb covers every and only same-event input ordinal once in canonical
order. Derive occurs on challenge attempt and carries the exact independent or
joint intended distribution contract and linked failure; distributional
correspondence remains exclusively an `FSCompile`/property theorem question.

The lifecycle is exact and three-part:

```text
ConstructFS(admitted Fresh Protocol, admitted construction)
  -> FS target candidate + FSConstructionMaps
authenticate and independently admit that FS target Protocol
FinalizeFSConstruction(source, target, construction, maps, regime)
  -> Qualified<CheckedFSConstruction>
```

`FSConstructionMaps` contains source/target Protocol IDs, shared Core ID,
interpretation change, total scoped event/challenge bijections, and exact
potential/action-occurring prefix descriptors. Construction authentication,
dependency authentication, and construction-law admission use separately
typed capability bundles. A composed construction is authenticated/admitted
only after Core formation through the exact `FiatShamirFormationInput` and
same-invocation `ScopedCompositionFormationAuthority`; cold replay reconstructs
that authority from admitted spec and child views.

### 3.7 Exact composition contract

`CoreCompositionSpec` commits to target Protocol regime, ordered child Core
IDs/slots, occurrence-indexed face maps, ordinary and terminal origin maps,
local additions, child seams and local causal edges, a complete target-event
permutation, total challenge/private-randomness/failure/reach policies, the
terminal combiner, and the complete local target fragment.

- v0 requires every child Core regime to equal the target Protocol regime.
  Dependencies are the exact target-required least reachable closure selected
  from reachable child views plus disjoint local supplies; unused child history
  is dropped. Obligations and obligation failures are recomputed after every
  event/basis/randomness rewrite.
- Face maps are occurrence-indexed and sequence-valued. `InternalInputs` cannot
  replace a claim-producing input occurrence. `ordinary_origin_maps`, total
  `terminal_origin_map` with propagation/capture/removal partition,
  `locally_added`, and the exact causal-edge union form a disjoint exhaustive
  origin/provenance account.
- Challenge policies are `IndependentChallenge`, `JointChallengeMember`,
  `SharedChallenge`, `DerivedChallenge`, or `ImportedChallenge`; private
  policies are preserve, joint, derived, or external supply. Shared members
  have exactly equal post-suppression coactivation and one target occurrence;
  joint groups derive one noncircular common base and exact member guards.
  Derived/imported substitutions remove the old randomness, failure,
  obligations, and coin index and name the exact public observation. Private
  substitution also names the exact owner-event construction-basis rewrite.
- Failure/reach handling is occurrence-total. Propagation preserves exact
  class/effect/result/payload/envelope; capture is an `IntentionalChange`, is
  claim-quiescent, suppresses the complete child suffix, and records a complete
  typed exit tuple. `ExplicitProtocolAbort` cannot be captured. Every captured
  status is an exact `InjectVariant` into one per-child sum; one selected-branch
  `GuardedMerge` feeds the combiner.
- The combiner has an authenticated terminal-result value domain, exact
  result/public-output `Apply` equations, canonical projections, non-last
  finite-equality guards, and one canonical-true final fallback. Completion and
  schedule laws ensure all children resolve before a final and propagated exits
  preempt every combiner route.
- `ConstructAndSubadmitCore` receives exact Core admission authority;
  `FormAndAdmitProtocol` receives Fresh or the closed FS formation record; and
  `FinalizeCoreComposition` compares the independently admitted target.
  `ResolveCoreCompositionMaps` is a total deterministic comparison returning
  `CoreCompositionCheckedPayload = Affirmative(ResolvedCoreCompositionMaps) |
  Negative(nonempty typed mismatches, unaffected agreements)`. Negative keeps
  no maps. Only affirmative `CheckedCoreComposition` grants composition-context
  authority. Cold replay reconstructs all live authority and reruns the three
  phases.

### 3.8 Authority, outcomes, and scenario contract

Every identity-bearing subject follows candidate -> physical authentication ->
domain admission -> opaque immutable process-local capability. Producers and
constructors mint candidates only; every target is independently authenticated
and admitted before a checked relation. Positive consumers require the exact
affirmative checked capability. IDs, signatures, stored results, normalization
audits, and dependency declarations never launder authority.

Owner outcomes keep `Affirmative`, fact-retaining `Negative`, `Unsupported`,
`CannotAnswer`, `Refused`, `Malformed`, and `CheckerFailure` distinct wherever
the boundary can produce them. Absence of support, authority, or named input is
never semantic disagreement. Normalization, structural admission, execution,
correspondence, satisfaction, construction, theorem transport, and endpoint
validity remain separate judgments.

The common scenario surface is `P1`--`P3`, `I1`--`I2`, `L1`--`L3`, `R1`,
`F1`--`F2`, `C1`--`C2`, `T1`, `S1`, and the hidden-input, regime,
outcome-separation, laundering, unknown-extension, and opportunity probes.
`O1` is only a required owner handoff: Stage 3 preserves the exact source view
needed later to distinguish local OIR validity from projection coverage, but no
candidate claims either result here.

## 4. Candidate A — semantic quotient over a rich sealed representative

### Thesis

Preserve the strongest form of the current architecture. A rich MLIR
representative carries open and sealed Protocol material. Language-independent
semantics is recovered by a canonical semantic projection, and several
physically different representatives may denote the same subject.

```text
rich Open PIR
  -> seal rich representative
  -> structurally authenticate that exact rich carrier
  -> ReadUnchecked projection + pre-erasure/read-set audit
  -> authenticate dependencies and projected identities
  -> admit that exact representative under projected semantics
```

### Canonicality and identity

`CoreId` and `ProtocolId` are computed over the projected semantic object, not
MLIR text or bytecode. Author labels, presentation order declared irrelevant,
caches, derived routes, and diagnostic metadata may differ between admitted
representatives with one ID.

The admitted capability retains the exact rich representative plus the
projection regime. Every consumer must either read only the semantic
projection or name separately authenticated representative-specific inputs.

### Interface and Plan

Interface and Plan are distinct identity-bearing roots, but the sealed rich
container may carry convenient copies, indexes, routes, and labels. Admission
must prove each copy agrees with its owning root. A consumer cannot read a
carrier label unless it also cites the exact Interface or Plan.

### Relations

Relation subjects remain external. A binding note or opaque anchor in the rich
representative is ingress material only. Post-admission correspondence
consumes the projected Protocol view, exact Interface, relation interface and
binding and, when requested, an exact checked artifact/interface comparison
and/or committed-object grounding—never a raw artifact observation.

### Fiat--Shamir and composition

The semantic projection distinguishes fresh and FS Protocol identities and
exports occurrence/prefix maps. Link manipulates rich open representatives,
then seal reprojects and subadmits a new Core only inside target Protocol
formation. Composition provenance is retained as rich carrier material and
separately checked when a later consumer needs it.

### Exact instantiation on the common axes

| Axis | Candidate A instantiation |
|---|---|
| Subject, producer, result, and export inventory | Projection emits separately identified `InteractiveCore`, `TranscriptConstruction`, and `Protocol` semantic values. `Protocol` embeds the projected Core and carries only its selected challenge interpretation; the Fiat--Shamir branch contains the exact construction reference and dependency, never the `TranscriptConstruction` content. Interface and Plan remain projected-ID-dependent roots; all seven relation definition/interface/instance/binding/profile/adapter/observation roots and `CoreCompositionSpec` remain independently identified external roots. `NormalizationAudit<ProtocolAuthoring>`, `NormalizationAudit<RelationAuthoring>`, and `CanonicalRelationCandidateBundle` are capability-neutral producer outputs even when stored beside the rich representative. The seven completed relation families mint only their exact `CheckedPlanRealizes`, `CheckedArtifactInterfaceComparison`, `CheckedCommittedObjectGrounding`, `CheckedRelationCorrespondenceJudgment`, `CheckedInstanceCorrespondenceJudgment`, `CheckedFSConstruction`, or `CheckedCoreComposition` capability on A/N. `RelationSatisfies`, `FSCompile`, `PropertyTransport`, `ProjectionCorrect`, and `LocalOirValid` remain later-owner signatures. |
| Physical carrier and authoring boundary | The rich sealed MLIR representative is the admitted physical Protocol carrier. Its exact structure is authenticated and retained with the admission capability, while the canonical semantic projection supplies meaning and identity. Several structurally different authenticated and admitted representatives may therefore share one projected `ProtocolId`; no unique canonical physical PIR graph or bijective `Lower_R`/`Read_R` carrier exists in A. Every rich name, cache, label, route, and metadata field is included in a consumer read set, extracted to an identified satellite, proved projection-neutral before erasure, or rejected. This is precisely why A remains ineligible under the fixed physical-canonical-carrier gate unless that decision is reopened. |
| Core schema, references, and identity | Projection emits every frozen Core family, occurrence-indexed port and output-sequence grammar, all fourteen `ValueNode` constructors, closed `ObjectDecl`, seven event kinds, and the six-field `EventDecl` with exact obligation basis. It then recomputes regime-qualified `CoreId` and `ProtocolId`; the Protocol embeds that exact Core and holds only its Fresh selection or typed construction reference. Local references become typed Core references only after Core identity, while interpretation-dependent maps remain Protocol-scoped. The exact guard node is `GuardDecision(CanonicalGuardFormula)`, and the event envelope's sixth field is `obligation_basis: EventObligationBasis`. |
| Core execution, randomness, failures, and obligations | Projection materializes the frozen boundary-indexed availability/knowledge algebra, claim closure, `EventAttempted`/`EventActionOccurs`, two-phase Prover action, attempt-time challenge resolution, independent/joint randomness transitions, exact failure/terminal table, and complete endpoint/prover obligation families including `UnexpectedOutput`. It rejects any rich implicit RNG, output event, role knowledge, failure payload, claim scheduler, or exception. `ExecuteProtocol` consumes the exact invocation, trace, replay, and identity-matched execution-capability bundle and returns only the qualified `CoreExecutionRecord`; `AcceptProtocol` is recomputed separately. A rich runtime cannot override the deterministic binding/failure precedence or treat replay as evidence of correct sampling. The recomputed cause sum explicitly includes `UnexpectedOutput(output_ordinal)`. |
| Interface | Projection emits a separately identified `ProtocolInterface` with its exact least algorithm-dependency closure. It uses `StatementContainerMember` only for public Statement occurrences, otherwise `IndependentValueCodec`; the one connected statement binding yields the total dependent `ProtocolPublicAssignment<P>`. Proof positions use the three exact `EventActionOccurrence` presence constructors and decoding reconstructs a potential trace without executing Protocol. Decoders return only `Decoded` or `Malformed`. External outcomes biject exactly with terminals and exact terminal payloads; nonterminal failures/nonproduction have no tag, and nonterminal output ports acquire no exposure. Rich Interface copies are checked mirrors only. Authentication, retained dependency views, exact Protocol view, and law-checker capabilities remain separate inputs. Its successful statement value is exactly the dependent total map `ProtocolPublicAssignment<P>`. |
| Plan | Projection emits a separate Plan with exact private inputs, values/objects, nodes, holes, dependencies, suppliers, and proposed routes. Private Prover port values enter only through their unique Plan input; raw private randomness enters only through owner-matched `UsesProtocolRandomness`, never a generic Protocol value. Admission checks the exact dependency/DAG/deadline/effect grammar but not coverage. Separate `PlanRealizes` checks private-port coverage, total obligation basis/output routes, `RouteRandomnessIngresses(o) == o.private_randomness`, singleton owner consumption, and no dead or hidden ingress. Rich routes and semantic-class labels are non-authoritative; Stage 4B computes placement. No secret, provider, live capability, correctness, fidelity, termination, cost, or completeness claim enters Plan identity or the structural result. |
| Relations | All relation roots remain external to the quotient and independently regime-qualified. Their occurrence-indexed dependencies, ports, objects, accepted-result role, binding bridges, artifact/profile/adapter lifecycles, execution capabilities, and relation-authoring normalization are the frozen forms. A correspondence question has the four base clauses plus a separate optional artifact question; `ResultBindingReferenceShape` is structural only. Grounding is relation-occurrence-total, permits checked aliasing, and is neither Protocol-object-total nor inverse-injective. Instance correspondence consumes an affirmative `PublicPorts` capability, admitted bridge views/execution capabilities, and the exact dependent public assignment before applying `to_protocol`. A rich anchor, raw observation, adapter assertion, or binding shape grants none of comparison, grounding, correspondence, satisfaction, or property authority. The exact base-clause sum includes `ResultBindingReferenceShape`; an artifact request remains the separate optional `artifact_question`. |
| Fiat--Shamir | Projection emits the exact `TranscriptConstruction`: total context-occurrence initialization, one action per event, same-event all-input Absorb coverage, action-occurrence prefixes, linked `abort_map`, joint-step contracts, and closed standalone/composed context. `ConstructFS` returns only the target candidate plus exact `FSConstructionMaps`; that target is separately authenticated/admitted before `FinalizeFSConstruction`. Composed FS formation uses the closed candidate/preimage/authentication/law-capability record and same-invocation scoped formation authority after target Core construction; cold replay reconstructs it. Rich transcript history supplies no authority, and construction concludes no distribution theorem, `FSCompile`, or property transport. Composed admission uses the exact closed `FiatShamirFormationInput`, never a shorthand candidate or ambient authority. |
| Composition | Rich link must first emit the complete frozen `CoreCompositionSpec`: same-regime children; occurrence-sequence face equations; ordinary/terminal/local origin partitions; exact causal-edge provenance; target-required reachable dependency closure; complete independent/joint/shared/derived/imported challenge and private policies; exact failure/reach handling, claim-quiescent captures, suffix suppression, and total terminal combiner. Shared challenges require equal post-suppression coactivation; joint groups use the common noncircular base; substitutions remove and rewrite every owned field. Explicit abort cannot be captured. The three-phase transaction constructs/subadmits Core, forms/admit Protocol with Fresh or exact FS input, and finalizes by total map comparison. `ResolvedCoreCompositionMaps` exists only in the affirmative payload; a negative checked result retains nonempty typed mismatches and unaffected agreements but grants no composition-context authority. No caller-supplied provisional map record exists or escapes. Final comparison returns `CoreCompositionCheckedPayload`; only `Affirmative(ResolvedCoreCompositionMaps)` carries maps or context authority. |
| Authentication, admission, capabilities, and replay | A's exact Protocol path is: structural authentication of the rich sealed carrier; diagnostic `ReadUnchecked_R` projection with the complete pre-erasure and consumer-read-set audit; authentication of `ExactProtocolDependencyPreimageBundle` under `ExactCoreDependencyAuthenticationCapabilities` and the Fresh/FS-keyed `ExactProtocolDependencyAuthenticationCapabilities`; recomputation of projected Core/Protocol IDs and consistency with that exact representative; then exposure of the authoritative projected `Read_R` and Protocol admission under `ExactProtocolAdmissionCheckerCapabilities`, retaining the representative and projection regime. Core admission remains transaction-scoped inside Protocol admission; only `AdmittedProtocol` can attenuate an `AdmittedCoreView`. Every satellite and checked relation repeats its owner authentication/admission/check. Cold replay must reauthenticate the same exact rich representative, reproject, rerun the pre-erasure/read-set audit, dependencies, IDs, admission, satellites, and requested relation; a matching projected ID or different admitted representative grants nothing. |
| Qualified outcomes and nonclaims | Projection and producer operations distinguish malformed, unsupported, refusal, checker failure, and capability-neutral successful candidate production. Every owner relation keeps affirmative, fact-retaining negative, unsupported, cannot-answer, refused, malformed, and checker-failure outcomes distinct where applicable; only completed A/N results mint their exact checked capability. No admission, execution, normalization, artifact observation, construction, or structural relation implies satisfaction, cryptographic properties, compilation legality, OIR validity, projection correctness, endpoint support, or implementation correspondence. |
| Scenario disposition and falsifier | A can express the frozen operational scenarios only under a complete projection/read-set discipline. It remains gate-ineligible until physical canonicality is reopened. Its decisive falsifier is either two allowed same-ID representatives producing different normative results, or any refusal-sensitive distinction erased before its owner check. |

### Strengths

- preserves mature MLIR diagnostics, author intent, and current tooling;
- minimizes duplication between workbench and admitted carrier; and
- permits late improvement of physical normalization.

### Structural costs and falsifiers

- every normative consumer must prove it ignores quotient-neutral material;
- physical carriers with one semantic ID can drift in Interface- or Plan-like
  labels unless all read sets are closed;
- cross-language independent checking must reimplement a complex projection;
- canonical information loss can occur before a consumer-specific check; and
- cached or derived mirrors create recurrent authority ambiguity.

Candidate A fails if one admitted ID permits different normative results under
two allowed representatives without an additional identified input.

## 5. Candidate B — physically canonical multi-subject bundle

### Thesis

Normalize the closed reusable, non-occurrence Stage 3 subjects into one
physically canonical package. Protocols (each with its embedded Core subbody),
Interfaces, Plans, reusable relation subjects, construction subjects/results,
and composition specs/results remain separately identified subobjects but are
stored and admitted together. Occurrence-local private witnesses, artifact
bytes, and artifact observations remain outside the authoritative bundle; an
optional transport envelope may co-deliver them without changing membership
or authority. `CoreId` remains a Protocol subidentity, not a separately
packaged official root.

```text
authoring material
  -> canonical bundle {
       Protocol*,
       Interface*, Plan*,
       relation bindings*, composition results*
     }
  -> authenticate all roots
  -> admit bundle closure
```

### Canonicality and identity

The bundle has one deterministic physical form. Each subobject retains its own
semantic ID; a package transport digest identifies the bundle only. Canonical
order is by subject kind then semantic ID. No bundle field can enter a
subobject's ID unless owned by that subobject.

### Interface and Plan

Several Interfaces and Plans may coexist. Bundle closure validates member and
dependency references only; each member is independently admitted and every
`PlanRealizes` relation is checked afterward by its own operation. A consumer
names one exact subobject ID, never “the Interface” or “the Plan.”

### Relations

Relation definitions and interfaces may be embedded by semantic content or
cited by exact dependency. Artifact observations remain outside the bundle
because they concern bytes and interpretation occurrences, not Protocol
meaning.

### Fiat--Shamir and composition

One package can include fresh and FS Protocols plus an `FSConstructionMaps`
constructor operand and its separate `CheckedFSConstruction` result, or child
and composite Protocols plus a composition spec/result over their attenuated
Core views. Each Protocol, satellite, operand, or result keeps its own owner
boundary. Bundle closure rejects dangling references and ambiguous roots.

### Exact instantiation on the common axes

| Axis | Candidate B instantiation |
|---|---|
| Subject, producer, result, and export inventory | The authoritative package may co-store, but never collapses, Protocol/Core/construction members; dependent Interface and Plan members; relation definition/interface/instance/binding/profile/adapter members; and composition-spec members. `RelationArtifactObservation`, relation artifact bytes, and private witness occurrences remain external occurrence inputs; an optional non-authoritative transport envelope may co-deliver them but cannot make them authoritative bundle members. Normalization audits and `CanonicalRelationCandidateBundle` are non-authorizing producer members. The seven relation families mint separate member-scoped `CheckedPlanRealizes`, `CheckedArtifactInterfaceComparison`, `CheckedCommittedObjectGrounding`, `CheckedRelationCorrespondenceJudgment`, `CheckedInstanceCorrespondenceJudgment`, `CheckedFSConstruction`, and `CheckedCoreComposition` capabilities only on completed A/N; package closure mints none. The five later-owner exported signatures remain outside bundle admission and acquire no result by co-location. |
| Physical carrier and authoring boundary | The package has one deterministic physical form, but every Protocol member independently owns the unique canonical MLIR PIR graph used by `Lower_R` and `Read_R`. Canonical package order and its bundle digest are transport facts; the package may index roots but cannot merge preimages, turn one member into another's carrier, or authorize a member. B additionally makes that package a normative exchange/admission center and therefore remains ineligible unless the fixed no-normative-bundle decision is reopened. |
| Core schema, references, and identity | Every Protocol member independently contains the exact frozen Core: occurrence-indexed port/output sequences, all fourteen value constructors with canonical ROBDD guards, closed objects, randomness, claims, failures, and seven event kinds in the six-field obligation-bearing envelope. Each member independently recomputes its regime-qualified Core and Protocol IDs; local and scoped references remain member-exact, while bundle order and identity never enter those preimages. The exact guard node is `GuardDecision(CanonicalGuardFormula)`, and the event envelope's sixth field is `obligation_basis: EventObligationBasis`. |
| Core execution, randomness, failures, and obligations | Each Protocol member independently implements the exact availability/knowledge/claim fold, attempt/action split, Prover preparation, public/private independent and joint steps, failure-class terminal table, terminal payload rules, and complete endpoint/prover obligation and cause families including unexpected output. Execution accepts only the closed invocation/trace/replay grammar plus the exact per-Protocol execution capabilities and returns a qualified record with only Terminal or ProverDidNotProduce. A package-level runtime, RNG, claim table, or “valid bundle” flag cannot supply or combine these facts; `AcceptProtocol` is derived per exact member invocation. The recomputed cause sum explicitly includes `UnexpectedOutput(output_ordinal)`. |
| Interface | Each Interface is a separately identified bundle member with its own exact algorithm-dependency closure and owner capability. The frozen statement representation split, total dependent `ProtocolPublicAssignment<P>`, action-occurrence proof presence constructors, pure Decoded/Malformed codecs, terminal-only outcome bijection, terminal payload equality, and output-exposure nonclaim are all checked against the exact admitted Protocol member. Multiple Interfaces may coexist and package order/defaults have no meaning. Bundle authentication does not replace Interface dependency authentication or admission, and co-location of a codec/outcome cannot authorize its use. Its successful statement value is exactly the dependent total map `ProtocolPublicAssignment<P>`. |
| Plan | Each Plan member contains the exact frozen grammar and least Plan-dependency closure, including Protocol objects, unique private-port ingress, `PlanPrivateRandomnessRef`, typed `PlanBasisInputBinding`, effect-only raw randomness ingress, route deadlines, and owner-singleton consumption. Admission proves only local typing/closure. Its separate `PlanRealizes` result checks exact private-port and obligation coverage plus route-basis/output and transitive randomness-sequence equality. Bundle closure may verify that named members exist but cannot turn proposed routes into coverage, resolve secrets/providers, self-assign `PlanSemanticClass`, or infer correctness/completeness. |
| Relations | Relation definition/interface/instance, binding, profile, and adapter may be independent authoritative members. Private witness occurrences, artifact bytes, and `RelationArtifactObservation` remain external occurrence inputs; comparison, grounding, and both correspondence results remain separately owned checks rather than bundle members. The bundle retains occurrence-indexed relation schemas, exact dependency/preimage/capability lifecycles, bidirectional bridge algorithms, four base correspondence clauses plus optional artifact question, structural-only result-binding shape, relation-total noninjective grounding, and dependent public-assignment instance check. Optional non-authoritative transport co-delivery never substitutes an observation for comparison, a binding for grounding/correspondence, or correspondence for satisfaction. A bundle-wide relation index grants no transitive authority. The exact base-clause sum includes `ResultBindingReferenceShape`; an artifact request remains the separate optional `artifact_question`. |
| Fiat--Shamir | A construction member has the exact total context/action/prefix/abort schema, all-input Absorb law, attempt-time derive semantics, joint structural laws, and exact dependency authentication/admission inputs. `ConstructFS` produces a target candidate and `FSConstructionMaps`; the target Protocol member is independently authenticated/admitted before `FinalizeFSConstruction`. For composed FS, candidate/dependency/auth/law inputs and same-invocation formation authority are supplied in the exact closed record; cold reopen replays spec/children/Core formation. Co-packaging source, target, construction, and maps establishes neither admission nor the later theorem. Composed admission uses the exact closed `FiatShamirFormationInput`, never a shorthand candidate or ambient authority. |
| Composition | A composition member is the entire frozen spec and is admitted against exact ordered child views of the same Protocol regime. Target dependencies are the required reachable closure, not a union of all packaged child history. Faces are occurrence-sequence exact; ordinary/terminal/local and causal-edge partitions are explicit; obligations are recomputed; challenge/private policies include joint member and equal-coactivation sharing; substitutions and private basis rewrites are exact; captures are claim-quiescent, suffix-total, and cannot catch ExplicitProtocolAbort; the terminal combiner uses the typed result domain and canonical-true fallback. The three-phase transaction remains mandatory despite co-location. Total final comparison yields the A/N payload; only affirmative retains `ResolvedCoreCompositionMaps` and grants context authority, while negative retains facts and no maps. Final comparison returns `CoreCompositionCheckedPayload`; only `Affirmative(ResolvedCoreCompositionMaps)` carries maps or context authority. |
| Authentication, admission, capabilities, and replay | Bundle authentication validates its envelope and routes raw members to their exact owner authenticators. It mints no cross-owner capability. Protocol admission uses the closed dependency/authentication/admission records and transaction-scoped Core witness; every satellite and relation independently authenticates dependencies, admits with narrow views and law checkers, and checks with operation-specific execution capabilities. A bundle closure result cannot widen, serialize, or cast authority. Cold replay authenticates/readmits every consumed root and recomputes every checked relation, including composed-FS formation and A/N composition comparison. For each Protocol member, diagnostic `ReadUnchecked_R` precedes exact `ExactProtocolDependencyPreimageBundle` authentication by `ExactCoreDependencyAuthenticationCapabilities` and the Fresh/FS-keyed `ExactProtocolDependencyAuthenticationCapabilities`; ID agreement establishes `IdConsistentCanonicalPirGraph_R` before `Read_R`. Admission separately consumes `ExactProtocolAdmissionCheckerCapabilities`. |
| Qualified outcomes and nonclaims | Bundle parsing/closure outcomes remain separate from member outcomes. Each owner retains the exact qualified classes and only completed A/N results mint the matching checked capability; a missing package member or live authority is CannotAnswer or Refused as owned, never agreement. Core execution, Interface decode, Plan coverage, relation facts, FS construction, composition, satisfaction, properties, OIR validity, and implementation correspondence remain distinct. A package snapshot is useful archival provenance but proves none of them by co-presence. |
| Scenario disposition and falsifier | B gives field-complete answers after reopening, but it fails the fixed no-normative-bundle gate and must prove that package closure creates no transitive authority or irrelevant semantic compatibility. Its decisive falsifier is any consumer deriving one member's authority from another, or an inability to add/remove an unrelated Interface or Plan without changing another member's meaning or authority. |

### Strengths

- one deterministic exchange and archival unit;
- no admitted physical quotient;
- efficient cross-subject closure checks; and
- strong reproducibility for an exact package snapshot.

### Structural costs and falsifiers

- adding one Interface or Plan changes package identity and distribution even
  though Protocol identity is stable;
- whole-bundle admission can make authority appear transitive across subjects;
- partial consumers need projection and dependency extraction rules;
- independent evolution of Relations and PIR is coupled operationally; and
- it creates a compatibility product before a named cross-process bundle
  consumer exists.

Candidate B fails if package convenience causes one subobject's admission,
capability, or persistence to be inferred from another's, or if independent
subject evolution requires frequent irrelevant bundle churn.

## 6. Candidate C — small semantic kernel with typed satellites

### Thesis

Define one small language-independent semantic algebra. Give Protocol—with its
embedded Core subbody—one physically canonical, bijective MLIR carrier. Keep Interface, Plan,
relation subjects, artifact observations, and checked relations as separate
typed satellites connected only by explicit dependent IDs and narrow views.
Canonical MLIR PIR is the unique physical Protocol carrier: the algebra is its
specified meaning, not a second serializable Protocol representation.
Satellites are finite canonical algebraic values with owner-specific lossless
transport profiles only; no satellite or transport can re-encode or stand in
for Protocol.

```text
                 +--> ProtocolInterface[ProtocolId]
Canonical        +--> ProverPlan[ProtocolId]
Protocol carrier-+--> RelationCorrespondence[ProtocolId, InterfaceId, ...]
                 +--> FSConstruction[source ProtocolId, target ProtocolId]
                 `--> CoreComposition[children, target CoreId]
```

### Canonicality and identity

The canonical PIR root is isomorphic to Core and Protocol semantics modulo
only MLIR in-memory object identity and required SSA alpha-renaming. It
contains no author names, locations, metadata, caches, derived
views, policy results, proofs, or Plan/Interface copies. Authentication checks
physical canonicality, dependency preimages, and semantic ID. Admission then
checks the complete Core/Protocol predicate.

Typed semantic encodings, not printer or bytecode, are the identity preimages.
Every satellite has its own dependent ID; each has its owner regime except
`TranscriptConstruction`, which deliberately reuses the exact Protocol
semantic regime. A transport may package several subjects through their
lossless owner profiles but acquires no semantic or authority role and never
becomes another Protocol carrier.

### Interface and Plan

Interface binds external containers, names, codecs, role entries, canonical
ports, proof occurrences, and terminals to one Protocol. Its codecs
use a total semantic encoder and a total tagged byte decoder whose successful
round trip is injective and meaning-preserving over the Protocol domain; byte
decoding may instead return an exact malformed outcome. Invocation refusal is
owned by a later wrapper or OIR boundary, never by pure decoding. Any
semantic restriction, default, reordering, transcript framing, or other
transcript-visible change is routed to an adapter, policy, wrapper, or new
Protocol.

Plan owns a private construction DAG, typed holes, dependency requirements,
and supplier requirements. Plan admission checks only Plan well-formedness.
`PlanRealizes` independently checks structural coverage of every exact prover
obligation. Completeness and cost remain later judgments.

### Relations

Relations owns definition reference, interface, public instance, private
witness occurrence, binding proposal, checked committed-object grounding,
artifact interpretation, and field-factored correspondence.
`RelationCorrespondsAtInterface` consumes narrow admitted views and produces a
qualified result without minting Protocol or relation authority.

### Fiat--Shamir

An exact transcript construction deterministically maps an admitted fresh
Protocol to a distinct FS Protocol. `ConstructFS` returns the target candidate
and exact `FSConstructionMaps`; after independent target admission,
`FinalizeFSConstruction` retains those maps as the checked relation's exact
operand and records its field-factored A/N result. The maps are not authority,
and a negative FS result is not subject to composition's A-only resolved-map
rule. Target admission is independent of `FSCompile`; property transport is
later and property-specific.

### Composition

A `CoreCompositionSpec` names local child slots, face maps, causal seams, one
total interleaving, complete challenge and private-randomness bundle policies,
total failure and reach-exit policies, capture suffix suppression, a
multi-route terminal combiner, and dependency/obligation closure. Its identity
is minted before global child-occurrence references, avoiding a self-reference.
It constructs one new Core candidate, which becomes authoritative only inside
an independently admitted target Protocol.

A separate checked `CoreComposition` result retains exact child/target views in
both completed variants. Only its affirmative payload retains typed
child-to-target `ResolvedCoreCompositionMaps` and grants composition-context
authority; the negative payload retains nonempty typed mismatches and
unaffected agreements but no maps. Core identity commits to the exact bounded-
normal-form target encoding, not a general behavioral quotient or unobserved
construction history; behaviorally equivalent but differently encoded Cores
may have different IDs.

### Exact instantiation on the common axes

| Axis | Candidate C instantiation |
|---|---|
| Subject, producer, result, and export inventory | The canonical Protocol carrier owns `InteractiveCore` plus challenge interpretation; `TranscriptConstruction`, Interface, Plan, all seven relation definition/interface/instance/binding/profile/adapter/observation roots, and `CoreCompositionSpec` are separately identified typed satellites. Protocol- and relation-authoring audits plus `CanonicalRelationCandidateBundle` are capability-neutral producer outputs. Completed A/N checks mint exactly one of the seven `CheckedPlanRealizes`, `CheckedArtifactInterfaceComparison`, `CheckedCommittedObjectGrounding`, `CheckedRelationCorrespondenceJudgment`, `CheckedInstanceCorrespondenceJudgment`, `CheckedFSConstruction`, or `CheckedCoreComposition` capabilities. The five satisfaction/FS/property/projection/OIR signatures are exported without implementation or conclusion. |
| Physical carrier and authoring boundary | The small language-independent algebra is the direct meaning of one physically canonical MLIR PIR graph, not a second Protocol carrier. `Lower_R` and `Read_R` are bijective over that graph; unknown operations, attributes, reference forms, or algorithm dependencies fail closed. Rich workbench material must normalize to this graph with a pre-erasure audit, while Interface, Plan, Relations, constructions, and results remain separately transported satellites. |
| Core schema, references, and identity | The canonical graph directly contains every frozen Core family, occurrence-indexed `PortDecl` and `OutputValues`, all fourteen `ValueNode` forms, closed objects, claims, randomness, failures, and seven event kinds in the exact six-field obligation-bearing `EventDecl`. Core and Protocol IDs commit to the bounded normal form and exact Protocol regime; Core is an embedded subidentity, satellites keep their own dependent IDs, and local/scoped references remain typed at their owning boundary. The exact guard node is `GuardDecision(CanonicalGuardFormula)`, and the event envelope's sixth field is `obligation_basis: EventObligationBasis`. |
| Core execution, randomness, failures, and obligations | Core directly defines the boundary-indexed existence/knowledge algebra, one schedule and claim saturation, attempt/action split, two-phase Prover binding, attempt-time Fresh/FS challenge transition, and explicit independent/joint randomness relations. It closes failure sources, status values, class-to-terminal results, payload availability, endpoint/prover obligations, and all five nonproduction causes. `CoreInvocationInputs`, `ProverTrace`, and `RandomnessReplay` are the only invocation carriers; the exact dependency/transcript execution-capability record is required and never retained. The deterministic replay and binding precedence yields only `Terminal` or `ProverDidNotProduce`; `AcceptProtocol` separately checks Accept plus complete consumption/resource behavior. The recomputed cause sum explicitly includes `UnexpectedOutput(output_ordinal)`. |
| Interface | A satellite `ProtocolInterface[ProtocolId]` has the exact frozen schema and identity-bearing least algorithm closure. Public Statement occurrences alone use the connected statement container and produce the total dependent `ProtocolPublicAssignment<P>`; all other ports have independent codecs. Proof presence denotes `EventActionOccurs` through the three closed constructors, not local activation, and decode reconstructs a potential trace. Decoders are pure total Decoded/Malformed functions. Outcomes biject only with terminals and exact terminal payloads; continuing failures, nonproduction, and nonterminal outputs gain no final tag or exposure. Interface authentication/admission consumes its exact dependency preimages/capabilities, retained views, admitted Protocol view, and law-checker capability; restrictions or transcript-visible rewrites are rejected. Its successful statement value is exactly the dependent total map `ProtocolPublicAssignment<P>`. |
| Plan | A satellite `ProverPlan[ProtocolId]` owns the exact closed descriptor grammar, Plan dependency closure, objects, holes, suppliers, and proposed routes. The unique Plan input is the only private-port ingress and `UsesProtocolRandomness` is the only raw private-sample ingress; the generic Protocol value space excludes both aliases. Admission verifies exact typing, DAG, deadlines, singleton randomness ownership, dependencies, and no ambient reads but does not claim coverage. Separate `PlanRealizes` checks one-to-one private-port ingress, total obligation routes, basis/output maps, transitive dependency, and exact `RouteRandomnessIngresses` equality. Secrets and live providers remain occurrence-local; realization makes none of the frozen correctness, fidelity, completeness, cost, or production claims, and Stage 4B owns semantic-class placement. |
| Relations | C uses the full separately owned Relations ontology: occurrence-indexed Interface/Instance, local private witness, binding with exact two-way value bridges and committed-object entries, profile/adapter/observation lifecycles, normalization audit, comparison, grounding, and both correspondence checks. Each dependency or algorithm family has exact preimage/authentication/admission/execution capabilities. The question is four base clauses plus optional artifact; result shape is reference-only. Grounding covers relation object occurrences and permits checked aliasing without inverse or Protocol-total claims. Instance correspondence requires affirmative PublicPorts, the exact dependent public assignment, admitted bridge views, and identity-matched bridge execution capabilities. No observation, shape check, or correspondence result becomes satisfaction/property authority. The exact base-clause sum includes `ResultBindingReferenceShape`; an artifact request remains the separate optional `artifact_question`. |
| Fiat--Shamir | The first-class construction satellite directly instantiates total public context initialization, one action per event, exact same-event input absorption, action-occurrence prefixes, linked failure map, joint structural semantics, intended distribution references, and the closed composition context. Authentication closes every algorithm dependency; admission consumes the exact Core view/witness, context authority, retained dependency views, and law capability. `ConstructFS` emits the target candidate and exact `FSConstructionMaps`; target authentication/admission is independent; `FinalizeFSConstruction` alone mints the checked capability. In composition, `FiatShamirFormationInput` carries every candidate/preimage/auth/law input and same-invocation formation authority; cold replay reconstructs it. Construction stays separate from `FSCompile` and property transport. Composed admission uses the exact closed `FiatShamirFormationInput`, never a shorthand candidate or ambient authority. |
| Composition | C directly owns the complete frozen local-reference spec, including target regime, ordered slots, occurrence faces, ordinary and terminal origins, local additions, exact causal provenance, target permutation, all policies, combiner, and full target fragment. Spec admission consumes same-regime ordered child views and retains exactly the target-required reachable child dependencies plus disjoint local supplies. Face sequences, claim-producing input restriction, obligation recomputation, shared coactivation, joint base/effective guards, substitutions and basis rewrites, failure-result compatibility, claim-quiescent capture, complete captured tuples, suffix suppression, and typed terminal combiner are all direct equations. The three-phase formation authenticates/admit the independent target. Total `ResolveCoreCompositionMaps` returns the exact A/N payload; affirmative alone retains the resolved record and grants context authority, while negative retains mismatch/agreement facts and no maps. Final comparison returns `CoreCompositionCheckedPayload`; only `Affirmative(ResolvedCoreCompositionMaps)` carries maps or context authority. |
| Authentication, admission, capabilities, and replay | Each root follows candidate -> exact physical/dependency authentication -> domain admission -> opaque owner capability. Canonical PIR authentication consumes the closed Protocol dependency preimage and authentication-capability records; admission consumes retained views, context authority, and exact Core/transcript law capabilities. Core authority is only a transaction witness during Protocol admission or an attenuated view afterward. Satellites repeat their typed lifecycles and checked relations consume only narrow matching views/execution capabilities. Cold replay reconstructs every capability, including composed-FS authority, and recomputes all identities/maps; IDs, serialization, normalization audits, result bytes, and signatures never authorize. Concretely, `ReadUnchecked_R` is diagnostic only; exact `ExactProtocolDependencyPreimageBundle`, `ExactCoreDependencyAuthenticationCapabilities`, and Fresh/FS-keyed `ExactProtocolDependencyAuthenticationCapabilities` plus ID recomputation establish `IdConsistentCanonicalPirGraph_R` before `Read_R`. `AdmitProtocol` then consumes retained views, context authority, and `ExactProtocolAdmissionCheckerCapabilities`. |
| Qualified outcomes and nonclaims | C uses owner-qualified result sums exactly. Only completed affirmative/negative checks mint their distinct process capability; unsupported questions, missing semantic basis, missing authority, malformed carriers, and operational failures remain separate. The composition negative capability is especially non-authorizing because it carries no resolved maps. Protocol admission/execution, Interface decode, Plan coverage, artifact interpretation, correspondence, FS/composition construction, satisfaction, analysis properties, compiler legality, OIR validity, and implementation correspondence are mutually non-substitutable. |
| Scenario disposition and falsifier | C passes the complete model-level scenario suite, including the explicitly hypothetical R1 observer, and is the only candidate eligible under all fixed Stage 1/2 gates. It is falsified if a bounded Protocol requires ambient meaning or a non-bijective carrier, if separating Interface/Plan changes verifier semantics, or if exact satellite dependency/admission forms an unavoidable authority cycle. |

### Strengths

- smallest authority surface and cleanest functional closure;
- independent Interface, Plan, Relations, and result evolution;
- canonical PIR can be checked without reconstructing authoring history;
- precise narrow views for later domains;
- multiple Interfaces, Plans, transcript constructions, and composition
  derivations over stable semantic subjects; and
- best path to independent formal and cross-language models without creating a
  second production IR.

### Structural costs and falsifiers

- more explicit subject and result IDs at APIs;
- authoring tools need robust lowering and diagnostics into the small kernel;
- package management must assemble dependencies without implying bundle
  authority; and
- APIs must authenticate immutable satellites against exact dependency IDs and
  rederive any capability-neutral cached view.

Candidate C fails if the small kernel cannot express a required current or
credible future Protocol without pushing semantic behavior into ambient
dependencies, or if the canonical carrier cannot remain bijective.

## 7. Candidate D — typed event calculus as the canonical subject

### Thesis

Make one typed event-and-effect calculus the semantic center. Protocol,
Interface, Plan, and relation behavior are typed programs or handlers over
explicit effects. Claims, construction, and correspondence are interpretations
of that calculus.

```text
free typed protocol-effect syntax
  + claim/resource effects
  + handlers for fresh coins, Fiat--Shamir, endpoints, prover plans,
    relations, and composition
```

### Canonicality and identity

The canonical subject is a normal form of the typed syntax. Identity commits to
the syntax, effect signature, dependency imports, and selected total schedule.
MLIR is a bijective carrier for that normalized program.

### Interface and Plan

Interface is a boundary handler assigning external codecs and containers to
port and wire effects. Plan is a handler implementing prover-obligation effects
through a construction DAG. Handler types prohibit changing verifier-visible
effects.

### Relations

Relation definitions are separate predicates. Ingress and correspondence are
typed handlers or simulations relating relation ports to Protocol effects.
Satisfaction and property theorems remain separate logics over interpretations.

### Fiat--Shamir and composition

Fresh and FS are distinct handlers over challenge effects. An FS construction
is handler application plus a complete trace map. Composition combines syntax
through an explicit operator that rewrites occurrence namespaces and effect
order, then normalizes one new Core.

### Exact instantiation on the common axes

Candidate D is not shorthand for “use effects.” Its concrete v0 center is a
finite, first-order, intrinsically typed `ProtocolProgramNF`: a canonical free
syntax with no higher-order handlers, open effect rows, recursion, or dynamic
occurrence allocation in an admitted subject. Handlers below are separately
typed normal-form subjects or checked interpretations, not ambient host code.

| Axis | Candidate D instantiation |
|---|---|
| Subject, producer, result, and export inventory | `ProtocolProgramNF` contains the Core/Protocol center; `TranscriptHandlerNF`, Interface/Plan handler normal forms, the seven first-class relation definition/interface/instance/binding/profile/adapter/observation subjects, and `ComposeProgramSpec` are separately identified owner normal forms. Protocol/relation normalization audits and `CanonicalRelationCandidateBundle` are producer outputs only. The seven owner simulations/checks mint their matching `CheckedPlanRealizes`, `CheckedArtifactInterfaceComparison`, `CheckedCommittedObjectGrounding`, `CheckedRelationCorrespondenceJudgment`, `CheckedInstanceCorrespondenceJudgment`, `CheckedFSConstruction`, or `CheckedCoreComposition` capability only on completed A/N. Satisfaction, FS/property, projection, and local-OIR signatures remain later interpretations, not generic handler results. |
| Physical carrier and authoring boundary | `ProtocolProgramNF` is a finite first-order intrinsically typed syntax with no recursion, higher-order handler, open effect row, dynamic occurrence, or host callback. Administrative normal form and a total deterministic normalizer select its unique physical program/PIR carrier under the exact Protocol regime. Gate eligibility remains conditional on actually enumerating the syntax, proving or executing total normalization and decidable canonical equality, and closing every pre-erasure audit. |
| Core schema, references, and identity | The normal-form constructors are in exact bijection with every frozen Core family: occurrence-indexed port/output sequences, all fourteen value forms, closed objects, resources, randomness, failures, and seven event effects carrying the six-field actor/input/observation/guard/obligation-basis envelope. Canonical equality recomputes Core/Protocol IDs and typed local/scoped references from that finite normal form rather than trusting intrinsic host types. The exact guard node is `GuardDecision(CanonicalGuardFormula)`, and the event envelope's sixth field is `obligation_basis: EventObligationBasis`. |
| Core execution, randomness, failures, and obligations | D gives `ProtocolProgramNF` a deterministic small-step handler whose state and transition constructors are exactly the frozen availability/knowledge/claim fold, attempt/action split, Prover preparation, public/private independent/joint steps, terminal ordering, and trace/replay precedence. Intrinsic types enforce occurrence backlinks, the failure-class result table, terminal payload availability, and all endpoint/prover obligations and five nonproduction causes; admission rederives them rather than trusting types. Invocation is the same closed input/ProverTrace/RandomnessReplay grammar and requires identity-matched dependency/transcript execution capabilities. The handler returns the same qualified execution record and cannot handle nonproduction as a verifier terminal. An executable adequacy simulation to the declared transition relation, not host evaluation, is required. The recomputed cause sum explicitly includes `UnexpectedOutput(output_ordinal)`. |
| Interface | `InterfaceHandlerNF[ProtocolId]` is a separately identified finite normal form, not a generic effect handler. It contains the exact Interface algorithm closure, statement representation partition and dependent public assignment, action-occurrence proof-presence sum, pure Decoded/Malformed codecs, terminal-only outcome bijection, payload equality, application bindings, and output-exposure nonclaim. Authentication/admission consumes the same exact dependency preimages/capabilities, Protocol view, and law capability. A relation-specific executable preservation simulation must show that handler encode/decode changes neither Protocol values, potential/active proof ordering, transcript observations, nor terminal behavior; failure to provide that simulation is CannotAnswer, not an implicit Interface pass. Its successful statement value is exactly the dependent total map `ProtocolPublicAssignment<P>`. |
| Plan | `PlanHandlerNF[ProtocolId]` is a finite form isomorphic to the frozen Plan grammar, including Protocol objects, unique private-port Plan inputs, effect-only private randomness refs, basis bindings, holes, suppliers, deadlines, and proposed obligation routes. It has the exact typed Plan dependency closure and excludes runtime secrets/capabilities. Admission checks the form only. A separate `PlanRealizes` simulation recomputes private-port coverage, basis/output maps, route dependency, singleton ownership, and exact transitive randomness-ingress sequence. Handler typing alone proves none of these and cannot self-classify Stage 4B placement. Executable realization simulation and finite dependency evaluation remain open implementation obligations. |
| Relations | Relation definition/interface/instance/binding/profile/adapter/observation remain first-class finite subjects rather than generic effects. Their occurrence-indexed dependencies, bidirectional bridges, committed-object grounding entries, authoring normalization, and exact authentication/admission/execution-capability lifecycles are explicitly represented. `CorrespondenceSimulationNF` is indexed by the four base clauses plus optional artifact question; it keeps structural result-reference shape, relation-occurrence-total noninjective grounding, and dependent-assignment instance checking exact. Separate executable simulations are required for artifact comparison, grounding, structural and instance correspondence. No handler type or generic simulation token substitutes for checked relation capabilities or satisfaction. The exact base-clause sum includes `ResultBindingReferenceShape`; an artifact request remains the separate optional `artifact_question`. |
| Fiat--Shamir | `TranscriptHandlerNF` is a finite separately admitted subject with exact context occurrence initialization, total event actions, same-event all-input absorption, action-occurrence prefix templates, linked failure map, joint-step shape, and standalone/composed context. Handler application is the exact three-step FS construction: generate target candidate/maps, independently authenticate/admit target, then finalize the relation. Composed application uses the closed formation input and same-invocation authority; cold replay renormalizes/reconstructs them. A complete executable event/challenge/prefix-map simulation is required. The handler's intended distribution annotations create no `FSCompile` or property theorem. Composed admission uses the exact closed `FiatShamirFormationInput`, never a shorthand candidate or ambient authority. |
| Composition | `ComposeProgramSpec` is a finite syntax isomorphic to the complete frozen composition spec, not a generic binary handler. It explicitly stores target regime, ordered slots, occurrence faces, origin and causal partitions, target permutation, all complete policies, combiner, and target normal form. Its typing/admission enforces same-regime children, target-required reachable dependencies, exact face sequences and claim restriction, challenge/private group equations, failure/result/removal laws, basis rewrites, quiescent capture, suffix suppression, and typed terminal combination. The interpreter follows the three authority phases and independently admits the target; total map simulation produces the exact A/N payload, with resolved maps/context authority only in A. D remains conditional on a total normalizer plus executable composition-map simulation; a generic “handled” proof is insufficient. Final comparison returns `CoreCompositionCheckedPayload`; only `Affirmative(ResolvedCoreCompositionMaps)` carries maps or context authority. |
| Authentication, admission, capabilities, and replay | Each normal-form root is physically authenticated and then admitted by its exact owner. Core admission is transaction-scoped inside Protocol; handlers/simulations have separately identified subject, relation, and checker regimes and consume the frozen dependency/authentication/admission/execution capability records. No universal handled-token capability exists. Replay reparses and renormalizes exact syntax and imports, reruns pre-erasure checks, owner admissions, executable simulations, composed-FS formation, and A/N map comparison. A normalizer proof, program ID, serialized handler, or prior simulation result grants no authority. Its Protocol path must nevertheless instantiate diagnostic `ReadUnchecked_R`, exact `ExactProtocolDependencyPreimageBundle`, `ExactCoreDependencyAuthenticationCapabilities`, Fresh/FS-keyed `ExactProtocolDependencyAuthenticationCapabilities`, ID establishment of `IdConsistentCanonicalPirGraph_R`, then `Read_R`; admission separately consumes `ExactProtocolAdmissionCheckerCapabilities`. |
| Qualified outcomes and nonclaims | Normalization distinguishes malformed syntax, unsupported effect, refusal, and operational failure. Every owner simulation/check uses the frozen qualified classes; only completed A/N results mint that exact capability. Missing finite syntax case or adequacy simulation is CannotAnswer/conditional evidence, never an affirmative. Normalization, execution, correspondence, satisfaction, FS/property theory, composition, OIR, and implementation claims remain separate. |
| Scenario disposition and falsifier | D has a complete design-level schema on every axis, but scenario answers remain conditional on finite syntax, total normalizer, decidable equality, and executable Interface, Plan, relation, FS-map, and composition-map simulations. It is falsified if adequacy needs ambient host behavior, a generic handled token substitutes for domain authority, or domain-specific exceptions repeatedly reconstruct C inside the calculus. |

### Strengths

- mathematically uniform treatment of interaction, transcript, failure, and
  interpretation;
- strong fit with effect handlers and executable formal semantics;
- opportunities for mechanized laws and multiple interpreters; and
- explicit control over ambient effects.

### Structural costs and falsifiers

- a universal effect abstraction can obscure domain-owned result meanings;
- claim-flow linearity and committed-object semantics become encodings inside
  a general calculus rather than first-class review surfaces;
- proving handler adequacy may be harder than checking direct typed objects;
- even first-order effect normal forms and adequacy simulations can become
  complex; adding higher-order handlers would require an explicit reopening;
  and
- implementation teams may accidentally treat the host calculus as semantic
  authority.

Candidate D fails if relation correspondence, claim resources, or canonical
normalization require effect-specific exceptions that reconstruct Candidate C
inside a more general shell.

## 8. Candidate E — parameterized protocol modules and generative composition

### Thesis

Make reusable protocol modules and typed parameterization the primary design
surface. A module can abstract over relations, fields, commitment schemes,
transcript constructions, challenge policies, and child Protocol faces.
Instantiation elaborates a fully closed Candidate C-style Core and Protocol.

```text
ProtocolModule[relation interface, dependencies, construction policy, faces]
  + admitted parameter assignments
  -> elaboration witness
  -> closed Core and Protocol
  -> independent authentication and admission
```

### Canonicality and identity

Modules and parameter assignments have separate authoring identities. Only the
fully elaborated closed Core and Protocol are admitted canonical subjects. Two
different modules may elaborate the same Core and receive the same Core ID;
their elaboration results remain separately identified provenance.

### Interface and Plan

Modules may generate Interface and Plan candidates, but those candidates are
independently authenticated and admitted. Genericity cannot make Interface or
Plan fields part of Protocol identity accidentally.

### Relations

Relation interfaces are first-class parameters with variance and capability
constraints. Instantiation emits an exact post-admission correspondence
obligation rather than assuming that type compatibility proves semantic
correspondence.

### Fiat--Shamir and composition

Transcript constructions and composition faces are parameters. Elaboration
produces exact occurrence and prefix maps. The result still crosses ordinary
target admission and later theorem boundaries.

### Exact instantiation on the common axes

Candidate E is equal-resolution as a *generative authoring center*. Its open
module and assignment objects are never admitted as Protocol meaning. The
semantic result of elaboration is exactly a closed C-shaped subject family;
the elaboration witness is provenance and a checked construction relation, not
an alternative way to authorize the result.

| Axis | Candidate E instantiation |
|---|---|
| Subject, producer, result, and export inventory | Elaboration emits separately identified closed Protocol/Core/construction, Interface, Plan, seven relation definition/interface/instance/binding/profile/adapter/observation, and composition-spec candidates; the open module is not any of them. Both normalization audits, the `CanonicalRelationCandidateBundle`, and the elaboration audit are non-authorizing producer outputs. Ordinary owner checks over closed outputs mint exactly the seven `CheckedPlanRealizes`, `CheckedArtifactInterfaceComparison`, `CheckedCommittedObjectGrounding`, `CheckedRelationCorrespondenceJudgment`, `CheckedInstanceCorrespondenceJudgment`, `CheckedFSConstruction`, and `CheckedCoreComposition` capabilities on completed A/N only. Satisfaction, FS/property, projection, and local-OIR remain later-owner signatures and cannot be generated conclusions. |
| Physical carrier and authoring boundary | A module and parameter assignment are authoring subjects only. Deterministic terminating elaboration emits one closed canonical MLIR PIR graph; ordinary authentication and admission ignore module assertions and consume only that output. Different modules may yield the same closed Protocol ID, while module, assignment, and elaboration identities remain optional provenance. If interpretation or admission of the output requires the module or elaborator, E is falsified as an authoring overlay. |
| Core schema, references, and identity | The elaborated graph directly contains every frozen Core family: occurrence-indexed ports/output sequences, all fourteen value forms and canonical ROBDD guards, objects, resources, randomness, failures, and seven exact six-field obligation-bearing events. Ordinary owner checks recompute all laws, typed references, and regime-qualified Core/Protocol IDs from the closed output; generic parameter compatibility cannot alter them. The exact guard node is `GuardDecision(CanonicalGuardFormula)`, and the event envelope's sixth field is `obligation_basis: EventObligationBasis`. |
| Core execution, randomness, failures, and obligations | Elaboration materializes the exact availability/knowledge/claim structure, attempt/action and Prover-preparation rules, independent/joint randomness groups, failure/result table, terminal payload laws, endpoint/prover obligations, and complete five-cause nonproduction family. Generic effects cannot add an event output, implicit RNG, exception, role knowledge, failure payload, or new cause. Closed output executes only through the exact invocation/trace/replay grammar and matching execution capabilities, yielding the frozen record and separate Accept predicate. Elaboration success or module typing proves neither trace production nor stochastic fidelity and is never an execution capability. The recomputed cause sum explicitly includes `UnexpectedOutput(output_ordinal)`. |
| Interface | An Interface generator emits a separately identified candidate with the exact algorithm dependency closure, statement-container split and dependent `ProtocolPublicAssignment<P>`, action-occurrence proof-presence variants, Decoded/Malformed codecs, terminal-only outcome bijection/payloads, application bindings, and nonterminal output-exposure rule. The candidate then independently authenticates dependencies and admits against the exact Protocol/law capabilities. Generic constraints cannot authorize codecs, omit potential positions, turn activation into occurrence, add refusal/defaults, tag continuing failure/nonproduction, or expose a value. Several generated Interfaces remain independent roots. Its successful statement value is exactly the dependent total map `ProtocolPublicAssignment<P>`. |
| Plan | A Plan generator emits the complete frozen descriptor grammar and dependency closure, including Protocol objects, unique private-port input, effect-only private randomness, typed basis maps, holes, suppliers, deadlines, and proposed routes. It cannot serialize secrets/providers/capabilities. Ordinary Plan admission checks local closure only; independent `PlanRealizes` recomputes private-port coverage, total obligation routing, transitive basis/output dependencies, singleton randomness ownership, and exact route randomness sequence. Module variance or type satisfaction proves none of these and cannot assign `PlanSemanticClass` or claim correctness, completeness, cost, or production. |
| Relations | Relation parameters elaborate to independently identified occurrence-indexed interfaces, instances, bindings, profiles, adapters, and observations with the frozen dependency and capability lifecycles. Generated bindings carry exact two-way bridges, result-reference constructors, and relation-total committed-object entries; normalization emits candidates/audit only. The correspondence question remains four base clauses plus optional artifact, grounding remains noninverse/non-Protocol-total, and instance checking requires affirmative PublicPorts, exact dependent public assignment, retained bridge views, and execution capabilities. Parameter compatibility, variance, an observation, or generated shape is never comparison, grounding, correspondence, satisfaction, or property authority. The exact base-clause sum includes `ResultBindingReferenceShape`; an artifact request remains the separate optional `artifact_question`. |
| Fiat--Shamir | A construction parameter elaborates the exact closed construction subject: total context occurrence initialization, event action table, all-input Absorb, action-occurrence prefixes, linked aborts, joint structural rules, intended distribution contracts, and exact composition context. Ordinary construction authentication/admission closes dependencies and capabilities. `ConstructFS` emits only candidate plus maps; target authentication/admission and `FinalizeFSConstruction` remain independent. Generated composed constructions use the complete formation record and same-invocation authority after target Core construction; cold replay can admit the closed result without replaying module provenance. No module theorem substitutes for `FSCompile` or property transport. Composed admission uses the exact closed `FiatShamirFormationInput`, never a shorthand candidate or ambient authority. |
| Composition | A composition module elaborates every field of the frozen local-reference spec: same-regime ordered children, occurrence faces, ordinary/terminal/local origins, causal provenance, target permutation, complete policies, combiner, and target fragment. Elaboration must resolve exact target-required reachable dependencies, sequence-valued faces, challenge/private group and substitution equations, basis rewrites, failure/result/removal rules, claim-quiescent capture, suffix suppression, and terminal result/output laws; generic defaults are forbidden. Ordinary spec admission and three-phase target formation then run independently. Total final comparison returns the A/N payload; module provenance or proposed maps cannot enter `ResolvedCoreCompositionMaps`, and only an affirmative checked result grants context authority. Final comparison returns `CoreCompositionCheckedPayload`; only `Affirmative(ResolvedCoreCompositionMaps)` carries maps or context authority. |
| Authentication, admission, capabilities, and replay | Module/assignment/elaborator authentication authorizes only those authoring inputs. Deterministic elaboration returns candidate outputs plus a capability-neutral audit. Every closed output follows the exact owner authentication, dependency admission, Core-within-Protocol authority topology, satellite checks, composed-FS formation, and relation execution capabilities. Semantic cold replay needs only closed preimages and owner checks; optional provenance replay additionally names module/assignment/elaborator/dependencies. Neither provenance nor generated IDs/results serialize authority. Every generated Protocol candidate independently follows diagnostic `ReadUnchecked_R`, exact `ExactProtocolDependencyPreimageBundle` authentication under `ExactCoreDependencyAuthenticationCapabilities` and Fresh/FS-keyed `ExactProtocolDependencyAuthenticationCapabilities`, ID establishment of `IdConsistentCanonicalPirGraph_R`, then `Read_R` and admission under `ExactProtocolAdmissionCheckerCapabilities`. |
| Qualified outcomes and nonclaims | Elaboration has its own malformed, unsupported, negative-constraint, cannot-answer, refused, and checker-failure outcomes, but success is only candidate production. Closed subjects and checked relations retain the frozen owner-qualified outcomes and capabilities, including map-free negative composition. Generic constraint success establishes no Protocol admission, execution, Plan coverage, relation correspondence/satisfaction, FS theorem, composition property, OIR validity, or implementation correspondence. |
| Scenario disposition and falsifier | E delegates every semantic scenario to independently admitted closed outputs and is therefore not a second admitted center. Its distinct module-language scenarios remain conditional on termination, determinism, parameter closure/variance, exact elaborator audit, and useful refusal diagnostics. It is falsified if an admitted output needs the module to be interpreted, elaboration is ambient or nonterminating, or generic constraints substitute for owner correspondence/property checks. |

### Strengths

- maximum reusable protocol-family and multi-relation authoring capability;
- explicit specialization without polluting canonical Core;
- supports reusable composition patterns and generated Interfaces/Plans; and
- separates template evolution from closed Protocol identity.

### Structural costs and falsifiers

- module typing, elaboration termination, parameter variance, and diagnostics
  form a large new language design;
- users may mistake generic constraints for correspondence or property proofs;
- reproducibility requires exact module, parameter, and elaborator inputs even
  when only the closed result is semantically authoritative; and
- premature standardization could freeze abstractions before enough protocol
  families exist.

Candidate E fails as the v0 semantic center if the module system becomes
necessary to interpret an admitted Protocol, or if it delays a small closed
canonical kernel. It remains a strong authoring-layer opportunity over
Candidate C.

## 9. Equal-resolution comparison

The detailed tables close the portfolio's former schema-resolution gap. This
means every candidate now has a concrete answer at the design level; it does
not mean every answer passes an inherited gate, has an executable checker, or
has survived the scenario suite.

| Pressure | A: rich quotient | B: canonical bundle | C: typed satellites | D: event calculus | E: generative modules |
|---|---|---|---|---|---|
| Language-independent meaning | Yes, via projection | Yes | Yes, direct algebra | Yes, calculus | Yes after elaboration |
| Physical canonical PIR | No; admitted rich quotient carriers | Yes per Protocol member; bundle additionally canonical | Yes, Core/Protocol only | Yes, normalized syntax | Yes after elaboration |
| Closed origins, roles, obligations | Exact after projection; rich extras audited | Exact per Core member | Exact direct Core schema | Exact first-order term/effect signature | Exact only in closed elaborated output |
| Subject authority separation | Conditional on complete projection read discipline | Conditional on bundle discipline | Strong | Strong only with domain-specific handler subjects and result types | Strong after elaboration |
| Multiple Interface/Plan subjects | Exact independent roots; rich copies risky | Exact independent members | Native independent satellites | Independently admitted handler normal forms | Generated then independently admitted |
| Relation/artifact seam | Exact external roots after projection | Reusable roots co-packaged; private witness, bytes, and observations external | Exact narrow bridge and question | First-class relation roots plus checked simulations | Exact parameters emit roots and checked obligations |
| FS action/prefix maps | Exact projected construction result | Exact subject/result members | First-class checked result | Exact transcript-handler action and prefix maps | Exact generated subject, then ordinary check |
| Private randomness | Exact projected Core facts | Exact per Core member | Direct Core facts | Explicit private-sampling effects | Exact closed output and generated policy |
| Composition | Exact spec; rich link then projection/recheck | Exact spec/result co-packaged | New Core plus checked maps | Local syntax operator plus complete target normal form | Module-local composition then exact spec/elaboration |
| Replay and capability closure | Reauthenticate exact rich carrier; reproject, readmit, and recheck | Reauthenticate every root; bundle grants nothing | Reauthenticate/readmit/recompute narrow relation | Renormalize plus every owner check | Closed replay ordinary; provenance replay optional and exact |
| Qualified outcomes | Owner-specific, including projection refusal | Owner-specific; no bundle Boolean | Owner-specific field-factored results | Owner-specific typed handler results | Elaboration outcomes distinct from downstream outcomes |
| Same canonical target from different histories | Same semantic projection ID, rich representatives differ | Same subobject ID, bundle differs | Same bounded-normal-form Core ID, result provenance differs | Same canonical program-normal-form ID if the required normalization proof closes | Same closed-result ID, elaborations differ |
| Independent checker feasibility | Complex semantic projection | Large bundle closure | Smallest closed subject checks | Requires calculus implementation | Closed-result checker plus optional elaboration replay |
| Cross-language modelability | Difficult | Moderate | Strong | Strong but abstract | Moderate to difficult |
| Authoring expressiveness | Strong immediately | Moderate | Delegated to rich workbench | High | Highest |
| v0 complexity | Medium but recurrent closure risk | High product surface | Medium and explicit | High semantic machinery | Very high authoring machinery |
| Intake posture | Fails fixed physical-canonical-carrier gate absent reopening | Fails fixed no-normative-bundle gate absent reopening | Gate-eligible target | Alternate center; normalization proof and implementation absent | Authoring overlay; not an independent admitted center |
| Main irreversible risk | Quotient/read-set debt | Bundle compatibility debt | Underpowered kernel | General-calculus gravity | Premature generic language |

## 10. Preliminary pressure-test result

Candidate C has the strongest architecture center. It most directly satisfies
the fixed subject split, Stage 2 ownership and capability model, physical
canonicality, exact relation seams, and independent evolution. Its costs are
visible and local rather than hidden in representative projection or bundle
authority.

Candidate E supplies a valuable authoring direction over C but should not be
required to interpret admitted subjects. Candidate D supplies formal semantic
techniques, especially typed effects and handlers, but should not become a
universal runtime or replace explicit domain subjects. Candidate A remains the
best current-preserving baseline and therefore the most important gap
comparison. Candidate B is justified only if a named whole-package consumer
later demonstrates that co-packaging is worth the compatibility surface.

This portfolio records the comparison rather than exercising convergence
authority. Candidate C has passed the Stage 3 scenario, field-closure,
producer/consumer-seam, type/authority, and equal-resolution gates recorded in
the companion validation documents. Its standing rejection triggers remain:

- a credible Protocol family cannot be expressed without ambient meaning;
- physical canonicalization requires irreversible erasure before all
  refusal-sensitive checks;
- Interface or Plan semantics cannot be separated without changing verifier
  meaning;
- Relations needs to redefine a Protocol-owned fact to express
  correspondence; or
- independent satellite admission produces unavoidable authority cycles.

### Candidate-specific residual obligations

Equal-resolution instantiation removes “unspecified” as a reason to dismiss a
candidate, but it does not remove these blockers:

- **A** requires an explicit reopening of physical canonicality before it can
  enter selection, followed by a proof that projection and every consumer read
  set preserve all refusal-sensitive distinctions.
- **B** requires an explicit reopening of the no-normative-bundle decision and
  a named whole-package consumer. Bundle closure must also be shown not to
  create transitive authority or irrelevant compatibility churn.
- **C** has no remaining Stage 3 model-selection blocker. Later work must still
  demonstrate implementation correspondence and instantiate the explicitly
  deferred Analysis, OIR, compiler, endpoint, and property judgments; the
  model result pre-approves none of them.
- **D** needs a complete finite syntax, a total deterministic normalizer,
  decidable canonical equality, and executable domain-specific simulations for
  Interface preservation, `PlanRealizes`, artifact comparison,
  correspondence, FS maps, and composition maps. Until those exist, its
  design-level scenario answers are not executed passes.
- **E** needs a terminating deterministic module language, variance and
  parameter-closure rules, an exact elaborator contract and audit, and
  diagnostics adequate to explain rejected closed output. It remains optional
  authoring infrastructure even if all of those succeed.

No blocker above changes the preliminary preference for C, and none authorizes
migration or implementation from this non-authoritative portfolio.
