# Protocol interfaces and prover plans

> **Document kind:** Target semantic specification
> **Document state:** Active non-normative target
> **Target status:** Stage 3.5 durable promotion
> **Provisional owner:** `pir`
> **Authority:** This document specifies the selected target for `docs-next/`.
> It is not normative until explicit consolidation and cutover. The current
> specifications under [`docs/`](../../docs/README.md) remain authoritative.
> This document makes no implementation, compatibility, or migration claim.

## 1. Scope and architectural position

A Protocol fixes verifier-visible semantics. A `ProtocolInterface` and a
`ProverPlan` are separately identified dependent subjects over one exact
`ProtocolId`:

~~~text
AdmittedProtocol
  + independently admitted ProtocolInterface
      -> external semantic presentation and OIR input
  + independently admitted ProverPlan
      -> private construction description
      -> separate PlanRealizes check
~~~

Neither subject is part of `ProtocolId`. Multiple Interfaces and Plans may
coexist for one Protocol, and Protocol-only consumers remain independent of
both. An Interface cannot change Protocol meaning. A Plan cannot change
verifier-visible behavior or assert that its proposed routes cover the
Protocol merely by being well formed.

This specification refines the selected
[Protocol IR architecture](../project/protocol-ir-architecture.md) under the
shared authority and outcome rules in the
[transition and bridge architecture](../project/transition-and-bridge-architecture.md).
Its upstream semantic subject is the durable
[Protocol semantic model](protocol-model.md); this page does not redefine Core
or Protocol. The [PIR domain index](README.md) remains the ownership map. Stage
4B OIR work owns the later projection and placement decisions described below.

The words “exact,” “total,” and “canonical” are semantic requirements:

- every normative read is an explicit immutable field, dependency view, or
  typed capability;
- every identity preimage uses the subject family's semantic regime and
  canonical encoding;
- every map claimed total covers every and only the stated dependent domain;
- unknown meaning-bearing constructors, regimes, dependency kinds, references,
  or algorithms fail closed; and
- a semantic ID, serialized record, signature, or producer report never
  substitutes for admission or checked-result authority.

## 2. Common dependent-subject lifecycle

### 2.1 Regimes, references, canonical encoding, and algorithms

The typed regimes used here are:

~~~text
ProtocolSemanticRegime
InterfaceSemanticRegime
PlanSemanticRegime
PlanRealizesRegime
~~~

A semantic regime fixes the subject family's meanings, admission rules, and
identity encoding. It is not a tool release, MLIR bytecode version, package
version, policy, or checker build. A semantic change requires a new typed
regime and therefore a new subject identity.

After Core authentication, an intrinsic typed reference is:

~~~text
CoreRef<K> = (CoreId, K, canonical_ordinal)
~~~

`K` is one closed Core family and is not interchangeable with another family
when ordinals match. A reference whose meaning depends on Fresh versus
Fiat--Shamir interpretation is:

~~~text
ProtocolScopedRef<K> = (ProtocolId, CoreRef<K>)
~~~

For each regime `R`, `CanonicalEncode_R(T)` is an injective typed structural
encoding:

- sums carry domain-separated variant tags;
- products encode fields in declared order;
- sequences encode length and ordered elements;
- sets and maps sort by canonical encoded keys and reject duplicates;
- optional values use explicit absent/present tags;
- references encode their subject family and complete typed key;
- scalars use the regime-owned unique mathematical encoding; and
- strings occur only in name-owning subjects and use the regime-owned Unicode
  and length encoding.

Printer spelling, MLIR bytecode, host layout, map iteration, source position,
pointer identity, and process identity never enter the semantic preimage.

Every codec, encoder, decoder, and private construction algorithm is canonical
data:

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

`LosslessContainerCodec`, `TotalSemanticEncoder`, and
`TotalTaggedSemanticDecoder` are kind-specific aliases of this sum. A
content-addressed reference requires its exact authenticated preimage and
typed dependency closure. A closed finite term has no external dependency
entry. Live code, callbacks, registry lookups, handles, and checker
capabilities are outside semantic identity.

Interface and Plan are finite canonical algebraic values, not alternate
Protocol carriers. A transport profile is permitted only with a total tagged
lossless decode into the exact semantic value. Transport bytes and profile
revisions do not enter identity unless that subject explicitly owns a byte
language. Authentication includes transport/profile validation when
applicable, exact value reconstruction, dependency authentication, and
identity recomputation.

### 2.2 Authentication, admission, and replay

Each subject follows the same authority topology:

~~~text
raw candidate
  -> physical and dependency authentication
  -> authenticated candidate with attenuated dependency views
  -> domain admission against an exact AdmittedProtocol view
  -> exact inert admitted-subject source binding
     + opaque immutable process-local capability that retains it
~~~

Authentication establishes carrier form, the least declared dependency
closure, dependency identities and ABIs, and the dependent subject identity.
It does not establish the subject's semantic laws. Admission consumes the
authenticated candidate, the exact admitted Protocol view, retained dependency
views, and identity-matched law-checker capabilities. Checker implementations
are operation inputs; they are not retained as semantic authority.

After serialization, FFI, mutation, reopening, or a process boundary, all
capabilities are gone. Replay starts from raw bytes or semantic preimages,
re-authenticates every dependency, re-admits the Protocol and dependent
subject, and reruns any requested relation. Equal IDs and prior result bytes
may locate material but grant no authority.

Every exported Interface, Plan, or attenuated admitted view uses the PIR
`ExactAdmittedSubjectAuthorityBinding` and exact family-indexed
`PirCapabilityContractId` defined in [Canonical PIR](canonical-pir.md#51-cross-owner-capability-contract-and-inert-bindings).
The capability contract and ABI explicitly authenticate the
`OwnerDefinesNoOperationPolicy` disposition. The binding is not an admission
receipt and contains no live or occurrence identity.

Official semantic persistence is admission-gated. Workbench caches and
proposal packages are explicitly unauthoritative. A durable checked result is
introduced only for a named independent consumer and binds every exact
subject, regime, operation input, checker identity, qualified outcome, and
residual trust condition. Its bytes still carry no live capability and must be
rechecked against newly admitted operands.

Semantic identity, dependency closure, Interface preservation, Plan
well-formedness, and `PlanRealizes` structural coverage are directly
recomputed. There is no open universal checker registry: each checker is
selected by the exact owner operation and semantic regime. Heuristic producer
search may propose a candidate but cannot replace these complete predicates.

### 2.3 Qualified checked results

Owner operations preserve distinct outcomes where applicable:

~~~text
Affirmative
Negative(reason, retained_facts)
Unsupported(exact unsupported construct or question)
CannotAnswer(missing named semantic input or basis)
Refused(missing authority or prohibited invocation)
Malformed(exact framing or structural defect)
CheckerFailure(operational failure with no semantic conclusion)
~~~

A completed negative is a semantic result. Missing input, unavailable support,
malformed material, refusal, and checker failure are not negative truth.

`Qualified<CheckedX>` creates its exact `PirCheckedResultCoordinate<X>` and
mints its distinct opaque process-local checked capability only for a completed
affirmative or negative semantic outcome. The
capability retains the exact operands, question, regime, field-factored result,
checker identity, dependency/read closure, and complete
`ExactCheckedResultAuthorityBinding`. `Unsupported`, `CannotAnswer`, `Refused`,
`Malformed`, and `CheckerFailure` create neither result coordinate nor checked
capability. Serialized result bytes are not the capability and cannot be
widened to another subject, regime, question, or conclusion.

For `PlanRealizes`, both completed A and N results can be retained and
replayed, but only the affirmative `CheckedPlanRealizes` variant can satisfy
the OIR `InterfaceAndPlan` input.

## 3. `ProtocolInterface`

### 3.1 Complete subject and dependency closure

~~~text
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
~~~

`algorithm_dependencies` is identity-bearing and is exactly the least reachable
closure of every content-addressed codec, encoder, and decoder reference.
Every reachable reference has one declaration with the same kind, contract
regime, content ID, direct edges, and Interface-facing ABI. Closed finite terms
have no external entry. Missing or unused entries, duplicate aliases,
undeclared transitive reads, and same-digest kind/regime/ABI mismatches reject.

External names and application-role labels are Interface semantics and enter
Interface identity. They are not Protocol semantics and grant no application,
relation, or policy authority.

### 3.2 Public statement assignment

The statement container denotes one complete dependent Protocol assignment:

~~~text
ProtocolPublicStatementOccurrenceRef =
  InputPortOccurrenceRef restricted to a Public Statement port

ProtocolPublicAssignment<P: ProtocolId> = {
  protocol_id: P,
  values:
    TotalMap<ProtocolPublicStatementOccurrenceRef in P,
             CanonicalSemanticValue in the exact referenced port domain>
}

CanonicalPublicAssignmentDomain(P) =
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
~~~

The assignment contains one value for every and only public input occurrence
whose purpose is `Statement`, under that occurrence's exact domain. Missing,
extra, wrong-Protocol, wrong-occurrence, or wrong-domain entries are outside
the assignment domain. Decoding cannot produce a partial assignment.

Every and only external port mapped to such a statement occurrence uses
`StatementContainerMember` and has no independent value codec. Expanding port
multiplicities yields the exact statement-occurrence range, and the selected
shape is a total bijection over it. External field or position domains equal
their mapped external-port domains and are losslessly equivalent to the exact
Protocol occurrence domains through this one encoder/decoder. All other ports
use `IndependentValueCodec` and satisfy their own direct round-trip laws.

The statement binding is the sole identity-bearing statement-container byte
language:

~~~text
decode(encode(x)) = Decoded(x)
encode is injective over protocol_domain
every Decoded statement yields exactly one ProtocolPublicAssignment<P>
~~~

There is no independently variable outer statement codec.

### 3.3 Guarded proof-trace binding

Proof positions range over every and only potential `Message` event whose
channel is `Proof`:

~~~text
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
~~~

`ProofEventOccurrencePredicateRef` has no independent body, identity, or
capability. It denotes exactly the named event's `EventActionOccurs` predicate,
not its local activation guard.

Admission proves:

- the potential-position bijection covers every and only proof-channel message
  event;
- every presence condition names that exact action-occurrence predicate;
- `AlwaysOccurs` is used only when the predicate is true on every admitted
  execution;
- absence is either unambiguous or explicitly tagged; and
- each realized trace is the exact active Core schedule subsequence.

Decoding reconstructs a guarded potential-position trace. Protocol execution
later determines its realized subsequence; Interface decoding does not execute
the verifier. The proof binding is the sole proof-container byte language and
does not add an outer codec or an unrecorded composition step.

### 3.4 Codec and transcript-preservation law

Every Interface semantic encoder is total over its exact semantic domain.
Every decoder is total over all byte strings as this closed result:

~~~text
Decode(bytes) =
    Decoded(canonical semantic value or trace)
  | Malformed(exact structural reason)

Decode(Encode(x)) = Decoded(x)
Encode is injective over the semantic domain
each Decoded byte string reconstructs exactly one canonical semantic value
~~~

Pure codec decoding has no caller-authority, feature-availability, policy, or
environment input and therefore has no refusal variant. Authorization,
unavailable runtime features, value restrictions, semantic defaults, and
application acceptance belong to a Stage 4B wrapper, OIR, or Realization
boundary. If such a condition changes Protocol acceptance, it requires a
wrapper or new Protocol rather than a decoder branch.

Interface decoding is outside the Protocol transcript boundary. It must not:

- reorder canonical proof occurrences;
- change canonical message values or bytes observed by transcript
  interpretation;
- choose transcript framing or challenge behavior;
- change checks, claims, failures, terminals, or accepted language; or
- inject restrictions, defaults, or hidden environment reads.

Different Interfaces may use different external byte languages while
preserving the same canonical semantic trace language.

### 3.5 Ports, applications, outcomes, and output exposure

Every external port preserves direction, domain, multiplicity, and the exact
mapped Protocol port. A statement occurrence appears once in the connected
statement binding, without ordinal aliases. Every potential proof occurrence
appears once in the guarded proof binding.

`external_outcomes` is a total bijection over Core terminal declarations:

- exactly one entry names each `TerminalRef`;
- external tags are injective across terminals;
- `payload_binding` is exactly the terminal's ordered `public_outputs`; and
- its codec losslessly round-trips the complete typed tuple.

A complete Protocol execution therefore yields one external terminal tag and
payload. A terminating failure is represented only through its target
terminal. A continuing failure is a nonfinal observation and has no Interface
outcome tag. `ProverDidNotProduce` is a producer-trace outcome, not a verifier
terminal or Interface outcome. If callers must distinguish two final causes,
the Core must provide distinct terminals.

For an external output port, the Interface fixes only typed grouping and
lossless representation. It creates no Core occurrence and makes no
availability claim. Terminal outputs have the exposure semantics above.
Every nonterminal output requires Stage 4B to name an OIR exposure occurrence
and discharge exact `AvailableAt` and visibility obligations.

An `ApplicationBinding` adds a closed typed application label to an exact
external port, event, or Interface outcome. It makes no relation
correspondence, policy, or authorization claim.

### 3.6 Identity, authentication, and admission

~~~text
ProtocolInterfaceId = H(
  "zkc/protocol-interface",
  InterfaceSemanticRegimeId,
  ProtocolId,
  CanonicalEncode(ProtocolInterface))

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
  exact complete ExactSourceAuthorityBinding ledger for the admitted Protocol
    view and every authority-bearing retained dependency view, with separately
    supplied fresh capabilities,
  ExactInterfaceLawCheckerCapabilities)
  -> (exact ExactAdmittedSubjectAuthorityBinding<PIR, ProtocolInterface>,
      fresh AdmittedProtocolInterface)
~~~

Authentication checks closed physical form, authenticates every and only
declared dependency preimage, verifies exact kind/regime/ID/ABI/edges, and
recomputes the dependent ID. The authenticated candidate retains attenuated
immutable dependency views.

Admission uses the exact Protocol view and identity-matched checker
capabilities to prove:

- every cited port, role, event, check, failure, and terminal exists;
- maps are total and injective where lossless recovery requires it;
- statement and proof decoding preserve exact canonical values and event
  occurrences;
- malformed containers are classified before Protocol acceptance;
- no restriction, semantic default, transcript rewrite, challenge/check
  change, or accepted-language change occurs; and
- application bindings are well typed but imply no relation claim.

Before successful admission, PIR matches every ledger entry to its separately
supplied fresh capability, reauthenticates the exact family capability contract
and ABI, and freshly validates every bound policy or explicit no-policy
disposition for the named Interface-admission purpose. It constructs the
canonical total transitive source-operation-policy closure. The exported
`ExactAdmittedSubjectAuthorityBinding<PIR, ProtocolInterface>` and fresh
`AdmittedProtocolInterface` capability retain that complete closure and every
inert `OwnerCapabilityRequirement`, but no transitive live authority.

Failure of any preservation clause means the candidate is not an Interface.
The changed behavior belongs in an external policy, a separately checked
adapter into the Interface domain, or a wrapper/new Protocol.

## 4. `ProverPlan`

### 4.1 Complete subject

~~~text
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
                PortValue of a private Prover input occurrence or
                PrivateRandomnessValue of a private-randomness occurrence)

ProtocolAvailableObjectRef =
  ProtocolObject(ProtocolScopedRef<object>)

ConstructionOutputRef = (ConstructionNodeRef, output_ordinal)
HoleOutputRef = (TypedHoleRef, output_ordinal)

PlanPrivateRandomnessRef =
  ProtocolScopedRef<randomness> restricted to RandomnessDecl entries whose
  purpose is PrivateProverSample

PrivateProtocolPlanInputRef =
  PlanInputRef restricted to a PlanInput whose source is
  ProtocolPrivatePortOccurrence

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
~~~

Construction nodes form a pure or explicitly effect-typed private DAG. Plan
dependencies are typed references of exactly the declared
`ProverConstructionContract` or `SupplierContract` kind; Core dependency
declarations cannot be reinterpreted as Plan contracts. The dependency map is
the least closed graph of all referenced Plan contracts and commits to exact
kind, regime, content identity, ABI, and direct edges.

Each operand preserves kind and domain. Protocol objects remain objects and
cannot be reinterpreted as values. A Protocol operand must be available to the
Prover at every derived route deadline. Node and hole inputs and output
ordinals match their contract ABIs exactly. A hole has no private-effect
channel and is not an unbound domain assertion. Supplier requirements are
typed declarations, not providers.

Runtime secrets, supplier handles, credentials, mutable provider state, and
process-local capabilities never enter the Plan's canonical encoding or
identity. They are occurrence-local inputs when a Plan is executed.

### 4.2 Exclusive private input and randomness ingress

A private Prover input occurrence has one Plan ingress: the unique
`PlanInputRef` whose source is that
`ProtocolPrivatePortOccurrence`. `ProtocolAvailableValueRef` excludes the same
origin across nodes, holes, basis maps, and transitive edges. A producer cannot
cite both spellings or read a runtime secret without the declared Plan input.

A raw Core `PrivateRandomnessValue(r)` also has one direct Plan ingress:
`r` in exactly one `UsesProtocolRandomness` sequence.
`ProtocolAvailableValueRef` excludes the raw value across all ordinary and
transitive operands. Derived Core values may be cited only under their exact
availability laws.

For `UsesProtocolRandomness(rs)`:

- `rs` is the node contract ABI's exact private-effect input sequence in
  length, order, domain, and purpose;
- each `r` is owned by the routed obligation through the recomputed Core
  backlink family;
- the node is evaluated after successful sampling and before the owner
  obligation's output binding; and
- a source appears in exactly one node's private-effect sequence; reuse flows
  through ordinary node outputs.

A second effect occurrence, an owner mismatch, or a raw-value bypass rejects
Plan admission. The Plan neither creates nor correlates a randomness source.

### 4.3 Deadlines, route ownership, and local admission

Let `DownstreamObligationRoutes(x)` be the exact nonempty set of obligation
routes whose producer transitively depends on node or hole `x`. Empty sets
reject. For every Protocol value or object read by `x` and every downstream
obligation `o`, admission proves:

~~~text
EventAttempted(source_event(o))
  implies AvailableAt(Prover, operand, PreAttempt(source_event(o)))
~~~

This is checked for each path and route, including mutually exclusive routes.
Textual node order and one unconditional deadline are not substitutes.

For a node using private randomness, `DownstreamObligationRoutes(node)` is
exactly the singleton Core owner of every referenced source. Local admission
also checks same `ProtocolId`, reference existence and domains, DAG
acyclicity, contract typing, holes, supplier form, route form, least dependency
closure, and absence of ambient reads. It does not check total obligation
coverage.

### 4.4 Identity, authentication, and admission

~~~text
ProverPlanId = H(
  "zkc/prover-plan",
  PlanSemanticRegimeId,
  ProtocolId,
  CanonicalEncode(ProverPlan))

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
  exact complete ExactSourceAuthorityBinding ledger for the admitted Protocol
    view and every authority-bearing retained dependency view, with separately
    supplied fresh capabilities,
  ExactPlanLawCheckerCapabilities)
  -> (exact ExactAdmittedSubjectAuthorityBinding<PIR, ProverPlan>,
      fresh AdmittedPlan)
~~~

Authentication validates closed physical form and every and only dependency
preimage in the identity-bearing least closure, checks
kind/regime/ID/ABI/edges, and recomputes the Plan ID. Admission consumes the
retained views, exact Protocol typing view, and identity-matched checker
capabilities. Serialized IDs, declarations, or checker code grant no
authority.

Before successful admission, PIR matches every ledger entry to its separately
supplied fresh capability, reauthenticates the exact family capability contract
and ABI, and freshly validates every bound policy or explicit no-policy
disposition for the named Plan-admission purpose. It constructs the canonical
total transitive source-operation-policy closure. The exported
`ExactAdmittedSubjectAuthorityBinding<PIR, ProverPlan>` and fresh `AdmittedPlan`
capability retain that complete closure and every inert
`OwnerCapabilityRequirement`, but no transitive live authority.

An `AdmittedPlan` proves only the local grammar and well-formedness above. It
does not prove total obligation coverage, `PlanRealizes`, or any OIR field
classification.

### 4.5 `PlanRealizes`

~~~text
PlanRealizes(
  AdmittedProtocol,
  AdmittedPlan,
  exact ExactAdmittedSubjectAuthorityBinding for both operands with separately
    supplied fresh capabilities,
  PlanRealizesRegime)
  -> Qualified<CheckedPlanRealizes,
               exact ExactCheckedResultAuthorityBinding<PIR, PlanRealizes>>
~~~

This is a separate relation over exact admitted operands. It checks:

1. The Protocol IDs match exactly.
2. Every private Prover input occurrence is in range, has visibility
   `PrivateToRole`, has the exact Plan-input domain, and is covered once by
   one unique `PrivateProtocolPlanInputRef`. No two Plan inputs alias it.
3. Each `ExternalSecret` uses its enclosing `PlanInputRef` as its
   collision-free Plan-local requirement identity and cannot masquerade as a
   Protocol occurrence.
4. Every prover obligation has exactly one total route to its exact typed
   outputs.
5. Each route's `basis_input_map` covers every and only obligation-input
   ordinal. A Core private-input `PortValue(o)` maps to its one
   `PrivateProtocolPlanInputRef`. Every other binding is the same-kind exact
   Protocol value or object, is a transitive producer dependency, and
   preserves occurrence and domain. `ExternalSecret` cannot satisfy a Core
   basis ordinal.
6. For every obligation `o`, define `RouteRandomnessIngresses(o)` as all
   `PlanPrivateRandomnessRef` entries in `UsesProtocolRandomness` effects
   within the producer's transitive dependency graph, ordered by canonical
   node ordinal and effect-input ordinal. Then:

   ~~~text
   RouteRandomnessIngresses(o) == o.private_randomness
   ~~~

   The equality is exact in length, order, owner, occurrence, domain, and
   purpose. Missing, extra, reordered, or unrelated sources make the completed
   relation negative even if the Plan was locally admissible. A hole or
   `PurePrivate` node cannot replace a required source.
7. Route inputs come only from available Protocol values/objects, Plan inputs,
   prior construction outputs, or explicit typed hole/supplier requirements.
8. Producer outputs match the obligation contract and domains.
9. The Plan has no constructor or reference that creates, replaces, reorders,
   retypes, or deletes Core events, messages, randomness, transcript actions,
   checks, failures, terminals, identities, or accepted language. Routes bind
   only exact `ProverObligationOutput` references.
10. Every Plan read is in its declared closure.

Before either completed affirmative or negative outcome, PIR matches both
admitted-subject bindings to their separately supplied fresh capabilities,
reauthenticates the exact family capability contracts and ABIs, and freshly
validates every bound-policy or explicit no-policy disposition for the named
Plan-realization purpose. It constructs the canonical total transitive source-
operation-policy closure. The checked-result binding and its fresh capability
retain that complete closure and both inert `OwnerCapabilityRequirement`
values, but no transitive live authority.

An affirmative result proves structural obligation coverage only. It does not
prove value correctness, distributional fidelity, witness validity, provider
correctness, honest-prover completeness, termination, cost, performance,
acceptance, or successful proof production.

### 4.6 Stage 4B placement constraints

`PlanSemanticClass` is an exported classification vocabulary, not a Plan field
and not part of Plan admission:

~~~text
PlanSemanticClass =
    ProjectionRelevant
  | RealizationOnly
  | ExternalSupplyRequirement
~~~

Stage 4B computes this classification against exact OIR and projection
semantics:

- `ProjectionRelevant` means substituting the field, while Protocol and
  Interface stay fixed, can change canonical prover-OIR event/value
  dependencies, explicit inputs, or local failure/control structure without
  changing verifier-visible Protocol semantics. If projection reads one such
  field, it consumes `InterfaceAndPlan` and OIR identity commits to the full
  exact `ProverPlanId`.
- `RealizationOnly` selects an algorithm, schedule, buffer, resource,
  implementation, or supplier below an already fixed OIR obligation.
  Projection cannot read it.
- `ExternalSupplyRequirement` is a typed need. Stage 4B determines whether it
  changes the OIR input contract or is resolved below OIR. It cannot be read
  ambiently at both layers.

The Stage 4B reader reports its exact Plan-field read set, classification, and
adequacy check. Verifier projection never consumes Plan. This section exports
constraints only; it neither defines OIR nor preclassifies concrete fields.

## 5. Consumer exports and nonclaims

PIR may derive narrow immutable source views from the admitted subjects:

| Consumer | Exact additional basis | Permitted result owner |
|---|---|---|
| OIR prover projection | exact Interface, role, and `InterfaceOnly` or `InterfaceAndPlan(AdmittedPlan, affirmative CheckedPlanRealizes)` | OIR |
| OIR verifier projection | exact Interface and verifier role; never Plan | OIR |
| Relations | exact Interface plus independently admitted relation subjects and question | Relations |
| Analysis | Interface or Plan only when its exact question reads that subject | Analysis |
| Evidence | exact subject identities and attributed observations | Evidence |

An exported view has no independent semantic authority unless a named durable
consumer requires a separately identified result. Its adequacy predicate must
cover every fact the named consumer can read. No universal fact root is
created.

Neither admission nor `PlanRealizes` establishes:

- relation truth, correspondence, satisfaction, or witness validity;
- soundness, knowledge, completeness, zero knowledge, or Fiat--Shamir
  security;
- compilation legality, optimizer correctness, or target selection;
- OIR validity, projection correctness, endpoint support, or output exposure
  beyond the exact Interface terminal rule;
- concrete realization, supplier correctness, termination, cost, or
  performance;
- implementation correspondence, formal-model adequacy, proof-assistant
  verification, artifact provenance, independent review, or production
  readiness; or
- compatibility with another semantic regime.

Those are separately owned subjects and qualified judgments.
