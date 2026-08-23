# Relation semantic model

> **Document kind:** Target semantic specification
> **Document state:** Active non-normative target
> **Target status:** Stage 3.5 durable promotion with selected Stage 4A
> relation-satisfaction extension
> **Provisional owner:** `relations`
> **Authority:** This document specifies the selected target for `docs-next/`.
> It is non-normative until explicit consolidation and cutover. The current
> specifications under [`docs/`](../../docs/README.md) remain authoritative.
> This document makes no implementation, migration, compatibility, or
> downstream property-establishment claim.

## 1. Scope and ownership

This document defines the durable target model for relation-facing semantic
subjects:

- an externally owned relation definition reference;
- an admitted relation semantic model for interpreting one exact definition
  family;
- a relation Interface, public instance, and occurrence-local private witness;
- a Protocol-to-relation binding with explicit value bridges and
  committed-object grounding declarations;
- artifact profiles, adapters, exact bytes, and expectation-free completed
  observations;
- checked artifact/interface comparison, committed-object grounding, and
  occurrence-local relation satisfaction; and
- the authentication, admission, capability, persistence, replay, outcome,
  and nonclaim boundaries for those subjects and checks.

The sibling [Protocol correspondence specification](protocol-correspondence.md)
owns the exact structural and public-instance correspondence judgments over
these subjects. The [Protocol Interface and Plan specification](../pir/interfaces-and-plans.md)
owns `ProtocolInterface` and `ProtocolPublicAssignment<P>`. The
[Protocol IR architecture](../project/protocol-ir-architecture.md) and
[transition and bridge architecture](../project/transition-and-bridge-architecture.md)
own the shared subject, authority, and checked-transition invariants. The
[Relations index](README.md) remains the domain map.

The relation definition itself remains external. zkc describes and checks a
typed boundary to it; relation admission does not claim that zkc compiled the
predicate, represented it faithfully, found a witness, or established
satisfaction.

The words “exact,” “total,” and “canonical” are requirements:

- every semantic read is an explicit field, retained admitted view, or
  identity-matched process-local capability;
- every identity preimage includes its owning semantic regime;
- a total map covers every and only occurrence in its stated dependent domain;
- canonical encodings are injective over their typed semantic domain;
- unknown meaning-bearing constructors, regimes, dependency kinds,
  references, ABIs, or algorithms fail closed; and
- an ID, digest, serialized result, signature, producer report, or co-location
  in a package never substitutes for live authority.

## 2. Subject and authority inventory

### 2.1 Identified subjects and byte material

| Subject | Owner regime | Identity boundary |
|---|---|---|
| `RelationDefinitionRef` | `RelationDefinitionRegimeId` owned by the external definition family | Cites the externally computed `RelationDefinitionId`; an Interface never synthesizes it |
| `RelationSemanticModel` | `RelationSemanticModelRegimeId` | Exact definition family, value interpretation, evaluation/refutation meaning, assumption schemas, and semantic dependency/read closure |
| `RelationSatisfactionBasisRegistry` | `RelationSatisfactionBasisRegistryRegimeId` | Exact evaluation, proof, certificate, correspondence, premise, assumption, side-condition, refutation, and semantic-extension contracts |
| `RelationSatisfactionValidationProfile` | `RelationSatisfactionValidationProfileRegimeId` | Exact checker, decoder, translation, proof-rule, authentication, and validation-root contracts |
| `RelationSatisfactionOperationPolicy` | `RelationSatisfactionOperationPolicyRegimeId` | Exact requested result strength, assurance/trust acceptance, disclosure, capability, persistence, replay, and refusal policy |
| `RelationSatisfactionCapabilityContract` | None; cycle-free Relations owner capability root | Exact satisfaction operand/result ABI, binding schema, atomic result/capability creation, freshness, lifetime, and replay-equality contract; authenticated and bound by the admitted satisfaction operation policy |
| `RelationSatisfactionSupportInstantiation` | `RelationSatisfactionSupportInstantiationRegimeId` | Inert exact support-binding, correspondence-support-binding, `OwnerCapabilityRequirement`, and total dependency-disposition realization for one semantic basis; explicitly not live authority |
| `RelationSatisfactionAttemptRecord` | `RelationSatisfactionAttemptRecordRegimeId` | Inert public question, policy-disclosed request/support, profile/basis/policy identities, assurance/trust, qualified outcome class, and policy-permitted retained facts; explicitly not an admitted semantic subject |
| `RelationCheckedResultRecord<R>` | None; capability-neutral cross-owner result coordinate | Exact completed A/N operands, question, regime, named consumer, family-indexed operation purpose, result facts, checker, trust, owner-policy disposition, source-policy closure, and owner capability requirement; portable ID only when its complete preimage and policy permit |
| `RelationCheckedResultPremiseRecordRef<R>` | None; owner-private process-local occurrence | Mandatory inert local branch for a checked result whose complete preimage is confidential or otherwise nonportable; `RelationSatisfactionPremiseRecordRef` is its satisfaction specialization |
| `RelationInterface` | `RelationInterfaceRegimeId` | Definition ref, exact dependency closure, occurrence schemas, committed-object roles, and accepted-result role |
| `RelationInstance` | `RelationInstanceRegimeId` | Exact Interface ID and occurrence-total canonical public assignment |
| `RelationBinding` | `RelationBindingRegimeId` | Exact Protocol Interface and relation Interface IDs, occurrence maps, value bridges, grounding entries, and result binding |
| `RelationArtifactProfile` | `RelationArtifactProfileRegimeId` | Byte language, raw-byte identity domain, fact and malformed schemas, and structural limits |
| `RelationAdapterContract` | `RelationAdapterRegimeId` | Exact profile ID, deterministic interpreter dependency, emitted/unread schemas, and closed tagged outcome schema |
| Exact relation artifact bytes | Exact admitted profile | Exact raw bytes under the profile; the transport envelope has no semantic role |
| `RelationArtifactObservation` | `RelationArtifactObservationRegimeId` | Exact byte ID, profile, adapter, observed facts, and unread fields from completed interpretation |

Exact relation artifact bytes are profile-scoped identified material, not an
independently admitted semantic subject. They gain no semantic-use authority
until supplied to an operation with the exact admitted profile and adapter.

`RelationSatisfactionSupportInstantiation`,
`RelationSatisfactionAttemptRecord`, `RelationCheckedResultRecord<R>`, and the
owner-private `RelationCheckedResultPremiseRecordRef<R>` are excluded from the
admitted-subject lifecycle below. They are inert and grant no authority. The
first two regimes fix only canonical record encoding, identity, disclosure
where applicable, and replay. Relations owns three
distinct typed local coordinate families:

- `PrivateWitnessAssignment.local_occurrence` uses `UnlinkableLocalRef` for the
  holder-issued witness occurrence;
- a completed nonportable checked result uses
  `RelationCheckedResultPremiseRecordRef<R>`; satisfaction uses the specialized
  alias `RelationSatisfactionPremiseRecordRef`; and
- any derived satisfaction value whose own identity preimage names a local
  coordinate uses `LocalRelationSatisfactionHandle<T>`.

None has a semantic regime or global ID. All are valid only for their exact
Relations owner instance, process generation, and authority lifetime. The
first two families are **allocated-reference domains**: the owning holder or
Relations allocates a fresh collision-free reference independently of the
referenced body, then atomically retains a typed
`reference -> complete body` association. A body never contains the reference
that selects it, so allocation and association have no identity cycle. The
third family is a **value-derived handle domain**: Relations derives an
injective owner-internal handle from the complete typed body, which likewise
does not contain that handle. These allocation and derivation rules are not
interchangeable.

Equality is defined only within the same typed domain, owner instance, and
generation; the witness-occurrence reference, premise-record reference, and
derived-value handle remain domain-separated even when one check relates them,
and coordinates from different instances or generations are never equal. A
lookup is valid only in the allocating owner and generation and must recover
the one retained complete typed body; a missing, multiply associated, or
body-mismatched reference is malformed. Distinct fresh references may select
equal bodies: allocated occurrence identity is reference equality, never body
deduplication. Reset, process crossing, or the end of the authority lifetime
invalidates every member and association in all three families.
None is a pointer, serialized token, public digest, or portable content
reference. Record authentication never admits a semantic subject or mints
premise, checker, witness, or satisfaction authority.

`PrivateWitnessAssignment` deliberately has no mandatory global content ID. It
is an unlinkable occurrence-local confidential value containing live secret
capabilities. Checked result records are not new semantic subjects and are
never authority. Their distinct live capabilities remain opaque and process-
local.

Every completed A/N Relations result exposed across an owner boundary is
created with exactly one project-wide
[`ExactSourceAuthorityBinding`](../project/analysis-and-compiler-architecture.md#23-capability-neutral-source-bindings).
Its checked-result coordinate is:

~~~text
RelationCheckedResultCoordinate<R> =
    Portable(RelationCheckedResultRecordId<R>)
  | OwnerLocal(RelationCheckedResultPremiseRecordRef<R>)

RelationsOperationPurpose<R>  // closed, result-family-indexed purpose coordinate

RelationCheckedResultRecord<R> {
  exact Relations owner domain and result-family tag,
  exact operands, question, semantic regime, and prerequisites,
  exact named_consumer: NamedConsumer,
  exact operation_purpose: RelationsOperationPurpose<R>,
  exact field-factored completed A/N result,
  exact checker contract, implementation, ABI, dependency, and read closure,
  exact qualification, assurance, and residual-trust closure,
  exact authenticated OwnerOperationPolicyDisposition,
  exact transitive source-operation-policy dependency closure,
  exact OwnerCapabilityRequirement
}

RelationCheckedResultPremiseRecordBody<R> = {
  exact same completed checked-result fields required above,
  exact owner-instance and process-generation scope,
  no RelationCheckedResultPremiseRecordRef<R>
}

RelationCheckedResultPremiseRecordAssociation<R>:
  (exact Relations owner instance,
   exact process generation,
   fresh RelationCheckedResultPremiseRecordRef<R>)
    -> exact RelationCheckedResultPremiseRecordBody<R>

RelationCheckedResultRecordId<R> = H(
  "zkc/relations-checked-result",
  R,
  CanonicalEncode(exact RelationCheckedResultRecord<R>))
~~~

`RelationsOperationPurpose<R>` is not a free-form label. Each checked-result
family admits only its closed purpose values, and values indexed by different
result families are distinct even when their display text is equal. The exact
named consumer and family-indexed purpose are invocation inputs, result-body
fields, binding fields, capability indices, policy-check coordinates, and
portable replay coordinates. No consumer- or purpose-erased checked Relations
result exists.

The portable branch is legal only when every identity-bearing preimage is
portable, the exact owner contract permits completed-result creation, portable
stable identity, retention, and disclosure for the exact family, named
consumer, and typed purpose, and every disposition in the complete transitive
source-operation-policy closure permits that same construction and retention.
Otherwise Relations may construct the complete local body, allocate a fresh
collision-free owner-local reference independently of that body, and atomically
install the single-valued typed association above only when the owner contract
and every source-policy disposition permit the exact owner-local completed
result and its retention. Here “owner contract” means the exact authenticated
immediate `OwnerOperationPolicyDisposition`: the admitted owner operation policy
under `BoundTo`, or the capability contract and ABI under an explicit
`OwnerDefinesNoOperationPolicy` branch. A denial makes the operation `Refused` before
`Completed`; invocation, capability use, result-record, attempt-audit, and replay
permissions are distinct and none substitutes for another. Neither the body nor
its association contains or derives authority.

The `OwnerCapabilityRequirement` contains the capability-contract identity,
ABI, operand/result binding schema, and freshness/lifetime requirements, never
a capability token or occurrence identity. The owner creates the inert binding
as part of the same completed operation that mints the live capability, and the
capability retains the exact binding. U/C/R/M/F creates neither. A consumer
supplies the binding and fresh capability separately and must check complete
field equality plus fresh authority under the bound-policy or explicit no-
policy contract branch.

The local branch commits its body association, source binding, and capability
as one completed owner transaction. A failed or non-completed attempt exposes
no reference, orphan association, binding, or capability.

Every admitted Relations subject capability exported across an owner boundary
uses the admitted-subject branch of the same envelope. Relations defines one
family-indexed, authenticated `RelationsAdmissionCapabilityContractId<S>` and
exact ABI per admitted subject family. The contract explicitly declares that
subject admission has no separate owner operation policy, so the binding
contains:

~~~text
OwnerDefinesNoOperationPolicy(
  RelationsAdmissionCapabilityContractId<S> and exact capability ABI)
~~~

Its portable semantic coordinate is the exact subject ID, admission regime,
admission-basis/dependency closure, and contract/ABI tuple; it is not an
admission receipt. A subject with a local identity-bearing dependency uses the
owner-local branch instead. Every admitted capability retains the exact
binding. Reconstruction reauthenticates the contract and complete coordinate,
reruns admission, requires full binding equality, and only then obtains fresh
authority. The declaration never grants an operation that another bound source
policy forbids.

### 2.2 Semantic regimes

~~~text
RelationDefinitionRegime        // externally owned
RelationSemanticModelRegime
RelationSatisfactionBasisRegistryRegime
RelationSatisfactionValidationProfileRegime
RelationSatisfactionOperationPolicyRegime
RelationSatisfactionSupportInstantiationRegime
RelationSatisfactionAttemptRecordRegime
RelationInterfaceRegime
RelationInstanceRegime
RelationBindingRegime
RelationArtifactProfileRegime
RelationAdapterRegime
RelationArtifactObservationRegime
CorrespondenceRegime
~~~

Each semantic-subject regime fixes the syntax, canonical encoding, identity
rule, dependency and ABI interpretation, admission predicate, replay rule, and
qualified outcome meaning for its family. `CorrespondenceRegime` separately fixes the
artifact-comparison and grounding equations used here and the correspondence
questions defined in the sibling specification. The support-instantiation and
attempt-record regimes have the narrower inert-record contracts stated above
and no subject-admission rule. The owner-private premise-record reference has no
regime and is not a persistable subject.

A semantic change requires a regime change, a new identity where the regime
enters an identity preimage, and a fresh check for every regime-qualified
result. Equal unqualified digests under different regimes, dependency kinds,
or ABIs never alias.

### 2.3 Common lifecycle

Every zkc-owned identity-bearing relation subject follows:

~~~text
raw candidate
  -> physical and dependency authentication
  -> authenticated candidate retaining attenuated dependency views
  -> owner-domain admission
  -> exact ExactAdmittedSubjectAuthorityBinding<Relations, SubjectFamily>
     plus separately minted opaque immutable process-local admitted capability
~~~

Authentication establishes the closed physical form, exact typed dependency
preimages, least dependency closure, direct edges, ABIs, and identity. It does
not establish semantic admission. Admission consumes the authenticated
candidate, retained exact dependency views, exact admitted operands, and
their complete exact source bindings with separately supplied fresh
capabilities, plus identity-matched law-checker capabilities. It freshly
validates every source-policy disposition, constructs the canonical total
transitive source-operation-policy closure, and atomically creates the returned
binding and fresh capability. Live source, checker, and authentication
capabilities never enter a semantic identity and are not retained as ambient
authority.

After serialization, FFI, mutation, reopening, or a process boundary, every
capability is gone. A consumer must reauthenticate dependency preimages,
reconstruct admitted operands and every exact source binding/policy closure,
re-admit the subject, require full portable binding equality, and rerun any
requested check with separately fresh capabilities. An owner-local binding is
recreated only as a new local occurrence and is not exact cold replay. Equal
IDs and stored results locate material but grant no authority.
`RelationDefinitionRef` instead remains under its external owner's lifecycle;
the profile-scoped raw-byte identity has no independent admission; and a
`PrivateWitnessAssignment` remains an occurrence-local confidential
value rather than entering this public lifecycle.

## 3. Typed relation Interface

### 3.1 Complete algebra

~~~text
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
~~~

Every `FixedCount(n)` is canonically positive. Multiplicity expansion creates
the collision-free occurrence domains named by `RelationPublicValueRef`,
`RelationWitnessValueRef`, and `RelationCommittedObjectRef`. The public and
witness sequences assign role by position; a reference cannot reclassify a
port.

The three domains of a committed-object role remain distinct even when two
share an encoding. Every accepted result is canonical under `output_domain`,
and `accepted_values` is nonempty and duplicate-free.

The dependency map is identity-bearing. Its direct roots are exactly the
contracts named by ports, committed-object roles, and the accepted-result
role. Its contents are every and only declaration in the least reachable
closure under `direct_dependencies`. Missing, unused, aliased, or ambient
dependencies reject.

### 3.2 Identity

~~~text
RelationInterfaceId = H(
  "zkc/relation-interface",
  RelationInterfaceRegimeId,
  RelationDefinitionRef,
  CanonicalEncode(RelationInterface))
~~~

`RelationDefinitionId` is computed by its external owner regime. Interface
identity neither rehashes the definition under a zkc-owned rule nor asserts
that the Interface faithfully formalizes it. zkc cites the external definition
opaquely unless an explicitly selected and admitted definition-language
adapter authenticates its exact owner-regime preimage; even that
authentication is not definition truth.

### 3.3 Authentication and admission

~~~text
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
  exact ExactAdmittedSubjectAuthorityBinding for every authority-bearing
    retained dependency view, with separately supplied fresh capabilities,
  ExactRelationInterfaceLawCheckerCapabilities)
  -> (exact ExactAdmittedSubjectAuthorityBinding<Relations, RelationInterface>,
      fresh AdmittedRelationInterface)
~~~

The preimage and capability maps have identical key sets and cover the exact
least dependency closure. Authentication verifies the definition-reference
form, occurrence ranges, dependency kinds/regimes/IDs/ABIs/direct edges, and
Interface identity, then retains attenuated immutable views. Admission checks
the domain ABIs, multiplicities, role separation, committed-object domains,
canonical result values, direct-root equality, and all totality laws.

Before successful Interface admission, Relations matches every authority-
bearing dependency-view binding to its separately supplied fresh capability,
reauthenticates the exact owner capability contract and ABI, and freshly
validates its bound policy or explicit no-policy disposition for the named
relation-interface-admission purpose. It constructs the canonical total
transitive source-operation-policy closure with no omitted or extra dependency.
The returned Interface binding uses
`RelationsAdmissionCapabilityContractId<RelationInterface>`, retains that
source closure and every source `OwnerCapabilityRequirement`, includes its own
Interface `OwnerCapabilityRequirement`, and declares the admission family's
explicit no-separate-operation-policy disposition. The fresh
`AdmittedRelationInterface` capability retains the identical binding.

The admitted capability establishes only this exact Interface. It does not
load a Protocol, artifact, instance, or witness and does not establish
definition truth, satisfiability, or satisfaction.

## 4. Public instances and private witnesses

### 4.1 Complete forms and identity

~~~text
RelationInstance = {
  interface_id: RelationInterfaceId,
  public_values:
    TotalMap<RelationPublicValueRef, CanonicalSemanticValue>
}

RelationInstanceId = H(
  "zkc/relation-instance",
  RelationInstanceRegimeId,
  RelationInterfaceId,
  CanonicalEncode(public_values))

PrivateWitnessAssignmentBody = {
  instance_id: RelationInstanceId,
  interface_id: RelationInterfaceId,
  private_values:
    TotalSecretMap<RelationWitnessValueRef, SecretValueCapability>
}

PrivateWitnessOccurrenceAssociation:
  (exact authorized holder and Relations owner instance,
   exact process generation,
   fresh UnlinkableLocalRef)
    -> exact PrivateWitnessAssignmentBody

PrivateWitnessAssignment = {
  local_occurrence: UnlinkableLocalRef,
  exact body recovered through PrivateWitnessOccurrenceAssociation
}
~~~

An instance supplies one and only one canonical same-domain value for every
public occurrence and no extra occurrence. Private values never enter
`RelationInstanceId`.

A private witness supplies one live secret capability for every witness
occurrence. The authorized holder first constructs a body that contains no
occurrence coordinate, independently allocates a fresh collision-free
`UnlinkableLocalRef`, and atomically retains the single-valued association for
that reference.

The combined assignment is valid only when lookup of that reference recovers
the exact supplied body. It is nonserializable and local to its unlinkable
occurrence. It is not authenticated as a public semantic artifact, and no
Interface, instance, binding, artifact, or correspondence admission may
inspect it. Its body's `instance_id` and `interface_id` must name the exact
dependent instance and Interface for that occurrence, and its secret map is
total, extra-key-free, and domain-correct. Those local shape conditions still
establish neither witness validity nor satisfaction.

Failed allocation or association exposes no valid `PrivateWitnessAssignment`
or reusable occurrence reference.

### 4.2 Instance lifecycle

~~~text
AuthenticateRelationInstance(
  raw candidate,
  exact capability-neutral RelationInterface identity-and-domain view derived
    from an ExactAdmittedSubjectAuthorityBinding<Relations,
      RelationInterface>)
  -> AuthenticatedRelationInstanceCandidate

AdmitRelationInstance(
  AuthenticatedRelationInstanceCandidate,
  exact admitted RelationInterface subject value,
  exact ExactAdmittedSubjectAuthorityBinding<Relations, RelationInterface>,
  separately supplied fresh AdmittedRelationInterface capability,
  ExactRelationInstanceLawCheckerCapabilities)
  -> (exact ExactAdmittedSubjectAuthorityBinding<Relations, RelationInstance>,
      fresh AdmittedRelationInstance)
~~~

Authentication recomputes the exact occurrence-total public map and instance
identity. Admission rechecks canonical values and domains against the exact
admitted Interface. The authentication view is inert and grants no Interface
authority or policy permission; only the later admission consumes the complete
binding and separately fresh capability. Neither step requires or implies a
witness.

Before successful instance admission, Relations matches the exact Interface
binding to the separately supplied fresh Interface capability, reauthenticates
its capability contract and ABI, freshly validates its complete owner-policy
disposition for the named relation-instance-admission purpose, and constructs
the canonical total transitive source-operation-policy closure. The returned
instance binding uses
`RelationsAdmissionCapabilityContractId<RelationInstance>`, retains the full
source closure and every source `OwnerCapabilityRequirement`, includes its own
instance `OwnerCapabilityRequirement`, and is retained identically by the fresh
`AdmittedRelationInstance` capability. Interface authority is not
transferred into the instance capability.

## 5. Relation authoring ingress

Relation source languages cross one explicit unauthoritative normalization
boundary. This boundary is separate from backend artifact interpretation.

~~~text
NormalizeRelationAuthoring(
  RelationAuthoringUnit,
  ExactResolvedRelationReadClosureSnapshot,
  RelationAuthoringNormalizerContract,
  RelationSemanticRegimeSet)
  -> RelationAuthoringNormalizationAttemptOutcome

RelationAuthoringNormalizationAttemptOutcome =
    CandidateBundleProduced(
      CanonicalRelationCandidateBundle,
      NormalizationAudit<RelationAuthoring>)
  | Unsupported(exact unsupported authoring construct or regime)
  | CannotAnswer(exact unresolved or incomplete read)
  | Refused(exact prohibited or unclassified erasure)
  | Malformed(exact syntax, typing, resolution, or framing defect)
  | NormalizerFailure(exact operational failure; no semantic conclusion)

CanonicalRelationCandidateBundle = {
  interface: RelationInterfaceCandidate,
  instances: CanonicalSeq<RelationInstanceCandidate>,
  bindings: CanonicalSeq<RelationBindingCandidate>
}
~~~

The normalizer contract fixes a finite authoring language and syntax quotient,
the complete resolution and pre-erasure checks, the mapping into the canonical
relation algebra, supported regimes, and immutable dependencies. The resolved
read snapshot is complete and content-addressed. Ambient imports, registries,
environment lookups, clocks, and caller policy are forbidden.

The audit classifies every source distinction as retained in a candidate,
extracted to a typed nonsemantic output, proved neutral under the declared
finite quotient, or rejected before erasure. Unknown syntax, unresolved reads,
unsupported roles, and unclassified information loss refuse normalization.

Only `CandidateBundleProduced` emits candidates and an audit. This is an
operational producer outcome, not `Qualified`, a checked semantic result, or
evidence for any proposition. It creates no checked-result binding and mints
no capability. It authenticates and admits nothing. Each candidate follows its
ordinary owner lifecycle. A directly constructed canonical candidate remains
legal but carries no
source-language, provenance, resolution, or preservation claim. An artifact
observation cannot substitute for normalization because it records selected
facts about backend bytes, not authoring-unit semantics.

## 6. Protocol-to-relation binding

### 6.1 Binding algebra

~~~text
ProtocolPublicBindingTarget =
  ProtocolPublicAssignmentOccurrence(
    ProtocolPublicStatementOccurrenceRef)

ProtocolWitnessBindingTarget =
    ProtocolPrivatePortValue(PortOccurrenceRef)
  | ProtocolProverObligationOutput(
      ProverObligationRef,
      output_ordinal)

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
  TotalMap<RelationCommittedObjectRef,
           CommittedObjectGroundingEntry>

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
~~~

Every `CanonicalAlgorithmSpec` is either a closed finite typed total term or a
regime-qualified content-addressed contract reference retaining the exact ABI
and direct dependency IDs. Live code, callbacks, registries, or checker
process identities never enter a binding preimage.

### 6.2 Value-bridge laws

Every value bridge is a total canonical bijection between independently owned
relation and Protocol domains:

~~~text
to_relation(to_protocol(r)) = r
to_protocol(to_relation(p)) = p
~~~

The two algorithm ABIs name the exact source and target domain contracts. An
identity bridge is legal only when the regime-qualified domain contract is
literally shared. Byte equality, equal cardinality, or a mnemonic cannot
establish cross-domain equality.

The public map is total over relation public occurrences and injective in its
targets. A target is exactly one public input `Statement` occurrence appearing
once in the dependent Interface's canonical public-assignment domain. A
challenge, terminal output, merely public observation, prover-produced value,
or post-statement computation is not a legal public target.

The witness map is total over relation witness occurrences and injective in
its targets. A target is exactly one private Prover input occurrence or one
output ordinal of a named prover obligation. Each bridge domain equals its
source relation-port and target Protocol domain.

Neither image must exhaust the Protocol's statement, private-input, or
prover-obligation surface. Image equality belongs to the requested
`PublicPorts` or `WitnessPorts` correspondence clause, so a well-formed binding
proposal can later produce a meaningful negative correspondence result.

### 6.3 Committed-object and result-binding form

The committed-object map is total over relation object occurrences. Each
identity-bearing entry fixes:

- one exact Protocol object;
- three separate regime-qualified algorithm specs and ABIs for semantic-object
  derivation, commitment-value derivation, and canonical material encoding;
- zero or one occurrence-exact proof/application Interface-position chain;
  and
- either no artifact read or one exact adapter and typed fact selector.

A proof position must resolve through `GuardedProofTraceBinding` to the named
proof-message event and exact object input ordinal. An application position
must resolve through the named `ApplicationBinding` to the exact event and
input ordinal. Labels, ordinal coincidence, and untyped event links are
insufficient.

`NoArtifactDependency` prohibits artifact reads for that object occurrence.
`FromArtifactFact` selects only the named adapter/profile and typed fact. The
binding stores no observation or byte ID; a grounding invocation must supply
the one exact admitted observation that answers that entry. There is no global
unassigned adapter, observation, byte, or fact pool.

`ClaimPresence` names one in-range produced claim. `CheckTrue` names one
in-range invoked Boolean check. `AcceptingTerminals` is nonempty,
duplicate-free, in range, and contains only terminals whose static result is
`Accept`. These are reference-shape facts. They do not compare the relation
result role's output domain or accepted values with Protocol acceptance.

### 6.4 Binding identity and lifecycle

~~~text
RelationBindingId = H(
  "zkc/relation-binding",
  RelationBindingRegimeId,
  ProtocolInterfaceId,
  RelationInterfaceId,
  CanonicalEncode(RelationBinding))

ExactRelationBindingAlgorithmDependencyBundle =
  ExactMap<TypedRelationBindingAlgorithmDependencyRef,
           AuthenticatedRelationBindingAlgorithmDependencyPreimage>

ExactRelationBindingDependencyAuthenticationCapabilities =
  ExactMap<TypedRelationBindingAlgorithmDependencyRef,
           RelationBindingDependencyAuthenticationCapability restricted to
           the exact kind, contract regime, content ID, ABI, and direct
           dependency IDs>

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
  exact admitted Protocol binding-view, ProtocolInterface, and
    RelationInterface subject values,
  retained exact binding-algorithm dependency views,
  exact admitted adapter-view values required by FromArtifactFact,
  exact ExactAdmittedSubjectAuthorityBinding for every authority-bearing admitted
    operand, retained dependency view, and admitted adapter view, with
    separately supplied fresh capabilities,
  ExactRelationBindingLawCheckerCapabilities)
  -> (exact ExactAdmittedSubjectAuthorityBinding<Relations, RelationBinding>,
      fresh AdmittedRelationBinding)
~~~

The dependency bundle contains every and only preimage in the least closure of
all bridge and grounding algorithm specs. Authentication checks the exact
kind/regime/ID/ABI/direct-edge closure and binding identity and retains
attenuated immutable views.

Admission checks occurrence totality, target injectivity, exact domain and ABI
equations, both value-bridge round trips, Protocol and Interface reference
shape, the complete object-position chain, per-object artifact selectors, and
the closed result-binding constructors. It consumes a matching admitted
adapter view for every and only `FromArtifactFact` entry. It retains no
transitive Protocol, Interface, adapter, or checker authority.

Before successful admission, Relations matches every source binding to its
separately supplied fresh capability, reauthenticates the exact owner
capability contract and ABI, and freshly validates every bound policy or
explicit no-policy disposition for the named relation-binding-admission
purpose. It constructs the canonical total transitive source-operation-policy
closure over all admitted operands and authority-bearing retained views.
Successful admission constructs the exact
`ExactAdmittedSubjectAuthorityBinding<Relations, RelationBinding>` under
`RelationsAdmissionCapabilityContractId<RelationBinding>`; that binding and
the `AdmittedRelationBinding` capability retain the complete source closure,
every source `OwnerCapabilityRequirement`, and the relation-binding family's
own `OwnerCapabilityRequirement`, but no transitive live authority.

Binding admission establishes a well-formed proposal and dependency closure.
It establishes neither public/witness image agreement, artifact agreement,
committed-object grounding, bridge or derivation faithfulness beyond the
checked ABI/round-trip laws, nor result behavioral equivalence.

## 7. Artifact subjects and expectation-free interpretation

### 7.1 Profile and adapter

~~~text
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

TypedRelationArtifactProfileDependencyRef =
  exact profile dependency reference retaining kind, contract regime,
  content ID, exact ABI, and direct dependency IDs

TypedRelationAdapterDependencyRef =
  exact byte-language or deterministic-interpreter dependency reference
  retaining kind, contract regime, content ID, exact ABI, and direct
  dependency IDs

ExactRelationArtifactProfileDependencyBundle =
  ExactMap<TypedRelationArtifactProfileDependencyRef,
           AuthenticatedRelationArtifactProfileDependencyPreimage>

ExactRelationArtifactProfileDependencyAuthenticationCapabilities =
  ExactMap<TypedRelationArtifactProfileDependencyRef,
           RelationArtifactProfileDependencyAuthenticationCapability
             restricted to the exact kind, contract regime, content ID,
             ABI, and direct dependency IDs>

ExactRelationAdapterDependencyBundle =
  ExactMap<TypedRelationAdapterDependencyRef,
           AuthenticatedRelationAdapterDependencyPreimage>

ExactRelationAdapterDependencyAuthenticationCapabilities =
  ExactMap<TypedRelationAdapterDependencyRef,
           RelationAdapterDependencyAuthenticationCapability restricted to
           the exact kind, contract regime, content ID, ABI, and direct
           dependency IDs>

RelationArtifactProfileId = H(
  "zkc/relation-artifact-profile",
  RelationArtifactProfileRegimeId,
  CanonicalEncode(RelationArtifactProfile))

RelationAdapterId = H(
  "zkc/relation-adapter",
  RelationAdapterRegimeId,
  RelationArtifactProfileId,
  CanonicalEncode(RelationAdapterContract))
~~~

The profile defines bytes, facts, malformed reasons, and limits without
loading a relation or Protocol. The adapter is profile-dependent and owns one
deterministic total tagged interpretation contract. Its closed schemas prevent
ambient facts, unread fields, or outcome variants.

Profile and adapter authentication consume exact typed least-closure bundles:

~~~text
AuthenticateRelationArtifactProfile(
  raw candidate,
  ExactRelationArtifactProfileDependencyBundle,
  ExactRelationArtifactProfileDependencyAuthenticationCapabilities)
  -> AuthenticatedRelationArtifactProfileCandidate

AdmitRelationArtifactProfile(
  AuthenticatedRelationArtifactProfileCandidate,
  retained exact profile dependency views,
  exact ExactAdmittedSubjectAuthorityBinding for every authority-bearing
    retained profile dependency view, with separately supplied fresh
    capabilities,
  ExactRelationArtifactProfileLawCheckerCapabilities)
  -> (exact ExactAdmittedSubjectAuthorityBinding<Relations,
        RelationArtifactProfile>,
      fresh AdmittedRelationArtifactProfile)

AuthenticateRelationAdapter(
  raw candidate,
  exact capability-neutral RelationArtifactProfile identity view derived from
    an ExactAdmittedSubjectAuthorityBinding<Relations,
      RelationArtifactProfile>,
  ExactRelationAdapterDependencyBundle,
  ExactRelationAdapterDependencyAuthenticationCapabilities)
  -> AuthenticatedRelationAdapterCandidate

AdmitRelationAdapter(
  AuthenticatedRelationAdapterCandidate,
  exact admitted RelationArtifactProfile subject value,
  exact ExactAdmittedSubjectAuthorityBinding<Relations,
    RelationArtifactProfile>,
  separately supplied fresh AdmittedRelationArtifactProfile capability,
  retained exact adapter dependency views,
  exact ExactAdmittedSubjectAuthorityBinding for every authority-bearing
    retained adapter dependency view, with separately supplied fresh
    capabilities,
  ExactRelationAdapterInterpreterAndLawCheckerCapabilities)
  -> (exact ExactAdmittedSubjectAuthorityBinding<Relations,
        RelationAdapterContract>,
      fresh AdmittedRelationAdapter)
~~~

The typed dependency references retain kind, contract regime, content ID,
exact ABI, and direct dependency IDs. Each authentication-capability map has
exactly the same key set as its preimage bundle, and each bundle equals the
exact least reachable closure. Profile admission checks byte-language
identity, schemas, limits, and no relation/Protocol reads. Adapter admission
checks deterministic total tagged interpretation, schema and limit closure,
refusal closure, and absence of ambient reads. Executable authority is not
identity content.

The capability-neutral profile view used by adapter authentication carries
only exact identity coordinates extracted from the source binding. It grants no
profile authority or policy permission; adapter admission separately consumes
the complete binding and fresh profile capability.

Before either successful admission, Relations matches every exact source
binding to its separately supplied fresh capability, reauthenticates each
owner capability contract and ABI, and freshly validates every bound policy or
explicit no-policy disposition for the exact profile- or adapter-admission
purpose. Profile admission constructs the canonical total transitive source-
operation-policy closure over its authority-bearing dependency views. Adapter
admission constructs it over the exact admitted profile and every authority-
bearing adapter dependency view. No source may be omitted or added.

The returned bindings use
`RelationsAdmissionCapabilityContractId<RelationArtifactProfile>` and
`RelationsAdmissionCapabilityContractId<RelationAdapterContract>` respectively,
retain their complete source closures and every source
`OwnerCapabilityRequirement`, include their own family-specific
`OwnerCapabilityRequirement`, and declare the admission families' explicit no-
separate-operation-policy dispositions. Each separately minted fresh admitted
capability retains its exact returned binding and no transitive live authority.

### 7.2 Exact bytes and observation-candidate production

~~~text
RelationArtifactByteId = H(
  "zkc/relation-artifact-bytes",
  RelationArtifactProfileId,
  CanonicalEncode(ExactRawBytes))

InterpretRelationArtifact(
  ExactRawBytes,
  exact admitted RelationArtifactProfile and RelationAdapterContract subject
    values,
  exact ExactAdmittedSubjectAuthorityBinding<Relations,
    RelationArtifactProfile> and
    ExactAdmittedSubjectAuthorityBinding<Relations, RelationAdapterContract>,
  separately supplied fresh profile- and adapter-admission capabilities,
  ExactRelationAdapterInterpreterExecutionCapabilities)
  -> RelationArtifactInterpretationAttemptOutcome

RelationArtifactInterpretationAttemptOutcome =
    ObservationCandidateProduced(RelationArtifactObservationCandidate)
  | Unsupported(exact unsupported byte-language or adapter construct)
  | Refused(exact prohibited interpretation)
  | Malformed(exact byte, schema, limit, or framing defect)
  | InterpreterFailure(exact operational failure; no semantic conclusion)

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
~~~

`RelationArtifactByteId` is recomputed only from captured exact raw bytes that
inhabit the admitted profile's byte-identity domain. The resulting immutable
byte material is an interpretation input, not an admitted relation subject,
adapter authority, acquisition/provenance claim, or relation conclusion.

Interpretation is expectation-free. It reads no expected relation Interface,
Protocol, binding, or correspondence answer. Only
`ObservationCandidateProduced` forms an unauthenticated observation candidate.
This operational tag is not a qualified semantic polarity, creates no checked-
result binding, and mints no observation or checker capability. `Malformed`,
`Unsupported`, `Refused`, and `InterpreterFailure` form no observation and no
observation identity. There is no negative interpretation outcome because no
expected fact is being compared.

Before candidate production, the interpreter matches both exact admitted-
subject bindings to their separately supplied fresh capabilities,
reauthenticates both capability contracts and ABIs, and freshly validates every
bound policy or explicit no-policy disposition in their transitive closures for
the exact relation-artifact-observation-candidate-production purpose. A
prohibition or mismatch is `Refused` or `Malformed`, never a candidate. The
operational attempt may retain its capability-neutral policy-check audit, but
that audit does not enter observation content or identity and grants no later
admission authority.

The observation candidate and semantic subject have the same closed content.
Lifecycle authority changes through authentication and admission, never by
adding fields:

~~~text
AuthenticateRelationArtifactObservation(
  raw observation candidate,
  ExactRawBytes,
  exact capability-neutral profile and adapter identity views derived from
    ExactAdmittedSubjectAuthorityBinding<Relations, RelationArtifactProfile>
    and ExactAdmittedSubjectAuthorityBinding<Relations,
      RelationAdapterContract>)
  -> AuthenticatedRelationArtifactObservationCandidate

AdmitRelationArtifactObservation(
  AuthenticatedRelationArtifactObservationCandidate,
  ExactRawBytes,
  exact admitted RelationArtifactProfile and RelationAdapterContract subject
    values,
  exact ExactAdmittedSubjectAuthorityBinding<Relations,
    RelationArtifactProfile> and
    ExactAdmittedSubjectAuthorityBinding<Relations, RelationAdapterContract>,
  separately supplied fresh profile- and adapter-admission capabilities,
  ExactRelationAdapterInterpreterExecutionCapabilities)
  -> (exact ExactAdmittedSubjectAuthorityBinding<Relations,
        RelationArtifactObservation>,
      fresh AdmittedRelationArtifactObservation)
~~~

Authentication checks exact byte/profile/adapter scope, fact and unread-field
schemas, and identity. Its derived views are inert and grant no profile or
adapter authority or policy permission. Admission separately consumes the
complete source bindings and fresh capabilities, then reruns the exact interpreter with matching
execution authority and requires byte-for-byte and fact-for-fact equality.
A transport checksum protects delivery only; it enters no relation identity.

Before successful observation admission, Relations matches the exact profile
and adapter bindings to their separately supplied fresh admission capabilities,
reauthenticates both capability contracts and ABIs, freshly validates both
complete owner-policy dispositions for the named relation-artifact-observation-
admission purpose, and constructs the canonical total transitive source-
operation-policy closure. The returned observation binding uses
`RelationsAdmissionCapabilityContractId<RelationArtifactObservation>`, retains
that source closure and every source `OwnerCapabilityRequirement`, including
both direct values, includes its own observation `OwnerCapabilityRequirement`,
and declares the admission family's explicit no-separate-operation-policy
disposition. The
fresh `AdmittedRelationArtifactObservation` capability retains the identical
binding; neither interpreter execution authority nor profile/adapter authority
is transferred.

## 8. Artifact/interface comparison

Comparison is distinct from interpretation:

~~~text
RelationsPublicCheckedResultFamily =
    ArtifactInterfaceComparison
  | CommittedObjectGrounding
  | StructuralCorrespondence
  | InstanceCorrespondence

LocalRelationsCheckingAttemptInputHandle =
  fresh owner-issued process-local nonserializable opaque input-material handle

LocalRelationsCheckingAttemptRecordHandle<R> =
  fresh collision-free owner-local nonserializable record handle

RelationsCheckingAttemptSlotStatus =
    Authenticated(exact capability-neutral typed value, binding, contract,
                  policy, regime, or reference required by that slot)
  | OfferedCandidate(exact capability-neutral typed candidate and any claimed
                     reference or binding)
  | Missing
  | OpaqueMalformed(exact normalized defect class,
                    exact LocalRelationsCheckingAttemptInputHandle)

RelationsCheckingAttemptInput<R> {
  exact owner-selected entry point and
    R: RelationsPublicCheckedResultFamily,
  exact statically declared operand-slot schema for that entry point,
  exactly one RelationsCheckingAttemptSlotStatus for every and only declared
    input slot,
  exact slot-to-operation association,
  no result, live capability, or claim that a checking occurrence happened
}

PrepareRelationsCheckedOperation<R>(
  exact RelationsCheckingAttemptInput<R>,
  occurrence-local capability and execution-authority offers for the declared
    slots, which may be absent, stale, nonmatching, malformed, or prohibited
    and are never retained)
  ->
    Ready(exact typed complete operand tuple for the selected family signature)
  | Rejected(exact RelationsCheckingAttemptDisposition, failed requirement,
             and reached policy/contract checks)

RelationsCheckingAttemptDisposition =
    Unsupported(exact unsupported construct or question)
  | CannotAnswer(exact missing named semantic input or basis)
  | Refused(exact missing authority or prohibited invocation)
  | Malformed(exact framing or structural defect)
  | CheckerFailure(exact normalized operational-failure class)

RelationsCheckingAttemptRecord<R> {
  exact RelationsCheckingAttemptInput<R>,
  exact capability-neutral complete operand projection when preparation reached
    Ready, or exact rejected slot and preparation state otherwise,
  exact reached NamedConsumer, RelationsOperationPurpose<R>,
    CorrespondenceRegime, capability contract, ABI, source-policy closure, and
    residual trust, or exact unavailable governing slot and dependency path,
  exact successful and failed attempt-audit creation/disclosure checks that
    were reached,
  exact RelationsCheckingAttemptDisposition,
  no checked-result binding or live capability
}

RelationsCheckingAttemptRecordRef<R> =
    Portable(exact RelationsCheckingAttemptRecord<R>,
             exact Id(exact RelationsCheckingAttemptRecord<R>))
  | OwnerLocal(exact RelationsCheckingAttemptRecord<R>,
               exact LocalRelationsCheckingAttemptRecordHandle<R>)

RelationsCheckingAttemptOutcome<R> =
    Completed(exact owner-defined affirmative or negative result,
              exact ExactCheckedResultAuthorityBinding<Relations,R>,
              fresh process-local checked R capability bound to both)
  | Unsupported(exact RelationsCheckingAttemptRecordRef<R>)
  | CannotAnswer(exact RelationsCheckingAttemptRecordRef<R>)
  | Refused(exact RelationsCheckingAttemptRecordRef<R>)
  | Malformed(exact RelationsCheckingAttemptRecordRef<R>)
  | CheckerFailure(exact RelationsCheckingAttemptRecordRef<R>)

AttemptRelationsCheckedOperation<R>(
  exact RelationsCheckingAttemptInput<R>,
  occurrence-local capability and execution-authority offers)
  -> RelationsCheckingAttemptOutcome<R>

ArtifactComparisonQuestion =
  NonEmptyCanonicalSet<RelationInterfaceFieldRef>

RelationArtifactAgreesWithInterface(
  exact admitted RelationArtifactObservation and RelationInterface subject
    values,
  ArtifactComparisonQuestion,
  exact ExactAdmittedSubjectAuthorityBinding for both admitted operands with
    separately supplied fresh capabilities,
  exact named_consumer: NamedConsumer,
  exact operation_purpose:
    RelationsOperationPurpose<ArtifactInterfaceComparison>,
  CorrespondenceRegime)
  -> Qualified<CheckedArtifactInterfaceComparison,
               exact ExactCheckedResultAuthorityBinding<Relations,
                 ArtifactInterfaceComparison>>
~~~

This family-indexed capability-neutral ingress is shared by artifact comparison,
committed-object grounding, structural correspondence, and instance
correspondence. Each displayed exact signature in this document and
[Protocol correspondence](protocol-correspondence.md) is its `Ready` operand
tuple and completed A/N shorthand. A missing or malformed operand, consumer,
purpose, regime, contract, ABI, source policy, or fresh authority remains
representable in the outer carrier and returns an exact U/C/R/M/F attempt
record rather than requiring a complete call. A record is `Portable` only when
its complete canonical preimage is portable and the authenticated
`RelationsCorrespondenceCapabilityContract` audit rule plus every reached
applicable source-owner policy expressly permits audit creation, stable
equality linkage, and disclosure for the exact result family, named consumer,
and `RelationsOperationPurpose<R>`. If consumer, purpose, contract, any
governing policy/disposition, or its permission check is unavailable, the
record defaults to `OwnerLocal`; `OpaqueMalformed` also forces that lane. A
policy-prohibited semantic invocation does not itself authorize a portable
record of the rejection. The carrier, record, and local input handle are
capability-neutral, establish no checking/history occurrence, and can never
substitute for a completed checked-result binding or capability.

The checker reads every and only requested Interface field and the exact
observation facts/unread declarations that can answer it. A completed
affirmative result records agreement for every requested field. A completed
negative records every exact conflict and preserves unaffected agreements.
`CannotAnswer` means a requested fact was not emitted. Interpretation failure,
missing authority, malformed input, unsupportedness, and checker failure are
not disagreement.

Before completion, the checker matches both source bindings to their fresh
capabilities, freshly validates every bound policy or explicit no-policy
contract for the named comparison purpose, and constructs the canonical total
transitive source-policy closure. The completed result binding retains that
closure, both exact `OwnerCapabilityRequirement` values, the exact named
consumer, and the exact
`RelationsOperationPurpose<ArtifactInterfaceComparison>`.

Only completed A/N mints `CheckedArtifactInterfaceComparison`. The opaque
capability retains the exact admitted observation and Interface, nonempty
question, `CorrespondenceRegime`, checker identity, dependency/read closure,
field-factored result, qualified residual-trust basis, and the exact source
binding created with the result. The binding retains the authenticated
`OwnerDefinesNoOperationPolicy(RelationsCorrespondenceCapabilityContractId,
RelationsCorrespondenceCapabilityAbiId)` disposition and its exact
`OwnerCapabilityRequirement`; omission is not a no-policy declaration. It cannot be
widened to another observation, Interface, profile, adapter, regime, or field
set. A serialized observation or comparison record carries no live authority.

## 9. Committed-object grounding check

### 9.1 Signature and conditional reads

~~~text
ConditionalArtifactObservationMap =
  CanonicalMap<RelationCommittedObjectRef,
               RelationArtifactObservation>

GroundCommittedObjects(
  admitted Protocol object-declaration view,
  admitted ProtocolInterface,
  admitted RelationInterface,
  admitted RelationBinding,
  exact admitted grounding-algorithm dependency views attenuated from the
    binding,
  ExactGroundingAlgorithmExecutionCapabilities,
  ConditionalArtifactObservationMap,
  exact ExactAdmittedSubjectAuthorityBinding for every authority-bearing admitted
    operand, attenuated dependency view, and conditional observation, with
    separately supplied fresh capabilities,
  exact named_consumer: NamedConsumer,
  exact operation_purpose:
    RelationsOperationPurpose<CommittedObjectGrounding>,
  CorrespondenceRegime)
  -> Qualified<CheckedCommittedObjectGrounding,
               exact ExactCheckedResultAuthorityBinding<Relations,
                 CommittedObjectGrounding>>
~~~

The conditional map has one entry for every and only grounding entry whose
artifact dependency is `FromArtifactFact`. The observation must retain the
identical adapter/profile, exact raw-byte identity, and selected typed fact. A
missing or mismatched required observation is `CannotAnswer`. Supplying an
observation for `NoArtifactDependency` is an undeclared read and is refused.

The checker executes only the binding-owned equations under exact retained
algorithm views and identity-matched execution capabilities. It cannot choose
a codec, adapter, fact, Interface position, or algorithm at invocation time.
It first matches every exact source binding to the separately supplied fresh
capability, freshly validates every bound policy or explicit no-policy contract
for the named grounding purpose, and constructs the canonical total transitive
source-policy closure retained by the result binding.

### 9.2 Result

An affirmative result binds every `RelationCommittedObjectRef` to the exact:

- Protocol `CoreRef<object>`;
- semantic object domain;
- commitment-value derivation;
- canonical material encoding;
- optional proof/application Interface position; and
- assigned artifact derivation when declared.

Protocol objects outside the map need not be covered. Several relation object
occurrences may name one Protocol object when their independently checked
domains and derivations agree. No inverse injectivity is inferred.

A negative result names every conflicting equation and retains unaffected
agreements. Only completed A/N mints `CheckedCommittedObjectGrounding`. The
capability retains all admitted operands, binding-attenuated dependency views,
the exact conditional observation map, regime, checker identity, read closure,
field-factored result, and qualified residual-trust basis. It proves no
mathematical faithfulness beyond the checked contract equations, opening
knowledge, or satisfaction.

The exact source binding created with the result retains the authenticated
`OwnerDefinesNoOperationPolicy(RelationsCorrespondenceCapabilityContractId,
RelationsCorrespondenceCapabilityAbiId)` disposition, complete source-policy
closure, and exact `OwnerCapabilityRequirement`, together with the exact named
consumer and `RelationsOperationPurpose<CommittedObjectGrounding>`. The fresh
capability retains those identical coordinates. The binding uses the portable
or owner-local result coordinate selected by the common rule in Section 2.1.

It records the identities and ABIs of the invoked execution basis but retains
no live algorithm-execution capability.

## 10. Qualified outcomes and capabilities

Owner boundaries use distinct semantic outcomes where applicable:

~~~text
Affirmative
Negative(reason, retained_facts)
Unsupported(exact unsupported construct or question)
CannotAnswer(missing named semantic input or basis)
Refused(missing authority or prohibited invocation)
Malformed(exact framing or structural defect)
CheckerFailure(operational failure with no semantic conclusion)
~~~

`CandidateBundleProduced` and `ObservationCandidateProduced` are operational
producer tags outside this semantic A/N algebra. `NormalizerFailure` and
`InterpreterFailure` are their operation-scoped failure tags; neither is a
semantic negative or a checked result.

| Boundary | Accepted or produced branch | Other outcomes |
|---|---|---|
| Subject authentication | A/N under the exact physical/dependency predicate; A yields only the named authenticated candidate with retained attenuated views | U/R/M/F yield none; these direct subject-formation predicates do not emit C |
| Subject admission | A/N under the exact owner-domain predicate; A atomically yields the exact admitted-subject binding plus separately minted fresh named capability | U/R/M/F yield neither binding nor capability; these direct subject-formation predicates do not emit C |
| Profile-scoped exact-byte identity | A/N for exact raw-byte/profile identity formation; A yields exact immutable byte material, not an admitted semantic capability | U/R/M/F yield none and no relation conclusion; no expected Interface exists from which to derive C or N about correspondence |
| Authoring normalization | `CandidateBundleProduced` yields only an unauthenticated candidate bundle and capability-neutral audit; it is not a qualified semantic result and mints no capability | Unsupported or unclassified input, unresolved reads, refusal, malformed input, and operational failure yield no candidate bundle or admitted subject |
| Artifact interpretation | `ObservationCandidateProduced` yields only an unauthenticated observation candidate followed by independent authentication/admission; it creates no checked-result binding or capability | M/U/R/F yield no observation candidate; interpretation has no N and no expectation-derived C |
| Artifact/interface comparison | A or N yields exact `CheckedArtifactInterfaceComparison` plus its inert exact source binding with field facts | U/C/R/M/F yield neither binding nor checked capability |
| Committed-object grounding | A or N yields exact `CheckedCommittedObjectGrounding` plus its inert exact source binding with field facts | U/C/R/M/F yield neither binding nor checked capability |
| Relation satisfaction | `Completed` A or N yields exact occurrence-local `CheckedRelationSatisfaction` under the exact model, semantic basis, support instantiation, validation basis, policy, and total request-realization ledger | U/C/R/M/F yield no checked capability; missing or mismatched support/checker authority or incomplete request/limit realization is never negative satisfaction |

Absence of support, input, or authority never becomes negative semantic truth.
Only an affirmative capability can satisfy an affirmative-only consumer. A
negative capability may be consumed only by an owner that explicitly asks for
the exact retained refutation facts.

## 11. Persistence and replay

Official semantic-subject persistence is admission-gated. Inert support and
attempt records remain capability-neutral and separately policy-gated.
Workbench caches, normalization packages, raw artifacts, result bytes, and
provenance records remain unauthoritative.

For relation satisfaction, creating, retaining, disclosing, looking up, or
replaying any support or attempt record requires the conjunction of the exact
`RelationSatisfactionOperationPolicy` and a freshly authenticated disposition
for every source in its transitive closure. Every `BoundTo` policy must permit
the named consumer and purpose; every `OwnerDefinesNoOperationPolicy` entry must
be backed by its exact admitted owner capability-contract and ABI preimage. The
retained material must include exact owner-authorized reconstruction material
or explicit external owner replay prerequisites for every decisive premise and
correspondence input. If any owner forbids the operation or required material
cannot be retained, no corresponding record or replay claim is created.

| Subject or result | Cold replay requirement |
|---|---|
| `RelationDefinitionRef` | Reconstruct the exact external owner-regime reference through that owner's rules or rerun the explicitly selected admitted definition-language adapter; zkc cannot synthesize its identity or truth |
| `RelationSemanticModel` | Reauthenticate its exact definition-family schema, value interpretation, evaluation/refutation meaning, assumption schemas, semantic dependency/read closure, and ID; reconstruct every dependency and rerun model admission |
| Satisfaction basis registry, validation profile, and operation policy | Reauthenticate each exact closed regime, content, dependency closure, and ID; rerun its separate admission and obtain fresh local authority |
| Satisfaction semantic/validation basis, support instantiation, and request | In the portable lane, reconstruct the exact admitted-subject bindings for the model, instance, registry, validation profile, and operation policy; semantic basis/read closure; stable checker implementation and contract-correspondence identities; every complete portable checked-result source binding and `OwnerCapabilityRequirement`; total disposition realization; every bound operation-policy preimage or explicit no-policy owner capability-contract/ABI preimage with fresh owner validation; public question; request; and total request/limit realization. A local-source lane cannot cold-replay these values and instead performs an authorized confidential rerun with fresh affected handles. Either path supplies fresh capabilities separately and obtains fresh checker-execution authority for a new invocation; no inert binding or record carries premise, checker, witness, or live-result authority. |
| `RelationInterface` | Reconstruct its exact external definition reference, dependency preimages, complete source bindings and policies, and matching fresh capabilities; reauthenticate the least closure and ID; rerun admission; recreate the exact portable admitted-subject binding; require full binding equality; and mint fresh Interface authority. An owner-local source branch requires a new local binding and is not exact cold replay. |
| `RelationInstance` | Reconstruct the exact Interface binding and separately fresh Interface authority, reauthenticate the occurrence-total public map and ID, rerun instance admission, recreate the exact portable instance binding, require full binding equality, and mint fresh instance authority; an owner-local source branch instead creates a new local binding. |
| `RelationArtifactProfile` | Reauthenticate the exact byte-language dependency closure, complete source bindings/policies, ID, schemas, and limits; rerun admission; recreate the exact portable profile binding; require full equality; and mint fresh profile authority. An owner-local source branch creates a new local binding. |
| `RelationAdapterContract` | Reconstruct the exact profile binding and separately fresh profile authority, reauthenticate the interpreter dependency closure and every source binding/policy, rerun deterministic interpreter/law admission, recreate the exact portable adapter binding, require full equality, and mint fresh adapter authority; an owner-local source branch creates a new local binding. |
| Exact relation artifact bytes | Re-admit the exact profile, resupply the captured exact raw-byte preimage, and recompute `RelationArtifactByteId`; a caller digest, transport checksum, or provenance record is insufficient |
| `RelationBinding` | Reconstruct every exact source binding and separately fresh capability for the Protocol view, Protocol Interface, relation Interface, dependency views, and every and only conditionally selected adapter; reauthenticate the complete bridge/grounding closure and ID; rerun all laws; recreate the exact portable relation-binding authority binding; require full equality; and mint fresh authority. An owner-local source branch creates a new local binding. |
| `RelationArtifactObservation` | Reconstruct the exact profile/adapter bindings and separately fresh capabilities, reauthenticate exact bytes and observation identity, reconstruct matching interpreter authority, rerun interpretation and admission, recreate the exact portable observation binding, require full binding and observation equality, and mint fresh observation authority; an owner-local source branch creates a new local binding. |
| Relation authoring normalization and audit | Reconstruct the exact authoring unit, immutable resolved read-closure snapshot, normalizer contract, and supported regime set, then rerun normalization; the recreated bundle and audit still admit nothing |
| `CheckedArtifactInterfaceComparison` | Recreate the exact admitted operands, question, regime, capability contract and ABI, named consumer, `RelationsOperationPurpose<ArtifactInterfaceComparison>`, dependency/read closure, and checker authority; reauthenticate the contract's distinct invocation, capability-use, completed-result-record, and replay permissions plus every disposition in the transitive source-policy closure for the identical use; rerun comparison, recreate the exact portable source binding and result record, and require full binding equality before minting fresh authority; an owner-local coordinate instead requires a new authorized local rerun and is not exact replay |
| `CheckedCommittedObjectGrounding` | Recreate every admitted operand, binding dependency view, execution capability, exact conditional observation map, regime, capability contract and ABI, named consumer, and `RelationsOperationPurpose<CommittedObjectGrounding>`; reauthenticate the contract's distinct invocation, capability-use, completed-result-record, and replay permissions plus every disposition in the transitive source-policy closure for the identical use; rerun grounding, recreate the exact portable source binding and result record, and require full binding equality before minting fresh authority; an owner-local coordinate has no exact cold replay |
| `PrivateWitnessAssignment` | Cannot be replayed from public bytes; a new local occurrence must obtain fresh secret capabilities, construct a new body, independently allocate a new `UnlinkableLocalRef`, and retain a new holder-local reference-to-body association |
| `RelationSatisfactionPremiseRecordRef` | Cannot be cold-replayed or restored by matching bytes; an authorized confidential rerun creates a new witness occurrence, premise-record body, independently allocated private reference and association, live result, and capability. Independently portable question, semantic-basis, validation-basis, support, and request IDs remain equal only when their own public preimages remain equal, while any local-source-derived policy closure, support, or request receives a fresh local handle. |
| `RelationSatisfactionAttemptRecord` | Reauthenticate its public question, every policy-disclosed request/support identity, model/profile/basis identities, every exact source policy disposition including any explicit no-policy owner contract/ABI, disclosed outcome, trust closure, and permitted facts; the record remains inert and cannot reconstruct premise support, checker execution, a private witness occurrence, or live satisfaction authority |
| `CheckedRelationSatisfaction` | Public replay is prohibited by default; an approved confidential rerun reconstructs every exact source binding and policy closure, separately obtains fresh admitted-operand, premise, correspondence-support, checker-execution, and witness capabilities, rechecks total request realization and operational-limit accounting, and reruns the semantic and validation rules. The new witness occurrence, private premise-record reference/association, live result, and capability are not exact replay of the prior local result. |

No replay step may recover authority from a matching ID, serialized capability,
signature, or earlier process result.

## 12. Relation satisfaction

### 12.1 Ownership and semantic model

Relations owns `RelationSatisfies`. Whether one exact public instance and one
occurrence-local private witness satisfy one exact externally defined predicate
is base relation semantics, not a Protocol property or an Analysis inference.
Analysis may consume the resulting qualified capability in completeness,
knowledge, or another exact question; it cannot define or widen satisfaction.

An opaque `RelationDefinitionRef` is not executable meaning. Satisfaction
therefore requires an independently authenticated and admitted semantic model:

~~~text
RelationSemanticModel = {
  exact RelationDefinitionRegimeId and supported definition-family schema,
  exact canonical-value and public/witness occurrence interpretation,
  exact predicate-evaluation and refutation meaning,
  exact assumption and side-condition schemas,
  complete typed semantic dependency and read closure
}

RelationSemanticModelId = H(
  "zkc/relation-semantic-model",
  RelationSemanticModelRegimeId,
  CanonicalEncode(RelationSemanticModel))

RelationSatisfactionBasisRegistry = {
  RelationSatisfactionBasisRegistryRegimeId,
  exact direct-evaluation, proof, certificate, and correspondence contracts,
  exact premise, assumption, side-condition, and refutation rule schemas,
  exact semantic-basis extension boundary
}

RelationSatisfactionBasisRegistryId = H(
  "zkc/relation-satisfaction-basis-registry",
  RelationSatisfactionBasisRegistryRegimeId,
  CanonicalEncode(RelationSatisfactionBasisRegistry))

RelationSatisfactionValidationProfile = {
  RelationSatisfactionValidationProfileRegimeId,
  exact checker, decoder, translation, proof-rule, and authentication contracts,
  exact validation trust-root policy
}

RelationSatisfactionValidationProfileId = H(
  "zkc/relation-satisfaction-validation-profile",
  RelationSatisfactionValidationProfileRegimeId,
  CanonicalEncode(RelationSatisfactionValidationProfile))

RelationSatisfactionCapabilityAbi = {
  exact covered result family: RelationSatisfaction,
  exact successful CheckRelationSatisfaction operand schema, including the
    owner-private witness occurrence/reference boundary but no witness bytes,
  exact completed affirmative/negative result and
    ExactCheckedResultAuthorityBinding<Relations, RelationSatisfaction>
    schemas,
  exact NamedConsumer and RelationSatisfactionOperationPurpose indices retained
    by every invocation, result, binding, and capability,
  exact output triple schema: inert semantic result, inert owner-created
    checked-result binding, and separately fresh capability bound to both,
  exact freshness, owner-instance, process-generation, authority-lifetime, and
    complete binding-equality requirements
}

RelationSatisfactionCapabilityAbiId = H(
  "zkc/relation-satisfaction-capability-abi",
  CanonicalEncode(RelationSatisfactionCapabilityAbi))

RelationSatisfactionCapabilityContract = {
  exact Relations owner domain and contract version,
  exact RelationSatisfactionCapabilityAbiId,
  exact covered result family: RelationSatisfaction,
  exact owner-private completed-result/premise-record coordinate and association
    schemas; no portable completed-result coordinate for this family,
  exact OwnerCapabilityRequirement schema binding the contract, ABI,
    operand/result relation, freshness, and lifetime,
  exact atomic checked-result binding and capability-minting rule,
  exact reconstruction and full result/binding equality contract
}

RelationSatisfactionCapabilityContractId = H(
  "zkc/relation-satisfaction-capability-contract",
  CanonicalEncode(RelationSatisfactionCapabilityContract))

RelationSatisfactionOperationPolicy = {
  RelationSatisfactionOperationPolicyRegimeId,
  exact RelationSatisfactionCapabilityContractId and
    RelationSatisfactionCapabilityAbiId,
  requested polarity or complete-decision schema,
  accepted assurance and residual-trust policy,
  exact named-consumer- and RelationSatisfactionOperationPurpose-indexed
    invocation and capability-use policy,
  exact owner-private completed-result-record creation, association, retention,
    and disclosure policy,
  exact attempt-record creation, portable stable-identity, retention, and
    disclosure policy, separately from completed-result records,
  exact persistence, confidential replay, redaction, and refusal policy
}

RelationSatisfactionOperationPolicyId = H(
  "zkc/relation-satisfaction-operation-policy",
  RelationSatisfactionOperationPolicyRegimeId,
  CanonicalEncode(RelationSatisfactionOperationPolicy))

RelationSatisfactionOperationPurpose =
  RelationsOperationPurpose<RelationSatisfaction>

The capability ABI and contract preimages name neither the operation-policy
value nor its regime, so their identities are cycle-free. Authentication and
admission of a `RelationSatisfactionOperationPolicy` require the exact ABI and
contract preimages, recompute both IDs, check their agreement and exact family
coverage, and bind them immutably into the admitted policy. The contract is an
owner capability shape, not a reusable live capability and not an operation
policy. The admitted operation policy remains the exact `BoundTo` disposition
for every completed satisfaction result.

Every satisfaction `OwnerCapabilityRequirement` names the exact
`RelationSatisfactionCapabilityContractId`,
`RelationSatisfactionCapabilityAbiId`, operand/result binding schema,
freshness, owner/process scope, and authority lifetime. A missing or mismatched
contract or ABI prevents invocation and completed-result construction. Record
creation and retention permission is distinct from capability use, attempt-
audit disclosure, persistence, or replay permission; none implies another.
Because every satisfaction result names a fresh private witness occurrence, its
generic checked-result coordinate is always the owner-local premise-record arm.
The separately governed public attempt record is not a completed-result record,
does not identify the private occurrence, and cannot rehydrate its authority.

RelationSatisfactionSourcePolicyDependencyClosure = {
  exact ExactAdmittedSubjectAuthorityBinding<Relations, S> values for every
    admitted S in {RelationSemanticModel, RelationInstance,
    RelationSatisfactionBasisRegistry, RelationSatisfactionValidationProfile,
    RelationSatisfactionOperationPolicy} consumed by the invocation,
  every direct and transitive premise and correspondence-support
    ExactCheckedResultAuthorityBinding,
  exact origin, admitted/result semantic facts, assurance, residual trust, and
    OwnerCapabilityRequirement from every complete source binding,
  exactly one owner-policy disposition per source:
    BoundTo(exact authenticated owner operation policy)
      | OwnerDefinesNoOperationPolicy(
          exact owner capability-contract identity, exact capability ABI),
  exact named consumer and
    operation_purpose: RelationSatisfactionOperationPurpose,
  exact source-to-pre-result dependency edges targeting the invocation's
    admitted-operand slots or semantic-basis premise/correspondence-support
    slots and the purposes already exercised,
  canonical finite acyclic transitive closure
}

When every source binding and child coordinate is portable:
  RelationSatisfactionSourcePolicyDependencyClosureId = H(
    "zkc/relation-satisfaction-source-policy-closure",
    CanonicalEncode(RelationSatisfactionSourcePolicyDependencyClosure))

Otherwise:
  LocalRelationSatisfactionHandle<SourcePolicyDependencyClosure>
~~~

The canonical closure value, and therefore its portable ID preimage, contains
both coordinates of every explicit no-policy disposition. A contract identity
without its exact capability ABI is incomplete and cannot enter the closure.

The closure never names the future support-instantiation ID, satisfaction
result, private premise-record reference, attempt record, or live capability
whose construction reads it. Its edges terminate at cycle-free admitted-
operand or semantic-basis support slots and purposes.

~~~text
ExactRelationSatisfactionRef<T> =
    PortableRelationSatisfactionId<T>
  | LocalRelationSatisfactionHandle<T>

PortableRelationSatisfactionId<SourcePolicyDependencyClosure> =
  RelationSatisfactionSourcePolicyDependencyClosureId
PortableRelationSatisfactionId<BasisReadClosure> =
  RelationSatisfactionBasisReadClosureId
PortableRelationSatisfactionId<DependencyDispositionLedger> =
  RelationSatisfactionDependencyDispositionLedgerId
PortableRelationSatisfactionId<SemanticBasis> =
  RelationSatisfactionSemanticBasisId
PortableRelationSatisfactionId<SupportInstantiation> =
  RelationSatisfactionSupportInstantiationId
PortableRelationSatisfactionId<ValidationBasis> =
  RelationSatisfactionValidationBasisId
PortableRelationSatisfactionId<Question> =
  RelationSatisfactionQuestionId
PortableRelationSatisfactionId<Request> =
  RelationSatisfactionRequestId
~~~

Each coordinate selects its portable ID or local handle from its own preimage;
mixed bindings are valid and do not taint an independent public parent
backward. The content-ID formulas below apply only when every named child is
portable. The eight families listed in the mapping are the closed v0
`RelationSatisfactionLocalizableFamily`; no other raw ID is implicitly
rewritten into this sum. Every identity-bearing child field among these
families is written as an exact `ExactRelationSatisfactionRef<T>` below. The
portable arm requires the complete child preimage to recompute the mapped ID;
the local arm requires the same-owner, same-generation handle to resolve to the
exact child body. Neither arm is ambient lookup authority or live semantic
authority.

~~~text
RelationSatisfactionBasisReadClosure = {
  every exact definition, model, proposition, correspondence, encoding,
    certificate-language, and semantic dependency read only to instantiate or
    validate one satisfaction basis
}

RelationSatisfactionBasisReadClosureId = H(
  "zkc/relation-satisfaction-basis-read-closure",
  RelationSatisfactionBasisRegistryId,
  CanonicalEncode(RelationSatisfactionBasisReadClosure))

RelationSatisfactionDependencyDisposition =
    EstablishedPremise(exact proposition, required polarity, and semantic facts)
  | ResidualHypothesis(exact truth-apt proposition inherited by the result)
  | DefinitionalOrLogicTrustRoot(exact named adequacy claim)

RelationSatisfactionDependencyDispositionLedger = {
  every and only truth-apt dependency in one finite acyclic basis graph,
  exactly one disposition per dependency,
  exact rooted termination for every path
}

RelationSatisfactionDependencyDispositionLedgerId = H(
  "zkc/relation-satisfaction-dependency-disposition",
  RelationSatisfactionBasisRegistryId,
  CanonicalEncode(RelationSatisfactionDependencyDispositionLedger))

RelationSatisfactionSemanticBasis = {
  admitted RelationSatisfactionBasisRegistryId,
  exact evaluation, proof, certificate, or correspondence contract,
  exact premise, assumption, side-condition, substitution, and refutation schema,
  read_closure: ExactRelationSatisfactionRef<BasisReadClosure>,
  dependency_dispositions:
    ExactRelationSatisfactionRef<DependencyDispositionLedger>
}

RelationSatisfactionSemanticBasisId = H(
  "zkc/relation-satisfaction-semantic-basis",
  RelationSatisfactionBasisRegistryId,
  CanonicalEncode(RelationSatisfactionSemanticBasis))

RelationSatisfactionSupportInstantiation = {
  RelationSatisfactionSupportInstantiationRegimeId,
  semantic_basis: ExactRelationSatisfactionRef<SemanticBasis>,
  dependency_dispositions:
    ExactRelationSatisfactionRef<DependencyDispositionLedger>,
  exact premise ExactCheckedResultAuthorityBinding values, including any mixed
    basis/derivation/support origin coordinates,
  exact correspondence-support ExactCheckedResultAuthorityBinding values,
  source_policy_closure:
    ExactRelationSatisfactionRef<SourcePolicyDependencyClosure>,
  exact total realization of every dependency-disposition ledger entry,
    with source bindings and OwnerCapabilityRequirement values only for
    EstablishedPremise and exact preservation of ResidualHypothesis and
    DefinitionalOrLogicTrustRoot entries
}

RelationSatisfactionSupportInstantiationId = H(
  "zkc/relation-satisfaction-support-instantiation",
  RelationSatisfactionSupportInstantiationRegimeId,
  CanonicalEncode(RelationSatisfactionSupportInstantiation))

RelationSatisfactionValidationBasis = {
  admitted RelationSatisfactionValidationProfileId,
  semantic_basis: ExactRelationSatisfactionRef<SemanticBasis>,
  exact checker contract,
  stable checker implementation identity, exact CheckerAbiId, and exact implementation-to-contract
    correspondence identity,
  exact decoder, translation, proof-rule, and validation-root closure
}

RelationSatisfactionValidationBasisId = H(
  "zkc/relation-satisfaction-validation-basis",
  RelationSatisfactionValidationProfileId,
  CanonicalEncode(RelationSatisfactionValidationBasis))
~~~

Model admission checks its closed family, type and occurrence interpretation,
dependency closure, evaluation/refutation schema, assumption language, and
semantic reads. It does not admit a basis registry, validation profile, or
operation policy and does not prove the external definition true, satisfiable,
or faithfully modeled. Faithfulness to a definition language requires its own
exact checked statement/model correspondence and remains an explicit premise
or residual hypothesis of the satisfaction basis.

The basis registry, validation profile, and operation policy are separately
authenticated and admitted under their exact closed regimes. Admission checks
their canonical content, dependency closure, extension boundary, and
meaning-bearing tags and mints only the corresponding process-local profile
capability. A semantic basis binds one admitted registry; a validation basis
binds one admitted validation profile and one exact semantic basis. A support
instantiation is a separately identified inert record: it binds exact support
`ExactCheckedResultAuthorityBinding` values, correspondence-support bindings,
their exact basis/assurance/trust/policy coordinates and
`OwnerCapabilityRequirement` values, the
transitive source-operation-policy dependency closure, and a total realization
of the semantic basis's disposition ledger. It contains no
capability token and grants no premise or checker authority. None changes
`RelationSemanticModelId` or the public satisfaction-question meaning.

If a premise or correspondence-support binding uses an external owner-local
result-record coordinate, every Relations value whose own identity preimage
names that complete binding or a derived local child uses
`LocalRelationSatisfactionHandle<T>` instead of a portable ID.
This handle follows the same owner-instance/process-generation, collision-free
internal encoding, equality, nonserialization, and nonauthority rules as the
local domains in Section 2.1. Thus a support instantiation and request may be
local while an independently public question remains portable. A semantic basis
or validation basis remains portable only when every child in its own exact
identity preimage is portable; neither is tainted backward merely because a
later support instantiation is local. Taint propagates only forward through
explicit identity edges. The affected source-policy closure, support, request, result, private
premise-record body/association, and later consumer chain are same-process and
have no public attempt record or exact cold replay.

An `EstablishedPremise` contributes only proposition, required polarity, and
semantic facts to semantic-basis meaning. The selected complete
`ExactCheckedResultAuthorityBinding` values and their exact disposition
realization belong to the support instantiation; fresh matching capabilities
are supplied only to an invocation. Residual
hypotheses remain inherited truth-apt propositions, while only definitional or
logic adequacy may terminate at `DefinitionalOrLogicTrustRoot`.

Unknown definition families, semantic-model regimes, value interpretations,
evaluation rules, refutation meanings, basis contracts, support schemas,
checker contracts, or operation-policy tags are `Unsupported` at their exact
owning boundary. A loaded callback, registry entry, inert source binding, or
matching ID cannot acquire model, premise, basis, validation, checker-execution, or
operation authority.

### 12.2 Occurrence-local question and operation

The public question coordinates are:

~~~text
RelationSatisfactionQuestion = {
  exact RelationDefinitionRef,
  admitted RelationSemanticModelId,
  admitted RelationInstanceId,
  exact public assignment and interpretation regime,
  exact typed assumption and side-condition context
}

RelationSatisfactionQuestionId = H(
  "zkc/relation-satisfaction-question",
  exact public question coordinates)

RelationSatisfactionRequest = {
  question: ExactRelationSatisfactionRef<Question>,
  offered_semantic_basis: ExactRelationSatisfactionRef<SemanticBasis>,
  offered_support_instantiation: ExactRelationSatisfactionRef<SupportInstantiation>,
  offered_validation_basis: ExactRelationSatisfactionRef<ValidationBasis>,
  exact RelationSatisfactionOperationPolicyId,
  exact named consumer and
    operation_purpose: RelationSatisfactionOperationPurpose,
  exact operational limits
}

RelationSatisfactionRequestId = H(
  "zkc/relation-satisfaction-request",
  CanonicalEncode(RelationSatisfactionRequest))

RelationSatisfactionRequestField =
    Question
  | OfferedSemanticBasis
  | OfferedSupportInstantiation
  | OfferedValidationBasis
  | OperationPolicy
  | NamedConsumer
  | OperationPurpose
  | OperationalLimits

RelationSatisfactionPreExecutionRealizationLedger = {
  request: ExactRelationSatisfactionRef<Request>,
  exactly one pre-execution realization entry for every and only
    RelationSatisfactionRequestField,
  exact field equality between each offered coordinate/value and the
    corresponding invocation coordinate/value,
  exact equality of offered_validation_basis to the validation basis actually
    used, including its admitted validation-profile and semantic-basis links,
  exact ExactRelationSatisfactionRef<DependencyDispositionLedger> selected by
    the offered semantic basis,
  exact total support-instantiation realization of every and only disposition:
    matching ExactCheckedResultAuthorityBinding for EstablishedPremise,
    unchanged ResidualHypothesis, or exact DefinitionalOrLogicTrustRoot,
  exact pre-execution resource reservation and limit checks,
  exact terminal resource-counter schema
}

RelationSatisfactionRequestRealizationLedger = {
  exact RelationSatisfactionPreExecutionRealizationLedger,
  exact terminal resource accounting for every declared operational limit,
    with no omitted counter, unbounded substitution, or exceeded limit
}

PrepareRelationSatisfactionRequestRealization(
  exact RelationSatisfactionRequest,
  exact selected question, semantic basis, support instantiation,
    validation basis, operation policy, named consumer, and
    RelationSatisfactionOperationPurpose)
  ->
    Prepared(exact inert RelationSatisfactionPreExecutionRealizationLedger)
  | Unsupported(exact unsupported request field or limit kind)
  | CannotAnswer(exact missing pre-execution realization)
  | Refused(exact prohibited use or unavailable authorized budget)
  | Malformed(exact mismatch, duplicate, extra entry, or invalid reservation)
  | CheckerFailure(exact failed pre-execution operational boundary)

LocalRelationSatisfactionAttemptInputHandle =
  fresh owner-issued process-local nonserializable opaque input-material handle

RelationSatisfactionTerminalAccountingOffer =
    Completed(exact terminal accounting)
  | Missing
  | OpaqueMalformed(exact normalized accounting defect,
                    exact LocalRelationSatisfactionAttemptInputHandle)

SealRelationSatisfactionRequestRealization(
  exact RelationSatisfactionPreExecutionRealizationLedger,
  exact RelationSatisfactionTerminalAccountingOffer)
  -> RelationSatisfactionRequestRealizationOutcome

RelationSatisfactionRequestRealizationOutcome =
    Realized(exact inert RelationSatisfactionRequestRealizationLedger)
  | Unsupported(exact unsupported request field or limit kind)
  | CannotAnswer(exact missing realization or incomplete accounting)
  | Refused(exact prohibited use or unavailable authorized budget)
  | Malformed(exact mismatch, duplicate, extra entry, or invalid accounting)
  | CheckerFailure(exact failed operational boundary; no semantic conclusion)
~~~

These are mandatory internal totality checks, not separately consumable
semantic judgments. They mint no capability and create no checked-result
binding. Before semantic execution, Relations checks every nonterminal field
match, support disposition, and reservation and constructs only the exact
pre-execution ledger. During execution it accounts for every declared counter.
Immediately before any satisfaction `Completed`, it supplies a completed
terminal-accounting offer, seals the final ledger, and retains the exact
`Realized` ledger in the result. A missing or malformed accounting offer is
representable and produces the corresponding U/C/R/M/F outer class. Any
nonprepared or nonrealized branch prevents satisfaction `Completed` without
inventing an affirmative or negative semantic result.

`operation_purpose` is one typed coordinate, not interchangeable prose. The
source-policy closure, request, checking invocation, completed live result,
private premise-record body/association, attempt record when present, and live
capability must all bind and compare exactly the same
`RelationSatisfactionOperationPurpose` and named consumer.

The private witness is deliberately absent from the question and request
identities. Because a support-instantiation ID can still become a linkable
equality handle, the operation policy separately controls whether the request
or support identity may enter a public attempt record. At invocation, Relations
creates a fresh nonserializable occurrence binding:

~~~text
RelationSatisfactionAttemptSlotStatus =
    Authenticated(exact capability-neutral typed value, binding, contract,
                  policy, or reference required by that slot)
  | OfferedCandidate(exact capability-neutral typed candidate and any claimed
                     reference or binding)
  | PrivateOccurrenceOffered(
      exact LocalRelationSatisfactionAttemptInputHandle; no witness bytes)
  | Missing
  | OpaqueMalformed(exact normalized defect class,
                    exact LocalRelationSatisfactionAttemptInputHandle)

RelationSatisfactionAttemptShape =
    RequestUnavailable(
      exact request-root status whose variant is Missing or OpaqueMalformed;
      no request-derived child-slot obligation)
  | RequestParsed(
      exact capability-neutral RelationSatisfactionRequest,
      exact request-root status whose variant is Authenticated or
        OfferedCandidate,
      exact required-slot schema derived from that request,
      exactly one RelationSatisfactionAttemptSlotStatus for every and only
        derived checker-input slot, excluding owner-generated private-
        occurrence and result-reference fields,
      exact slot-to-schema association)

RelationSatisfactionAttemptInput = {
  exact Relations semantic regime and expected RelationSatisfaction entry point,
  exact RelationSatisfactionAttemptShape,
  no live capability, witness bytes, or claim that an operation occurrence
    happened
}

PrepareRelationSatisfactionInvocation(
  exact RelationSatisfactionAttemptInput,
  occurrence-local private input and capability offers for the declared slots,
    which may be absent, stale, nonmatching, malformed, or prohibited and are
    never retained)
  ->
    Ready(allocate the fresh private occurrence binding,
          construct the exact complete CheckRelationSatisfaction operand tuple,
          and construct the exact
            RelationSatisfactionPreExecutionRealizationLedger)
  | Rejected(exact noncompleted disposition, failed requirement, and reached
             policy/contract checks)

AttemptRelationSatisfaction(
  exact RelationSatisfactionAttemptInput,
  occurrence-local private input and capability offers)
  -> RelationSatisfactionAttemptOutcome

CheckRelationSatisfaction(
  exact admitted RelationSemanticModel and RelationInstance subject values,
  exact ExactAdmittedSubjectAuthorityBinding<Relations, RelationSemanticModel>
    and ExactAdmittedSubjectAuthorityBinding<Relations, RelationInstance>,
  separately supplied fresh model- and instance-admission capabilities,
  exact RelationSatisfactionQuestion reconstructed from those admitted subjects
    and the supplied assumptions and side conditions,
  occurrence-local PrivateWitnessAssignment,
  exact admitted RelationSatisfactionBasisRegistry subject value and
    RelationSatisfactionSemanticBasis,
  exact ExactAdmittedSubjectAuthorityBinding<Relations,
    RelationSatisfactionBasisRegistry>,
  separately supplied fresh registry-admission capability,
  exact RelationSatisfactionSupportInstantiation,
  exact authenticated RelationSatisfactionSourcePolicyDependencyClosure and
    matching ExactRelationSatisfactionRef<SourcePolicyDependencyClosure>,
  exact ExactCheckedResultAuthorityBinding values from the support
    instantiation with separately supplied fresh premise and
    correspondence-support capabilities,
  exact authenticated source-owner policy dispositions required by the support
    closure: complete `BoundTo` policy preimages with fresh policy/purpose
    authority, or exact `OwnerDefinesNoOperationPolicy` capability-contract and
    ABI preimages with fresh contract admission or owner-mediated confirmation,
  exact admitted RelationSatisfactionValidationProfile subject value and
    RelationSatisfactionValidationBasis,
  exact ExactAdmittedSubjectAuthorityBinding<Relations,
    RelationSatisfactionValidationProfile>,
  separately supplied fresh profile-admission capability,
  fresh identity/ABI-matched checker-execution capability,
  exact admitted RelationSatisfactionOperationPolicy subject value and
    RelationSatisfactionRequest,
  exact authenticated RelationSatisfactionCapabilityContract and
    RelationSatisfactionCapabilityAbi preimages whose IDs equal the admitted
    operation policy's bound contract and ABI,
  exact OwnerCapabilityRequirement derived from that contract and ABI for this
    operand/result schema, named consumer, and operation purpose,
  exact RelationSatisfactionPreExecutionRealizationLedger,
  exact ExactAdmittedSubjectAuthorityBinding<Relations,
    RelationSatisfactionOperationPolicy>,
  separately supplied fresh policy-admission capability,
  exact assumptions and side conditions)
  -> RelationSatisfactionAttemptOutcome
     + on Completed, mandatory owner-private
       RelationSatisfactionPremiseRecordRef
     + optional policy-permitted RelationSatisfactionAttemptRecord
~~~

`RelationSatisfactionAttemptInput` is the capability-neutral outer carrier.
`RequestUnavailable` makes a missing or noncanonical request representable
without inventing its dynamic child schema. `RequestParsed` derives that schema
from the inert request and totally classifies each slot. Witness material and
fresh authority remain separate occurrence-local offers; a carrier records at
most a private opaque input-material handle, never witness bytes or a
capability. Only `Ready` allocates the private occurrence binding, constructs
the pre-execution realization ledger, and enters the displayed
`CheckRelationSatisfaction` signature. Every `Rejected` branch returns the
matching noncompleted outcome and cannot produce a result binding, premise
record, or satisfaction capability. An opaque-malformed or private-input handle
is not portable, is not authority, and establishes no historical occurrence.
The displayed checker signature is therefore the successful preparation form,
not the outer ingress contract.

The operation first checks that the witness occurrence reference resolves
through the unique current holder/generation association to the supplied body;
that the body is total and well typed for every and only witness occurrence in
the admitted Interface; and that it belongs to the authorized local holder and
is bound to the exact instance and model. It checks complete binding equality
and fresh admission authority for the model, instance, basis registry,
validation profile, and operation policy. It also recomputes and cross-checks
the exact satisfaction capability contract and ABI, requires their closed
family and output schemas to cover this invocation, and checks the offered
`OwnerCapabilityRequirement` against the exact prospective result binding,
consumer, purpose, freshness, owner/process scope, and lifetime. The supplied authenticated source-
policy closure must contain every one of those admitted-subject bindings and
every premise/correspondence checked-result binding, their complete transitive
policy closures, and no extra source.

It then checks that the support instantiation names exactly the semantic basis
and the disposition ledger selected by that basis, and exactly the authenticated
source-policy closure supplied to the invocation. The request-realization check
must return `Realized` for every request field, the offered validation basis,
the total disposition realization, and terminal operational-limit accounting
before satisfaction can return `Completed`. The request, realization ledger,
closure, invocation, completed result, private premise-record body and
association, exact source binding, attempt record when present, and capability
bind the identical named consumer and
`RelationSatisfactionOperationPurpose`. It also checks that
every ledger disposition is realized without changing a residual hypothesis or
definitional/logic trust root; that every and only established premise is
realized by the stated binding and correspondence support; and that every fresh
support capability matches its exact checked-result binding and
`OwnerCapabilityRequirement`, polarity, semantic facts, exact
basis/derivation/support or qualification binding,
assurance, residual trust, source-operation-policy closure, and current process
authority. The requested assurance must accept every decisive source
qualification. The result's residual-trust closure is the total canonical
rooted union of every decisive premise and correspondence trust closure plus
the exact definition/model, semantic-basis, validation, translation, checker,
implementation-correspondence, and execution trust roots; no source root may be
dropped or relabeled. The operation verifies every direct and transitive source-
owner policy disposition, including every admitted-operand disposition,
against its exact authenticated preimage, and requires
the satisfaction policy plus every bound source policy to permit this named
consumer and exact `RelationSatisfactionOperationPurpose`. One mismatch,
refusal, or prohibition
prevents `Completed`. It separately checks that the
fresh checker-execution capability matches the validation basis's stable
implementation and contract-correspondence identities. It then checks the
exact selected evaluation, proof, certificate, or correspondence basis.
Neither an ID, inert source binding, checker implementation identity, instance
admission, nor witness possession establishes satisfaction.

The live result binds:

- the exact definition, Interface, instance, public assignment, and model;
- one fresh occurrence-local witness binding and its confidential capability;
- exact assumptions and side conditions, basis-registry and validation-profile
  IDs, exact question, semantic-basis, support-instantiation, validation-basis,
  and request IDs or local handles, and the exact operation-policy ID;
- the exact `RelationSatisfactionCapabilityContractId`,
  `RelationSatisfactionCapabilityAbiId`, and matching
  `OwnerCapabilityRequirement`;
- the exact transitive source-operation-policy dependency closure and every
  complete admitted-subject and checked-result source binding;
- the exact total `RelationSatisfactionRequestRealizationLedger`, including
  disposition realization and terminal operational-limit accounting;
- the exact named consumer and `RelationSatisfactionOperationPurpose`
  authorized by that closure and request;
- exact stable checker implementation and contract-correspondence identities,
  plus the completed current-process support and checker-capability matches;
- exact assurance class and residual-trust closure;
- the exact affirmative or negative evaluation facts;
- the process generation in which the check completed; and
- one mandatory owner-private premise-record reference, its exact associated
  body, and complete `ExactCheckedResultAuthorityBinding` created atomically
  with every `Completed` result.

It is not a globally content-addressed witness proposition. For every
`Completed` result, Relations creates one inert owner-private premise-record
body and a separately allocated reference/association for same-process typed
consumers. The specialized body below is the complete
`RelationCheckedResultPremiseRecordBody<RelationSatisfaction>` required by
Section 2.1:

~~~text
RelationSatisfactionPremiseRecordRef =
  RelationCheckedResultPremiseRecordRef<RelationSatisfaction>

RelationSatisfactionPremiseRecordBody = {
  every exact generic field of
    RelationCheckedResultPremiseRecordBody<RelationSatisfaction>,
  exact Relations owner domain and RelationSatisfaction result-family tag,
  exact owner-issued PrivateWitnessAssignment.local_occurrence,
  question: ExactRelationSatisfactionRef<Question>,
  request: ExactRelationSatisfactionRef<Request>,
  semantic_basis: ExactRelationSatisfactionRef<SemanticBasis>,
  support_instantiation: ExactRelationSatisfactionRef<SupportInstantiation>,
  validation_basis: ExactRelationSatisfactionRef<ValidationBasis>,
  RelationSatisfactionOperationPolicyId,
  RelationSatisfactionCapabilityContractId,
  RelationSatisfactionCapabilityAbiId,
  source_policy_closure:
    ExactRelationSatisfactionRef<SourcePolicyDependencyClosure>,
  exact complete admitted-subject and checked-result source bindings,
  exact total RelationSatisfactionRequestRealizationLedger,
  exact checker contract, stable implementation, CheckerAbiId,
    implementation-to-contract correspondence, dependency, and read closure,
  exact named consumer and
    operation_purpose: RelationSatisfactionOperationPurpose,
  exact polarity, assurance, semantic facts, and residual-trust closure,
  exact authenticated BoundTo(RelationSatisfactionOperationPolicyId and
    admitted policy contract) disposition,
  exact OwnerCapabilityRequirement,
  exact Relations owner instance and process generation,
  no RelationSatisfactionPremiseRecordRef
}

RelationSatisfactionPremiseRecordAssociation:
  (exact Relations owner instance,
   exact process generation,
   fresh RelationSatisfactionPremiseRecordRef)
    -> exact RelationSatisfactionPremiseRecordBody
~~~

This is the `RelationSatisfaction` specialization of the generic association
in Section 2.1, not a second coordinate or duplicate association table.

The private body contains no witness bytes, capability token, or selecting
reference and grants no authority. Relations constructs that complete body,
independently allocates a fresh reference in the collision-free owner-local
domain defined in Section 2.1, and atomically retains exactly one association
entry from that reference to the body before exposing the result. The fresh
reference, not the body or association, is the owner-local checked-result
coordinate inside the result's `ExactCheckedResultAuthorityBinding`; the
separately supplied live capability retains the identical binding. The
association exists even when public persistence is forbidden, so an
Analysis `SupportInstantiation` can retain the exact owner-private result
binding whose coordinate is that premise-record reference, and require the
separately supplied matching live capability. The relation
operation policy controls whether the private reference may be disclosed to a
named same-process consumer; any derived operation must preserve its disclosure
and persistence restrictions. Reset or process crossing destroys the private
reference, retained body association, and live authority. An explicitly
authorized confidential rerun may reconstruct a new witness occurrence,
premise-record body, and association, but it creates a new private reference,
live result, and capability rather than replaying the prior exact local result.
Independently public Relations question, semantic-basis, and validation-basis
IDs remain equal exactly when their public preimages remain equal. Any source-
policy closure, support instantiation, or request whose own
preimage names a newly created local coordinate instead receives a fresh local
handle; Relations defines no witness-indexed derivation ID. Downstream Analysis
values that actually name the new private reference use new owner-local handles
under Analysis's private-reference rule.

Only when every field and identity preimage is portable, and the satisfaction
operation policy plus every policy in the transitive source-policy dependency
closure permit public record creation and disclosure for the exact named
consumer and `RelationSatisfactionOperationPurpose`, may the following public
inert form exist. A
local handle makes this public attempt form unavailable regardless of policy:

~~~text
RelationSatisfactionAttemptRecord = {
  RelationSatisfactionAttemptRecordRegimeId,
  RelationSatisfactionQuestionId,
  optional disclosed RelationSatisfactionRequestId and
    RelationSatisfactionSupportInstantiationId, together or neither as fixed by
    RelationSatisfactionOperationPolicyId,
  RelationSemanticModelId,
  RelationSatisfactionBasisRegistryId,
  RelationSatisfactionSemanticBasisId,
  RelationSatisfactionValidationProfileId,
  RelationSatisfactionValidationBasisId,
  RelationSatisfactionOperationPolicyId,
  RelationSatisfactionCapabilityContractId,
  RelationSatisfactionCapabilityAbiId,
  RelationSatisfactionSourcePolicyDependencyClosureId when every contributing
    owner policy permits its disclosure,
  exact named consumer and
    operation_purpose: RelationSatisfactionOperationPurpose,
  disclosed assurance and residual-trust closure,
  public qualified outcome class,
  exactly policy-permitted public retained facts and refutation scope
}

RelationSatisfactionAttemptRecordId = H(
  "zkc/relation-satisfaction-attempt-record",
  RelationSatisfactionAttemptRecordRegimeId,
  CanonicalEncode(RelationSatisfactionAttemptRecord))
~~~

The record explicitly excludes the private witness assignment, witness bytes,
premise and correspondence-support capabilities, checker-execution capability,
secret capabilities, private occurrence reference, undisclosed support IDs and
witness-derived facts, checking-process identity, and live result capability.
Neither the record nor its ID carries or rehydrates premise, checker, witness,
or satisfaction authority. Omitting the request/support pair makes no claim
about which undisclosed support instantiation realized the public outcome, and
omitting a source-policy closure from disclosed fields is never authorization to
ignore it. Reauthenticating the record validates only its bounded record-
relative statement; it does not prove that a checking occurrence happened or
that the disclosed outcome was historically observed. Such a history claim
would require a separately owner-authenticated occurrence/log result, which
Stage 4A does not define.

### 12.3 Qualified outcomes and exact negative meaning

~~~text
RelationSatisfactionAttemptOutcome =
    Completed(
      result:
          Affirmative(exact satisfaction facts)
        | Negative(exact evaluation counterfact),
      binding: exact ExactCheckedResultAuthorityBinding<Relations,
        RelationSatisfaction>,
      fresh capability: CheckedRelationSatisfaction<
        exact result polarity, exact AssuranceClass,
        exact RelationSatisfactionOperationPolicyId,
        exact RelationSatisfactionCapabilityContractId,
        exact RelationSatisfactionCapabilityAbiId,
        exact OwnerCapabilityRequirement,
        exact ExactRelationSatisfactionRef<SourcePolicyDependencyClosure>,
        exact ExactRelationSatisfactionRef<Request>,
        exact RelationSatisfactionRequestRealizationLedger,
        exact NamedConsumer, exact RelationSatisfactionOperationPurpose,
        exact ExactCheckedResultAuthorityBinding<Relations,
          RelationSatisfaction>> bound to both preceding values)
  | Unsupported(exact RelationSatisfactionAttemptInput and exact unsupported
                model, definition family, basis, or construct)
  | CannotAnswer(exact RelationSatisfactionAttemptInput and exact missing
                 semantic input or incomplete basis)
  | Refused(exact RelationSatisfactionAttemptInput and exact missing authority
            or prohibited disclosure)
  | Malformed(exact RelationSatisfactionAttemptInput and exact typing,
              occurrence, identity, or framing defect)
  | CheckerFailure(exact RelationSatisfactionAttemptInput and exact failed
                   operational boundary; no semantic conclusion)
~~~

Only `Completed` atomically returns the semantic result, exact checked-result
binding, and a separately fresh process-local
`CheckedRelationSatisfaction<Polarity, AssuranceClass,
RelationSatisfactionOperationPolicyId,
RelationSatisfactionCapabilityContractId,
RelationSatisfactionCapabilityAbiId,
OwnerCapabilityRequirement,
ExactRelationSatisfactionRef<SourcePolicyDependencyClosure>,
ExactRelationSatisfactionRef<Request>,
RelationSatisfactionRequestRealizationLedger,
NamedConsumer, RelationSatisfactionOperationPurpose,
ExactCheckedResultAuthorityBinding<Relations, RelationSatisfaction>>`
capability bound to both. U/C/R/M/F return no checked-result binding and no
satisfaction capability. Their retained outer attempt input is capability-
neutral and record-relative; it establishes neither a checking occurrence nor
the noncompleted condition as history. A public
`RelationSatisfactionAttemptRecord` may additionally exist only when every
field required by its schema was reached, portable, and policy-permitted; early
missing or opaque-malformed ingress therefore has no invented public record.
There is no policy- or request-erased satisfaction capability. An
affirmative states that this exact witness occurrence satisfies this exact
instance under this exact model, assumptions, and basis. A negative states only
that this exact witness occurrence fails it under the same coordinates. It
does not establish instance unsatisfiability, witness nonexistence, failure of
another witness, or disagreement under another model.

Missing authority, unavailable witness fields, unsupported definitions,
timeouts, failed proof search, invalid certificates, and checker failure are
not negative satisfaction results. An invalid certificate may be negative for
the separately stated certificate-validity question only.

No relation admission, artifact observation, artifact/interface comparison,
grounding, or Protocol correspondence result can substitute for satisfaction.
Equal bytes, matching public values, accepted result shape, or affirmative
correspondence proves no witness predicate.

### 12.4 Confidentiality, persistence, and replay

Public persistence of a satisfaction result is prohibited by default. Secret
witness values, witness-derived counterexamples, and stable witness digests do
not enter public records, caches, logs, replay bundles, or semantic IDs. A
remote non-revealing proof is a separately modeled proof/certificate basis; it
does not serialize the underlying witness capability.

A named confidential consumer may justify a separately reviewed private replay
contract. That contract must state encryption and access ownership, disclosure
surface, occurrence unlinkability, model, semantic-basis, support,
validation-basis, and checker reconstruction, expiry, revocation, and deletion.
Creation, retention, lookup, acquisition, and replay under that contract require
fresh validation of every direct and transitive source-owner policy disposition:
each bound policy must permit this named consumer and purpose, while each
no-policy disposition requires fresh admission or owner-mediated confirmation
of its exact capability-contract and ABI preimage. One
prohibition, refusal, or unavailable owner-authorized reconstruction prerequisite
means no contract, bundle, or replay claim is created. Even then, the portable
untainted lane reconstructs the exact support-instantiation preimage. A lane
with owner-local source inputs instead performs a new confidential rerun and
creates fresh affected source-policy-closure, support, request, premise-record
body/association, result, and consumer handles; independently public question,
semantic-basis, and validation-basis IDs may remain equal. Either lane
reauthenticates the exact satisfaction capability contract and ABI preimages,
requires equality with the admitted operation policy and retained
`OwnerCapabilityRequirement`, and rechecks completed-result creation,
association, retention, disclosure, and replay permission for the identical
named consumer and typed purpose; then it
reauthenticates every source policy disposition, including every exact explicit
no-policy owner contract and exact owner-authorized reconstruction material or
external replay prerequisite; reconstructs and revalidates every complete
admitted-subject and checked-result binding and disposition edge; separately
obtains fresh binding-matched admitted-operand, premise, correspondence-support,
checker-execution, and witness capabilities; reruns total request realization
and operational-limit accounting; reruns the exact semantic check; requires the
same permitted public result; and mints a fresh local capability. Matching
stored bytes never restore any old support, checker, witness, or result
capability.

### 12.5 Nonclaims

This specification does not establish:

- truth, satisfiability, or faithful formalization of an external relation;
- premise truth or current premise authority from an inert source binding,
  support-instantiation ID, correspondence result record, or matching bytes;
- checker correctness, executable checker authority, or completed checker
  execution from a validation-basis or implementation identity;
- public-instance truth, witness existence, possession, validity, or secrecy
  beyond the local capability boundary;
- instance satisfiability, existence or validity of any other witness, or
  equivalence of relation and Protocol acceptance;
- artifact provenance, parser correctness beyond the named checked contract,
  or agreement from an observation alone;
- bridge or committed-object derivation faithfulness beyond the exact admitted
  ABI, round-trip, and checked-equation laws;
- opening knowledge, completeness, soundness, zero knowledge, or another
  cryptographic property;
- Protocol admission, execution, compiler preservation, OIR validity,
  endpoint support, or realization; or
- implementation correspondence, migration safety, compatibility, or
  production readiness.

Each conclusion requires its own exact subject, model, assumptions, checker,
and qualified result.
