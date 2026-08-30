# Protocol Interfaces and Prover Plans

> **Document kind:** Target semantic specification
> **Document state:** Active non-normative K3 target
> **Provisional owner:** `pir`
> **Authority:** This page specifies the K1/K2-aligned dependent subjects for
> `docs-next/`. It is not normative until explicit consolidation and cutover.
> The current specifications under [`docs/`](../../docs/README.md) remain
> authoritative. This page makes no implementation, compatibility, migration,
> or cryptographic-security claim.

## 1. Contract and boundary

An admitted [Protocol](interactive-core.md) fixes verifier-observable
interaction and challenge interpretation. A `ProtocolInterface` fixes one
external presentation of that Protocol. A `ProverPlan` fixes one finite,
reviewable proposal for implementing its K2 prover-decision boundary.

```text
AdmittedProtocol
  + independently admitted ProtocolInterface
      -> total invocation assignment
      -> scoped Statement presentation
      -> role-qualified transport and completion presentation
  + independently admitted ProverPlan
      -> private-material, randomness, and persistent-state interfaces
      -> one recipe for every potential K2 prover decision
      -> optional bounded private recipes at exact Accept terminals
      -> exact Plan-owned adapter for InteractiveCore strategy execution
      -> atomic accepted-terminal continuation output
      -> separate PlanRealizes judgment
```

Neither subject is part of `ProtocolId`. Several Interfaces and Plans may
coexist for one Protocol. Substituting either cannot change Core occurrences,
visibility, transcript framing, challenge interpretation, checks, claims,
reductions, terminals, accepted language, or any Protocol-only result.

A user-facing proof package is not another PIR subject. The Interface may
expose several protocol-produced slots, each with its one exact Core origin;
OIR or Realization may place those slots in one record or byte string under an
exact projection and codecs. Physical co-location never merges semantic
message occurrences or moves a publication across a Challenge. A protocol
with several causal prover messages therefore remains several Core messages
even when its endpoint transports one proof blob, while a genuinely
zero-challenge one-message protocol may use one record-valued message.

This page consumes, without redefining:

- K1 `PriorMetaAuthenticationBasis`, `SemanticContentId<K>`, `ValueType`,
  canonical values, `PortableAlgorithmRef`, `EvaluationContractId`,
  `PortableEvaluationLimitsV0`, typed completion, exact-used module closure,
  and authority rules from
  [Executable Semantic Foundations](../foundation/executable-foundations.md);
- K2 public and verifier-private inputs, `BindingRef`, occurrences,
  `ProverDecisionPoint`, exact `ProverView`, legal `ProverMove`, completed
  records, and owner-derived source views from
  [Interactive Core and Causal Execution](interactive-core.md); and
- canonical-framed interpretation-failure coordinates from
  [Canonical-Framed Fiat--Shamir](fiat-shamir.md).

Every sequence is finite and ordered. Sets and maps use sorted-unique K1
canonical key bodies. Local references are dense ordinals unless a keyed form
is stated. All bodies and derived aggregates fit the K1 constitutional bounds.
Unknown kinds, modules, fields, tags, algorithms, or references fail closed.

Authentication, admission, opaque process-local authority, qualified
completion, persistence, and cold replay follow
Canonical PIR [Section 4](canonical-pir.md#4-algebra-to-carrier-correspondence),
[Section 5](canonical-pir.md#5-authentication-admission-and-live-authority),
and [Section 7](canonical-pir.md#7-authoring-persistence-and-information-loss).
This page adds the owner predicates for Interface, Plan,
`PlanWitnessSurface` extraction, and `PlanRealizes`; it does not restate the
generic capability machinery.

All identified subjects on this page select one standalone
`PIRInterfacePlanProfileId`. Its required exact profile imports are
`{PIRInteractionProfileId, PIRCanonicalFramedFSProfileId}`. Its supported subject kinds are
`{"pir.protocol-interface", "pir.prover-plan",
"pir.plan-witness-surface", "pir.source-binding-payload",
"pir.source-capability-requirement", "pir.source-consumer",
"pir.confidential-plan-witness-disclosure-policy",
"pir.source-no-policy", "pir.source-policy-closure",
"pir.source-purpose"}`. Its inline declaration catalog contains every exact
owner body below, the Interface and Plan owner-view schemas, their
field-expansion and closure laws, the Plan execution adapter and continuation
schemas, the process-local input and accepted-continuation witness-handoff
laws, the confidential Plan-witness source envelope, and `PlanRealizes` intake
semantics. The
two imports are exact: Interface and Plan interpret Fresh and canonical-framed
Fiat--Shamir Protocol identities, but no subject on this page names the duplex
sibling or the invocation-issued public-setup quotient. Duplex formation is
`Unsupported` until a downstream sibling profile owns construction-material
assignment and pre-execution generation. An unrelated profile change
therefore cannot rotate this Interface/Plan meaning. The Foundation profile-import DAG,
rather than an authored module root list, is the complete generic language
closure.

This revision changes the Interface/Plan declaration catalog and therefore
requires a newly formed `PIRInterfacePlanProfileId`. It does not change
`SemanticRegimeId`, `PIRInteractionProfileId`, `CoreId`, `ProtocolId`, or
InteractiveCore execution meaning. Old Interface/Plan-profiled bytes are never
interpreted under the rotated profile.

The required Interface/Plan root closure has three entries once their owners
publish complete profile preimages: the two K2 profiles plus
`PIRInterfacePlanProfileId`. The five-entry convenience bundle
that also contains the unrelated K2 public-setup profile and
`RelationsProfileId` is not valid Interface/Plan intake. Interface formation
and owner-view issuance authenticate only this three-entry
closure and require only the Interface/Plan root in evaluator support; lack of
Relations support cannot block an Interface view. An authenticated but
evaluator-unrecognized root is `Unsupported`, while a supported profile that
omits the Interface or any emitted owner-authority subject kind is `Refused`.

This section fixes the target profile owner, import topology, supported-kind
set, catalog responsibility, and no-extra closure law. It does not yet publish
the complete six-field owner-local K1 profile preimage or its full typed ID.
The bounded executable profile pin is evidence only for deterministic
topology, authentication, and rotation. The owner must publish the complete
preimage and independently reconstructible full typed ID before any dependent
K4 ID is treated as persistent and before K5 freeze.

## 2. Shared local vocabulary

### 2.1 Invocation references and audiences

```text
InvocationInputRef =
    Public(PublicInputRef)
  | VerifierPrivate(VerifierPrivateInputRef)

InputAudience(Public(_))          = {Prover, Verifier}
InputAudience(VerifierPrivate(_)) = {Verifier}
```

The audience is derived K2 meaning, never an authored disclosure flag. An
Interface may expose an input only to its exact audience. A Plan can read a
runtime public input only through the exact current `ProverView`; it has no
constructor for a verifier-private input.

### 2.2 Exact Interface codecs

An Interface codec is either structural by construction or selects one exact
same-regime General-codec law declaration:

```text
StructuralCodec =
    Identity(value_type)
  | Record {
      external_type: ValueType restricted to a K1 root record,
      semantic_type: ValueType restricted to a K1 root record,
      fields: CanonicalMap<field_ordinal, InterfaceCodecRef>
    }
  | Variant {
      external_type: ValueType restricted to a K1 root variant,
      semantic_type: ValueType restricted to a K1 root variant,
      cases: CanonicalMap<case_ordinal, InterfaceCodecRef>
    }
  | BoundedSequence {
      external_type: ValueType restricted to a K1 root sequence,
      semantic_type: ValueType restricted to a K1 root sequence,
      element: InterfaceCodecRef
    }

GeneralCodec = {
  law: ModuleDeclarationRef<"pir.interface-codec-law">
}

InterfaceCodecLawDeclaration = {
  external_type: ValueType,
  semantic_type: ValueType,
  encode: PortableAlgorithmRef,
  encode_evaluation: EvaluationContractId,
  decode: PortableAlgorithmRef,
  decode_evaluation: EvaluationContractId,
  certificate_verifier:
    None | Some {
      certificate_type: ValueType,
      checker: PortableAlgorithmRef,
      checker_evaluation: EvaluationContractId
    }
}

InterfaceCodecDecl = Structural(StructuralCodec) | General(GeneralCodec)
GeneralCodecRef = InterfaceCodecRef restricted to a `General` declaration

InterfaceDecodeResult(T) =
  RootVariant<[
    (0, RootRecord<[(0, RootNat[65535])]>),
    (1, T)
  ]>
CanonicalCodecLaw(C) := for all semantic x and external y,
  decode_C(y) = Decoded(x) iff y = encode_C(x)

GeneralCodecAdmissionEvidence(g: GeneralCodecRef) =
    DerivedExhaustive {
      maximum_pair_checks: Natural,
      per_request_limits: PortableEvaluationLimitsV0
    }
  | CheckedCertificate {
      certificate:
        CanonicalValue<ResolvedLaw(g).certificate_verifier.certificate_type>,
      per_request_limits: PortableEvaluationLimitsV0
    }
```

`ResolvedLaw(g)` is the exact admitted same-regime declaration named by
`g.law`; it is never a registry lookup or caller-selected body. The certificate
lane is formable only when its `certificate_verifier` is `Some`.

`Identity` is literal same-`ValueType` identity. Record and variant ordinals
must match exactly, their child maps cover every and only fields or cases, and
each child codec's external and semantic types equal the corresponding field
or case types. Bounded sequences have equal declared maxima and an element
codec with the two exact element types. `ExternalType` and `SemanticType` are
therefore derived structurally (`Identity(T)` yields `T,T`). Acyclic
earlier-codec references give the structural constructors the exact law by
induction.

The exact-used owner module for declaration kind `pir.interface-codec-law`
gives exactly the body above and the proposition `CanonicalCodecLaw`; the
proposition is fixed by the kind and is not an authored Boolean. The
declaration and every
algorithm it names use the Protocol's complete `B`, enter the exact-used module
closure, and determine a General codec's types and algorithms. Its encoder ABI
is `[semantic_type] -> external_type`; its decoder ABI is
`[external_type] -> InterfaceDecodeResult(semantic_type)`. Both are total,
failure-free K1 algorithms. If present, the certificate checker is total and
failure-free with ABI `[certificate_type] -> RootBool`, and the supported
declaration meaning makes `true` an affirmation of this exact law for the
fixed types and algorithm IDs.

`AdmitInterfaceCodecLawDeclaration` authenticates the exact module and
declaration under `DependentAdmissionBasis(P)`, validates precisely this body,
the same-regime references, exact-used closures, both codec ABIs and totality
contracts, and the optional verifier ABI and shape. Only its affirmative result may
form a General codec; wrong kind or regime, an unknown declaration body, or an
unclosed dependency retains the ordinary distinct K1 outcome.

`DerivedExhaustive` is available only when K1 derives both domains from its
closed root grammar (`Unit`, `Bool`, bounded naturals, bounded integers,
bounded bytes or symbols, and recursively bounded sequence, record, or
variant) and can enumerate every canonical datum once in canonical-body order.
Admission evaluates the iff law over the Cartesian product and requires its
derived cardinality not to exceed `maximum_pair_checks`. It never consults a
module-supplied enumeration. `CheckedCertificate` requires the declaration's
exact verifier and an affirmative evaluation on the supplied certificate.
An exhausted pair-check or portable-evaluation limit is
`DeterministicLimitExceeded`, not a negative law result or identity change.
When neither lane is formable or supported, General-codec admission returns
`Unsupported(UnclosedGeneralCodecLaw)`; a sample, producer assertion, or bare
Boolean cannot close it.

The law declaration is semantic selection and therefore enters Interface
identity. `GeneralCodecAdmissionEvidence`, its certificate, pair-check bound,
and evaluation limits are non-identity admission inputs. The admitted handle
may retain their checked result, but cold admission must resupply and recheck
them; changing them cannot change `ProtocolInterfaceId`.

The iff law forbids aliases: an external value decodes successfully exactly
when it is the unique canonical encoding of its semantic value. All other
external values decode to `Malformed`; missing support or checker failure is
not malformed input. A codec cannot add a default, restriction, policy read,
transcript frame, or Protocol transition.

### 2.3 External keys and slots

`ExternalKey` and `WitnessSurfaceKey` are nonempty bounded K1 `MetaSymbol`
values. The shared regime supplies only their canonical carrier; their spelling
is semantic only inside the exact owner-local profiled subject that contains
them and is never Core meaning.

```text
ExternalValueSlot = {
  key: ExternalKey,
  codec: InterfaceCodecRef
}
```

Keys are unique. A slot denotes one external value under its codec. Direction,
role, active/inactive meaning, and K2 target come from its exact uses below,
not from mutable host metadata. Every declared slot must be used by invocation
assignment, Statement presentation, or transport/completion presentation. An
unreferenced slot refuses admission.

Every slot has exactly one `SlotOrigin`:

```text
SlotOrigin =
    ExternalSupply
  | StatementExposure(BindingRef)
  | TransportProduction(TransportTarget)
  | CompletionProduction(CompletionPayloadCoordinate)
```

`SlotOrigin` is derived during admission from the slot's complete inverse-use
set; it is not an additional identity field.

An `ExternalSupply` slot is decoded once and may have a nonempty inverse fibre
of invocation targets. Every target in that fibre must have the same exact
semantic type and derived audience; copying the decoded value to those targets
is the asserted equality. A `SuppliesInvocation` Statement member merely
annotates one public-input target already in this fibre and creates no second
origin. Every protocol-produced slot has exactly one binding, transport, or
completion coordinate. It cannot also supply invocation input, combine two
coordinates, or alias a differently visible origin merely because runtime
values happen to be equal.

### 2.4 Retained basis equality

For an exact live `AdmittedProtocol P`, let `B_P` and `E_P` be its retained
complete authenticated `PriorMetaAuthenticationBasis` and evaluator identity.
`DependentAdmissionBasis(P)` means byte-for-byte equality with `B_P`, identity
with the same live evaluator `E_P`, and dependency/support checks performed by
that evaluator under that basis. Equality of a regime ID, digest, or advertised
support is insufficient. Every `B` in an Interface, Plan, or derived-surface
identity equation below is exactly `B_P`.

Interface admission, Plan admission, and `PlanRealizes` accept only this
basis. Their admitted or checked handles retain the exact Protocol handle,
`B_P`, and `E_P`. Serialization transfers none of that authority. Under a new
evaluator, a cold consumer must reauthenticate and readmit the Protocol first,
then reauthenticate and readmit the Interface or Plan and recheck General-codec
evidence or `PlanRealizes`. An old ID, result, or handle cannot be paired with
the new evaluator.

## 3. `ProtocolInterface`

### 3.1 Complete subject

```text
ProtocolInterface = {
  protocol_id: ProtocolId,
  codecs: CanonicalSeq<InterfaceCodecDecl>,
  external_slots: CanonicalSeq<ExternalValueSlot>,
  invocation_assignment:
    TotalMap<InvocationInputRef, ExternalSlotRef>,
  statement_members: CanonicalSeq<StatementMember>,
  transport_entries: CanonicalSeq<RoleTransportEntry>,
  completion_entries: CanonicalSeq<CompletionEntry>
}
```

The codec sequence is exactly used: every codec is referenced and every
reachable algorithm, evaluation contract, value domain, primitive, and module
dependency is authenticated through K1. No second dependency graph or opaque
ABI exists here.

### 3.2 Total invocation assignment

`invocation_assignment` covers every and only the keys of both total maps in
K2 `CoreInvocation`:

```text
Domain(invocation_assignment) =
  { Public(p) | p in core.public_inputs }
  union
  { VerifierPrivate(v) | v in core.verifier_private_inputs }
```

For every entry, the slot codec's `semantic_type` equals the exact declared
input type. Decoding all assigned slots constructs one complete
`CoreInvocation`; missing, extra, wrong-type, or malformed values cannot
construct a partial invocation.

One slot may intentionally supply several inputs only when their exact types
and derived audiences agree. This explicit inverse fibre asserts value
equality. Reusing one slot for public and verifier-private targets refuses,
even when their value types are equal. A verifier-private slot cannot be a
Statement member or Prover-facing transport entry.

### 3.3 Scoped Statement presentation

K2 Statement occurrences are `PublicBindingDecl`s, not input-port labels. A
Statement may bind a public input, a constant, a derived value, or an earlier
public occurrence output, and one semantic value may be bound in several
scopes. Interface therefore uses an occurrence graph rather than a bijection
between fields and inputs:

```text
StatementFlow =
    SuppliesInvocation(PublicInputRef)
  | ExposesOpenedBinding

StatementMember = {
  slot: ExternalSlotRef,
  binding: BindingRef restricted to class Statement,
  flow: StatementFlow
}
```

For `SuppliesInvocation(p)`, the binding value is exactly `PublicInput(p)` and
the invocation assignment maps `Public(p)` to the same slot. For
`ExposesOpenedBinding`, the slot encoder is applied to the exact canonical
value recorded by `PublicBindingOpened(binding, value)` after that scope
opens. In both cases the codec semantic type equals the binding value type.

Define `StatementCoverage(I,C)` as:

1. every `statement_members` entry names an exact K2 Statement `BindingRef`;
2. every K2 Statement `BindingRef` has at least one member;
3. every member has exactly one slot, binding, and flow;
4. duplicate `(slot,binding,flow)` entries refuse; and
5. all equality and derivation claims are the two exact laws above.

Several `SuppliesInvocation` bindings may annotate one `ExternalSupply` slot
only when every associated public input is in that slot's exact inverse fibre.
Several separately keyed slots may expose one binding, but one
protocol-produced slot cannot combine distinct bindings. Equal values never
collapse distinct `BindingRef`s. A caller-created value, bare content ID, or
successful run replay cannot replace the exact binding occurrence. Relations
later owns relation-instance correspondence and execution grounding; Interface
establishes no relation or witness claim.

### 3.4 Role-qualified transport

```text
TransportTarget =
    MessageOccurrence(OccurrenceRef)
  | ChallengeOccurrence(OccurrenceRef)
  | OraclePublication(OccurrenceRef)
  | OracleQuery(OccurrenceRef)
  | OracleAnswer(OccurrenceRef)
  | ModuleObservation(OccurrenceRef, observation_ordinal)

TransportSemanticValue(T) =
  RootVariant<[(0, RootUnit), (1, T)]> // Inactive | Active(T)

RoleTransportEntry = {
  target: TransportTarget,
  source: Prover | Verifier | PublicDerivation,
  destination: Prover | Verifier | ExternalApplication,
  value_slot: ExternalSlotRef
}
```

For every formable target, source and destinations are the following total
owner-derived functions; an authored role never overrides them:

| Exact K2 target | `ExpectedTransportSource` | `AllowedTransportDestinations` |
|---|---|---|
| `ProverMessage` | `Prover` | `{Prover, Verifier, ExternalApplication}` |
| `DeterministicVerifierMessage` | `Verifier` | `{Prover, Verifier, ExternalApplication}` |
| Fresh Challenge | `Verifier` | `{Prover, Verifier, ExternalApplication}` |
| FS Challenge | `PublicDerivation` | `{Prover, Verifier, ExternalApplication}` |
| Oracle publication | `Prover` | `{Prover, Verifier, ExternalApplication}` |
| Public Oracle query or answer | `Verifier` | `{Prover, Verifier, ExternalApplication}` |
| Verifier-only Oracle query or answer | `Verifier` | `{Verifier}` |
| supported module observation with `ProverDecision` or `ProverPublication` | `Prover` | its exact K2-visible party set, plus `ExternalApplication` iff exported public |
| supported module observation with `NoProverDecision` | `Verifier` | its exact K2-visible party set, plus `ExternalApplication` iff exported public |

A module occurrence that does not export the named observation, visibility,
type, replay law, and one closed K2 decision class is not a formable target.
Admission requires
`entry.source = ExpectedTransportSource(entry.target)` and
`entry.destination` to be a member of
`AllowedTransportDestinations(entry.target)`; this is the complete legality
table.

The target's actor, visibility, value type, guard occurrence, and semantic
order are derived from exact owner-issued K2 `EffectView` and `ExecutionView`
projections with their matching fresh capabilities. `EffectView` supplies the
Core occurrence/value closure; the Protocol-scoped `ExecutionView` supplies the
selected Fresh or Fiat--Shamir interpretation and cannot alias the other
Protocol over the same Core.
Every transport slot has semantic type
`TransportSemanticValue(TargetType(target))`, including an unguarded target.
Its semantic value is `Active(v)` exactly when that occurrence is active and
has produced `v`; otherwise it is `Inactive`. Thus a prior Core terminal or FS
interpretation failure makes every not-yet-executed target `Inactive` without
an `AlwaysOccurs` assertion. Admission requires exact type, legal
source/destination visibility, a unique target/role/value use, and this exact
presence law. Absence can never decode as an active value.

Whether `Inactive` is emitted as an omitted field, explicit tag, or fixed wire
slot is not Interface semantics. K3-D OIR preserves this uniform semantic
value and its exact transport obligation; Stage 4B execution or a concrete
Realization profile selects the wire representation and proves it implements
that value. In particular, an FS
challenge is locally derived and never an externally supplied challenge; a
Fresh challenge is Verifier-sourced only after its exact receipt exists.

Transport entries describe external representation. They do not define FS
framing, prove endpoint sufficiency, or assert that a concrete OIR realizes the
transport. K3-D owns that exact read and coverage judgment.

### 3.5 Completion presentation

```text
CompletionTarget =
    CoreTerminal(TerminalRef)
  | FiatShamirInterpretationFailure

CompletionPayloadCoordinate =
    TerminalPublicOutput(TerminalRef, output_ordinal)
  | FSFailureDomainPayload
  | FSFailureChallenge
  | FSFailurePrefixReceiptCount
  | FSFailurePrefixState
  | FSFailureDraws
  | FSFailureFinalState

CompletionEntry = {
  target: CompletionTarget,
  external_tag: ExternalKey,
  payload_bindings:
    CanonicalMap<CompletionPayloadCoordinate, ExternalSlotRef>
}
```

Completion entries are total and injectively tagged over the exact completed
record family admitted by the Protocol:

- one `CoreTerminal(t)` entry exists for every and only `TerminalRef`; its
  map domain is every and only
  `TerminalPublicOutput(t, output_ordinal)` from that terminal declaration; and
- a canonical-framed FS Protocol has exactly one interpretation-failure entry
  whose map domain is exactly the six `FSFailure*` coordinates above; a Fresh
  Protocol has none. A duplex Protocol is not formable under this profile.

`TerminalPublicOutput(t,o)` selects the exact canonical value and K2
`ValueType` of the `o`th public output of `t`. For a canonical-framed FS
Protocol the failure coordinates select, without omission or reordering:

1. the payload of the construction's exact
   `sampling_exhausted_failure` `DomainFailure`, represented at
   `SamplingExhaustedPayloadType` (the declaration coordinate is already fixed
   by `ProtocolId`);
2. the receipt challenge injected at `FSChallengeRefType`;
3. `prefix_receipt_count` injected at the exact K1 root natural type
   `Nat(2^20)`;
4. `prefix_state` at `TranscriptStateType`;
5. `draws` at
   `RootSeq<FSDrawReceiptPresentationType, 2^20>`; and
6. `final_state` at `TranscriptStateType`.

`FSDrawReceiptPresentationType` is the exact K1 root record, in receipt-field
order, of `FSChallengeRefType`, `Nat(2^20)`, `Nat(2^20)`,
`TranscriptBytesType`, `TranscriptStateType`, `TranscriptStateType`,
`TranscriptBytesType`, and `RootBool`. Its canonical value is the fieldwise K1
injection of `challenge`, `draw_ordinal`, `requested_bytes`, `namespace`,
`pre_state`, `post_state`, `output`, and `accepted`; the admitted FS bounds
make every injection total. The draws sequence is nonempty and has exactly the
receipt's admitted order and length. Each payload slot codec's semantic type
must equal its coordinate's type exactly. A slot binds one coordinate only.
The Core-terminal and FS-failure variants remain disjoint completed records;
this presentation cannot turn one into the other.

`StrategyStopped`, missing capabilities, unsupported semantics, deterministic
limit exhaustion, and checker failure are not completion entries or terminal
tags. A later runtime API may report them only in their qualified
noncompletion plane.

### 3.6 Identity and admission

```text
ProtocolInterfaceId =
  ProfiledSemanticId<"pir.protocol-interface">(
    B, PIRInterfacePlanProfileId,
    ProtocolInterfaceBody(interface))

AuthenticateProtocolInterface(
  raw, exact AdmittedProtocol P,
  exact dependency preimages under DependentAdmissionBasis(P))
  -> AuthenticatedProtocolInterfaceCandidate

AdmitProtocolInterface(
  authenticated candidate,
  exact AdmittedProtocol P,
  exact DependentAdmissionBasis(P),
  TotalMap<GeneralCodecRef g, GeneralCodecAdmissionEvidence(g)>)
  -> QualifiedAdmission<AdmittedProtocolInterface>
```

After generic K1 authentication, admission checks in order:

1. exact Protocol identity, retained-basis/evaluator equality, and every local
   reference;
2. exact-used codecs, structural formation or same-regime General law
   declaration, exact evidence-map coverage, ABI, totality, and exact iff law;
3. total public plus verifier-private invocation assignment and audience
   confinement;
4. `StatementCoverage` and flow laws;
5. transport target, type, role, visibility, uniform semantic-presence, and
   FS/Fresh laws;
6. total completion variants, tags, and payloads;
7. exact slot-use closure; and
8. noninterference with all K2-owned meaning.

Only a completed affirmative admission mints an `AdmittedProtocolInterface`.
The ordinary qualified K1/PIR outcome partition remains intact.

### 3.7 Exact owner view for downstream reads

`ProtocolInterfaceBody` remains the only Interface meaning. PIR exports an
attenuated field projection rather than letting Relations or Analysis recreate
codec, slot, assignment, member, or transport facts:

```text
ProtocolInterfaceOwnerViewCoordinate =
  ProtocolInterfaceView(ProtocolInterfaceId)

ProtocolInterfaceOwnerFieldCoordinate = {
  view_coordinate: ProtocolInterfaceOwnerViewCoordinate,
  path: NonEmptyFiniteSeq<PIRViewPathStep>,
  boundary: PIRViewAtomicBoundary
}

ProtocolInterfaceOwnerReadManifest =
  CanonicalNonEmptySortedUniqueSeq<ProtocolInterfaceOwnerFieldCoordinate>

ProtocolInterfaceOwnerViewProjection = {
  coordinate: ProtocolInterfaceOwnerViewCoordinate,
  manifest: ProtocolInterfaceOwnerReadManifest,
  entries:
    CanonicalMap<ProtocolInterfaceOwnerFieldCoordinate,exact Interface leaf>
}
```

The path and atomic-boundary grammars are imported from
[PIR-owned source views](interactive-core.md#131-common-view-schema-coordinates-and-projection-law).
They resolve against the exact `ProtocolInterfaceBody` schema; free names,
reflection, and consumer-defined fields do not form.

`RequiredProtocolInterfaceReadClosure` is the least exact field closure with
these rules:

1. an invocation assignment closes to its target input, external slot, slot
   origin, semantic type, and codec;
2. a Statement member closes to its slot, binding/flow, origin, type, codec,
   and any `SuppliesInvocation` assignment;
3. a transport or completion entry closes to its exact target, slot, origin,
   type, codec, presence/payload law, and role or tag closure;
4. an external slot closes to every inverse use that derives its unique
   `SlotOrigin` and to its codec; and
5. a codec closes transitively over every structural child, exact K1 ABI,
   algorithm/evaluation/declaration dependency, and General-codec law
   coordinate. General-codec evidence remains admission authority and is not
   copied into Interface meaning.

```text
IssueProtocolInterfaceView(
  exact AdmittedProtocolInterface,
  exact inert admitted-Interface authority binding,
  matching fresh Interface admission capability,
  exact ProtocolInterfaceOwnerReadManifest,
  exact PIR evaluator and limits)
    -> Affirmative({
         ProtocolInterfaceOwnerViewProjection,
         ExactProtocolInterfaceViewAuthorityBinding
           = OwnerLocalSourceAuthorityBinding,
         ProtocolInterfaceViewCapability
       })
       | Unsupported | MissingDependency | KindMismatch | Malformed | Refused
       | DeterministicLimitExceeded | CheckerFailure
```

Issuance independently derives the closure and requires requested, realized,
and returned field sets to be identical. Missing closure is
`MissingDependency`; extra, duplicate, aliased, reordered, or unused fields are
`Malformed`; wrong subject, admission, evidence binding, purpose, or stale
capability is `Refused`. Only Affirmative returns a projection, project-wide
inert source binding, and fresh process-local capability. The binding has
owner `"pir"`, family `"interface-correspondence-view"`, and the exact projection object as
its local coordinate. Its Interface/Plan-profiled payload binds the source
Interface and closed manifest; its explicit no-policy declaration, policy
closure, and owner requirement name the exact typed consumer and purpose. The
capability retains that exact envelope object. The binding, capability, and
issued aggregate are noncopyable and nonserializable; only the identical live
bearer may be delegated, and reconstructed, cross-family, or cross-purpose
substitutes refuse. No downstream correspondence result can mint or widen
them.

As in the common PIR source-view law, the supplied consumer and purpose are
arbitrary exact same-regime downstream `TypedContentId` coordinates. The owner
wraps them separately as Interface/Plan-profiled `pir.source-consumer` and
`pir.source-purpose` IDs over `(family,ContentRef(coordinate))`; payload and
requirement identities use those nominal roles, while the live capability
retains and exactly compares the original coordinates. No downstream kind
union is imported into PIR, and swapping the two roles changes authority.

## 4. `ProverPlan`

### 4.1 Boundary and complete subject

A Plan describes the semantic dataflow needed to propose legal K2 prover
moves and, when declared, to derive bounded private outputs after one exact
`Accept` terminal. It contains no relation definition, relation interface,
relation-owned reference, runtime parameter value, witness value, random
value, supplier handle, executable callback, credential, buffer, thread
schedule, search queue, cache, cost target, resource choice, or mutable host
object.

```text
PrivateMaterialKind =
    WitnessIngress
  | Advice
  | ConfidentialContext

PrivateMaterialDecl = {
  key: WitnessSurfaceKey,
  kind: PrivateMaterialKind,
  value_type: ValueType
}

PrivateRandomnessRequirement = {
  value_type: ValueType,
  first_available_at: ProverDecisionPointRef
}

StateInitialValue =
    PrivateMaterial(PrivateMaterialRef)
  | Constant(CanonicalValue<state value type>)

StrategyStateSlot = {
  value_type: ValueType,
  initial: StateInitialValue
}

PlanRecipeSiteRef =
    DecisionSite(ProverDecisionPointRef)
  | AcceptedTerminalSite(TerminalRef)

ProverPlan = {
  protocol_id: ProtocolId,
  private_material: CanonicalSeq<PrivateMaterialDecl>,
  randomness_requirements: CanonicalSeq<PrivateRandomnessRequirement>,
  persistent_state: CanonicalSeq<StrategyStateSlot>,
  decision_recipes:
    CanonicalMap<ProverDecisionPointRef, DecisionRecipe>,
  derived_witness_exports: CanonicalSeq<DerivedWitnessExport>,
  accepted_terminal_recipes:
    CanonicalMap<TerminalRef, AcceptedTerminalRecipe>
}
```

Every `PrivateRandomnessRequirement` becomes available at a Core
`ProverDecisionPointRef`. It therefore cannot generate duplex-sponge salt,
which exists before the first Core decision and is construction-public rather
than private strategy state. Supporting that sibling requires a separate
construction-material Plan satellite and checked realization judgment; adding
a fake decision or Core message would change the source interaction.

`WitnessIngress` is a generic private-material class, not an assertion that a
value satisfies or corresponds to any relation. `Advice` is private
nonwitness material. `ConfidentialContext` is private static context. Surface
keys are unique across `WitnessIngress` material and derived witness exports.
Relations may later attach one of these generic coordinates to a relation-
owned witness occurrence through a separate checked subject; there is no
Relations-to-Plan authority edge in Plan formation or admission.

There is no public Plan-parameter lane. A value read by verifier behavior or
strong Fiat--Shamir belongs in Core as an exact `PublicParameter`. A public
prover-only value fixed for one Plan is an exact typed `Constant` and therefore
specializes `ProverPlanId`. Advice, confidential context, or ambient registry
lookup cannot be used to evade this distinction. Parametric substitution is a
separate deferred design and contributes no field, operand, runtime assignment,
or endpoint ingress to this profile.

### 4.2 Site-qualified recipes

Plan owns this closed read grammar. Decision-site reads map to one exact
InteractiveCore `ProverView`; accepted-terminal reads use a separate
constructor-wise owner predicate:

```text
PlanReadCoordinate =
    StaticConstant(ConstantRef)
  | OpenPublicInput(PublicInputRef)
  | OpenedBinding(BindingRef)
  | ObservedMessage(OccurrenceRef)
  | ObservedChallenge(OccurrenceRef)
  | ObservedOraclePublication(OccurrenceRef)
  | ObservedOracleQuery(OccurrenceRef)
  | ObservedOracleAnswer(OccurrenceRef)
  | ObservedModuleValue(OccurrenceRef, observation_ordinal)
  | PriorOwnMove(ProverDecisionPointRef)
  | AcceptedTerminalPublicOutput(output_ordinal)
```

The mapping to K2 is total and constructor-preserving except for the one local
name shown explicitly:

```text
K2ReadOf(StaticConstant(x))            = K2.StaticConstant(x)
K2ReadOf(OpenPublicInput(x))           = K2.PublicInvocationInput(x)
K2ReadOf(OpenedBinding(x))             = K2.OpenedBinding(x)
K2ReadOf(ObservedMessage(x))           = K2.ObservedMessage(x)
K2ReadOf(ObservedChallenge(x))         = K2.ObservedChallenge(x)
K2ReadOf(ObservedOraclePublication(x)) = K2.ObservedOraclePublication(x)
K2ReadOf(ObservedOracleQuery(x))       = K2.ObservedOracleQuery(x)
K2ReadOf(ObservedOracleAnswer(x))      = K2.ObservedOracleAnswer(x)
K2ReadOf(ObservedModuleValue(x,n))     = K2.ObservedModuleValue(x,n)
K2ReadOf(PriorOwnMove(d))              = K2.PriorOwnMove(d)

AvailableDecisionRead(P,d,c) iff
  d is an exact decision of admitted Protocol P and
  K2.GuaranteedProverRead(d, K2ReadOf(c)) = true
    in P's exact StrategyDecisionView
```

`K2ReadOf` is undefined for `AcceptedTerminalPublicOutput`; that constructor
is legal only at the identical accepted-terminal site described below.

This is an alias of the InteractiveCore owner table, not a second path
analysis. It inherits InteractiveCore's exact type, source, visibility, order,
scope-opening, and guard-implication rules. Membership in one runtime view, a
replay sample, or a Plan assertion cannot widen it.

For one admitted `Accept` terminal, availability is derived constructor by
constructor from the exact InteractiveCore owner views rather than from generic
history membership:

```text
TerminalOccurrence(P.core,t) =
  the unique admitted OccurrenceRef whose effect is ReachTerminal(t)

AvailableAcceptedTerminalRead(P,t,StaticConstant(c)) = true
  exactly when c is an exact admitted Core constant

AvailableAcceptedTerminalRead(P,t,OpenPublicInput(i)) = true
  exactly when ProverInputOpening(i) is no later than
  BeforeOccurrence(TerminalOccurrence(P.core,t)) and its complete opening
  path is guaranteed on the t-active path

AvailableAcceptedTerminalRead(P,t,OpenedBinding(b)) = true
  under the analogous exact binding-opening and t-path law

AvailableAcceptedTerminalRead(P,t,Observed*(o,...)) = true
  exactly when o precedes TerminalOccurrence(P.core,t), has the requested
  source kind/type and Prover visibility, every source scope is guaranteed
  open on the t-active path, and
  GuardImplies(guard(t),guard(o))

AvailableAcceptedTerminalRead(P,t,PriorOwnMove(d)) = true
  under that same law and only when d is an exact earlier Prover decision

AvailableAcceptedTerminalRead(
  P,t,AcceptedTerminalPublicOutput(n)) = true
  exactly when n is an in-range public-output ordinal of t
```

`Observed*` expands exactly to the six Message, Challenge, Oracle
publication/query/answer, and module-observation constructors. Every arm also
requires `t` to be an admitted `Accept` terminal. `guard(t)` is the guard of
its terminal occurrence. Failure to derive the constructive scope, order, and
guard implication is unavailability even when no sample run reaches `t`.

```text
RecipeOperand =
    PlanRead(PlanReadCoordinate)
  | PrivateMaterial(PrivateMaterialRef)
  | PrivateRandomness(PrivateRandomnessRequirementRef)
  | StateBefore(StrategyStateSlotRef)
  | Constant(CanonicalValue<declared type>)
  | NodeOutput(RecipeNodeRef)

RecipeNode = {
  algorithm: PortableAlgorithmRef,
  evaluation: EvaluationContractId,
  inputs: CanonicalSeq<RecipeOperand>,
  output_type: ValueType
}

RecipeValueRef = RecipeOperand restricted to value-producing variants

StateAfterBinding =
    KeepState
  | ReplaceState(RecipeValueRef)

DecisionRecipe = {
  nodes: CanonicalSeq<RecipeNode>,
  move: ProverMoveBinding,
  state_after:
    TotalMap<StrategyStateSlotRef, StateAfterBinding>
}

AcceptedTerminalRecipe = {
  nodes: CanonicalSeq<RecipeNode>
}

ProverMoveBinding =
    MessageValue(RecipeValueRef)
  | OracleValue(RecipeValueRef)
  | ModuleMove(RecipeValueRef)

DerivedWitnessExport = {
  key: WitnessSurfaceKey,
  source_site: PlanRecipeSiteRef,
  value: RecipeValueRef,
  value_type: ValueType
}
```

Each recipe is a local acyclic graph evaluated only at its exact site. At a
decision, `PlanRead(c)` requires `AvailableDecisionRead`; at an accepted
terminal it requires `AvailableAcceptedTerminalRead`. It cannot name a whole
view, future history, another site's local node, or another inactive terminal.
`NodeOutput` is local to the selected site.

A randomness requirement is readable only at or after its declared first
decision boundary and may flow later only through explicit state or a local
node output. Direct `PrivateRandomness` is forbidden at an accepted terminal;
a value needed there must have been retained in a typed state slot during the
generated run. At a decision site, `StateBefore` reads the exact immutable
pre-step state owned by the Plan adapter. At an accepted-terminal site, it
reads the sealed state after the last active decision, or the exact initialized
state when no decision was active. It never reads a caller-mutable buffer, an
initial-state shortcut after an active decision, or a reconstruction from
`RunRecord`. An inactive decision performs no state update.

For a randomness requirement `r`, let `DirectUseSites(P,r)` be the sorted-
unique decision sites containing at least one direct
`PrivateRandomness(r)` operand occurrence. Operand occurrences include recipe
node inputs, move payloads, state replacements, and a
`DerivedWitnessExport.value` root at that exact source site; an export-only
read is therefore a real demand rather than an unaudited annotation.
`PathwiseOneShotRandomness(P,r)` holds exactly when every such site is no
earlier than `r.first_available_at` under InteractiveCore's owner order, and no
admitted Core path can activate two distinct sites in `DirectUseSites(P,r)`. Multiple
operands in one active site share the single value returned by that site's one
bearer consumption. A path with no active direct-use site does not consume the
bearer. If the declared boundary is inactive, the first later active
direct-use site may consume it; after that site, only an explicit state
replacement can carry the value. Plan admission rejects direct terminal use,
including an export root; `PlanRealizes` requires
`PathwiseOneShotRandomness` for every declared requirement.

An accepted-terminal recipe runs only after the exact terminal occurrence has
completed with static verdict `Accept`, after the ordinary `RunRecord` and
`CausalGenerationCapability` are fixed. It has no move or `state_after` arm. It
cannot publish a Message or Oracle, invoke a module effect, change a Core value,
modify a terminal payload, create a claim, alter a Challenge prefix, or write
hidden post-terminal state. It never runs on `Reject`, `Abort`, interpretation
failure, `StrategyStopped`, or another inactive `Accept` terminal.

Every node algorithm has the exact derived K1 ABI and one `output_type`, with
an empty semantic-failure row. Multiple results use one exact K1 record value.
A mathematical partial operation returns a tagged value and makes its branch
explicit in the recipe. Typed holes may be added only as an
exact supported Plan module constructor with complete input/output, read,
state, and OIR-projection laws; there is no opaque hole in the selected base
Plan.

`DerivedWitnessExport` names a typed Plan output that Relations may later
consider as a witness occurrence. It does not classify its derivation as
correct or its value as satisfying. Advice and confidential context never
silently become witness exports. Its `value` is interpreted only in the local
namespace named by `source_site`: `NodeOutput(n)` can name only node `n` of
that site's recipe, and `PlanRead(c)` must satisfy the corresponding decision-
or terminal-availability predicate. No local node or read of another site can
be captured by ordinal coincidence.

The terminal-recipe map may omit an `Accept` terminal when no private
completion output is declared there. Every present terminal recipe must own
at least one export; every terminal-scoped export must have exactly one
matching recipe; and every terminal recipe node must lie in the transitive
operand closure of at least one export at that site. Thus terminal evaluation
is export-rooted. An output-free recipe, dangling export, or dead terminal
node is malformed Plan structure. Equal-valued exports from two terminals
remain distinct site-owned occurrences.

### 4.3 Identity, admission, and `PlanRealizes`

```text
ProverPlanId =
  ProfiledSemanticId<"pir.prover-plan">(
    B, PIRInterfacePlanProfileId, ProverPlanBody(plan))

AuthenticateProverPlan(
  raw, exact AdmittedProtocol P,
  exact dependency preimages under DependentAdmissionBasis(P))
  -> AuthenticatedProverPlanCandidate

AdmitProverPlan(
  authenticated candidate,
  exact AdmittedProtocol P,
  exact DependentAdmissionBasis(P))
  -> QualifiedAdmission<AdmittedProverPlan>
```

Plan admission checks exact Protocol identity, retained-basis/evaluator
equality, reference formation, private witness-key uniqueness and material separation, randomness
boundaries, state typing and initialization, site-local DAG order, algorithm
ABIs, result types, decision move-binding shape, total decision state-after
maps, accepted-terminal verdict and no-move/no-update shape, terminal
recipe/export bijection, export-rooted terminal-node closure, witness-export
typing, exact-used dependency closure, and absence of ambient or realization-
only fields. Every used algorithm, evaluation, module, and type preimage
belongs to that closure. It does not establish decision coverage or read
availability against InteractiveCore; those remain an independent relation.

The cross-owner intake for that relation is one nonidentified operation
aggregate:

```text
PlanLifecycleReadBasis = {
  strategy_decisions: exact owner-issued StrategyDecisionView projection,
  public_bindings: exact owner-issued PublicBindingView projection,
  public_coins: exact owner-issued PublicCoinView projection,
  effects: exact owner-issued EffectView projection,
  authority_bindings:
    the four matching ExactPIRStaticViewAuthorityBinding objects,
  capabilities:
    four distinct matching fresh PIRStaticViewCapability objects,
    one for each view and authority binding
}
```

Each capability retains its own exact view, family, and matching authority
binding. All four view/binding/capability triples name the identical admitted
Core, retained admission basis, and evaluator and carry every and only the
closed fields required by the Plan reads. They are not mutually substitutable
or “identical capabilities.” `PlanLifecycleReadBasis` has no canonical body,
ID, serialization, or authority of its own; copied projections, reused
capabilities, or an incomplete set cannot form it.

```text
PlanRealizes(
  exact AdmittedProtocol P,
  exact AdmittedProverPlan,
  exact PlanLifecycleReadBasis,
  exact DependentAdmissionBasis(P))
  -> Qualified<Affirmative(CheckedPlanRealizes)
             | Negative(PlanRealizesReason)>
```

Negative is a completed answer to the formed cross-subject proposition, not a
catch-all validation error. The following closed coordinates and reason
algebra are the complete negative payload:

```text
RecipeUseRef =
    NodeInput(PlanRecipeSiteRef, RecipeNodeRef, input_ordinal)
  | MovePayload(ProverDecisionPointRef)
  | StateReplacement(ProverDecisionPointRef, StrategyStateSlotRef)
  | WitnessExportValue(DerivedWitnessExportRef)

DerivedWitnessExportRef =
  dense ordinal into the exact Plan's derived_witness_exports

PlanMoveShape =
    Message(ValueType)
  | Oracle(OracleRef, ValueType)
  | Module(ModuleEffectRef, ValueType)

PlanReadDisagreement =
    NotGuaranteedAtSite
  | TypeDisagreement {
      owner_type: ValueType,
      use_type: ValueType
    }
  | OriginDisagreement {
      requested: PlanReadCoordinate,
      owner_derived: PlanReadCoordinate
    }

PlanRealizesDisagreement =
    MissingDecisionRecipe(ProverDecisionPointRef)
  | SiteReadDisagreement {
      use: RecipeUseRef,
      site: PlanRecipeSiteRef,
      coordinate: PlanReadCoordinate,
      cause: PlanReadDisagreement
    }
  | OperandAvailabilityDisagreement {
      use: RecipeUseRef,
      operand: RecipeOperand
    }
  | MoveShapeDisagreement {
      decision: ProverDecisionPointRef,
      expected: PlanMoveShape,
      observed: PlanMoveShape
    }
  | WitnessExportValueUnavailable(DerivedWitnessExportRef)

PlanRealizesReason = {
  disagreements:
    NonEmptyCanonicalSortedUniqueSeq<PlanRealizesDisagreement>
}
```

`RecipeUseRef` is interpreted only in the exact Plan named by the invocation.
`use_type` is the exact type required by that node input, move, replacement,
or export declaration. `WitnessExportValue(e)` is interpreted at the exact
`source_site` of export `e` and names its root operand even when no recipe node
uses that operand. `PlanMoveShape` is derived twice rather than supplied:
`expected` comes from the InteractiveCore decision kind and exact module
occurrence, while `observed` comes
from the recipe constructor and the statically resolved payload type. Thus
one shape comparison covers the constructor, module coordinate, and payload
type without a caller-authored summary. The `Oracle` shape's type is exactly
the selected `OracleRef`'s owner-derived `OracleCarrierType`. A witness-export
coordinate is interpreted relative to its declared `source_site`, as in
Section 4.2. At a decision site, an owner-issued InteractiveCore coordinate is
mapped back through the exact constructor-preserving Plan/InteractiveCore map
before an origin disagreement is formed. At a terminal site, the owner
coordinate is derived independently by
`AvailableAcceptedTerminalRead`.

The checker emits every applicable atomic disagreement once, in written
variant-tag order and then canonical field-body order. Missing decision
recipes are emitted from exact set difference. An unexpected
`ProverDecisionPointRef`, duplicate key, or ill-formed key cannot reach this
relation because dependent-reference formation, `CanonicalMap` formation, and
Plan admission already reject it under their ordinary distinct outcome. A
dependent check is evaluated only after its coordinate
and required predecessor form. In particular, a missing source recipe is not
also reported as arbitrary downstream operand, move, or export disagreement.
Terminal recipe/export membership is already closed by Plan admission; only a
missing required decision recipe can suppress dependent reasons here.
This dependency order makes the negative payload deterministic rather than an
implementation-selected first error.

For `PrivateRandomness(r)`, deterministic availability additionally means
`PathwiseOneShotRandomness(P,r)`. Multiple operands at the same active site
share one consumption and do not disagree. At every later direct-use site for
which some admitted reaching path also activates an earlier distinct direct-
use site, the checker emits `OperandAvailabilityDisagreement` for each exact
operand use there in canonical use order. A later site reached only on paths
mutually exclusive with all earlier direct-use sites remains available.

The result is Affirmative exactly when this complete traversal emits no
disagreement, and Negative exactly when the resulting sequence is nonempty.

The nine checks below split across the qualified outcome boundary as follows:

| Check | Completed Negative | Never a negative reason |
|---|---|---|
| 1 | none | A wrong typed axis is `KindMismatch`; a well-formed handle for another Protocol, source authority, retained basis, or evaluator is `Refused`. An internally inconsistent admitted handle is `CheckerFailure`. |
| 2 | `MissingDecisionRecipe` | Duplicate or noncanonical map structure is `Malformed`; a formed key on a wrong owner/kind axis is `KindMismatch`, and a formed same-axis key that fails the dependent decision-point predicate is `Refused`. |
| 3 | `SiteReadDisagreement` for a formed owner coordinate | An ill-formed coordinate is `Malformed`; absent supported owner interpretation is `Unsupported`. |
| 4 | `OperandAvailabilityDisagreement` for a formed operand that is not available on every reaching path | Local node order, reference formation, and node ABI are Plan-admission postconditions; contradiction in an exact admitted handle is `CheckerFailure`. |
| 5 | `MoveShapeDisagreement` | An ill-formed move carrier is `Malformed`; an unsupported same-kind module decision is `Unsupported`. |
| 6 | availability failure is the check-4 reason above | Constructor-separated declared ingress is a Plan-admission postcondition; contradiction is `CheckerFailure`. |
| 7 | availability failure is the check-4 reason above | Total, type-preserving initialization and transition maps are Plan-admission postconditions; contradiction is `CheckerFailure`. |
| 8 | `WitnessExportValueUnavailable` when a formed export whose source recipe exists lacks an all-path value | A missing source recipe is already check 2. Wrong-recipe capture or a declared/resolved type mismatch contradicts Plan admission; a raw ill-formed local reference is `Malformed`, while contradiction in an admitted handle is `CheckerFailure`. |
| 9 | none | Authenticated-body membership and exact-used closure are Plan-admission postconditions; contradiction is `CheckerFailure`. |

At any point, a required named preimage that is absent yields
`MissingDependency`; a declared deterministic bound exhausted before the
complete disagreement set is computed yields `DeterministicLimitExceeded`.
Neither may mint a partial reason. A malformed request, unsupported meaning,
authority refusal, or checker failure likewise produces no
`PlanRealizesReason`. Conversely, every emitted reason cites only exact
coordinates in the retained admitted operands; it contains no diagnostic
string, ambient lookup, supplied Boolean, or live capability.

The completed relation checks:

1. exact Protocol IDs, source authority, retained basis, and evaluator identity
   match;
2. the recipe map covers every and only potential K2
   `ProverDecisionPoint` exactly once, including guarded points;
3. every `PlanRead(c)` satisfies owner-derived `AvailableDecisionRead` or
   `AvailableAcceptedTerminalRead`, according to its exact site, with exact
   type and origin on every path reaching that site;
4. every other operand is deterministically available before its use on every
   such path, every `NodeOutput` is earlier in the same site-local recipe,
   every randomness requirement satisfies `PathwiseOneShotRandomness`, direct
   terminal randomness is absent, and every node ABI is exact;
5. the move constructor, module coordinate, and payload type equal the K2
   legal move at that decision;
6. private material, randomness, and current state use only their distinct
   declared ingress;
7. state initialization and every active state transition are total and
   type-preserving;
8. each witness export, interpreted relative to `source_site`, names an
   all-path available same-type value or an earlier node in that exact local
   recipe;
   and
9. every Plan read is in the authenticated body and exact-used closure.

Verifier-private input, future history, ambient registry, clock, file, process
object, strategy capability, or mutable Core handle has no `RecipeOperand`
constructor. `PlanRealizes` therefore cannot affirm a route containing such a
read. A negative result is meaningful and distinct from unsupported semantics,
missing authority, malformed input, refusal, limit exhaustion, and checker
failure.

Affirmative `CheckedPlanRealizes` proves structural decision coverage, typed
site-local dataflow, causal read confinement, and state closure only. It
proves no algorithmic
correctness beyond the exact K1 denotations, witness correspondence or
satisfaction, random distribution, supplier fidelity, successful generation,
termination, completeness, cost, or cryptographic property.

### 4.4 Exact Plan adapter and accepted-terminal continuation

Plan execution is an owner-local wrapper around unchanged InteractiveCore
generation. The caller supplies the admitted Plan and its private authorities, never an
arbitrary strategy implementation:

```text
PlanPrivateMaterialInput =
    OrdinaryPrivateSupply(
      value: CanonicalValue<target declaration's exact ValueType>)
  | AcceptedContinuationHandoff(
      exact ReadyPlanWitnessIngressSupply,
      identical live ReadyPlanWitnessIngressSupplyCapability)

PlanPrivateMaterialInputMap =
  TotalMap<PrivateMaterialRef,PlanPrivateMaterialInput>

PlanPrivateRandomnessInput = {
  value: CanonicalValue<target requirement's exact ValueType>,
  reveal: fresh one-shot PlanRandomnessRevealRight
}

PlanPrivateRandomnessInputMap =
  TotalMap<PrivateRandomnessRequirementRef,PlanPrivateRandomnessInput>

FormPlanPrivateMaterialInputs(
  exact admitted ProverPlan plan,
  exact every-and-only private-material input entries)
    -> Affirmative({
         inputs: PlanPrivateMaterialInputMap,
         capability: PlanPrivateMaterialInputMapCapability
       })
     | Unsupported | MissingDependency | CannotAnswer | KindMismatch
     | Malformed | Refused | DeterministicLimitExceeded | CheckerFailure

FormPlanPrivateRandomnessInputs(
  exact admitted ProverPlan plan,
  exact every-and-only typed private randomness values)
    -> Affirmative({
         inputs: PlanPrivateRandomnessInputMap,
         capability: PlanPrivateRandomnessInputMapCapability
       })
     | Unsupported | MissingDependency | KindMismatch | Malformed | Refused
     | DeterministicLimitExceeded | CheckerFailure
```

Both maps are immutable, process-local snapshots. Their domains are exactly
the dense declaration coordinates of the admitted Plan: a missing, extra,
duplicate, reordered, aliased, or wrong-Plan entry is not a partial map.
Every value is fixed before execution and has the identical declared
`ValueType`. Formation copies no caller-mutable buffer and accepts no delayed
callback, file, registry, sampler, conversion, or value-producing closure.

The private-material map may use an ordinary fixed value for any declared
private-material kind. Its handoff arm forms only for an exact
`WitnessIngress` target and is defined in Section 4.5; `Advice` and
`ConfidentialContext` have no handoff arm. The randomness map creates one
fresh reveal right per exact requirement. The fixed randomness value remains
unavailable to the Plan adapter until its first actual operand demand at an
active site allowed by `PathwiseOneShotRandomness`; that demand consumes the
right once and caches the value only for that site-local DAG. A requirement
with no active demand is never revealed, and every unused right expires when
the session closes. These rules establish fixed input and one-shot access, not
randomness origin or distribution.

Each map capability is fresh, noncopyable, nonserializable, and bound to the
identical admitted Plan, complete map object, formation occurrence, lifetime,
and process generation. Formation of a map containing a handoff retains each
ready supply and its identical live capability without spending the supply.
Affirmative formation moves their exclusive custody into the map capability;
no caller-visible alias remains. A stale, spent, wrong-target, or cross-Plan
supply is `Refused`; a missing or expired otherwise matching live supply is
`CannotAnswer`; a wrong kind, regime, or `ValueType` is `KindMismatch`; and
malformed map structure is `Malformed`. No nonaffirmative formation result
moves, consumes, reveals, or returns a partial input or capability.

```text
PreparePlanExecution(
  exact admitted Protocol P,
  exact admitted ProverPlan plan,
  exact affirmative CheckedPlanRealizes(P,plan),
  exact CoreInvocation I,
  exact PlanPrivateMaterialInputMap private_inputs,
  identical live PlanPrivateMaterialInputMapCapability,
  exact PlanPrivateRandomnessInputMap randomness_inputs,
  identical live PlanPrivateRandomnessInputMapCapability,
  exact evaluator and deterministic limits)
    -> Affirmative({
         session: PreparedPlanExecution,
         capability: ReadyPlanExecutionCapability
       })
     | Unsupported | MissingDependency | CannotAnswer | KindMismatch
     | Malformed | Refused | DeterministicLimitExceeded | CheckerFailure

PlanStrategyStep(
  exact running PreparedPlanExecution S,
  identical internal PlanStrategyExecutionCapability,
  exact active ProverDecisionPoint d,
  identical ProverView V,
  exact adapter-private PlanExecutionState before_d)
    -> Produce(exact ProverMove for d,
               exact PlanExecutionState after_d)
     | Stop(qualified Plan strategy cause)
```

Preparation authenticates the identical Protocol, Plan, affirmative
`CheckedPlanRealizes`, invocation, both exact total maps and their identical
live capabilities, evaluator, and limits. It first validates the complete
request without consuming an input authority. Only when every check and every
state initializer can complete does one atomic commit consume both map
capabilities, every retained ready handoff supply and its capability, and
ownership of every randomness reveal right. A nonaffirmative result consumes
none of them and creates no private occurrence, handoff capability, session,
adapter, or partial initializer state.

On that commit both map objects transition from Ready to Consumed. The new
session retains their immutable value snapshots for execution and audit, not a
reusable map authority; neither map can prepare a second session.

That affirmative commit creates one fresh target private-material occurrence
for every declaration, even when two values are canonically equal. An ordinary
supply copies its fixed typed value. A handoff copies the identical source
export value without conversion and mints one fresh
`CausalPlanWitnessHandoffCapability` bound to its role-distinct exact source
and target endpoints. The commit also installs the unrevealed randomness
rights, evaluates every admitted state initializer against the fresh target
occurrences, and creates one process-local `PlanStrategyAdapter` plus one fresh
internal `PlanStrategyExecutionCapability`.

The adapter retains that capability and encloses the only InteractiveCore
`ProverStrategyCapability` that may represent this prepared Plan; neither
capability is a caller-supplied operation input or substitutable by the caller.
The internal capability authorizes callbacks only while that identical adapter
is Running and becomes unusable when the adapter closes. The prepared session
retains the exact input maps, fresh private-material occurrences, causal
handoff capabilities in target-reference order, adapter, initialized state,
remaining randomness rights, session occurrence, and process generation.

The two input maps, their map capabilities, all private-material occurrences,
randomness reveal rights, `PreparedPlanExecution`, both adapter capabilities,
`CausalPlanWitnessHandoffCapability`, and `ReadyPlanExecutionCapability` are
noncopyable, nonserializable, process-local objects with no canonical body or
semantic ID.
The ready capability is the only authority that may start generation and is
consumed atomically before the InteractiveCore executor is invoked. A stale,
copied, cross-Plan, cross-Protocol, cross-invocation, cross-evaluator, or
cross-session aggregate is
`Refused`; malformed authority collections are `Malformed`; wrong types or
regimes are `KindMismatch`; missing evaluator or dependency preimages are
`MissingDependency`; and a missing or expired otherwise matching input bearer
is `CannotAnswer`. No failure exposes a partial session or adapter.

The adapter implements InteractiveCore's existing
`StrategyStep(private_state,ProverView,private_randomness)` interface. Its
private state contains the exact Plan state vector, remaining randomness
rights, next-step occurrence, and decision-local trace. For each active
decision, `PlanStrategyStep` performs one indivisible transition:

1. authenticate `d`, `V`, and `before_d` against the same running session and
   select the unique admitted recipe through `CheckedPlanRealizes`;
2. materialize every and only its owner-derived public reads, exact private-
   material occurrences, typed constants, and pre-step state values;
3. consume each randomness reveal right exactly once at its first actual
   `PrivateRandomness` operand demand, including an export root, which must
   occur at or after its declared `first_available_at` decision; mere activity
   at that boundary does not consume it, the returned value is available
   throughout that site's local DAG, and any later-site use is possible only
   through an explicit state replacement made at the consuming site;
4. evaluate every recipe node in canonical order under the exact algorithm
   ABI, evaluation contract, tagged partial-operation law, evaluator, and
   deterministic limits;
5. construct the unique legal `ProverMove` selected by `ProverMoveBinding`,
   evaluate the total type-preserving `state_after` map, and resolve every
   decision-derived export root in canonical export order; and
6. atomically return `Produce(move,after_d)` while sealing every local node and
   resolved decision-derived export under the exact decision occurrence.

No move, state replacement, randomness consumption, or export becomes
authoritative before all six steps succeed. An unavailable operand, exhausted
right, wrong view, wrong move shape, evaluation noncompletion, or limit failure
returns `Stop` with its qualified Plan cause, closes the running adapter, and
exposes no partial step trace. There is no fallback to another strategy.

At a decision, `StateBefore(slot)` is exactly `before_d[slot]`. When
InteractiveCore execution reaches a terminal, the adapter accepts no further
strategy step and seals the exact state after the last active decision, or the exact initialized state if no
decision was active, as `final_plan_state`. At an accepted-terminal recipe,
`StateBefore(slot)` is exactly `final_plan_state[slot]`.

For one admitted Plan, affirmative `CheckedPlanRealizes`, and admitted `Accept`
terminal `t`, derive:

```text
AcceptedPlanContinuationArm(P,plan,t) =
  CanonicalSortedUniqueSeq<DerivedWitnessExportRef>
```

The arm contains every and only export whose source is either a decision site
that the exact InteractiveCore scope/order/guard laws guarantee active before
`t`, or the accepted-terminal site `t` itself. A decision export may belong to several
terminal arms when it is guaranteed on each path. An export owned by another
terminal and a conditionally active decision export not guaranteed on `t`'s
path are absent. An empty derived sequence means that terminal has no Plan
continuation arm; it is not an active empty runtime value.

```text
AcceptedPlanContinuationDisposition =
    NoAcceptedPlanContinuation
  | PendingAcceptedPlanContinuation(
      terminal: TerminalRef,
      right: AcceptedPlanContinuationRight)

GeneratePlanRun(
  exact PreparedPlanExecution S,
  identical live ReadyPlanExecutionCapability for S,
  exact initial-Oracle, challenge-resolver, check, and extension capabilities
    required by S.protocol,
  exact S.execution_evaluation_control)
    -> CompletedPlanRun(
         RunRecord(S.protocol),
         CausalGenerationCapability,
         CausalPlanGenerationCapability,
         AcceptedPlanContinuationDisposition)
     | InterpretationFailed(ProtocolFailureRecord(S.protocol))
     | StrategyStopped(PartialRunRecord(S.protocol), qualified Plan cause)
     | qualified operational noncompletion

CompleteAcceptedPlanContinuation(
  exact CompletedPlanRun G whose RunRecord reaches Accept terminal t,
  identical live CausalPlanGenerationCapability,
  identical live AcceptedPlanContinuationRight from G,
  exact continuation evaluation control using G's identical evaluator)
    -> Affirmative(CompletedPlanContinuation(t,active_arm_outputs),
                   CausalPlanContinuationCapability)
     | Unsupported | MissingDependency | KindMismatch | Malformed | Refused
     | DeterministicLimitExceeded | CheckerFailure
```

`GeneratePlanRun` consumes the ready capability once and passes only the
enclosed Plan adapter capability to unchanged `GenerateRun`. Only
`GenerateRun`'s `CompletedRun` branch mints
`CausalPlanGenerationCapability`. That Plan-owned capability retains the exact
prepared session, adapter, returned record object,
`CausalGenerationCapability`, evaluator, all active decision-local values and
exports,
sealed `final_plan_state`, and every target-side
`CausalPlanWitnessHandoffCapability` created at preparation. The handoff
capabilities remain distinct entries and cannot collapse merely because source
or target IDs or values compare equal. It contains no second ready, input-map,
supply, or randomness right. Interpretation failure, strategy stop, and every
operational noncompletion close the adapter and mint no Plan-generation
capability; their closed session cannot export its retained handoff
capabilities.

The pending continuation arm is formed exactly when the reached terminal is
`Accept` and `AcceptedPlanContinuationArm` is nonempty. Its right is linear and
consumed when continuation completion begins. The operation reads decision-
derived values only from the sealed adapter trace, evaluates only the missing
export-rooted accepted-terminal node closure against `final_plan_state`, and
issues every and only output in the selected arm atomically. Success and every
noncompletion close the right. No failure issues a partial arm or permits retry
against the same generated run. Other terminal arms are inactive and provide
neither values nor access authority.

`CompletedPlanContinuation` contains the private process-local output values.
Its fresh noncopyable `CausalPlanContinuationCapability` retains the identical
Plan-generation capability, prepared session, invocation, Plan,
`CheckedPlanRealizes`, record, `CausalGenerationCapability`, reached terminal,
selected arm, evaluator, limits, and consumed-right occurrence. Neither has a canonical
semantic ID. Equal records, output tuples, values, digests, or reconstructed
aggregates grant no authority.

Core and Plan completion remain two planes. Continuation noncompletion after
Core `Accept` leaves the accepted `RunRecord` and `CausalGenerationCapability`
intact but issues no continuation arm. It cannot rewrite Accept to Reject,
erase the
record, or expose a partial arm. Reject, Abort, interpretation failure, and
strategy stop select no accepted continuation.

The complete Plan-owned lifecycle is
`Prepared/Ready -> Running -> Completed/Closed`, followed, when present, by
`PendingContinuation -> Continued/Closed`. No state is both reusable for
generation and authoritative for completion. Generic `ReplayRun` remains
Protocol replay: it never executes Plan recipes or mints Plan-generation or
continuation authority. There is no cold Plan-recomputation operation. A fresh
prepare/generate/complete sequence creates fresh occurrences and capabilities
even when its record bytes and output values equal an earlier run.

### 4.5 Accepted-continuation witness handoff

One accepted continuation export may directly supply one later Plan's exact
`WitnessIngress` declaration without becoming public, serialized, or
reclassified as ambient advice. The source and target coordinates are separate
role-tagged process-local endpoints:

```text
AcceptedPlanWitnessHandoffSourceEndpoint = {
  source_protocol: exact admitted Protocol,
  source_plan: exact admitted ProverPlan,
  source_invocation: exact completed invocation occurrence,
  source_continuation: exact CompletedPlanContinuation occurrence,
  accepted_terminal: TerminalRef,
  source_export: DerivedWitnessExportRef,
  source_output: exact active continuation output occurrence
}

AcceptedPlanWitnessHandoffTargetEndpoint = {
  target_protocol: exact admitted Protocol,
  target_plan: exact admitted ProverPlan,
  target_private_material: PrivateMaterialRef,
  target_key: WitnessSurfaceKey
}

ReadyPlanWitnessIngressSupply = {
  source: AcceptedPlanWitnessHandoffSourceEndpoint,
  target: AcceptedPlanWitnessHandoffTargetEndpoint,
  value_type: ValueType,
  private_value: exact source export value,
  issuance_occurrence: fresh process-local occurrence
}

IssueAcceptedPlanWitnessIngressSupply(
  exact CompletedPlanContinuation C,
  identical live CausalPlanContinuationCapability for C,
  exact DerivedWitnessExportRef source_export in C's active arm,
  exact admitted target Protocol P_target,
  exact admitted target ProverPlan plan_target,
  exact PrivateMaterialRef target in plan_target)
    -> Affirmative({
         supply: ReadyPlanWitnessIngressSupply,
         capability: ReadyPlanWitnessIngressSupplyCapability
       })
     | Unsupported | MissingDependency | CannotAnswer | KindMismatch
     | Malformed | Refused | DeterministicLimitExceeded | CheckerFailure
```

Issuance authenticates the identical completed continuation and live causal
capability, derives the source endpoint from its retained Plan, invocation,
reached terminal, active arm, export coordinate, and exact issued output
occurrence, and requires that the export was actually issued in that arm. It
independently authenticates the target Protocol and Plan, requires the target
reference to name exactly one
`WitnessIngress` declaration, and derives the target key from that
declaration. Source and target `ValueType` must be identical. No codec,
truncation, extension, field conversion, decoding, reinterpretation, or
caller-supplied equality witness exists in this operation.

The ready supply and its capability are fresh, target-bound, one-use,
noncopyable, nonserializable process-local objects. Each retains both complete
endpoints, the exact private value and type, the source continuation and causal
capability, target admission handles, issuance occurrence, lifetime, and
process generation. The endpoints are distinct role-bearing objects; they may
name the same Plan ID in a recursive use, but source occurrence/export and
target declaration are never one interchangeable coordinate.

Issuance does not consume the source continuation capability. Explicit fan-out
is therefore possible only by calling the operation separately for each
desired target, producing distinct issuance occurrences, ready supplies, and
capabilities. One ready supply cannot be duplicated, retargeted, split, or
used for two preparations. Canonically equal target values do not merge those
authorities.

When an affirmative `PreparePlanExecution` consumes a ready supply, it creates
the fresh target private-material occurrence described in Section 4.4 and
mints:

```text
CausalPlanWitnessHandoffCapability = {
  source: exact AcceptedPlanWitnessHandoffSourceEndpoint,
  target: exact AcceptedPlanWitnessHandoffTargetEndpoint plus
          the target CoreInvocation and
          the fresh target private-material occurrence,
  consumed_ready_supply: exact ReadyPlanWitnessIngressSupply,
  consumed_ready_supply_capability:
    exact ReadyPlanWitnessIngressSupplyCapability,
  source_causal_continuation_capability:
    exact CausalPlanContinuationCapability,
  source_causal_plan_generation_capability:
    exact CausalPlanGenerationCapability retained by that continuation,
  consumed_supply_occurrence,
  target_preparation_occurrence,
  identical_value_type,
  identical_private_value
}
```

The capability is fresh, noncopyable, nonserializable, process-local, and
minted only by that atomic successful preparation. It attests that the exact
active continuation export supplied the exact fresh target occurrence with no
conversion. The prepared target session retains it, and only successful target
generation propagates it inside the target
`CausalPlanGenerationCapability`. A later target continuation retains it only
transitively through that generation capability. There is no standalone
handoff receipt, semantic ID, digest, replay constructor, or cold-import path.

An absent or inactive source export, or a continuation that did not atomically
issue it, is `CannotAnswer`. A malformed source or target coordinate is
`Malformed`; a wrong kind, regime, or unequal `ValueType` is `KindMismatch`;
a stale, spent, retargeted, cross-continuation, cross-Plan, cross-process, or
nonidentical capability is `Refused`; and a missing named admission or
dependency preimage is `MissingDependency`. Limit exhaustion or checker defect
uses the ordinary qualified outcomes. No nonaffirmative result issues a
partial supply, exposes the private value, consumes the source capability, or
changes either endpoint. Preparation failure likewise leaves every ready
supply unconsumed; preparation success consumes all selected supplies
atomically and permanently.

`ReplayRun`, equal records, equal continuation tuples, equal export values,
serialization, process restart, or possession of a confidential witness view
cannot recreate a ready supply or causal handoff capability. The handoff makes
no claim that the value satisfies a relation, is a valid recursive witness,
preserves folding or accumulation, was sampled honestly, remains secret under
the host, or causes the target run to complete. Relations owns any later
correspondence, recurrence, or satisfaction judgment over the two retained
endpoints.

## 5. `PlanWitnessSurface`

### 5.1 Static surface and private extraction

Relations needs a narrower acyclic attachment seam. PIR derives:

```text
PlanWitnessRole = WitnessIngress | DerivedWitnessExport

PlanWitnessOccurrenceClass =
    SuppliedForGeneration
  | ProducedWhenSourceDecisionActive
  | ProducedWhenAcceptedTerminalReached

PlanWitnessSurfaceEntry = {
  role: PlanWitnessRole,
  value_type: ValueType,
  occurrence_class: PlanWitnessOccurrenceClass
}

PlanWitnessSurfaceBody = {
  protocol_id: ProtocolId,
  entries: CanonicalMap<WitnessSurfaceKey,
                        PlanWitnessSurfaceEntry>
}

PlanWitnessSurfaceId(surface) =
  ProfiledSemanticId<"pir.plan-witness-surface">(
    B, PIRInterfacePlanProfileId,
    PlanWitnessSurfaceBody(surface))

PlanWitnessOccurrenceRef = {
  surface_id: PlanWitnessSurfaceId,
  key: WitnessSurfaceKey
}
```

The body contains no `ProverPlanId`, Plan-local reference, node reference,
decision reference, source ordinal, advice, confidential context, randomness,
or state. Entry references used by Relations are local to the surface and
keyed by `WitnessSurfaceKey`; the pair above is the complete exported
occurrence coordinate. A private `WitnessIngress` Plan declaration derives
role `WitnessIngress` and class `SuppliedForGeneration`. A
`DerivedWitnessExport` derives role `DerivedWitnessExport` and class
`ProducedWhenSourceDecisionActive` or
`ProducedWhenAcceptedTerminalReached` according to its exact `source_site`.
The value type is copied exactly. No other Plan field can derive an entry.

Exact derivation from an admitted Plan yields a
`CheckedPlanWitnessSurfaceExtraction` capability that retains the full Plan
ID, source authority, and private mapping from each key to its exact private
material declaration or derived export plus source site and recipe-local
value. That mapping is authority-bearing extraction state and is absent from
the surface identity. Consequently neither an entry nor any transitive entry
field leaks a Plan ID or Plan-local reference.

A later Relations-owned attachment may bind its own witness occurrence to a
surface entry. Neither the surface nor its extraction claims correspondence,
satisfaction, confidentiality, availability of a concrete value, or validity
of a derived witness.

### 5.2 Confidential occurrence view

Static extraction proves shape, not possession of one runtime private
occurrence. PIR exposes a purpose-bound, process-local attenuation operation:

```text
ConfidentialPlanWitnessFamily = "confidential-plan-witness-view"
ConfidentialPlanWitnessQualification = CausallyGeneratedPlanOnly

ConfidentialPlanWitnessReadManifest =
  NonEmptyCanonicalSortedUniqueSeq<WitnessSurfaceKey>

ConfidentialPlanWitnessSource =
    Generated(
      exact CompletedPlanRun,
      identical live CausalPlanGenerationCapability)
  | Finalized(
      exact CompletedPlanContinuation,
      identical live CausalPlanContinuationCapability)

ConfidentialPlanWitnessSourceRequirement =
    GeneratedSufficient
  | FinalizedRequired

ConfidentialPlanWitnessEntry = {
  key: WitnessSurfaceKey,
  role: PlanWitnessRole,
  occurrence_class: PlanWitnessOccurrenceClass,
  value_type: ValueType,
  value: CanonicalValue<value_type>
}

ConfidentialPlanWitnessView = {
  protocol_id: ProtocolId,
  plan_witness_surface_id: PlanWitnessSurfaceId,
  source_tag: Generated | Finalized,
  qualification: CausallyGeneratedPlanOnly,
  entries: CanonicalSeq<ConfidentialPlanWitnessEntry>
}

ConfidentialPlanWitnessDisclosurePolicy = {
  family: ConfidentialPlanWitnessFamily,
  plan_witness_surface_id: PlanWitnessSurfaceId,
  manifest: ConfidentialPlanWitnessReadManifest,
  qualification: CausallyGeneratedPlanOnly,
  source_requirement: ConfidentialPlanWitnessSourceRequirement,
  consumer_id:
    PIRSourceConsumerRoleId(PIRInterfacePlanProfileId,family,consumer),
  purpose_id:
    PIRSourcePurposeRoleId(PIRInterfacePlanProfileId,family,purpose)
}

ConfidentialPlanWitnessBindingPayload = {
  family,
  plan_witness_surface_id,
  manifest,
  qualification,
  source_requirement,
  disclosure_policy_id,
  consumer_id,
  purpose_id,
  result_schema: "whole-confidential-plan-witness-selection-v1"
}

ConfidentialPlanWitnessCapabilityRequirement = {
  family,
  binding_payload_id,
  disclosure_policy_id,
  consumer_id,
  purpose_id,
  source_requirement,
  bearer_law:
    "fresh-identical-generated-or-finalized-plan-source"
}

ConfidentialPlanWitnessPolicyClosure = {
  family,
  binding_payload_id,
  disclosure_policy_id,
  capability_requirement_id
}
```

The nominal consumer and purpose IDs are independently formed even when their
underlying coordinates are byte-equal. The generic owner-profiled
`PIRSourceConsumerRoleId` and `PIRSourcePurposeRoleId` constructors and their
exact role bodies are imported from the Interactive Core owner. This profile
supplies `PIRInterfacePlanProfileId` explicitly; it does not redeclare an
unqualified constructor or a second physical body.

The four policy-artifact IDs are:

```text
ConfidentialPlanWitnessDisclosurePolicyId =
  ProfiledSemanticId<"pir.confidential-plan-witness-disclosure-policy">(
    B, PIRInterfacePlanProfileId,
    ConfidentialPlanWitnessDisclosurePolicyBody(policy))

ConfidentialPlanWitnessBindingPayloadId =
  ProfiledSemanticId<"pir.source-binding-payload">(
    B, PIRInterfacePlanProfileId,
    ConfidentialPlanWitnessBindingPayloadBody(payload))

ConfidentialPlanWitnessCapabilityRequirementId =
  ProfiledSemanticId<"pir.source-capability-requirement">(
    B, PIRInterfacePlanProfileId,
    ConfidentialPlanWitnessCapabilityRequirementBody(requirement))

ConfidentialPlanWitnessPolicyClosureId =
  ProfiledSemanticId<"pir.source-policy-closure">(
    B, PIRInterfacePlanProfileId,
    ConfidentialPlanWitnessPolicyClosureBody(closure))
```

Policy admission resolves every manifest key against the exact admitted
surface and derives, rather than accepts, `source_requirement`.
`FinalizedRequired` is mandatory when any selected entry is
`ProducedWhenAcceptedTerminalReached`; otherwise the requirement is
`GeneratedSufficient`. A `Generated` source satisfies only the latter. A
`Finalized` source may satisfy either because its continuation capability
retains the identical Plan-generation capability; the issued view still records
the actual `Finalized` source tag. The manifest order is ascending canonical
`WitnessSurfaceKey` body order. Empty, duplicate, reordered, or unknown-key
manifests are not alternate selections.

```text
IssueConfidentialPlanWitnessView(
  exact ConfidentialPlanWitnessSource source,
  exact admitted PlanWitnessSurface surface,
  identical live CheckedPlanWitnessSurfaceExtraction,
  exact ConfidentialPlanWitnessReadManifest manifest,
  exact consumer and purpose,
  exact admitted ConfidentialPlanWitnessDisclosurePolicyId,
  exact admitted binding payload, capability requirement, and policy closure,
  exact Foundation operation-policy disposition and capability-requirement
    wrapper derived from those artifacts)
    -> Affirmative({
         view: ConfidentialPlanWitnessView,
         authority: CheckedConfidentialPlanWitnessViewAuthority,
         capability: ConfidentialPlanWitnessViewCapability
       })
     | Unsupported | MissingDependency | CannotAnswer | KindMismatch
     | Malformed | Refused | DeterministicLimitExceeded | CheckerFailure
```

For `SuppliedForGeneration`, issuance reads the exact private-material
occurrence retained by the source's prepared session. For
`ProducedWhenSourceDecisionActive`, it requires that exact decision to be
active in the source record and reads the value sealed by the Plan adapter. For
`ProducedWhenAcceptedTerminalReached`, it requires a `Finalized` source whose
active continuation arm contains that exact terminal export and reads the
atomically issued value. An inactive decision or terminal occurrence is
`CannotAnswer`; byte equality cannot make it active.

The returned entry sequence is every and only manifest key in manifest order,
with role, class, type, and value derived from the exact extraction and live
source. `CheckedConfidentialPlanWitnessViewAuthority` is a Foundation
`OwnerLocalSourceAuthorityBinding` with owner `"pir"`, family
`ConfidentialPlanWitnessFamily`, the identical issued view as local coordinate,
the exact payload and policy-closure IDs, operation policy bound to the exact
disclosure-policy ID, and capability requirement wrapping the exact requirement
ID. It has no canonical body or content ID.

`ConfidentialPlanWitnessViewCapability` is fresh, noncopyable,
nonserializable, and process-local. It retains the complete view, authority,
manifest, admitted surface and extraction, exact tagged source, consumer,
purpose, policy artifacts, issuance occurrence, lifetime, and process
generation. A missing or expired otherwise matching live source is
`CannotAnswer`; wrong source tag for a required terminal value, surface, Plan,
session, consumer, purpose, policy, or source occurrence is `Refused`; wrong
kind or regime is `KindMismatch`; malformed manifest or envelope shape is
`Malformed`; and missing named preimages are `MissingDependency`. No
nonaffirmative result exposes a partial view or authority.

`ReplayRun`, an equal record, an equal continuation tuple, copied private
values, a serialized digest, or a fresh byte-equal generation cannot recreate
either source tag or issue a view for the historical occurrence. Only the
identical live generation or continuation capability can cross this seam.

### 5.3 Distinct downstream quotients

The OIR-specific quotients are now defined by
[Endpoint Projection Views](endpoint-projection-views.md). They are distinct
from this Relations-specific surface. The Interface quotient retains exactly
the role ABI and transitive codec laws required by its endpoint purpose. The
ordinary Plan-specialized prover quotient is the transitive closure reachable
from every decision move and state-after root; it excludes derived witness
exports, dead declarations and nodes, and full source IDs. The distinct
`PlanContinuationProverEndpoint` purpose additionally retains the exact
accepted-terminal-indexed continuation contract, every site-qualified export
reachable from an active arm, and the recipe closure needed to construct it.
Inactive arms are absent rather than empty runtime tuples. Checked extraction
retains the exact source authority privately. Endpoint Projection owns both
purpose identities and their static quotients; PIR owns runtime generation and
atomic continuation issuance; OIR cannot mint a live private output. Neither
quotient is a generic `projected_facts` constructor or an invitation for a
consumer-selected read.

Imported-verifier placement follows verifier observability rather than
implementation reuse. A pure verifier-observable Boolean verification is an
exact Core `Check`; richer verifier-observable transition, observation, or
output behavior is a `ModuleEffect`; and verification embedded in the
predicate being proved is Relations-owned. None of those routes grants Plan
authority or substitutes for an accepted-terminal continuation.

## 6. Exact canonical bodies

The K1 notation `R`, `S`, `V`, `N`, `Q`, and `Y` is used as in the K1 and K2
appendices. `ContentRef(x) = Y(ContentRefV0(x))`; `VT(T)` is
`CanonicalValueTypeBody(T)`. Tags follow the written variant order and no
other tag or field is legal.

```text
InvocationInputRefBody = V(0,N(public_input_ref))
                       | V(1,N(verifier_private_input_ref))
StructuralCodecBody(x) =
    V(0,VT(x.value_type))
  | V(1,R{0:VT(x.external_type),1:VT(x.semantic_type),
          2:S[R{0:N(field_ordinal),1:N(codec_ref)}...
              in field_ordinal order]})
  | V(2,R{0:VT(x.external_type),1:VT(x.semantic_type),
          2:S[R{0:N(case_ordinal),1:N(codec_ref)}...
              in case_ordinal order]})
  | V(3,R{0:VT(x.external_type),1:VT(x.semantic_type),
          2:N(x.element)})
CodecCertificateVerifierBody(x) = V(0,Unit)
  | V(1,R{0:VT(x.certificate_type),1:ContentRef(x.checker),
          2:ContentRef(x.checker_evaluation)})
InterfaceCodecLawDeclarationBody(x) = R {
  0:VT(x.external_type),1:VT(x.semantic_type),
  2:ContentRef(x.encode),3:ContentRef(x.encode_evaluation),
  4:ContentRef(x.decode),5:ContentRef(x.decode_evaluation),
  6:CodecCertificateVerifierBody(x.certificate_verifier)}
GeneralCodecBody(x) = R {0:ModuleDeclarationRefBody(x.law)}
InterfaceCodecBody(x) = V(0,StructuralCodecBody(x.structural))
                      | V(1,GeneralCodecBody(x.general))
ExternalSlotBody(x) = R { 0:Q(x.key), 1:N(x.codec) }
StatementFlowBody = V(0,N(public_input_ref)) | V(1,Unit)
StatementMemberBody(x) = R {0:N(x.slot),1:N(x.binding),
  2:StatementFlowBody(x.flow)}
TransportTargetBody = V(0,N(message_occurrence))
  | V(1,N(challenge_occurrence))
  | V(2,N(oracle_publication_occurrence))
  | V(3,N(oracle_query_occurrence))
  | V(4,N(oracle_answer_occurrence))
  | V(5,R{0:N(module_occurrence),1:N(observation_ordinal)})
TransportActorBody = V(0,Unit) | V(1,Unit) | V(2,Unit)
TransportDestinationBody = V(0,Unit) | V(1,Unit) | V(2,Unit)
RoleTransportEntryBody(x) = R {0:TransportTargetBody(x.target),
  1:TransportActorBody(x.source),2:TransportDestinationBody(x.destination),
  3:N(x.value_slot)}
CompletionTargetBody = V(0,N(terminal_ref)) | V(1,Unit)
CompletionPayloadCoordinateBody(x) =
    V(0,R{0:N(x.terminal_ref),1:N(x.output_ordinal)})
  | V(1,Unit) | V(2,Unit) | V(3,Unit) | V(4,Unit)
  | V(5,Unit) | V(6,Unit)
CompletionEntryBody(x) = R {0:CompletionTargetBody(x.target),
  1:Q(x.external_tag),
  2:S[R{0:CompletionPayloadCoordinateBody(coordinate),1:N(slot_ref)}...
      in CompletionPayloadCoordinateBody byte order]}
ProtocolInterfaceBody(I) = R {0:ContentRef(I.protocol_id),
  1:S[InterfaceCodecBody(x)...],2:S[ExternalSlotBody(x)...],
  3:S[R{0:InvocationInputRefBody(k),1:N(slot)}...
      in canonical InvocationInputRef order],
  4:S[StatementMemberBody(x)...],5:S[RoleTransportEntryBody(x)...],
  6:S[CompletionEntryBody(x)...]}
```

Plan bodies are:

```text
PrivateMaterialKindBody = V(0,Unit) | V(1,Unit) | V(2,Unit)
PrivateMaterialBody(x) = R {0:Q(x.key),
  1:PrivateMaterialKindBody(x.kind),2:VT(x.value_type)}
RandomnessRequirementBody(x) = R {0:VT(x.value_type),
  1:N(x.first_available_at)}
StateInitialValueBody = V(0,N(private_material_ref))
  | V(1,R{0:VT(value_type),1:value.datum})
StrategyStateSlotBody(x) = R {0:VT(x.value_type),
  1:StateInitialValueBody(x.initial)}
PlanRecipeSiteRefBody = V(0,N(decision_ref))
  | V(1,N(accepted_terminal_ref))
PlanReadCoordinateBody = V(0,N(constant_ref))
  | V(1,N(public_input_ref))
  | V(2,N(binding_ref))
  | V(3,N(message_occurrence))
  | V(4,N(challenge_occurrence))
  | V(5,N(oracle_publication_occurrence))
  | V(6,N(oracle_query_occurrence))
  | V(7,N(oracle_answer_occurrence))
  | V(8,R{0:N(module_occurrence),1:N(observation_ordinal)})
  | V(9,N(prior_decision_ref))
  | V(10,N(accepted_terminal_public_output_ordinal))
RecipeOperandBody = V(0,PlanReadCoordinateBody)
  | V(1,N(private_material_ref))
  | V(2,N(randomness_requirement_ref))
  | V(3,N(state_slot_ref))
  | V(4,R{0:VT(value_type),1:value.datum})
  | V(5,N(node_ref))
RecipeNodeBody(x) = R {0:ContentRef(x.algorithm),
  1:ContentRef(x.evaluation),2:S[RecipeOperandBody(input)...],
  3:VT(x.output_type)}
ProverMoveBindingBody = V(0,RecipeOperandBody(message_value))
  | V(1,RecipeOperandBody(oracle_value))
  | V(2,RecipeOperandBody(module_value))
StateAfterBindingBody = V(0,Unit)
  | V(1,RecipeOperandBody(value))
DecisionRecipeBody(x) = R {0:S[RecipeNodeBody(node)...],
  1:ProverMoveBindingBody(x.move),
  2:S[R{0:N(state_slot_ref),1:StateAfterBindingBody(binding)}...
      in StrategyStateSlotRef order]}
AcceptedTerminalRecipeBody(x) = R {
  0:S[RecipeNodeBody(node)...]}
DerivedWitnessExportBody(x) = R {0:Q(x.key),
  1:PlanRecipeSiteRefBody(x.source_site),
  2:RecipeOperandBody(x.value),3:VT(x.value_type)}
ProverPlanBody(P) = R {0:ContentRef(P.protocol_id),
  1:S[PrivateMaterialBody(x)...],2:S[RandomnessRequirementBody(x)...],
  3:S[StrategyStateSlotBody(x)...],
  4:S[R{0:N(decision_ref),1:DecisionRecipeBody(recipe)}...
      in ProverDecisionPointRef order],
  5:S[DerivedWitnessExportBody(x)...],
  6:S[R{0:N(terminal_ref),1:AcceptedTerminalRecipeBody(recipe)}...
      in TerminalRef order]}
PlanWitnessRoleBody = V(0,Unit) | V(1,Unit)
PlanWitnessOccurrenceClassBody = V(0,Unit) | V(1,Unit) | V(2,Unit)
PlanWitnessSurfaceEntryBody(x) = R {0:PlanWitnessRoleBody(x.role),
  1:VT(x.value_type),
  2:PlanWitnessOccurrenceClassBody(x.occurrence_class)}
PlanWitnessSurfaceBody(S) = R {0:ContentRef(S.protocol_id),
  1:S[R{0:Q(key),1:PlanWitnessSurfaceEntryBody(entry)}... in key order]}
PlanWitnessOccurrenceRefBody(x) = R {0:ContentRef(x.surface_id),1:Q(x.key)}

ConfidentialPlanWitnessReadManifestBody(x) =
  S[Q(key)... in canonical sorted-unique WitnessSurfaceKey body order]
ConfidentialPlanWitnessQualificationBody = V(0,Unit)
ConfidentialPlanWitnessSourceRequirementBody = V(0,Unit) | V(1,Unit)
ConfidentialPlanWitnessDisclosurePolicyBody(x) = R {
  0:Q("confidential-plan-witness-view"),
  1:ContentRef(x.plan_witness_surface_id),
  2:ConfidentialPlanWitnessReadManifestBody(x.manifest),
  3:ConfidentialPlanWitnessQualificationBody,
  4:ConfidentialPlanWitnessSourceRequirementBody(x.source_requirement),
  5:ContentRef(x.consumer_id),
  6:ContentRef(x.purpose_id)}
ConfidentialPlanWitnessBindingPayloadBody(x) = R {
  0:Q("confidential-plan-witness-view"),
  1:ContentRef(x.plan_witness_surface_id),
  2:ConfidentialPlanWitnessReadManifestBody(x.manifest),
  3:ConfidentialPlanWitnessQualificationBody,
  4:ConfidentialPlanWitnessSourceRequirementBody(x.source_requirement),
  5:ContentRef(x.disclosure_policy_id),
  6:ContentRef(x.consumer_id),
  7:ContentRef(x.purpose_id),
  8:Q("whole-confidential-plan-witness-selection-v1")}
ConfidentialPlanWitnessCapabilityRequirementBody(x) = R {
  0:Q("confidential-plan-witness-view"),
  1:ContentRef(x.binding_payload_id),
  2:ContentRef(x.disclosure_policy_id),
  3:ContentRef(x.consumer_id),
  4:ContentRef(x.purpose_id),
  5:ConfidentialPlanWitnessSourceRequirementBody(x.source_requirement),
  6:Q("fresh-identical-generated-or-finalized-plan-source")}
ConfidentialPlanWitnessPolicyClosureBody(x) = R {
  0:Q("confidential-plan-witness-view"),
  1:ContentRef(x.binding_payload_id),
  2:ContentRef(x.disclosure_policy_id),
  3:ContentRef(x.capability_requirement_id)}
```

`PlanReadCoordinateBody` and every local node reference are interpreted
relative to the exact `PlanRecipeSiteRefBody` that owns their recipe. The
terminal-public-output tag forms only at an accepted-terminal site; direct
randomness forms only at a decision site. In `DerivedWitnessExportBody`,
`RecipeOperandBody(x.value)` is interpreted relative to `x.source_site` and
its exact local recipe; the site is not an ambient argument. The witness-
surface map contains only its keyed entry bodies; the checked extraction,
source Plan ID, and source mapping are not serialized fields.

The manifest body is nonempty, sorted by the complete canonical
`WitnessSurfaceKey` body, and duplicate-free. Qualification tag 0 is
`CausallyGeneratedPlanOnly`. Source-requirement tags 0 and 1 are respectively
`GeneratedSufficient` and `FinalizedRequired`; admission derives the tag from
the selected occurrence classes. The policy, payload, capability requirement,
and closure bodies above are complete: no consumer, purpose, manifest,
qualification, source requirement, result schema, bearer law, or policy edge
is ambient or prose-only. `PIRSourceConsumerRoleBody` and
`PIRSourcePurposeRoleBody` use the same exact family and are nominally
distinct identified subjects even when their coordinates are byte-equal.

`PlanPrivateMaterialInputMap`, `PlanPrivateRandomnessInputMap`, their values and
capabilities, private-material occurrences, randomness reveal rights,
`AcceptedPlanWitnessHandoffSourceEndpoint`,
`AcceptedPlanWitnessHandoffTargetEndpoint`,
`ReadyPlanWitnessIngressSupply`, `ReadyPlanWitnessIngressSupplyCapability`,
`CausalPlanWitnessHandoffCapability`, `ConfidentialPlanWitnessSource`,
`ConfidentialPlanWitnessView`, completed Plan runs and continuations, causal
capabilities, owner authority bindings, and issued view capabilities are
process-local runtime objects. They deliberately have no canonical body or
semantic ID; equal canonical values, endpoint fields, or record bytes cannot
reconstruct them.

Changing a body field, order, tag, admission law, input-map formation law,
atomic preparation or handoff law, witness-surface derivation, or
`PlanRealizes` proposition rotates the owner-local Interface/Plan profile ID
and every downstream profile that imports it. It does not add any of the live
objects above to a semantic preimage. A module-owned declaration change instead
rotates that module and its exact users. The shared Foundation semantic regime
rotates only when a Foundation-owned mechanism or its interpretation changes.
Old bytes are never reinterpreted.

## 7. Nonclaims and reopening conditions

Interface admission, Plan admission, input-map formation, Plan preparation,
accepted-continuation handoff, `PlanWitnessSurface` extraction, and
`PlanRealizes` do not establish:

- relation-instance correspondence, witness attachment, witness satisfaction,
  or validity of a derived witness export;
- soundness, knowledge, completeness, zero knowledge, Fiat--Shamir security,
  random-coin quality, or any theorem hypothesis;
- OIR local validity, projection correctness, endpoint support, transport
  availability, or concrete realization;
- supplier behavior, private-state isolation, side-channel freedom,
  termination, cost, or performance; or
- implementation correspondence, formal verification, evidence reliability,
  deployment, or production readiness.

K3-D's selected consumer is one whole-source-provenance-free
`EndpointSourceView`; its shared semantic graph contains the role-qualified
Interface component and, for the specialized Prover, the reachable Plan
component. Exact read and identity laws are owned by the endpoint-view
specification.

Reopen this page if a concrete bounded consumer shows that the
`PlanWitnessSurface` cannot preserve a required role, type, or occurrence
distinction without a Plan-local identity; that one Interface slot needs
incompatible audiences; that the uniform transport semantic value cannot
represent a required K2 occurrence state; or that one semantic Plan fact
cannot be placed unambiguously in private ingress, randomness, persistent
state, recipe, or witness export. A later missing consumer-specific projection
grammar is not evidence for a generic view constructor here.

Reopen K2 only if a concrete case needs verifier-observable invocation
material not expressible as a public or verifier-private input, a
verifier-observable Statement not expressible as a scoped K2 binding, a legal
prover decision fact missing from its exact `ProverView`, or an
acceptance-relevant effect lacking an exact Core/module occurrence and source
view. Witness typing, private advice, private randomness, strategy state,
external codecs, transport packaging, consumer identity, and OIR placement
remain dependent-subject concerns and do not by themselves reopen K2.
