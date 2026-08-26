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
      -> separate PlanRealizes judgment
```

Neither subject is part of `ProtocolId`. Several Interfaces and Plans may
coexist for one Protocol. Substituting either cannot change Core occurrences,
visibility, transcript framing, challenge interpretation, checks, claims,
reductions, terminals, accepted language, or any Protocol-only result.

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
- K2 interpretation-failure coordinates from
  [Fiat--Shamir Construction](fiat-shamir.md).

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

The selected PIR regime gives declaration kind `pir.interface-codec-law`
exactly the body above and the proposition `CanonicalCodecLaw`; the proposition
is fixed by the kind and is not an authored Boolean. The declaration and every
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
values owned by the selected PIR semantic regime. Their spelling is semantic
only for the dependent subject that contains them; it is never Core meaning.

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
order are derived from the admitted K2 `EffectView` and `ExecutionView`.
Every transport slot has semantic type
`TransportSemanticValue(TargetType(target))`, including an unguarded target.
Its semantic value is `Active(v)` exactly when that occurrence is active and
has produced `v`; otherwise it is `Inactive`. Thus a prior Core terminal or FS
interpretation failure makes every not-yet-executed target `Inactive` without
an `AlwaysOccurs` assertion. Admission requires exact type, legal
source/destination visibility, a unique target/role/value use, and this exact
presence law. Absence can never decode as an active value.

Whether `Inactive` is emitted as an omitted field, explicit tag, or fixed wire
slot is not Interface semantics. K3-D OIR selects that representation and
proves it implements this uniform semantic value. In particular, an FS
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
- an FS Protocol has exactly one interpretation-failure entry whose map domain
  is exactly the six `FSFailure*` coordinates above; a Fresh Protocol has none.

`TerminalPublicOutput(t,o)` selects the exact canonical value and K2
`ValueType` of the `o`th public output of `t`. For an FS Protocol the failure
coordinates select, without omission or reordering:

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
  SemanticContentId<"pir.protocol-interface">(
    B, ProtocolInterfaceBody(interface))

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

## 4. `ProverPlan`

### 4.1 Boundary and complete subject

A Plan describes the semantic dataflow needed to propose legal K2 prover
moves. It contains no relation definition, relation interface, relation-owned
reference, witness value, random value, supplier handle, executable callback,
credential, buffer, thread schedule, search queue, cache, cost target, resource
choice, or mutable host object.

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

ProverPlan = {
  protocol_id: ProtocolId,
  private_material: CanonicalSeq<PrivateMaterialDecl>,
  randomness_requirements: CanonicalSeq<PrivateRandomnessRequirement>,
  persistent_state: CanonicalSeq<StrategyStateSlot>,
  decision_recipes:
    CanonicalMap<ProverDecisionPointRef, DecisionRecipe>,
  derived_witness_exports: CanonicalSeq<DerivedWitnessExport>
}
```

`WitnessIngress` is a generic private-material class, not an assertion that a
value satisfies or corresponds to any relation. `Advice` is private
nonwitness material. `ConfidentialContext` is private static context. Keys are
unique across private material and derived witness exports. Relations may
later attach one of these generic coordinates to a relation-owned witness
occurrence through a separate checked subject; there is no Relations-to-Plan
authority edge in Plan formation or admission.

### 4.2 Decision recipes

Plan owns this closed coordinate grammar over one exact K2 `ProverView`:

```text
ProverViewCoordinate =
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

AvailableProverCoordinate(P,d,c) iff
  d is an exact decision of admitted Protocol P and
  K2.GuaranteedProverRead(d, K2ReadOf(c)) = true
    in P's exact StrategyDecisionView
```

This is an alias of the K2 owner table, not a second path analysis. It inherits
K2's exact type, source, visibility, order, scope-opening, and guard-implication
rules. Membership in one runtime view, a replay sample, or a Plan assertion
cannot widen it.

```text
RecipeOperand =
    ViewValue(ProverViewCoordinate)
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

ProverMoveBinding =
    MessageValue(RecipeValueRef)
  | OracleValue(RecipeValueRef)
  | ModuleMove(RecipeValueRef)

DerivedWitnessExport = {
  key: WitnessSurfaceKey,
  source_decision: ProverDecisionPointRef,
  value: RecipeValueRef,
  value_type: ValueType
}
```

Each recipe is a local acyclic graph evaluated only if its decision point is
active. A `ViewValue` names one exact coordinate present in the K2
`ProverView` at that decision; it cannot name the whole view or a future
history. A randomness requirement is readable only at or after its declared
first boundary and may flow later only through an explicit state or node
output. `StateBefore` reads the value installed by initialization or the most
recent active decision recipe. An inactive decision performs no state update.

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
silently become witness exports. Its `value` is interpreted in the
recipe-local namespace selected by `source_decision`: `NodeOutput(n)` can name
only node `n` of that decision's recipe, and `ViewValue(c)` requires
`AvailableProverCoordinate(protocol, source_decision, c)`. No local node or
view coordinate of another decision can be captured by ordinal coincidence.

### 4.3 Identity, admission, and `PlanRealizes`

```text
ProverPlanId =
  SemanticContentId<"pir.prover-plan">(B, ProverPlanBody(plan))

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
equality, reference formation, unique keys, private-material separation,
randomness boundaries, state typing and
initialization, local DAG order, algorithm ABIs, result types, move-binding
shape, total state-after maps, witness-export typing, exact-used dependency
closure, and absence of ambient or realization-only fields. It does not
establish decision coverage against K2; that remains an independent relation.

```text
PlanRealizes(
  exact AdmittedProtocol P,
  exact AdmittedProverPlan,
  exact StrategyDecisionView,
  exact DependentAdmissionBasis(P))
  -> Qualified<Affirmative(CheckedPlanRealizes)
             | Negative(PlanRealizesReason)>
```

Negative is a completed answer to the formed cross-subject proposition, not a
catch-all validation error. The following closed coordinates and reason
algebra are the complete negative payload:

```text
RecipeUseRef =
    NodeInput(ProverDecisionPointRef, RecipeNodeRef, input_ordinal)
  | MovePayload(ProverDecisionPointRef)
  | StateReplacement(ProverDecisionPointRef, StrategyStateSlotRef)

DerivedWitnessExportRef =
  dense ordinal into the exact Plan's derived_witness_exports

PlanMoveShape =
    Message(ValueType)
  | Oracle(OracleRef, ValueType)
  | Module(ModuleEffectRef, ValueType)

PlanViewReadDisagreement =
    NotGuaranteedAtDecision
  | TypeDisagreement {
      owner_type: ValueType,
      use_type: ValueType
    }
  | OriginDisagreement {
      requested: K2ProverReadCoordinate,
      owner_derived: K2ProverReadCoordinate
    }

PlanRealizesDisagreement =
    MissingDecisionRecipe(ProverDecisionPointRef)
  | ViewReadDisagreement {
      use: RecipeUseRef,
      coordinate: ProverViewCoordinate,
      cause: PlanViewReadDisagreement
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
`use_type` is the exact type required by that node input, move, or replacement
site. `PlanMoveShape` is derived twice rather than supplied: `expected` comes
from the K2 decision kind and exact module occurrence, while `observed` comes
from the recipe constructor and the statically resolved payload type. Thus
one shape comparison covers the constructor, module coordinate, and payload
type without a caller-authored summary. The `Oracle` shape's type is exactly
the selected `OracleRef`'s owner-derived `OracleCarrierType`. A witness-export
coordinate is interpreted relative to its declared `source_decision`, as in
Section 4.2.

The checker emits every applicable atomic disagreement once, in written
variant-tag order and then canonical field-body order. Missing decision
recipes are emitted from exact set difference. An unexpected
`ProverDecisionPointRef`, duplicate key, or ill-formed key cannot reach this
relation because dependent-reference formation, `CanonicalMap` formation, and
Plan admission already reject it under their ordinary distinct outcome. A
dependent check is evaluated only after its coordinate
and required predecessor form. In particular, a missing source recipe is not
also reported as arbitrary downstream operand, move, or export disagreement.
This dependency order makes the negative payload deterministic rather than an
implementation-selected first error.

The result is Affirmative exactly when this complete traversal emits no
disagreement, and Negative exactly when the resulting sequence is nonempty.

The nine checks below split across the qualified outcome boundary as follows:

| Check | Completed Negative | Never a negative reason |
|---|---|---|
| 1 | none | A wrong typed axis is `KindMismatch`; a well-formed handle for another Protocol, source authority, retained basis, or evaluator is `Refused`. An internally inconsistent admitted handle is `CheckerFailure`. |
| 2 | `MissingDecisionRecipe` | Duplicate or noncanonical map structure is `Malformed`; a formed key on a wrong owner/kind axis is `KindMismatch`, and a formed same-axis key that fails the dependent decision-point predicate is `Refused`. |
| 3 | `ViewReadDisagreement` for a formed owner coordinate | An ill-formed coordinate is `Malformed`; absent supported owner interpretation is `Unsupported`. |
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
3. every `ViewValue(c)` satisfies owner-derived
   `AvailableProverCoordinate(protocol, decision, c)` with exact type and
   origin on every path reaching that active decision;
4. every other operand is deterministically available before its use on every
   such path, every `NodeOutput` is earlier in the same recipe, and every node
   ABI is exact;
5. the move constructor, module coordinate, and payload type equal the K2
   legal move at that decision;
6. private material, randomness, and current state use only their distinct
   declared ingress;
7. state initialization and every active state transition are total and
   type-preserving;
8. each witness export, interpreted relative to `source_decision`, names an
   all-path available same-type value or an earlier node in that exact recipe;
   and
9. every Plan read is in the authenticated body and exact-used closure.

Verifier-private input, future history, ambient registry, clock, file, process
object, strategy capability, or mutable Core handle has no `RecipeOperand`
constructor. `PlanRealizes` therefore cannot affirm a route containing such a
read. A negative result is meaningful and distinct from unsupported semantics,
missing authority, malformed input, refusal, limit exhaustion, and checker
failure.

Affirmative `CheckedPlanRealizes` proves structural decision coverage, typing,
causal read confinement, and state closure only. It proves no algorithmic
correctness beyond the exact K1 denotations, witness correspondence or
satisfaction, random distribution, supplier fidelity, successful generation,
termination, completeness, cost, or cryptographic property.

## 5. `PlanWitnessSurface`

Relations needs a narrower acyclic attachment seam. PIR derives:

```text
PlanWitnessRole = WitnessIngress | DerivedWitnessExport

PlanWitnessOccurrenceClass =
    SuppliedForGeneration
  | ProducedWhenSourceDecisionActive

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
  SemanticContentId<"pir.plan-witness-surface">(
    B, PlanWitnessSurfaceBody(surface))

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
`ProducedWhenSourceDecisionActive`. The value type is copied exactly. No other
Plan field can derive an entry.

Exact derivation from an admitted Plan yields a
`CheckedPlanWitnessSurfaceExtraction` capability that retains the full Plan
ID, source authority, and private mapping from each key to its exact private
material declaration or derived export plus source decision and recipe-local
value. That mapping is authority-bearing extraction state and is absent from
the surface identity. Consequently neither an entry nor any transitive entry
field leaks a Plan ID or Plan-local reference.

A later Relations-owned attachment may bind its own witness occurrence to a
surface entry. Neither the surface nor its extraction claims correspondence,
satisfaction, confidentiality, availability of a concrete value, or validity
of a derived witness.

Concrete Interface and Plan projections for OIR are deferred to K3-D. K3-D
must define each closed purpose grammar, exact read manifest, view-local
normalization, checked extraction, and identity effect; it may not use a
generic `projected_facts` placeholder or bind a full source ID while claiming
that unread source fields are nonsemantic.

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
ProverViewCoordinateBody = V(0,N(constant_ref))
  | V(1,N(public_input_ref))
  | V(2,N(binding_ref))
  | V(3,N(message_occurrence))
  | V(4,N(challenge_occurrence))
  | V(5,N(oracle_publication_occurrence))
  | V(6,N(oracle_query_occurrence))
  | V(7,N(oracle_answer_occurrence))
  | V(8,R{0:N(module_occurrence),1:N(observation_ordinal)})
  | V(9,N(prior_decision_ref))
RecipeOperandBody = V(0,ProverViewCoordinateBody)
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
      in StateSlotRef order]}
DerivedWitnessExportBody(x) = R {0:Q(x.key),1:N(x.source_decision),
  2:RecipeOperandBody(x.value),3:VT(x.value_type)}
ProverPlanBody(P) = R {0:ContentRef(P.protocol_id),
  1:S[PrivateMaterialBody(x)...],2:S[RandomnessRequirementBody(x)...],
  3:S[StrategyStateSlotBody(x)...],
  4:S[R{0:N(decision_ref),1:DecisionRecipeBody(recipe)}...
      in ProverDecisionPointRef order],
  5:S[DerivedWitnessExportBody(x)...]}
PlanWitnessRoleBody = V(0,Unit) | V(1,Unit)
PlanWitnessOccurrenceClassBody = V(0,Unit) | V(1,Unit)
PlanWitnessSurfaceEntryBody(x) = R {0:PlanWitnessRoleBody(x.role),
  1:VT(x.value_type),
  2:PlanWitnessOccurrenceClassBody(x.occurrence_class)}
PlanWitnessSurfaceBody(S) = R {0:ContentRef(S.protocol_id),
  1:S[R{0:Q(key),1:PlanWitnessSurfaceEntryBody(entry)}... in key order]}
PlanWitnessOccurrenceRefBody(x) = R {0:ContentRef(x.surface_id),1:Q(x.key)}
```

`ProverViewCoordinateBody` is always interpreted relative to the exact
decision key containing the recipe. In
`DerivedWitnessExportBody`, `RecipeOperandBody(x.value)` is instead interpreted
relative to `x.source_decision` and its exact local recipe; that decision is not
an ambient argument. The witness-surface map contains only its keyed entry
bodies; the checked extraction, source Plan ID, and source mapping are not
serialized fields.

Changing a body field, order, tag, admission law, witness-surface derivation, or
`PlanRealizes` proposition requires a new supported PIR semantic regime. Old
bytes are never reinterpreted.

## 7. Nonclaims and reopening conditions

Interface admission, Plan admission, `PlanWitnessSurface` extraction, and
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

Reopen this page if a concrete bounded consumer shows that the
`PlanWitnessSurface` cannot preserve a required role, type, or occurrence
distinction without a Plan-local identity; that one Interface slot needs
incompatible audiences; that the uniform transport semantic value cannot
represent a required K2 occurrence state; or that one semantic Plan fact
cannot be placed unambiguously in private ingress, randomness, persistent
state, recipe, or witness export. A missing OIR-specific projection grammar is
first a K3-D obligation, not evidence for a generic view constructor here.

Reopen K2 only if a concrete case needs verifier-observable invocation
material not expressible as a public or verifier-private input, a
verifier-observable Statement not expressible as a scoped K2 binding, a legal
prover decision fact missing from its exact `ProverView`, or an
acceptance-relevant effect lacking an exact Core/module occurrence and source
view. Witness typing, private advice, private randomness, strategy state,
external codecs, transport packaging, consumer identity, and OIR placement
remain dependent-subject concerns and do not by themselves reopen K2.
