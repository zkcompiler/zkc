# Canonical-Framed Fiat--Shamir Construction

> **Document kind:** Target semantic specification
> **Document state:** Active redesign target; canonical-framed sibling
> **Target status:** The bounded canonical-framed construction, influence, and
> same-Core eligibility model is complete at its stated construction boundary.
> The separately identified duplex-sponge sibling owns runtime-instance
> initialization, proof-carried construction material, and raw overwrite
> transitions; theorem applicability and property transport remain open
> Analysis work.
> **Provisional owner:** `pir`
> **Authority:** None during the transition. Current normative Fiat--Shamir
> semantics remain under [`docs/`](../../docs/README.md).

## 1. Contract

This page is the sole target definition owner for the current canonical-framed
construction's:

- transcript-construction identity, authentication, admission, and support;
- initialization, typed framing, absorption, squeezing, challenge decoding,
  bounded retry, and completed sampling failure;
- Core-derived transcript actions, required influence, and exact prefixes;
- structural Fiat--Shamir eligibility and execution;
- the same-Core Fresh/Fiat--Shamir structural relation; and
- composition-sensitive challenge namespaces and continuous transcript state.

The [Interactive Core](interactive-core.md) owns parties, values, scopes,
effects, public-coin eligibility, causal execution, and replay. Foundation owns
the value, identity, portable-algorithm, ABI, typed-failure, and deterministic-
evaluation mechanisms used here.

The [duplex-sponge family](duplex-sponge-fiat-shamir.md) is a sibling profile
over the same Core language. Neither family is a mode, parameter value,
fallback, or implementation of the other.

This page does not prove soundness, knowledge, zero knowledge, random-oracle or
quantum-random-oracle applicability, distribution preservation, hash or sponge
security, oracle-binding security, BCS correctness, or implementation
conformance. Those are Analysis, construction-family, Realization, and Evidence
questions over the exact structural coordinates exported here.

## 2. Foundation and Core intake

For one exact K1 `PriorMetaAuthenticationBasis B`, K2 uses:

- `SemanticContentId<K>`, `ContentRefV0`, `ValueType`, and
  `CanonicalValue<T>`;
- authenticated same-regime `PortableAlgorithmRef` and its derived
  `SemanticFunctionType`;
- exact `EvaluationContractId` and deterministic request bounds; and
- `Success`, typed `DomainFailure`, and the qualified noncompletion partition.

`B.semantic_regime.id` is the sole semantic-regime coordinate used by the
admitted Core and this construction. Every ordinary ID and body authenticates
under the same complete `B`; every value type resolves under it; and every
canonical value is strictly decoded and owner-admitted at its exact value type.
Exact-used modules additionally resolve through that basis's authenticated
same-root module closure. A construction cannot introduce a second basis or
regime axis; a formed reference selecting another basis or regime is
`KindMismatch`, while malformed carriers and failed owner admission retain
their K1 classifications.

The input Core is an exact `AdmittedCore` from the companion page. Its
occurrence order, values, scope tree, public bindings, challenges, messages,
oracles, reductions, extensions, and public-coin result are immutable.

The exact-used PIR owner-module closure additionally recognizes
`ProtocolDeclarationRef<"pir.fs-application-domain">`, and this profile fixes
its declaration body: exactly the companion page's
`NominalProtocolDeclarationBody`, one nonempty semantic symbol and no other
field, so that a declaration of this kind is `MetaRecord { 0: MetaSymbol(s) }`
and a declaration with any other shape is `Malformed`. The reference keeps
the companion page's `ModuleDeclarationRefBody`. It is an authenticated
static application-purpose coordinate, not a display string or a freshness
claim; the symbol separates applications and carries no other meaning.

This page selects one standalone `PIRCanonicalFramedFSProfile`. Its required exact
profile imports are `{PIRInteractionProfileId}`; its supported subject kinds are
`{"pir.transcript-construction", "pir.protocol",
"pir.source-binding-payload", "pir.source-capability-requirement",
"pir.source-consumer", "pir.source-no-policy",
"pir.source-policy-closure", "pir.source-purpose"}`; and its inline declaration
catalog contains the canonical-framed body compiler, the profile-local
`FSChallengeReceipt` and `FSInterpretationFailureReceipt` dependent runtime
templates, the exact construction admission, checked-construction,
profile-closure, issuance, and nonclaim laws, one evaluator signature, and one
qualified failure schema. The imported Interaction body compiler owns the
`pir.protocol` body arm. A construction and its canonical-framed FS Protocol rotate
together when this family meaning changes, while Fresh and an unreferenced FS
sibling remain under their own profiles. The profile import is the only
generic upstream closure; it is not a declaration-module root.
Construction formation, FS Protocol/view issuance, and checked-construction
authority authenticate exactly the two-entry
`{PIRInteractionProfileId,PIRCanonicalFramedFSProfileId}` closure and require only
`PIRCanonicalFramedFSProfileId` in evaluator support. Public-setup-profile support is
irrelevant to those operations. An unrecognized exact root is `Unsupported`,
while a supported root omitting any emitted Protocol, construction, or
owner-authority subject kind is `Refused`.

The complete six-field profile body, owner-source manifest, exact import-use
table, root closure, and independently reproduced full typed ID are published
by [Published PIR Semantic Profiles](profiles/README.md). The bounded protocol
witness still uses a witness-local approximation profile because its finite
Core carrier is not the Appendix-A body compiler on this page. Its IDs remain
nonpersistent evidence coordinates and must not be substituted for this
published target profile.

All collections and bodies obey the K1 constitutional bounds. In addition:

```text
maximum challenge rules       = core.challenge_count <= 2^14
maximum draws per challenge   = 2^20
maximum bytes per squeeze     = 2^20 - 26
maximum frames per execution  =
  exact derived bound from the admitted finite Core <= 2^20
maximum total transition calls per execution =
  frames + sum(maximum_draws for every challenge) <= 2^20
maximum cumulative framed/squeezed bytes per execution = 2^30
```

The enclosing canonical body and every runtime canonical value may impose a
smaller bound. Construction admission derives the worst-case sums from Core
schemas, module frame bounds, draw widths, and challenge rules, and preflights
them before allocation or hashing. Reaching a bound is allowed; crossing it
refuses admission rather than becoming evaluator-dependent behavior.

<!-- zkc-profile-source:canonical-framed-fs-semantics:start -->

## 3. Construction subject

### 3.1 Exact algorithm uses

Every algorithm coordinate uses the shared `PIRAlgorithmUse` record from the
Interaction profile.

The construction names four common K1 value types:

```text
TranscriptStateType : ValueType
TranscriptBytesType : ValueType   // bounded K1 byte string
NaturalType         : ValueType   // selected K1 natural domain
BooleanType         : ValueType   // exact K1 root Boolean type
```

Precisely,
`BooleanType = ValueType(Root(B.semantic_regime.id,
"foundation.root-value-domain",1), Boolean)` under the `Root` abbreviation
made explicit in Section 3.2. `TranscriptBytesType` must use the same regime's
root byte-string domain at ordinal 4 with a `Bytes(0,L)` schema for some
`L <= 2^20 - 26` large enough for every admitted frame, namespace, and draw.
`NaturalType` must use the root natural domain at ordinal 2 with a `Nat(Ln)`
schema that admits every `draw_bytes` value and all construction counters.
K1 gives a standalone byte datum `Worst(Bytes(0,L)) = 9 + L`, then wraps every
algorithm success in a tagged completion adding another `17` octets. Because
`TranscriptBytesType` is the success type of `SqueezeBytesUse`, its tight
common ceiling is therefore `17 + 9 + L <= 2^20`, or `L <= 2^20 - 26`.
Construction admission also preflights the complete tagged-completion schema of
every other algorithm use; a larger state, challenge, or failure type may
impose a smaller admissible construction.
In particular, both `AbsorbUse` and `AdvanceStateUse` require
`17 + MaxDatumBytes(TranscriptStateType) <= 2^20`; their complete failure
payload schemas must fit the same maximum-completion preflight.

After K1 admits `CanonicalValue<TranscriptBytesType>(O(x))`, this owner defines
the structural projection
`OctetLength(CanonicalValue<TranscriptBytesType>(O(x))) = length(x)`.
`OctetLength` is not an additional portable algorithm or an opaque host method:
K1 owns the unique byte-string carrier and admission, while this page owns the
bounded postcondition on its exact octet payload.

The exact derived ABIs are:

```text
AbsorbUse:
  (TranscriptStateType, TranscriptBytesType)
    -> TranscriptStateType

SqueezeBytesUse:
  (TranscriptStateType, TranscriptBytesType, NaturalType)
    -> TranscriptBytesType

AdvanceStateUse:
  (TranscriptStateType, TranscriptBytesType, NaturalType,
   TranscriptBytesType)
    -> TranscriptStateType
```

All three algorithms are total, deterministic, and have empty typed-failure
rows on admitted inputs. `SqueezeBytesUse` computes the requested output from
`(pre_state, namespace, requested_count)`. `AdvanceStateUse` computes the
corresponding post-state from those same inputs plus the exact output bytes.
This split is an ordinary sequence of two K1 algorithms, each with one exact
success `ValueType`; it does not assume a heterogeneous product result that K1
has not separately declared.

At runtime the FS owner additionally requires the successful
`SqueezeBytesUse` value to contain exactly `requested_count` bytes. A different
length is owner-qualified
`Refused(PIR.FiatShamir, SqueezeLengthMismatch)`: it produces no Protocol
outcome, no `DrawReceipt`, and `AdvanceStateUse` is not evaluated. A provider
whose returned value differs from evaluation of the admitted portable
algorithm is instead `CheckerFailure`. State is explicit; none of the three
algorithms may read or mutate ambient state.

### 3.2 Challenge rule

For Core challenge `c`, derive:

```text
SamplingInputTypes(c) =
  [TranscriptBytesType]
  ++ map(core.challenges[c].public_conditions, exact value type)
  ++ map(core.challenges[c].correlation.prior_members,
         exact challenge value type)

ChallengeRule = {
  challenge: ChallengeRef,
  draw_bytes: positive Natural,
  maximum_draws: positive Natural,
  accept: PIRAlgorithmUse,
  decode: PIRAlgorithmUse
}
```

For `TranscriptBytesType = Bytes(0,L)`, construction admission requires
`1 <= draw_bytes <= L`, `1 <= maximum_draws <= 2^20`, and the cumulative
transition bounds in Section 2. Every derived frame and namespace body must
also encode to at most `L` raw octets before it can be admitted as a transcript
byte value.

The admitted acceptance ABI is exactly
`SamplingInputTypes(c) -> BooleanType`, and the admitted decoder ABI is exactly
`SamplingInputTypes(c) -> core.challenges[c].value_type`. Both have empty
typed-failure rows. Acceptance is evaluated first. The decoder is evaluated
only when acceptance is true, and therefore every successful decoder result is
already an exact domain-admitted challenge value. Neither algorithm can return
a partial value, new transcript state, or untyped error. A one-shot rule sets
`maximum_draws = 1` and uses an acceptance algorithm that always returns true.
A rejection rule returns false from its acceptance algorithm.

`draw_bytes`, `maximum_draws`, and both algorithms enter construction identity.
Reaching the draw bound with only false acceptance results completes with the
construction's exact K1 typed failure. Its outward payload types are fixed:

```text
FSChallengeRefType = ValueType(
  Root(B.semantic_regime.id,
       "foundation.root-value-domain", 2),
  Nat(2^14 - 1))

FSDrawCountType = ValueType(
  Root(B.semantic_regime.id,
       "foundation.root-value-domain", 2),
  Nat(2^20))

SamplingExhaustedPayloadType = ValueType(
  Root(B.semantic_regime.id,
       "foundation.root-value-domain", 7),
  Record { 0: FSChallengeRefType, 1: FSDrawCountType })

SamplingExhaustedFailure = SemanticFailureType {
  declaration: ModuleDeclarationRef<"semantic-failure">,
  payload_type: SamplingExhaustedPayloadType
}
```

Here `Root(r,K,n)` in a `ValueType` abbreviates the exact K1
`Root(RootDeclarationRef<K>(r,K,n))`; it is not a digest-only reference. If
`f = T.sampling_exhausted_failure` and its declaration owner is module `m`,
admission requires that declaration to resolve exactly to:

```text
LocalSemanticFailureDeclarationBody(
  "pir.fs.sampling-exhausted",
  SamplingExhaustedPayloadDeclarationType(B))
```

`SamplingExhaustedPayloadDeclarationType(B)` is the K1 declaration-local
version of the payload above: its outer domain is
`Durable(Root(B.semantic_regime.id,"foundation.root-value-domain",7))`, its
schema is `Record`, and fields 0 and 1 use respectively the durable root
natural-domain reference at ordinal 2 with `Nat(2^14 - 1)` and `Nat(2^20)`.
Thus `LiftType_m(SamplingExhaustedPayloadDeclarationType(B))` must equal
`SamplingExhaustedPayloadType` exactly. The declaration module must carry
`B.semantic_regime.id`.

The exact canonical failure coordinate is
`CanonicalSemanticFailureTypeBody(f)`, whose declaration component is
`DeclarationRefBody(Module(f.declaration))`; it is stored in construction
identity. Its only payload datum is
`R{0:N(challenge_ref),1:N(attempted_draws)}` admitted at the payload type. The
result is a semantic `DomainFailure` of the Fiat--Shamir interpretation, not a
Core terminal, fresh-coin source failure, invalid prover message,
evaluator-budget exhaustion, or checker defect. Two same-shaped declarations
owned by different module IDs are different failure coordinates.

### 3.3 Complete subject and identity

```text
TranscriptConstruction = {
  core_id: CoreId,
  transcript_state_type: TranscriptStateType,
  transcript_bytes_type: TranscriptBytesType,
  natural_type: NaturalType,
  initial_state: CanonicalValue<TranscriptStateType>,
  absorb: PIRAlgorithmUse,
  squeeze_bytes: PIRAlgorithmUse,
  advance_state: PIRAlgorithmUse,
  application_domain:
    ProtocolDeclarationRef<"pir.fs-application-domain">,
  sampling_exhausted_failure: SamplingExhaustedFailure,
  challenge_rules: CanonicalSeq<ChallengeRule>
}
```

`challenge_rules` is in ascending `ChallengeRef` order and is total over every
Core challenge. The Core challenge sequence must be nonempty. An empty map over
a zero-challenge Core is not a Fiat--Shamir construction: it transforms no
public coin while adding transcript initialization, absorption, resource, and
noncompletion behavior. Proof hashing or audit logging without a transformed
challenge belongs to Interface, OIR, or Evidence rather than
`ChallengeInterpretation`. The canonical body is in Appendix A:

```text
TranscriptConstructionId =
  ProfiledSemanticId<"pir.transcript-construction">(
    B, PIRCanonicalFramedFSProfileId,
    TranscriptConstructionBody(construction))

AuthenticatedTranscriptConstructionProfile(
  exact authenticated admitted handle for construction) =
  PIRCanonicalFramedFSProfileId
```

The construction body contains no literal copy of its own ID. Initialization
has a fixed semantic `BindConstructionSelfId` step: after authentication,
execution frames the resolved `TranscriptConstructionId`. This is an
instruction fixed by this subject kind, not an editable field or hash fixpoint.

The construction ID commits to the Core, state/value types, initial state,
algorithms and evaluation contracts, application domain, exact sampling
failure coordinate, challenge rule order, draw sizes, bounds, and
acceptance/decoder algorithms. Session and Statement values are runtime
invocation values whose types, scope, order, and binding classes are already
committed by `CoreId`.

### 3.4 Lifecycle

```text
CanonicalTranscriptConstructionCandidate
  --AuthenticateTranscriptConstruction-->
      AuthenticatedTranscriptConstructionCandidate
  --AdmitTranscriptConstruction---------->
      AdmittedTranscriptConstruction
```

Authentication recomputes the typed construction ID and all consulted K1
dependencies in one request-local binding ledger. Admission uses Section 8.
Only an exact admitted construction can form an FS Protocol or resolve a
challenge.

## 4. Canonical transcript frames

### 4.1 Frame algebra

Every absorbed value first becomes one exact K1 `MetaValueV0` body:

```text
TranscriptFrame =
    CoreHeader(CoreId)
  | ConstructionHeader(TranscriptConstructionId)
  | ApplicationDomainHeader(
      ProtocolDeclarationRef<"pir.fs-application-domain">)
  | ScopeOpened(NonEmptyCanonicalSeq<ScopeRef>)
  | PublicBinding {
      binding: BindingRef,
      class: PublicBindingClass,
      value_type: ValueType,
      value: CanonicalValue<value_type>
    }
  | GuardOutcome {
      occurrence: OccurrenceRef,
      active: Boolean
    }
  | ProverMessage {
      occurrence: OccurrenceRef,
      channel: MessageChannelRef,
      value_type: ValueType,
      payload: CanonicalValue<value_type>
    }
  | VerifierMessage { same typed fields }
  | OraclePublication {
      occurrence: OccurrenceRef,
      oracle: OracleRef,
      publication:
          PublishedMaterial {
            publication_mode:
              FullCanonicalOracle | PublicBinding,
            public_material_type: ValueType,
            public_material: CanonicalValue<public_material_type>
          }
        | LogicalAccessFixed {
            origin: OracleOrigin,
            domain_law:
              ProtocolDeclarationRef<"pir.oracle-domain-law">
          }
    }
  | OracleQuery {
      occurrence: OccurrenceRef,
      oracle: OracleRef,
      index_type: ValueType,
      index: CanonicalValue<index_type>
    }
  | OracleAnswer {
      occurrence: OccurrenceRef,
      oracle: OracleRef,
      answer_type: OracleAnswerOutputType(core.oracles[oracle]),
      answer: CanonicalValue<answer_type>
    }
  | ChallengeCondition {
      challenge: ChallengeRef,
      input_ordinal: ordinal,
      value_type: ValueType,
      value: CanonicalValue<value_type>
    }
  | ModuleFrame {
      effect: ModuleEffectRef,
      frame_ordinal: ordinal,
      exact_module_body: MetaValueV0
    }
```

`FrameBody` and tags are fixed in Appendix A. First derive raw octets, then
admit the exact K1 byte datum at the construction's byte type:

```text
FrameOctets(frame) = M(FrameBody(frame))

FrameBytes(frame) =
  CanonicalValue<TranscriptBytesType>(O(FrameOctets(frame)))
```

Construction admission proves from the exact value schemas and module frame
bounds that every possible `FrameOctets` length is at most `L`; runtime still
performs exact byte-value admission before each absorb. K1's injective canonical
encoding and the explicit tag, occurrence coordinate, type, and payload framing
prevent cross-kind, empty-value, concatenation, and reordering aliases. No
caller codec, display label, host serialization, or raw concatenation can
replace `FrameBytes`. Wire/proof serialization remains a separate Interface/OIR
concern. Every `AbsorbUse` evaluation uses the exact evaluator and fresh
per-request limits supplied to that run call's `ExecutionEvaluationControl`.

For each standard frame variant, that proof applies K1's exact `M` size law to
the fixed tag and record fields and substitutes `MaxDatumBytes(value_type)` for
each typed datum. Each supported module rule supplies the corresponding finite
maximum for its exact module body. The construction takes the maximum over all
reachable variants and refuses admission unless it is at most `L`.

### 4.2 Initialization

For admitted construction `T`, initialization is exactly:

```text
s0 = T.initial_state
s1 = Absorb(s0, FrameBytes(CoreHeader(T.core_id)))
s2 = Absorb(s1, FrameBytes(ConstructionHeader(T.id)))
s3 = Absorb(s2, FrameBytes(
       ApplicationDomainHeader(T.application_domain)))
s4 = OpenScope(s3, RootScope)
```

`OpenScope` absorbs `ScopeOpened(root_path)` and then every exact root binding
in ascending `BindingRef` order. The value comes from the admitted invocation
or an already available derived public value. Root opening occurs before the
first Core occurrence and therefore before every prover publication and
challenge.

A child scope opens at its Core-declared boundary. It absorbs its complete path
and every child binding in order before that boundary's guard or action. The
state is the current state from earlier scopes and occurrences; it is never
reset at a composition seam.

### 4.3 Derived occurrence actions

There is no authored event-action map. For each attempted Core occurrence, the
construction derives:

| Core occurrence | Exact transcript action |
|---|---|
| non-`Always` guard | absorb one `GuardOutcome`, whether active or inactive |
| active Prover message | absorb one `ProverMessage` frame |
| active deterministic Verifier message | absorb one `VerifierMessage` frame |
| active Challenge | absorb its condition frames, then run Section 7 |
| active full or bound Oracle publication | absorb its full canonical oracle value or public binding material |
| active logical-access Oracle publication | absorb only `LogicalAccessFixed(origin,domain_law)`; no carrier or carrier-derived digest enters the frame |
| active Public Oracle query | absorb one `OracleQuery` frame |
| active Public Oracle answer | absorb one `OracleAnswer` frame |
| Verifier-only Oracle query/answer | no FS frame; any path from such activity to `PCSinks(core)` is rejected by Section 8 |
| Check, Reduction, Terminal | no direct frame; any later public control dependence is represented by a guard outcome or public derived value |
| supported module effect | exact frames derived by its authenticated `pir.core-effect` declaration |

An `Always` occurrence has no guard frame. An inactive guarded occurrence has
only its false guard frame. Thus an absent publication cannot alias an empty or
different publication, and two control histories reaching a later challenge
have distinct typed frame sequences.

The logical fixation frame proves only that the exact declaration occurrence
was activated. It is invariant across carrier choices and cannot be treated as
a commitment, publication of unqueried entries, or authority to disclose the
carrier. Interactive Core admission rejects same-Core FS whenever that opaque
carrier can influence acceptance; the marker exists only to frame any
semantically dead logical publication without a control-history alias.

Semantically dead verifier-private Oracle activity may coexist with an FS
interpretation when it reaches no member of `PCSinks(core)`. It emits no frame
and its descendant cone must remain disjoint from that exact sink set while the
Core's Challenge special transfer remains valid. This is the ordinary public-
coin dependency criterion, not a special exemption.

An extension declaration's transcript rule is part of the Core's exact-used
semantic module. It returns a bounded canonical frame sequence from the exact
effect occurrence and public outputs. Unknown or unsupported rules refuse
construction admission; the construction cannot select `NoAction` for them.

## 5. Required influence

### 5.1 Influence atoms

The resolver records one exact transition sequence. A draw records the two
separate K1 algorithm evaluations as one atomic FS transition only after both
have completed and the exact-length check has passed:

```text
AbsorbReceipt = {
  frame: TranscriptFrame,
  pre_state: CanonicalValue<TranscriptStateType>,
  post_state: CanonicalValue<TranscriptStateType>
}

DrawReceipt = {
  challenge: ChallengeRef,
  draw_ordinal: ordinal,
  requested_bytes: positive Natural,
  namespace: CanonicalValue<TranscriptBytesType>,
  pre_state: CanonicalValue<TranscriptStateType>,
  post_state: CanonicalValue<TranscriptStateType>,
  output: CanonicalValue<TranscriptBytesType>,
  accepted: Boolean
}

TransitionReceipt = Absorbed(AbsorbReceipt) | Squeezed(DrawReceipt)

FSChallengeReceipt = {
  challenge: ChallengeRef,
  prefix_receipt_count: Natural,
  prefix_state: CanonicalValue<TranscriptStateType>,
  draws: NonEmptyCanonicalSeq<DrawReceipt>,
  accepted_value: CanonicalValue<declared challenge type>,
  post_state: CanonicalValue<TranscriptStateType>
}

FSSamplingFailureReceipt = {
  challenge: ChallengeRef,
  prefix_receipt_count: Natural,
  prefix_state: CanonicalValue<TranscriptStateType>,
  draws: NonEmptyCanonicalSeq<DrawReceipt>,
  final_state: CanonicalValue<TranscriptStateType>
}

FSInterpretationFailureReceipt =
  FiatShamirSamplingFailure {
    construction: TranscriptConstructionId,
    receipt: FSSamplingFailureReceipt
  }
```

Every field is derived and replayed; none is supplied as a shortcut. The last
draw in a successful receipt has `accepted = true`, and all preceding draws
have `accepted = false`. Every draw in a sampling-failure receipt has
`accepted = false`, and its length equals the admitted `maximum_draws`. The
accepted decoder value is recorded once in `FSChallengeReceipt`; a rejected
draw has no decoded-value field.

The exact finite influence-coordinate algebra is:

```text
InfluenceAtom =
    CoreHeaderAtom(CoreId)
  | ConstructionHeaderAtom(TranscriptConstructionId)
  | ApplicationDomainAtom(
      ProtocolDeclarationRef<"pir.fs-application-domain">)
  | ScopeOpenedAtom(NonEmptyCanonicalSeq<ScopeRef>)
  | PublicBindingAtom(BindingRef)
  | GuardOutcomeAtom(OccurrenceRef)
  | ProverMessageAtom(OccurrenceRef)
  | VerifierMessageAtom(OccurrenceRef)
  | OraclePublicationAtom(OccurrenceRef)
  | OracleQueryAtom(OccurrenceRef)
  | OracleAnswerAtom(OccurrenceRef)
  | ChallengeConditionAtom(ChallengeRef, input_ordinal)
  | ModuleFrameAtom(ModuleEffectRef, frame_ordinal)
  | ChallengeDrawAtom(ChallengeRef, draw_ordinal)
```

Appendix A fixes variant tags 0 through 13 in precisely this order and gives
the exact body of each atom. That tag order is the canonical order only when a
canonical sorted set of atoms is required by a module declaration. An
influence trace is never sorted: its sole canonical order is transition order,
with the frames of one occurrence in the order fixed by Section 4 and an
extension's authenticated rule.

Define the exact input projection:

```text
TransitionInput =
    AbsorbInput(TranscriptFrame)
  | DrawInput {
      challenge: ChallengeRef,
      draw_ordinal: ordinal,
      requested_bytes: positive Natural,
      namespace: CanonicalValue<TranscriptBytesType>,
      output: CanonicalValue<TranscriptBytesType>
    }

TransitionInputOf(Absorbed(r)) = AbsorbInput(r.frame)
TransitionInputOf(Squeezed(r)) = DrawInput {
  challenge = r.challenge,
  draw_ordinal = r.draw_ordinal,
  requested_bytes = r.requested_bytes,
  namespace = r.namespace,
  output = r.output
}

InfluenceAtomOf(AbsorbInput(CoreHeader(x))) =
  CoreHeaderAtom(x)
InfluenceAtomOf(AbsorbInput(ConstructionHeader(x))) =
  ConstructionHeaderAtom(x)
InfluenceAtomOf(AbsorbInput(ApplicationDomainHeader(x))) =
  ApplicationDomainAtom(x)
InfluenceAtomOf(AbsorbInput(ScopeOpened(path))) =
  ScopeOpenedAtom(path)
InfluenceAtomOf(AbsorbInput(PublicBinding{binding=b,...})) =
  PublicBindingAtom(b)
InfluenceAtomOf(AbsorbInput(GuardOutcome{occurrence=o,...})) =
  GuardOutcomeAtom(o)
InfluenceAtomOf(AbsorbInput(ProverMessage{occurrence=o,...})) =
  ProverMessageAtom(o)
InfluenceAtomOf(AbsorbInput(VerifierMessage{occurrence=o,...})) =
  VerifierMessageAtom(o)
InfluenceAtomOf(AbsorbInput(OraclePublication{occurrence=o,...})) =
  OraclePublicationAtom(o)
InfluenceAtomOf(AbsorbInput(OracleQuery{occurrence=o,...})) =
  OracleQueryAtom(o)
InfluenceAtomOf(AbsorbInput(OracleAnswer{occurrence=o,...})) =
  OracleAnswerAtom(o)
InfluenceAtomOf(AbsorbInput(
  ChallengeCondition{challenge=c,input_ordinal=j,...})) =
  ChallengeConditionAtom(c,j)
InfluenceAtomOf(AbsorbInput(
  ModuleFrame{effect=e,frame_ordinal=j,...})) =
  ModuleFrameAtom(e,j)

InfluenceAtomOf(DrawInput{challenge=c,draw_ordinal=i,...}) =
  ChallengeDrawAtom(c,i)

TransitionInputLog(receipts) =
  map(receipts in receipt order, TransitionInputOf)

InfluenceTrace(receipts) =
  map(TransitionInputLog(receipts), InfluenceAtomOf)
```

The coordinate projection drops a frame's value but not its kind or exact
owner coordinate. `DerivedPrefix` below compares the full `TransitionInput`,
including exact frame value, namespace, requested length, and squeeze output;
the atom trace cannot substitute for that comparison.

`TransitionInputLog` is not an assertion of cryptographic security. Influence
is always indexed by the actual ordered receipt prefix, never inferred from
transcript state alone: absorb and advance algorithms are not required to be
injective, and cryptographic state binding remains an Analysis assumption.
Thus `InfluenceTrace(receipts)` means only “presented to the admitted state
transition under exact framing.” It does not mean collision resistance,
indifferentiability, entropy, binding, or unpredictability.

### 5.2 Derived requirement

For active Core challenge `c`, first derive one finite requirement predicate
over `InfluenceAtom`. Its base cases select:

1. `CoreHeader`, `ConstructionHeader`, and `ApplicationDomainHeader`;
2. every opened scope path in the active scope ancestry;
3. every Statement, SessionContext, and PublicParameter binding in that
   ancestry;
4. every active prior Prover message;
5. every active prior Verifier message;
6. every active prior Oracle publication's exact public material or exact
   logical-access fixation marker;
7. every active prior public Oracle query and answer;
8. every nontrivial prior guard outcome;
9. every `ChallengeConditionAtom(c,j)` in declared condition order and every
   actual earlier draw of a joint member consumed by `c`;
10. every earlier challenge squeeze coordinate in the continuous state; and
11. every additional prior publication/module atom selected below.

Items 4--8 are limited to prior occurrences in the exact total Core schedule.
A response or query answer after `c` is not retroactively required by `c`.
For each Reduction `r`, every requirement `q` in
`r.required_publications` whose `q.next_challenge = Some(c)` adds every
transcript atom emitted by the active occurrence `q.publication`, in its
ordinary frame order. Core admission has already proved that `c` is the least
required challenge following that publication. A `None` requirement is a
post-last-challenge response and adds no earlier challenge obligation. The
continuous base prefix still carries any such publication to a later challenge
outside that reduction. Construction admission refuses a named prerequisite
that emits no transcript atom on the applicable path. A supported module's
authenticated influence rule can similarly add exact atoms already present in
the pre-draw prefix. Reduction and module rules may strengthen the base
predicate, never remove an atom or name a future/current-draw coordinate.

Runtime guards determine which occurrence frames and additions exist. A false
guard frame for an inactive guarded occurrence remains a base requirement;
effect frames for that inactive occurrence do not exist. Now derive, without
set sorting:

```text
DerivedInfluencePrefix(c) =
  InfluenceTrace(DerivedPrefix(c))

RequiredInfluence(c) =
  filter(DerivedInfluencePrefix(c) in transition order,
         BaseRequired(c, atom)
           or ReductionRequired(c, atom)
           or ModuleRequired(c, atom))
```

Filtering the unique temporal prefix fixes requirement order and multiplicity.
At admission, every base, reduction, and module requirement must resolve
symbolically to one exact prefix occurrence on every applicable finite guard
path; ambiguous, absent, or path-inconsistent coordinates refuse admission.
Immediately before the first draw of `c`, after all of `c`'s condition frames
have been absorbed, the independent runtime law is:


```text
TransitionInputLog(actual_receipts_before_draw_c) = DerivedPrefix(c)
```

Together with the admission-time resolution and the definition of
`RequiredInfluence` as an ordered filter of `DerivedInfluencePrefix`, the
runtime equality entails the exported audit corollary:

```text
RequiredInfluence(c) is an exact order-preserving subtrace of
  InfluenceTrace(actual_receipts_before_draw_c),
with every required atom matched exactly once
```

This subtrace is a derived audit view, not a second weaker runtime escape hatch.
The full-prefix equality prevents an implementation from injecting, omitting,
duplicating, reordering, or substituting any actual frame or draw. Missing,
delayed, wrongly scoped, wrong-kind, or conditionally ambiguous required
material refuses admission or replay at the first affected coordinate. In
particular, no requirement is compared against a state predating its own
condition frame.

### 5.3 Exact prefix

`DerivedPrefix(c)` is the full `TransitionInputLog` obtained by folding
initialization, scope openings, every prior active derived action in Core
order, the challenge occurrence's own non-`Always` guard frame, and then all
of `c`'s `ChallengeCondition` frames in input-ordinal order. It ends after the
last condition absorption and before draw 0 of `c`. It includes earlier draw
inputs and all their retry attempts. It is a function of the admitted Core,
construction, invocation, and prior execution receipts.

No `challenge_prefixes` field is stored in construction identity. A cache or
replay witness may carry the derived sequence but must compare equal before it
is used. A causal subset, event label, dependency list, or event-local absorb
flag cannot replace it.

This subsumes the structural purposes of the current E211--E216 family:

- exact required material cannot be unabsorbed;
- no active prover-controlled publication before a future challenge is
  Wire-only;
- reduction round requirements can add Last-Challenge material;
- every declared Statement occurrence is bound at its scope opening;
- child scope openings reset the local “first challenge” boundary without
  resetting global transcript state; and
- derived occurrence namespaces are collision-free under composition.

The stronger K2 completeness rule also requires every Core public input to have
a binding. K3 must check that an external relation/interface Statement is mapped
to the complete expected `BindingRef` set; PIR cannot infer an omitted external
statement from no declaration at all.

## 6. Challenge namespace

For construction `T`, challenge `c`, and zero-based draw ordinal `i`, derive:

```text
ChallengeNamespaceOctets(T, c, i) = M(R {
  0: Y(ContentRefV0(T.id)),
  1: Y(ContentRefV0(T.core_id)),
  2: S[N(scope_ref) ... exact root-to-c scope path],
  3: N(c),
  4: DeclarationRefBody(Module(core.challenges[c].domain)),
  5: CanonicalValueTypeBody(core.challenges[c].value_type),
  6: CoinCorrelationBody(core.challenges[c].correlation),
  7: N(i)
})

ChallengeNamespace(T, c, i) =
  CanonicalValue<TranscriptBytesType>(O(
    ChallengeNamespaceOctets(T, c, i)))
```

Construction admission proves the exact namespace body has at most `L` raw
octets; runtime performs exact byte-value admission before squeeze. The
namespace contains no display name. A construction cannot author, omit, or
override one field.

Two independent challenge draws have different `(scope path, ChallengeRef,
draw ordinal)` coordinates. Members of an explicit joint group still have
distinct occurrence coordinates, and a joint decoder consumes exact prior
members. Intentional reduction-level reuse cites one Challenge occurrence and
passes its `ReductionUsePolicy`; it creates no second squeeze. Composition
creates a new Core ID and exact child scope paths, then re-runs construction
admission.

A namespace mismatch, reused coordinate, wrong draw ordinal, wrong domain/type,
or namespace not equal to this derivation is `Refused`. Equal human labels and
repeated semantic-purpose domains have no collision effect because the exact
scope and `ChallengeRef` remain in the coordinate.

## 7. Challenge transition

Let `state` be the exact transcript state after all prefix frames and challenge
condition frames for challenge `c`. The resolver first performs the Section 5
full-prefix equality against this exact pre-draw state and exports the derived
required-influence audit view. Let `rule[c]` be the admitted rule.
Every `Evaluate` below uses the exact evaluator and fresh per-request
`PortableEvaluationLimitsV0` from the run call's
`ExecutionEvaluationControl`; those controls are ephemeral and do not enter
construction, Protocol, invocation, receipt, or transcript identity.

```text
for i in 0 .. rule.maximum_draws - 1:
    draw_pre_state = state
    namespace = ChallengeNamespace(T, c, i)
    bytes = Evaluate(T.squeeze_bytes,
        [draw_pre_state, namespace, rule.draw_bytes])

    if OctetLength(bytes) != rule.draw_bytes:
        return Refused(PIR.FiatShamir, SqueezeLengthMismatch)

    next_state = Evaluate(T.advance_state,
        [draw_pre_state, namespace, rule.draw_bytes, bytes])
    state = next_state

    accepted = Evaluate(rule.accept,
        [bytes]
        ++ exact public condition values
        ++ exact prior joint-member challenge values)

    append DrawReceipt {
      challenge = c, draw_ordinal = i,
      requested_bytes = rule.draw_bytes,
      namespace, pre_state = draw_pre_state, post_state = state,
      output = bytes, accepted
    }

    if accepted = false:
        continue

    value = Evaluate(rule.decode,
        [bytes]
        ++ exact public condition values
        ++ exact prior joint-member challenge values)
    return Success(state, value, draw_receipts[0..i])

return DomainFailure(
  T.sampling_exhausted_failure,
  CanonicalValue<SamplingExhaustedPayloadType>(
    R{0:N(c),1:N(rule.maximum_draws)}),
  final_state = state,
  draw_receipts = all attempts)
```

`pre_state` in the appended receipt is the value of `state` at loop entry. The
state update is committed after the length check and before acceptance. Every
false result, including the last one, therefore advances state exactly once;
retry and final exhaustion never roll back. A true result also advances state
before decoding. The returned challenge is never separately absorbed: the
admitted `AdvanceStateUse` transition has already changed the state, and the
draw receipt records its exact input/output coordinate. A later challenge
prefix includes that draw coordinate.

Algorithm `DomainFailure` is impossible because admitted absorb,
squeeze-bytes, advance-state, acceptance, and decode ABIs have empty failure
rows. Wrong provider output is `CheckerFailure`; an exact admitted algorithm
whose successful byte value violates the FS exact-length postcondition is the
owner-qualified `Refused` above; missing provider is `Unsupported`; request
budget exhaustion is `DeterministicLimitExceeded`; malformed bytes or types
fail at their K1 boundaries. Only exhausting semantic false acceptance results
produces the exact `SamplingExhaustedFailure` `DomainFailure`.

`maximum_draws` is the semantic retry bound. A lower incidental evaluator
budget cannot be relabeled as semantic exhaustion. `draw_bytes` is checked
before each squeeze, static state/output capacity is preflighted under the
evaluation contract, and the FS owner performs the exact runtime byte-length
postcondition before permitting state advancement.
Replay may use the same limits or limits componentwise sufficient for the same
deterministic requests. Insufficient limits produce
`DeterministicLimitExceeded`, never a semantic sampling failure or replay
mismatch.

## 8. Construction admission

`AdmitTranscriptConstruction(candidate, AdmittedCore)` runs through the exact
evaluator retained by the supplied admitted-Core handle; a caller cannot
substitute another evaluator. It proceeds in this order:

1. require the exact complete prior-meta basis retained by the supplied Core,
   then authenticate the construction ID/body, exact `CoreId`,
   application-domain and sampling-failure declarations, algorithm IDs/bodies,
   evaluation contracts, primitives, and exact-used module closure in one K1
   ledger;
2. validate Appendix A shape and bounds, require the supplied Core to contain
   at least one Challenge, then require an ordered total nonempty challenge-
   rule map over every and only those challenges, exact references, and no
   unknown fields;
3. require exact equality between the candidate `core_id` and the supplied
   admitted Core;
4. require `PublicCoinEligible(core) = true`, including the empty intersection
   between each logical-access influence cone and the Core's acceptance sinks,
   with first-active-terminal preemption included as an exact control
   dependency;
5. admit the state, bytes, natural, Boolean, and initial-state values, require
   all three common algorithm ABIs from Section 3.1, and preflight each exact
   K1 maximum tagged-completion schema;
6. resolve `sampling_exhausted_failure`, require its exact declaration body,
   lifted payload type, canonical coordinate, regime, and construction-body
   occurrence from Section 3.2;
7. for each challenge in order, derive `SamplingInputTypes(c)`, admit the exact
   Boolean acceptance and challenge-value decoder ABIs and their maximum tagged-
   completion schemas, and check positive draw size and bounds;
8. require support for every exact-used Core effect module's transcript-frame
   and influence derivation rule;
9. derive initialization, scope actions, occurrence actions, every finite
   required-influence predicate/ordered sequence, namespace form, and maximum
   frame/draw work from the
   Core; refuse any missing action, unsupported effect, invalid scope,
   verifier-private influence, or bound crossing;
10. for every reduction requirement with `next_challenge = Some(c)`, check
   that its publication precedes `c` and emits one or more unambiguous derived
   transcript atoms before `c`; and
11. mint one immutable `AdmittedTranscriptConstruction` retaining every exact
    authenticated dependency and derivation result, including the supplied
    Core handle's evaluator identity.

Step 9 does not execute runtime values or prove a cryptographic property. It
checks the totality of the derivation for every finite Core constructor and
guard path. Because actions are derived, there is no positive admission route
for an authored Wire-only proof message, omitted Statement, manual prefix, or
manual namespace.

Authentication success does not imply admission. An admitted construction is
scoped to one Core and cannot be attached to another equal-shaped or related
Core without a new body and ID.

## 9. FS Protocol formation and execution

### 9.1 Protocol admission

```text
AdmitFS(
  AdmittedCore C,
  AdmittedTranscriptConstruction T)
  -> AdmittedFSProtocol
```

requires `T.core_id = C.id` and rechecks the exact retained public-coin and
module-support results. It also requires `C.challenges` to be nonempty; a
zero-challenge Core remains Fresh-valid but cannot form a canonical-framed FS
Protocol. It also requires literal equality of the evaluator
identities retained by `C` and `T`; a same-ID construction admitted elsewhere
is cold-reauthenticated and readmitted before use. The returned FS Protocol
handle retains that evaluator identity. It forms:

```text
Protocol {
  core_id = C.id,
  challenge_interpretation = FiatShamir(T.id)
}
```

and authenticates its `ProtocolId` under the companion page. The corresponding
Fresh Protocol uses the same `C.id` and the closed `Fresh` tag.

### 9.2 Transcript state and resolver

```text
FSTranscriptState = {
  semantic_state: CanonicalValue<TranscriptStateType>,
  transition_receipts: CanonicalSeq<TransitionReceipt>,
  opened_scopes: CanonicalSeq<ScopeRef>,
  resolved_challenges: CanonicalSeq<FSChallengeReceipt>
}
```

At execution start, the FS resolver performs Section 4.2. The Core engine calls
the resolver's deterministic hook before and after each scope/occurrence. The
hook derives exactly the actions in Section 4.3 and commits state atomically.
At a Challenge, it absorbs all condition frames in input-ordinal order, freezes
the pre-draw receipt prefix, checks exact equality with `DerivedPrefix`, exports
the derived `RequiredInfluence` audit view, and only then runs Section 7.

Successful resolution returns the exact challenge value and
`FSChallengeReceipt` to the unchanged Core engine. The exact
`sampling_exhausted_failure` `DomainFailure` returns an `InterpretationFailed`
Protocol record whose interpretation receipt is the exact
`FSSamplingFailureReceipt`; it does not select a Core terminal. All other K1
noncompletion classes produce no semantic Protocol outcome.

### 9.3 Replay

FS replay recomputes initialization, every frame, namespace, squeeze-bytes
result, exact-length check, state advancement, acceptance result, successful
decode, retry, state, challenge receipt, Core effect, check, claim transition,
and terminal or exact sampling-exhaustion failure. It compares the closed
`CompletedProtocolRecord` variant and requires exact field exhaustion. A cached
state digest or prefix is only a comparison witness and cannot replace the
canonical state transition.

Replay proves consistency of one public record with the admitted construction.
It does not prove causal strategy generation, hash security, coin distribution,
or an adversary theorem. The Core engine separately records whether the run was
strategy-generated under a restricted `ProverView`.

### 9.4 Grinding

Fiat--Shamir grinding is expressed in the unchanged Core as:

1. a prior Challenge;
2. an ordinary Prover decision searching private candidates;
3. one published nonce or witness message; and
4. a total Verifier check over the prior challenge and published value.

The search loop is strategy/Plan work and does not clone, rewind, or mutate the
canonical transcript during rejected private candidates. Only the selected
public value gets its derived message frame. Strategy search exhaustion is
operational `Stop`; an invalid supplied value makes the ordinary check false.
Neither path is a false sampling acceptance result or the construction's
`SamplingExhaustedFailure`.

## 10. Checked same-Core construction

### 10.1 Structural question

```text
FSConstructionDefect =
    SharedCoreMismatch
  | ConstructionCoreMismatch
  | TargetConstructionMismatch
  | PublicCoinEligibilityMissing
  | OccurrenceDomainMismatch
  | NonChallengeValueDomainMismatch
  | ChallengeDomainMismatch
  | TargetCoreFieldMismatch

FSConstructionDefectSet =
  CanonicalNonEmptySortedUniqueSeq<FSConstructionDefect in written tag order>

CheckFSConstruction(
  AdmittedFreshProtocol source,
  AdmittedFSProtocol target,
  AdmittedTranscriptConstruction construction)
  -> Qualified<
       Affirmative({
         CheckedFSConstruction,
         ExactCheckedFSConstructionAuthorityBinding,
         CheckedFSConstructionCapability
       })
       | Negative(FSConstructionDefectSet)>
```

The affirmative result contains:

```text
CheckedFSConstruction = {
  source_protocol_id,
  target_protocol_id,
  shared_core_id,
  transcript_construction_id,
  occurrence_map: IdentityOnEveryOccurrenceRef,
  value_map: IdentityOnEveryNonChallengeValueRef,
  challenge_map: IdentityOnEveryChallengeRef,
  conclusion: StructurallyConstructed
}
```

The checker requires:

1. both exact admitted Protocol handles and construction;
2. source interpretation `Fresh` and target interpretation
   `FiatShamir(construction.id)`;
3. literal equality of both `CoreId`s and the construction's `core_id`;
4. affirmative Core public-coin eligibility;
5. successful construction admission and total standard/module action
   derivation;
6. identity maps over all Core coordinates; and
7. no target-side Core field, event, value, claim, check, terminal, scope, or
   extension difference.

A mismatch returns a field-factored negative or qualified noncompletion and
mints no affirmative capability. There is no authored map that can hide a
different Core.

The negative tags are request-comparison facts over the admitted operands.
Their producing predicates are, in written order: unequal source/target Core
IDs; construction/Core disagreement; target/construction disagreement;
absent public-coin eligibility on the source; unequal occurrence domains;
unequal non-Challenge value domains; unequal Challenge domains; and any
unequal Core body field. The checker evaluates all eight comparisons and
emits every applicable tag in canonical order. Several tags may therefore
co-occur when different Core bodies are presented: the domain and field tags
are deliberate diagnostics beneath `SharedCoreMismatch`, not claims that two
equal admitted Core IDs can carry different preimages. Cold authentication
failure, missing preimages, wrong kinds, limit exhaustion, and checker faults
remain qualified noncompletion and never manufacture a negative tag.

`CheckedFSConstruction` has no semantic ID. An affirmative checking occurrence
creates one collision-free owner-local `CheckedFSConstructionResultRef`, an
exact K1 `OwnerLocalSourceAuthorityBinding`, and one fresh opaque
`CheckedFSConstructionCapability`. The binding records the exact result ref,
source and target Protocol IDs, shared Core, construction, full result schema,
affirmative polarity, checker contract, domain-profiled owner payload, explicit
`OwnerDefinesNoPolicy(exact PIR no-policy declaration ID)`, policy closure, and an
`OwnerCapabilityRequirement` for the exact typed consumer and purpose. Its
owner is `"pir"`, its family is `"checked-fs-construction"`, and its local
source coordinate is the exact result-ref object; it contains no live token.
The capability retains the exact live admitted handles, result and
binding objects, checker/evaluator, consumer, purpose, and checking occurrence.
The local binding, capability, and checked-result aggregate are noncopyable and
nonserializable. A copied result, reconstructed binding, equal tuple, stale
capability, different family or purpose, or different result schema grants no
authority. Cold use must reauthenticate and readmit all three subjects and
rerun `CheckFSConstruction`.

For every affirmative result formed by this operation:

```text
CheckedFSConstructionProfile(result.ref) =
  PIRCanonicalFramedFSProfileId
```

### 10.2 Exact meaning

The affirmative result proves only:

- the target replaces the source's public challenge resolution through the
  exact admitted transcript construction;
- all other Core semantics are literally shared; and
- the structural strong-FS, namespace, public-coin, and state-transition gates
  on this page passed.

It does not prove that a property of the Fresh Protocol holds for the FS
Protocol. Analysis must name the source property, adversary model, construction
assumptions, theorem, loss, target property, and exact checked construction.

## 11. Oracle and BCS boundary

The standard Oracle effects preserve a logical IOP/IOR lifecycle:

```text
PublishOracle -> QueryOracle -> AnswerOracle
```

This page does not equate the logical Oracle with a Merkle root. A BCS-like
construction ordinarily creates or relates a concrete Core in which:

- a binding root is published before dependent coins;
- public query positions are derived after those coins;
- answers and authentication paths occur after their queries; and
- exact checks relate openings to the earlier root and query.

The BCS relation, commitment-binding assumption, random-oracle purpose
separation, RBR/state-restoration hypotheses, and quantitative loss are not
`CheckedFSConstruction`. The separate
[Oracle-Commitment Construction](oracle-commitment-construction.md) now owns
the exact structural transformation from a logical-Oracle Core to a concrete
commitment-and-opening Core. Its checked authority establishes deterministic
bounded elaboration and total static correspondence only. Analysis must still
supply every cryptographic assumption, theorem-applicability result, and
property transport. Plain same-Core FS may be used after the concrete target
Core is independently admitted.

`LogicalAccess` is intentionally not a hidden same-Core shortcut. Its
publication frame is only a typed fixation marker and commits to no carrier
entry. If its publication influence cone reaches an accepting Check,
Reduction, Terminal, or acceptance-relevant module sink, structural public-coin
eligibility fails and no transcript construction is admitted for that Core.
The influence cone includes first-active-terminal control: an Oracle answer
that guards an earlier `Reject`, `Abort`, or `Accept` reaches every later
accepting sink that the earlier terminal can preempt. Thus an Oracle-dependent
early `Reject` cannot evade the gate merely because the final fallback
`Accept` has no direct data operand from that Oracle. The separately checked
commitment-and-opening target is the route that makes the prover's prior Oracle
material publicly binding before later challenges.

An Oracle Core also fails same-Core FS when a descendant of its verifier-private
Query or Answer reaches `PCSinks(core)`, or when the Core's special Challenge
transfer is invalid. Such a Core remains Fresh-valid but cannot receive this FS
interpretation. Semantically dead verifier-private or logical-access activity
does not fail merely by existing.
An Oracle Core whose binding, live public queries, answers, and accepting
computation are publicly reconstructible can pass, subject to its exact module
and theorem obligations.

## 12. Composition and session separation

Composing Cores creates a new admitted Core and therefore requires a new
construction scoped to its new `CoreId`. Child scope paths enter every binding
frame and challenge namespace. Transcript state continues through the total
composed schedule; a child scope never initializes a fresh state implicitly.

The construction binds semantic Core identity and application/session
material, not authoring provenance. A `CoreCompositionSpecId`, compiler route,
source filename, or child build history does not enter the transcript unless it
is itself selected as identified public SessionContext. Two routes producing
one exact Core and application domain are intentionally replay-compatible.

Applications needing nonreplay, proof uniqueness, or concurrent-session
separation must supply exact SessionContext values with those semantics. The
mere presence of a session field does not establish freshness.

## 13. Exact source view contracts

The common coordinate, field-path, projection, issuance, and capability laws
are those of
[PIR-owned source views](interactive-core.md#13-pir-owned-source-views). This
page supplies the three construction schemas and one checked-result schema:

```text
CanonicalFramedConstructionViewKind =
    TranscriptDeclarationView
  | RequiredInfluenceView
  | ChallengeTransitionView

CanonicalFramedConstructionViewKindRef(kind) =
  (PIRCanonicalFramedFSProfileId, written tag of kind)

CanonicalFramedFSResultViewKind = FSConstructionView
CanonicalFramedFSResultViewKindRef =
  (PIRCanonicalFramedFSProfileId, written tag of FSConstructionView)

AlgorithmUse = {
  algorithm: PortableAlgorithmRef,
  evaluation_contract: EvaluationContractId
}

CanonicalFrameCoordinate = {
  position: Natural,
  occurrence_ref: OccurrenceRef,
  occurrence_kind: OccurrenceKind
}

TranscriptDeclarationViewBody = {
  transcript_construction_id: TranscriptConstructionId,
  core_id: CoreId,
  state_type: ValueType,
  absorbed_bytes_type: ValueType,
  initial_state: CanonicalValue<state_type>,
  initialization_schedule_law: PIRProfileLawReference,
  absorb: AlgorithmUse,
  squeeze_bytes: AlgorithmUse,
  advance_state: AlgorithmUse,
  application_domain: ProtocolDeclarationRef<"pir.fs-application-domain">,
  sampling_failure_coordinate: SemanticFailureType,
  frame_body_law: PIRProfileLawReference,
  frame_schedule: CanonicalSeq<CanonicalFrameCoordinate>
}

ScopeBindingRequirement = {
  scope_ref: ScopeRef,
  parent: None | Some(ScopeRef),
  opening: None | Some(OccurrenceRef)
}

InfluenceRequirementEntry = {
  atom: InfluenceAtom,
  required: MetaBoolean
}

RequiredInfluenceViewBody = {
  transcript_construction_id: TranscriptConstructionId,
  core_id: CoreId,
  scope_bindings: CanonicalSeq<ScopeBindingRequirement>,
  required_influence: CanonicalSeq<{
    challenge_ref: ChallengeRef,
    entries: CanonicalSeq<InfluenceRequirementEntry>
  }>,
  additions: CanonicalSeq<{
    challenge_ref: ChallengeRef,
    values: CanonicalSeq<ValueRef>
  }>,
  exact_prefix_law: PIRProfileLawReference
}

ChallengeABI = {
  use: AlgorithmUse,
  input_types: CanonicalSeq<ValueType>,
  result_type: ValueType
}

ChallengeTransitionRule = {
  challenge_ref: ChallengeRef,
  position: Natural,
  acceptance_abi: ChallengeABI,
  decoder_abi: ChallengeABI,
  draw_bounds: { squeeze_length: Natural, maximum_draws: Natural }
}

ChallengeTransitionViewBody = {
  transcript_construction_id: TranscriptConstructionId,
  core_id: CoreId,
  namespace_derivation_law: PIRProfileLawReference,
  exact_length_law: PIRProfileLawReference,
  state_update_before_decode_law: PIRProfileLawReference,
  retry_law: PIRProfileLawReference,
  sampling_failure_law: PIRProfileLawReference,
  challenge_rules: CanonicalSeq<ChallengeTransitionRule>
}

FSConstructionViewBody = {
  result_schema: PIRRuntimeSchema,
  fresh_protocol_id: ProtocolId,
  fiat_shamir_protocol_id: ProtocolId,
  shared_core_id: CoreId,
  transcript_construction_id: TranscriptConstructionId,
  occurrence_map: CanonicalSeq<{ source: OccurrenceRef, target: OccurrenceRef }>,
  value_map: CanonicalSeq<{ source: ValueRef, target: ValueRef }>,
  challenge_map: CanonicalSeq<{ source: ChallengeRef, target: ChallengeRef }>,
  structural_conclusion: {
    tag: StructurallyConstructed,
    law: PIRProfileLawReference
  }
}
```

Every `_law` field is a `PIRProfileLawReference` naming one `pir.semantic-law`
declaration of this profile: `initialization_schedule_law`,
`frame_body_law`, and `exact_length_law` name the body-grammar law;
`namespace_derivation_law` and `exact_prefix_law` name the required-influence
law of Section 5; the state-update, retry, and sampling-failure laws name the
admission-and-execution law of Section 8; the conclusion's law names the
checked same-Core construction law of Section 10. `frame_schedule` lists every
framed occurrence in prefix order with its position. `required_influence`
gives, per challenge `c` in ascending `ChallengeRef` order, one entry per
static influence atom of `c`'s schedule universe: the atoms of variant tags 0
through 12 of Section 5.1, in the exact total Core schedule's transition
order, of every transition input that Section 4 frames before the first draw
of `c`, namely the three header atoms, each scope opening due at or before
`c`'s occurrence together with the binding atoms it emits in `BindingRef`
order, the atoms under `InfluenceAtomOf` of every occurrence before `c` in
the total schedule, every `ChallengeConditionAtom` of a challenge at or before
`c`, and every module frame atom scheduled before `c`. An entry's `required`
is true exactly when its atom's coordinate belongs to the symbolic requirement
that Section 5.2's admission resolves for `c` from the base, Reduction, and
module requirements, and false when the atom is only framed. On any admitted
guard path, `RequiredInfluence(c)` of Section 5.2 is exactly the entries with
`required` true whose transition inputs occur on that path, in transition
order, followed by the run's draw atoms of variant tag 13 that items 9 and 10
of Section 5.2 select; draw atoms depend on the run and are never enumerated
statically. The entries carry the exact atom algebra rather than an
occurrence-kind summary: two public bindings emitted at one opening are two
`PublicBindingAtom` entries with distinct `BindingRef`s, and a header atom
carries its identifier. `additions` are the Reduction and module values a
challenge additionally absorbs; `challenge_rules` gives, per challenge in
ascending `ChallengeRef` order, that challenge's own acceptance ABI, decoder
ABI, and draw bounds together with its occurrence's `frame_schedule`
position, projected entry by entry from the construction's `challenge_rules`,
so a construction whose rules differ in ABI or bounds has one exact view and
no singleton field that two producers could fill differently, while the laws
shared by every rule appear once; the three maps are identity maps written
out entry by entry, so a consumer reads the correspondence rather than a
slogan; `result_schema` is the description of the `CheckedFSConstruction`
result, and the owner-local result reference is not a body field. The execution view's `visible_history_law` and
`relation_run_view_issuance_law` name the Interaction profile's visible-history
and run-view-issuance laws through imported declaration dependencies,
`generated_execution_law` names the protocol-execution law of Section 9.2, and
`replay_qualification_law` names the replay law of Section 9.3. The complete
selection, which the field resolver and `StaticViewBody` consume exactly as
the Interaction page states for its own table, is:

```text
PIRStaticViewLawFieldSelection(CanonicalFramedFiatShamir) = CanonicalMap [
  (TranscriptDeclarationView, initialization_schedule_law)
      -> canonical-framed-body-grammar-v0,
  (TranscriptDeclarationView, frame_body_law)
      -> canonical-framed-body-grammar-v0,
  (RequiredInfluenceView, exact_prefix_law)
      -> canonical-framed-prefix-and-domain-v0,
  (ChallengeTransitionView, namespace_derivation_law)
      -> canonical-framed-prefix-and-domain-v0,
  (ChallengeTransitionView, exact_length_law)
      -> canonical-framed-body-grammar-v0,
  (ChallengeTransitionView, state_update_before_decode_law)
      -> canonical-framed-admission-and-execution-v0,
  (ChallengeTransitionView, retry_law)
      -> canonical-framed-admission-and-execution-v0,
  (ChallengeTransitionView, sampling_failure_law)
      -> canonical-framed-admission-and-execution-v0,
  (FSConstructionView, structural_conclusion.law)
      -> canonical-framed-same-core-construction-v0,
  (ExecutionView, visible_history_law)
      -> interaction visible-history-v0, imported,
  (ExecutionView, generated_execution_law)
      -> canonical-framed-protocol-execution-v0,
  (ExecutionView, replay_qualification_law)
      -> canonical-framed-replay-v0,
  (ExecutionView, relation_run_view_issuance_law)
      -> interaction run-view-issuance-v0, imported
]
```

Every right-hand side is a `pir.semantic-law` declaration of this profile's
catalog, or of the Interaction profile where marked imported, at its catalog
ordinal.

The first three coordinates are
`ConstructionView(TranscriptConstructionId,
CanonicalFramedConstructionViewKindRef(kind))` and are issued by the common
`IssuePIRStaticView` operation from the exact admitted construction, its Core,
their inert authority bindings, and matching fresh capabilities.
`FSConstructionView` is not exported by construction admission. Its coordinate
is `FSResultView(CheckedFSConstructionResultRef,
CanonicalFramedFSResultViewKindRef)`, and it is
issued only by:

```text
IssueFSConstructionView(
  exact affirmative CheckedFSConstruction result,
  exact ExactCheckedFSConstructionAuthorityBinding,
  matching fresh CheckedFSConstructionCapability,
  exact closed PIRStaticViewReadManifest,
  exact PIR evaluator and limits)
    -> PIRStaticViewIssueOutcome
```

The operation reruns result/binding/capability equality, resolves the exact
result-view schema, computes the required field closure, and requires realized
reads to equal the manifest. Any result field closes to all four owner subjects
and the exact checked-result schema; a map field additionally closes to both
its source and target coordinate domains. Missing capability is
`MissingDependency`; wrong result origin or stale/equal-looking authority is
`Refused`; malformed, duplicate, extra, or nonclosed reads are `Malformed`.
No nonaffirmative check result can issue a view or partial projection. The
`CheckedFSConstructionResultRef` is live authority outside the body: it
selects the result and is compared exactly at issuance, but it is not a body
field, because it has no serialization. The body carries the identities the
reference commits to, and the coordinate's body-safe form below carries the
same identities with the result schema.

This profile's view catalog has the same form as the Interaction catalog:

```text
CanonicalFramedViewSchemaCatalog = {
  TranscriptDeclarationView: StaticViewSchema(TranscriptDeclarationView),
  RequiredInfluenceView:     StaticViewSchema(RequiredInfluenceView),
  ChallengeTransitionView:   StaticViewSchema(ChallengeTransitionView),
  FSConstructionView:        StaticViewSchema(FSConstructionView),
  ExecutionView:             StaticViewSchema(ExecutionView)
}

StaticViewSchema(TranscriptDeclarationView) = {
  owner: ConstructionView(TranscriptConstructionId, TranscriptDeclarationView),
  body: TranscriptDeclarationViewBody,
  derivation: construction admission (Section 8),
  resolver: PIRStaticViewFieldResolution,
  closure: RequiredPIRViewReadClosure,
  binding: CanonicalFramedStaticViewSourceBinding,
  capability: PIRStaticViewCapability
}

StaticViewSchema(RequiredInfluenceView) = {
  owner: ConstructionView(TranscriptConstructionId, RequiredInfluenceView),
  body: RequiredInfluenceViewBody,
  derivation: required influence and construction admission (Sections 5 and 8),
  resolver: PIRStaticViewFieldResolution,
  closure: RequiredPIRViewReadClosure,
  binding: CanonicalFramedStaticViewSourceBinding,
  capability: PIRStaticViewCapability
}

StaticViewSchema(ChallengeTransitionView) = {
  owner: ConstructionView(TranscriptConstructionId, ChallengeTransitionView),
  body: ChallengeTransitionViewBody,
  derivation: challenge transition and construction admission
              (Sections 7 and 8),
  resolver: PIRStaticViewFieldResolution,
  closure: RequiredPIRViewReadClosure,
  binding: CanonicalFramedStaticViewSourceBinding,
  capability: PIRStaticViewCapability
}

StaticViewSchema(FSConstructionView) = {
  owner: FSResultView(CheckedFSConstructionResultRef, FSConstructionView),
  body: FSConstructionViewBody,
  derivation: checked same-Core construction (Section 10),
  resolver: PIRStaticViewFieldResolution,
  closure: RequiredPIRViewReadClosure,
  binding: CanonicalFramedStaticViewSourceBinding,
  capability: PIRStaticViewCapability
}

StaticViewSchema(ExecutionView) = {
  owner: ProtocolView(ProtocolId, ExecutionView) of a canonical-framed Protocol,
  body: CanonicalFramedExecutionViewBody,
  derivation: construction admission and execution (Sections 8 and 9) over
              challenge-parameterized execution of the Interaction page,
  resolver: PIRStaticViewFieldResolution,
  closure: RequiredPIRViewReadClosure,
  binding: CanonicalFramedStaticViewSourceBinding,
  capability: PIRStaticViewCapability
}

CanonicalFramedExecutionViewBody = {
  protocol_id: ProtocolId,
  core_id: CoreId,
  transcript_construction_id: TranscriptConstructionId,
  challenge_interpretation: ChallengeInterpretation,
    exactly FiatShamir(transcript_construction_id),
  visible_history_law: PIRProfileLawReference,
  resolver_coordinates: CanonicalSeq<{
    challenge_ref: ChallengeRef,
    occurrence_ref: OccurrenceRef,
    value_type: ValueType,
    frame_schedule_coordinate: the challenge occurrence's entry of the
      transcript declaration view's frame_schedule,
    decoding_coordinate: the challenge's entry of the challenge-transition
      view's challenge_rules
  }>,
  generated_execution_law: PIRProfileLawReference,
  run_record_schema: PIRRuntimeSchema,
    exactly the description of CompletedProtocolRecord(P) with
    FSChallengeReceipt and FSInterpretationFailureReceipt,
  interpretation_failure_schema: None | PIRRuntimeSchema,
    exactly the description of FSSamplingFailureReceipt,
  outcome_partition: PIRRuntimeSchema,
    exactly the description of ProtocolOutcomeLane(P), six lanes,
  replay_qualification_law: PIRProfileLawReference,
  relation_run_view_issuance_law: PIRProfileLawReference
}
```

A canonical-framed Protocol's `ExecutionView` is owned by this profile and
never by the Interaction profile: its interpretation names the construction,
its record schema carries the framed draw/retry receipt and the sampling
failure receipt, and its outcome partition has the `InterpretationFailed`
lane.

The construction-view closure is likewise exact: a frame field closes to its
algorithm/contract, source occurrence and prefix position; an influence entry
closes to the complete ordered requirement of its challenge and every Core
coordinate its atom names; a challenge-transition rule closes to its own
challenge's namespace, draw, state, decoder, retry, and failure semantics
together with the laws shared by every rule. Thus a consumer cannot read an
application-domain label, challenge sampler, or influence set while omitting
the law that gives it meaning.

Analysis must read these exact views when selecting an FS theorem. It may add
ROM/QROM model, strategy class, query bounds, soundness notion, hash/codec/
sampler assumptions, binding assumptions, and quantitative loss. It may not
substitute a second transcript declaration, treat construction admission as a
checked Fresh/FS result, or infer structural success from a theorem citation.

OIR may later read the same occurrence and framing coordinates to project proof
serialization and challenge execution, but endpoint correctness cannot change
this construction's meaning. Evidence binds concrete observations to exact
algorithm and construction IDs.

This profile compiles its own source-authority subjects over exactly the two
families it issues: the static views of this section (arm 0, family
`"static-view"`, values tagged `StaticView(y)`, under an explicit no-policy
declaration) and the checked construction result of Section 10 (arm 1,
family `"checked-fs-construction"`, values tagged `CheckedConstruction(y)`,
likewise under a no-policy declaration). Each compiler is a function of the
tagged family value; the identities of both families are formed by the
Interaction page's `PIRStaticView*Id(PIRCanonicalFramedFSProfileId, x)`
constructors, which select this profile's compilers and never apply
`ProfiledSemanticId` to a family-local body. The consumer and purpose roles are
the common Interaction role bodies applied with `PIRCanonicalFramedFSProfileId`;
the path-step, atomic-boundary, and description bodies are those of the
Interaction page.

```text
CanonicalFramedConstructionViewKindBody = V(0,Unit) | V(1,Unit) | V(2,Unit)

CanonicalFramedViewCoordinateBody(x) = R {
  0: V(0, R{0:ContentRef(protocol_id)})
   | V(1, R{0:ContentRef(transcript_construction_id),
            1:CanonicalFramedConstructionViewKindBody(kind)})
   | V(2, R{0:ContentRef(fresh_protocol_id),
            1:ContentRef(fiat_shamir_protocol_id),
            2:ContentRef(shared_core_id),
            3:ContentRef(transcript_construction_id),
            4:PIRDescriptionBody(result_schema)}),
  1: ContentRef(x.semantic_language_profile_id)
}

CanonicalFramedFieldCoordinateBody(x) = R {
  0: CanonicalFramedViewCoordinateBody(x.view_coordinate),
  1: S[ PIRViewPathStepBody(step) ... ],
  2: PIRViewAtomicBoundaryBody(x.boundary)
}

CanonicalFramedStaticViewBindingPayloadBody(x) = R {
  0: CanonicalFramedViewCoordinateBody(x.coordinate),
  1: S[ CanonicalFramedFieldCoordinateBody(c) ... ascending, no repeat ]
}
CheckedFSConstructionBindingPayloadBody(x) = R {
  0: ContentRef(x.fresh_protocol_id),
  1: ContentRef(x.fiat_shamir_protocol_id),
  2: ContentRef(x.shared_core_id),
  3: ContentRef(x.transcript_construction_id),
  4: PIRDescriptionBody(x.result_schema),
  5: ContentRef(x.checker_contract)
}
CanonicalFramedRequirementBody(x) = R {
  0: ContentRef(x.consumer_role_id), 1: ContentRef(x.purpose_role_id)
}
CanonicalFramedNoPolicyBody(x) = R {
  0: ContentRef(x.owner_profile_id)
}
CanonicalFramedClosureBody(x) = R {
  0: ContentRef(x.binding_payload_id), 1: ContentRef(x.no_policy_id),
  2: ContentRef(x.capability_requirement_id)
}

CanonicalFramedSourceBindingPayloadBody(x) =
    V(0, CanonicalFramedStaticViewBindingPayloadBody(y))
      if x = StaticView(y)
  | V(1, CheckedFSConstructionBindingPayloadBody(y))
      if x = CheckedConstruction(y)
CanonicalFramedSourceCapabilityRequirementBody(x) =
    V(0, CanonicalFramedRequirementBody(y)) if x = StaticView(y)
  | V(1, CanonicalFramedRequirementBody(y)) if x = CheckedConstruction(y)
CanonicalFramedSourceNoPolicyBody(x) =
    V(0, CanonicalFramedNoPolicyBody(y)) if x = StaticView(y)
  | V(1, CanonicalFramedNoPolicyBody(y)) if x = CheckedConstruction(y)
CanonicalFramedSourcePolicyClosureBody(x) =
    V(0, CanonicalFramedClosureBody(y)) if x = StaticView(y)
  | V(1, CanonicalFramedClosureBody(y)) if x = CheckedConstruction(y)
```

The result-view coordinate is body-safe: arm 2 of
`CanonicalFramedViewCoordinateBody` carries the four identities and the result
schema that the owner-local result reference commits to, and never the
reference itself. `CanonicalFramedStaticViewSourceBinding` and the
`ExactCheckedFSConstructionAuthorityBinding` of Section 10 are the
`OwnerLocalSourceAuthorityBinding` values formed from these identities under
their families.

## 14. Admission failures and nonclaims

PIR reports owner-specific reasons while preserving K1's outer distinctions.
Examples include:

| Boundary | Result class |
|---|---|
| noncanonical construction body or ID/body mismatch | `Malformed` |
| wrong Core/algorithm/contract kind, regime, or ABI | `KindMismatch` |
| absent exact dependency preimage | `MissingDependency` |
| authenticated but evaluator-unsupported effect or algorithm | `Unsupported` |
| non-public-coin Core; late/omitted binding; invalid rule totality; namespace/prefix/influence mismatch | `Refused` |
| admitted squeeze result has a byte length different from the requested count | owner-qualified `Refused(PIR.FiatShamir, SqueezeLengthMismatch)` |
| K1 request budget exhausted before semantic transition | `DeterministicLimitExceeded` |
| provider disagrees with admitted absorb/squeeze-bytes/advance-state/accept/decode evaluation | `CheckerFailure` |
| admitted acceptance returns false for every semantic draw | exact typed `SamplingExhaustedFailure` `DomainFailure` |

Passing these structural boundaries establishes none of the following:

- collision resistance, random-oracle behavior, indifferentiability, entropy,
  uniformity, independence, constant time, or side-channel resistance;
- soundness, adaptive soundness, knowledge extraction, completeness, zero
  knowledge, state-restoration/RBR security, or QROM security;
- adequacy of an oracle binding, commitment, opening scheme, or BCS compiler;
- proof serialization uniqueness or endpoint parser safety;
- causal generation of a record that was only replayed; or
- production support for the identified algorithms or construction.

### 14.1 Exact construction boundary

The construction defined on this page is one closed **canonical-framed**
construction,
not a universal normal form for every Fiat--Shamir transform. Its fixed
initial state, Core/construction/application headers, typed binding and message
frames, derived challenge namespaces, and bounded retry are all semantic
parts of this profile.

In particular, this page does not literally represent Construction 4.3 of
Chiesa and Orrù's
[*A Fiat--Shamir Transformation From Duplex Sponges*](https://eprint.iacr.org/2025/536).
That construction initializes from the runtime instance, absorbs one
proof-carried salt owned by the transform, absorbs raw fixed-codec prover
messages without zkc headers or namespaces, and uses one-shot total decoding.
Its explicit mutable state machine and construction-public material are owned
by the separate
[Duplex-Sponge Fiat--Shamir Construction](duplex-sponge-fiat-shamir.md).

Treating the salt as Core SessionContext or as an extra Core prover message
would change the Fresh source interaction. Treating typed zkc frames as the
paper's raw codec would claim correspondence to a different transcript. Neither
is an admissible workaround. The sibling profile leaves this construction
unchanged and gives the duplex family a distinct construction and Protocol
identity. None of its security theorems applies to this page's construction,
and the sibling itself activates no theorem without a separate Analysis
correspondence, source-validation result, and applicability judgment.

<!-- zkc-profile-source:canonical-framed-fs-semantics:end -->

## 15. Bounded executable evidence

The repository package
[`evaluation/k2-protocol-fiat-shamir/`](../../evaluation/k2-protocol-fiat-shamir/)
provides bounded executable pressure for the lifecycle, causal/public-coin
refusals, transcript order, retries, replay, composition, and selected
reduction shapes defined here. Its Appendix-A contract vectors use the exact K1
carrier for guard Booleans and present/absent Oracle-answer result values.

The remaining fixture is intentionally smaller than the durable carrier. It
does not execute raw Core canonical bodies, nonserializable causal or replay
capabilities, the complete Foundation algorithm request ABI, the complete PC graph
and module-sink algebra, first-class reduction effects, generic typed Oracle
indices, or OIR serialization. Fixture success is therefore structural and
behavioral evidence for the named finite cases, not implementation conformance,
cryptographic security, or theorem evidence.

The additive
[`evaluation/native-fri-ior/`](../../evaluation/native-fri-ior/README.md)
package includes an exact three-fold, scalar-terminal classical FRI control.
It exercises a logical-Oracle source Core, an independently elaborated
committed Core, statement-bound Fresh and strong-Fiat--Shamir executions, and
a separately coded public replay. That finite control establishes neither a
commitment-security theorem nor any FRI or Fiat--Shamir security property.

## 16. Reopening conditions

Reopen this construction if a later protocol inhabitant requires:

- challenge derivation from verifier-private state under a justified transform;
- an exact distribution that cannot use a total decoder or bounded semantic
  retry;
- deliberate challenge correlation not expressible by a joint group, or
  reduction-level reuse not expressible by `ReductionUsePolicy`;
- transcript rollback, fork, merge, or tree state as semantic meaning;
- an event whose required influence cannot be derived from an exact supported
  module rule;
- a dynamic Statement introduced after its active scope's first challenge;
- theorem-qualified pre-challenge prover material that must deliberately remain
  unabsorbed without weakening the default strong-FS rule;
- a same-Core transformation whose verifier-observable interaction actually
  changes.

Runtime-instance initialization, transform-owned public proof material, and
raw fixed-codec overwrite semantics route to the duplex sibling and do not
reopen this family. Any further materially different construction routes to a
new exact sibling or checked prior construction, not an opaque callback,
manual prefix, skip flag, or theorem name stored in the Core.
K2 intentionally chooses the stricter baseline in which every active prior
prover publication is absorbed. A future theorem-backed relaxation must define
a distinct checked source/target construction and Analysis obligation; it may
not be an authored per-message omission flag.

<!-- zkc-profile-source:canonical-framed-fs-body-grammar:start -->

## Appendix A. Canonical bodies

Use the K1 notation from the companion page: `R{...}`, `S[...]`, `V(tag,x)`,
`MF`, `MT`, `N(n)`, `Q(symbol)`, `Y(bytes)`, `Unit`, `ContentRefV0`,
`CanonicalValueTypeBody`, and admitted canonical datums. Fields are exact,
ordered, and closed.

```text
ChallengeRuleBody(x) = R {
  0: N(x.challenge),
  1: N(x.draw_bytes),
  2: N(x.maximum_draws),
  3: PIRAlgorithmUseBody(x.accept),
  4: PIRAlgorithmUseBody(x.decode)
}

TranscriptConstructionBody(T) = R {
  0: Y(ContentRefV0(T.core_id)),
  1: CanonicalValueTypeBody(T.transcript_state_type),
  2: CanonicalValueTypeBody(T.transcript_bytes_type),
  3: CanonicalValueTypeBody(T.natural_type),
  4: T.initial_state.datum,
  5: PIRAlgorithmUseBody(T.absorb),
  6: PIRAlgorithmUseBody(T.squeeze_bytes),
  7: PIRAlgorithmUseBody(T.advance_state),
  8: DeclarationRefBody(Module(T.application_domain)),
  9: CanonicalSemanticFailureTypeBody(T.sampling_exhausted_failure),
 10: S[ ChallengeRuleBody(rule) ... ]
}
```

The construction body does not repeat a `core_id` outside field 0 or store
derived prefixes, namespaces, statement maps, effect actions, dependency
closures, algorithm ABIs, direct primitive sets, or its self ID. Each is
recomputed from the exact authenticated sources.

Frame bodies are:

```text
FrameBody =
  V(0, Y(ContentRefV0(core_id)))
| V(1, Y(ContentRefV0(transcript_construction_id)))
| V(2, DeclarationRefBody(Module(application_domain_ref)))
| V(3, S[N(scope_ref) ...])
| V(4, R{
      0:N(binding_ref),
      1:PublicBindingClassBody(class),
      2:CanonicalValueTypeBody(value_type),
      3:value.datum})
| V(5, R{0:N(occurrence_ref),1:MetaBooleanDatum(active)})
| V(6, MessageFrameBody)
| V(7, MessageFrameBody)
| V(8, OraclePublicationFrameBody)
| V(9, OracleQueryFrameBody)
| V(10, OracleAnswerFrameBody)
| V(11, R{
      0:N(challenge_ref),
      1:N(input_ordinal),
      2:CanonicalValueTypeBody(value_type),
      3:value.datum})
| V(12, R{
      0:FSModuleEffectCoordinateBody(effect),
      1:N(frame_ordinal),
      2:exact_module_body})

MessageFrameBody = R {
  0:N(occurrence_ref),
  1:DeclarationRefBody(Module(channel_ref)),
  2:CanonicalValueTypeBody(value_type),
  3:payload.datum
}

FSModuleEffectCoordinateBody(x) = R {
  0:Y(ContentRefV0(x.module)),
  1:DeclarationRefBody(Module(x.declaration)),
  2:x.payload
}

OraclePublicationFrameBody = R {
  0:N(occurrence_ref),
  1:N(oracle_ref),
  2:
    V(0,R{
      0:OraclePublicationModeBody(mode),
      1:CanonicalValueTypeBody(public_material_type),
      2:public_material.datum})
  | V(1,R{
      0:OracleOriginBody(origin),
      1:ModuleDeclarationRefBody(domain_law)})
}

The outer publication tag `0` forms only when `mode` is
`FullCanonicalOracle` or `PublicBinding`; tag `1` forms only for the exact
`LogicalAccess` declaration and carries its Core-owned origin and domain-law
reference. A logical carrier, carrier digest, invented binding value, or
published-material tag with logical mode is malformed.

OracleQueryFrameBody = R {
  0:N(occurrence_ref),
  1:N(oracle_ref),
  2:CanonicalValueTypeBody(index_type),
  3:index.datum
}

OracleAnswerFrameBody = R {
  0:N(occurrence_ref),
  1:N(oracle_ref),
  2:CanonicalValueTypeBody(
      OracleAnswerOutputType(core.oracles[oracle_ref])),
  3:answer.datum
}
```

Here `MetaBooleanDatum` is the Foundation total constructor for `MF` and `MT`;
neither case is a `MetaVariant`. For a `FullCanonicalOracle` or `PublicBinding` Oracle, an
answer datum is the exact Core-owned lookup-result sum: `V(0,Unit)` when absent
or `V(1,element.datum)` when present. For `LogicalAccess`, the exact-domain law
makes absence unformable and the answer datum is the bare element admitted at
`o.element_type`. In both cases the framing type is exactly
`OracleAnswerOutputType(o)` and no frame may choose the other arm.

The exact influence and transition-input bodies are:

```text
InfluenceAtomBody =
  V(0,Y(ContentRefV0(core_id)))
| V(1,Y(ContentRefV0(transcript_construction_id)))
| V(2,DeclarationRefBody(Module(application_domain_ref)))
| V(3,S[N(scope_ref)...])
| V(4,N(binding_ref))
| V(5,N(occurrence_ref))
| V(6,N(occurrence_ref))
| V(7,N(occurrence_ref))
| V(8,N(occurrence_ref))
| V(9,N(occurrence_ref))
| V(10,N(occurrence_ref))
| V(11,R{0:N(challenge_ref),1:N(input_ordinal)})
| V(12,R{
      0:FSModuleEffectCoordinateBody(effect),
      1:N(frame_ordinal)})
| V(13,R{0:N(challenge_ref),1:N(draw_ordinal)})

TransitionInputBody =
  V(0,FrameBody(frame))
| V(1,R{
      0:N(challenge_ref),
      1:N(draw_ordinal),
      2:N(requested_bytes),
      3:namespace.datum,
      4:output.datum})
```

Tags 0 through 13 of `InfluenceAtomBody` correspond one-for-one to the algebra
in Section 5.1. When an authenticated module declaration needs a canonical
sorted-unique atom set, it sorts by the full bytes
`M(InfluenceAtomBody(atom))`; runtime `InfluenceTrace` instead preserves
transition order. `TransitionInputBody` is interpreted under the construction's
exact `TranscriptBytesType`, so both datums are owner-admitted at that type
before comparison. It is an exact structural comparison form, not a single
`MetaValueV0` submitted to `M`; no implementation may concatenate its two byte
datums and treat the resulting aggregate as another transcript byte value.

The message variants 6 and 7 distinguish Prover from Verifier without another
party field. Boolean false and true use the `MF` and `MT` cases above. Reused bodies
such as `PublicBindingClassBody`, `CoinCorrelationBody`,
and `OraclePublicationModeBody` are exactly those in
[Interactive Core Appendix A](interactive-core.md#appendix-a-canonical-bodies).

For `f = T.sampling_exhausted_failure`, its canonical coordinate is exactly
`CanonicalSemanticFailureTypeBody(f)`, and its completed payload datum is:

```text
R { 0:N(challenge_ref), 1:N(attempted_draws) }
```

The datum is admitted at `SamplingExhaustedPayloadType`; its two fields are not
an untyped diagnostic record. The declaration body and declaration-local type
are exactly those in Section 3.2.

Changing any tag, field, order, derived action, namespace law, transition, or
admission predicate rotates `PIRCanonicalFramedFSProfile` and every downstream
profile that imports it. It does not rotate an unreferenced duplex-sponge or
future sibling. A module-owned declaration change instead rotates
that module and its exact users. The shared Foundation semantic regime rotates
only when a Foundation-owned mechanism or its interpretation changes. Old
bytes are never reinterpreted.

<!-- zkc-profile-source:canonical-framed-fs-body-grammar:end -->
