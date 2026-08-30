# Fiat--Shamir Construction

> **Document kind:** Target semantic specification
> **Document state:** Active non-normative redesign target
> **Target status:** The bounded construction, strong-influence, and same-Core
> eligibility model is complete; theorem applicability and property transport
> remain separate open Analysis work.
> **Provisional owner:** `pir`
> **Authority:** None during the transition. Current normative Fiat--Shamir
> semantics remain under [`docs/`](../../docs/README.md).

## 1. Contract

This page is the sole target definition owner for:

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
`ProtocolDeclarationRef<"pir.fs-application-domain">` with the exact nominal
declaration body defined by the companion page. It is an authenticated static
application-purpose coordinate, not a display string or a freshness claim.

This page selects one standalone `PIRTranscriptFSProfile`. Its required exact
profile imports are `{PIRInteractionProfileId}`; its supported subject kinds are
`{"pir.transcript-construction", "pir.protocol",
"pir.source-binding-payload", "pir.source-capability-requirement",
"pir.source-consumer", "pir.source-no-policy",
"pir.source-policy-closure", "pir.source-purpose"}`; and its inline declaration
catalog contains `TranscriptConstructionBody`, `FSProtocolBody`, the three
construction-view schemas, `FSConstructionViewBody`, and their closure and
issuance laws. There is intentionally no second FS-only profile:
`PIRFSProfileId = PIRTranscriptFSProfileId`. A construction and an FS Protocol
therefore rotate together when transcript/FS meaning changes, while a Fresh
Protocol remains under `PIRInteractionProfileId`. The profile import is the
only generic upstream closure; it is not a declaration-module root.
Construction formation, FS Protocol/view issuance, and checked-construction
authority authenticate exactly the two-entry
`{PIRInteractionProfileId,PIRTranscriptFSProfileId}` closure and require only
`PIRTranscriptFSProfileId` in evaluator support. Public-setup-profile support is
irrelevant to those operations. An unrecognized exact root is `Unsupported`,
while a supported root omitting any emitted Protocol, construction, or
owner-authority subject kind is `Refused`.

This fixes the target owner, import topology, supported-kind set, catalog
responsibility, and no-extra closure law. It does not yet publish the complete
six-field K1 profile preimage or its full typed ID. The deterministic profile
pin used by the bounded executable witness tests topology, authentication, and
rotation only and is not semantic authority. This page must publish the
complete owner-local preimage and independently reconstructible full typed ID
before any dependent K4 ID is treated as persistent and before K5 freeze.

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

## 3. Construction subject

### 3.1 Exact algorithm uses

```text
AlgorithmUse = {
  algorithm: PortableAlgorithmRef,
  evaluation_contract: EvaluationContractId
}
```

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
  accept: AlgorithmUse,
  decode: AlgorithmUse
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
  absorb: AlgorithmUse,
  squeeze_bytes: AlgorithmUse,
  advance_state: AlgorithmUse,
  application_domain:
    ProtocolDeclarationRef<"pir.fs-application-domain">,
  sampling_exhausted_failure: SamplingExhaustedFailure,
  challenge_rules: CanonicalSeq<ChallengeRule>
}
```

`challenge_rules` is in ascending `ChallengeRef` order and is total over every
Core challenge. The canonical body is in Appendix A:

```text
TranscriptConstructionId =
  ProfiledSemanticId<"pir.transcript-construction">(
    B, PIRTranscriptFSProfileId,
    TranscriptConstructionBody(construction))
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
2. validate Appendix A shape, bounds, ordered total challenge-rule map, exact
   references, and no unknown fields;
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
module-support results. It also requires literal equality of the evaluator
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
ConstructionStaticViewKind =
    TranscriptDeclarationView
  | RequiredInfluenceView
  | ChallengeTransitionView

TranscriptDeclarationViewBody = {
  transcript_construction_id: TranscriptConstructionId,
  core_id: CoreId,
  state_type,
  absorbed_bytes_type,
  initial_state,
  initialize_algorithm_and_contract,
  absorb_algorithm_and_contract,
  squeeze_bytes_algorithm_and_contract,
  advance_state_algorithm_and_contract,
  application_domain,
  sampling_failure_coordinate,
  frame_body_law,
  exact_frame_schedule_coordinates
}

RequiredInfluenceViewBody = {
  transcript_construction_id: TranscriptConstructionId,
  core_id: CoreId,
  influence_atom_algebra,
  scope_binding_requirements,
  per_challenge_ordered_required_influence_sets,
  reduction_and_module_additions,
  exact_prefix_law
}

ChallengeTransitionViewBody = {
  transcript_construction_id: TranscriptConstructionId,
  core_id: CoreId,
  challenge_namespace_derivation,
  acceptance_abi,
  decoder_abi,
  draw_bounds,
  exact_length_law,
  state_update_before_decode_law,
  retry_law,
  sampling_failure_law,
  challenge_decoding_coordinates
}

FSConstructionViewBody = {
  result_ref: CheckedFSConstructionResultRef,
  result_schema: exact CheckedFSConstruction schema,
  fresh_protocol_id: ProtocolId,
  fiat_shamir_protocol_id: ProtocolId,
  shared_core_id: CoreId,
  transcript_construction_id: TranscriptConstructionId,
  occurrence_map: IdentityOnEveryOccurrenceRef,
  value_map: IdentityOnEveryNonChallengeValueRef,
  challenge_map: IdentityOnEveryChallengeRef,
  structural_conclusion: StructurallyConstructed
}
```

The first three coordinates are
`ConstructionView(TranscriptConstructionId,kind)` and are issued by the common
`IssuePIRStaticView` operation from the exact admitted construction, its Core,
their inert authority bindings, and matching fresh capabilities.
`FSConstructionView` is not exported by construction admission. Its coordinate
is `FSResultView(CheckedFSConstructionResultRef,FSConstructionView)`, and it is
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
No nonaffirmative check result can issue a view or partial projection.

The construction-view closure is likewise exact: a frame field closes to its
algorithm/contract, source occurrence and prefix position; an influence field
closes to the complete ordered requirement and every referenced Core
coordinate; a challenge-transition field closes to namespace, draw, state,
decoder, retry, and failure semantics. Thus a consumer cannot read an
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

## 15. Bounded executable evidence

The repository package
[`evaluation/k2-protocol-fiat-shamir/`](../../evaluation/k2-protocol-fiat-shamir/)
provides bounded executable pressure for the lifecycle, causal/public-coin
refusals, transcript order, retries, replay, composition, and selected
reduction shapes defined here. Its Appendix-A contract vectors use the exact K1
carrier for guard Booleans and present/absent Oracle-answer result values.

The remaining fixture is intentionally smaller than the durable carrier. It
does not execute raw Core canonical bodies, nonserializable causal or replay
capabilities, the complete K1 `AlgorithmUse` request ABI, the complete PC graph
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

Reopen the K2 construction if a K4 inhabitant requires:

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
  unabsorbed without weakening the default strong-FS rule; or
- a same-Core transformation whose verifier-observable interaction actually
  changes.

The response is a new exact model or checked prior construction, not an opaque
callback, manual prefix, skip flag, or theorem name stored in the Core.
K2 intentionally chooses the stricter baseline in which every active prior
prover publication is absorbed. A future theorem-backed relaxation must define
a distinct checked source/target construction and Analysis obligation; it may
not be an authored per-message omission flag.

## Appendix A. Canonical bodies

Use the K1 notation from the companion page: `R{...}`, `S[...]`, `V(tag,x)`,
`MF`, `MT`, `N(n)`, `Q(symbol)`, `Y(bytes)`, `Unit`, `ContentRefV0`,
`CanonicalValueTypeBody`, and admitted canonical datums. Fields are exact,
ordered, and closed.

```text
AlgorithmUseBody(x) = R {
  0: Y(ContentRefV0(x.algorithm)),
  1: Y(ContentRefV0(x.evaluation_contract))
}

ChallengeRuleBody(x) = R {
  0: N(x.challenge),
  1: N(x.draw_bytes),
  2: N(x.maximum_draws),
  3: AlgorithmUseBody(x.accept),
  4: AlgorithmUseBody(x.decode)
}

TranscriptConstructionBody(T) = R {
  0: Y(ContentRefV0(T.core_id)),
  1: CanonicalValueTypeBody(T.transcript_state_type),
  2: CanonicalValueTypeBody(T.transcript_bytes_type),
  3: CanonicalValueTypeBody(T.natural_type),
  4: T.initial_state.datum,
  5: AlgorithmUseBody(T.absorb),
  6: AlgorithmUseBody(T.squeeze_bytes),
  7: AlgorithmUseBody(T.advance_state),
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
| V(5, R{0:N(occurrence_ref),1:K1BooleanDatum(active)})
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

Here `K1BooleanDatum(false) = MF` and `K1BooleanDatum(true) = MT`; neither case
is a `MetaVariant`. For a `FullCanonicalOracle` or `PublicBinding` Oracle, an
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
admission predicate rotates `PIRTranscriptFSProfile` and every downstream
profile that imports it. A module-owned declaration change instead rotates
that module and its exact users. The shared Foundation semantic regime rotates
only when a Foundation-owned mechanism or its interpretation changes. Old
bytes are never reinterpreted.
