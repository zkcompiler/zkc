# Fiat--Shamir Construction

> **Document kind:** Target semantic specification
> **Document state:** Active non-normative K2 target
> **Target status:** Bounded K2 candidate complete; K3 theorem integration
> remains open
> **Provisional owner:** `pir`
> **Authority:** None during the transition. Current normative Fiat--Shamir
> semantics remain under [`docs/`](../../docs/README.md).

## 1. Contract

This page is the sole K2 definition owner for:

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

The input Core is an exact `AdmittedCore` from the companion page. Its
occurrence order, values, scope tree, public bindings, challenges, messages,
oracles, reductions, extensions, and public-coin result are immutable.

The selected PIR regime additionally recognizes
`ProtocolDeclarationRef<"pir.fs-application-domain">` with the exact nominal
declaration body defined by the companion page. It is an authenticated static
application-purpose coordinate, not a display string or a freshness claim.

All collections and bodies obey the K1 constitutional bounds. In addition:

```text
maximum challenge rules       = core.challenge_count <= 2^14
maximum draws per challenge   = 2^20
maximum bytes per squeeze     = 2^20
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
`L <= 2^20` large enough for every admitted frame, namespace, and draw.
`NaturalType` must use the root natural domain at ordinal 2 with a `Nat(Ln)`
schema that admits every `draw_bytes` value and all construction counters.
These constraints make `ByteLength` and requested-count admission exact K1
operations rather than methods of an opaque bytes-like domain.

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
  SemanticContentId<"pir.transcript-construction">(
    B, TranscriptConstructionBody(construction))
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
      publication_mode: OraclePublicationMode,
      public_material_type: ValueType,
      public_material: CanonicalValue<public_material_type>
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
      element_type: ValueType,
      answer: CanonicalValue<element_type>
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

`FrameBody` and tags are fixed in Appendix A. The exact bytes supplied to
`AbsorbUse` are:

```text
FrameBytes(frame) = M(FrameBody(frame))
```

K1's injective canonical encoding and the explicit tag, occurrence coordinate,
type, and payload framing prevent cross-kind, empty-value, concatenation, and
reordering aliases. No caller codec, display label, host serialization, or raw
concatenation can replace `FrameBytes`. Wire/proof serialization remains a
separate Interface/OIR concern.

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
| active Oracle publication | absorb its full canonical oracle value or public binding material, according to its admitted mode |
| active Public Oracle query | absorb one `OracleQuery` frame |
| active Public Oracle answer | absorb one `OracleAnswer` frame |
| Verifier-only Oracle query/answer | no FS action because Section 8 rejects the construction first |
| Check, Reduction, Terminal | no direct frame; any later public control dependence is represented by a guard outcome or public derived value |
| supported module effect | exact frames derived by its authenticated `pir.core-effect` declaration |

An `Always` occurrence has no guard frame. An inactive guarded occurrence has
only its false guard frame. Thus an absent publication cannot alias an empty or
different publication, and two control histories reaching a later challenge
have distinct typed frame sequences.

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

`TransitionInputLog` is not an assertion of cryptographic security. Define:

```text
Influence(state_before_challenge) =
  InfluenceTrace(the exact receipt prefix producing that state)
```

This means “presented to the admitted state transition under exact framing.” It
does not mean collision resistance, indifferentiability, entropy, binding, or
unpredictability; Analysis owns those assumptions.

### 5.2 Derived requirement

For active Core challenge `c`, first derive one finite requirement predicate
over `InfluenceAtom`. Its base cases select:

1. `CoreHeader`, `ConstructionHeader`, and `ApplicationDomainHeader`;
2. every opened scope path in the active scope ancestry;
3. every Statement, SessionContext, and PublicParameter binding in that
   ancestry;
4. every active prior Prover message;
5. every active prior Verifier message;
6. every active prior Oracle publication's exact public material;
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
An addition must resolve to one exact prefix occurrence; ambiguous or absent
coordinates refuse admission/replay. Immediately before the first draw of
`c`, after all of `c`'s condition frames have been absorbed, the resolver
checks both laws in this order:


```text
TransitionInputLog(actual_receipts_before_draw_c) = DerivedPrefix(c)

RequiredInfluence(c) is an exact order-preserving subtrace of
  Influence(actual_state_immediately_before_draw_c),
with every required atom matched exactly once
```

The second law allows safe extra influence, while the first law prevents an
implementation from using that allowance to inject, omit, duplicate, reorder,
or substitute any actual frame or draw. Missing, delayed, wrongly scoped,
wrong-kind, or conditionally ambiguous required material refuses the
construction or replay at the first affected coordinate. In particular, no
requirement is checked against a state that predates its own condition frame.

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
ChallengeNamespace(T, c, i) = M(R {
  0: Y(ContentRefV0(T.id)),
  1: Y(ContentRefV0(T.core_id)),
  2: S[N(scope_ref) ... exact root-to-c scope path],
  3: N(c),
  4: DeclarationRefBody(Module(core.challenges[c].domain)),
  5: CanonicalValueTypeBody(core.challenges[c].value_type),
  6: CoinCorrelationBody(core.challenges[c].correlation),
  7: N(i)
})
```

The byte value is admitted at `TranscriptBytesType` before squeeze. The
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
condition frames for challenge `c`. The resolver first performs both Section
5 comparisons against this exact pre-draw state. Let `rule[c]` be the admitted
rule.

```text
for i in 0 .. rule.maximum_draws - 1:
    draw_pre_state = state
    namespace = ChallengeNamespace(T, c, i)
    bytes = Evaluate(T.squeeze_bytes,
        [draw_pre_state, namespace, rule.draw_bytes])

    if ByteLength(bytes) != rule.draw_bytes:
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

## 8. Construction admission

`AdmitTranscriptConstruction(candidate, AdmittedCore)` runs in this order:

1. authenticate the prior-meta basis, construction ID/body, exact `CoreId`,
   application-domain and sampling-failure declarations, algorithm IDs/bodies,
   evaluation contracts, primitives, and exact-used module closure in one K1
   ledger;
2. validate Appendix A shape, bounds, ordered total challenge-rule map, exact
   references, and no unknown fields;
3. require exact equality between the candidate `core_id` and the supplied
   admitted Core;
4. require `PublicCoinEligible(core) = true`;
5. admit the state, bytes, natural, Boolean, and initial-state values and
   require all three common algorithm ABIs from Section 3.1;
6. resolve `sampling_exhausted_failure`, require its exact declaration body,
   lifted payload type, canonical coordinate, regime, and construction-body
   occurrence from Section 3.2;
7. for each challenge in order, derive `SamplingInputTypes(c)`, admit the exact
   Boolean acceptance and challenge-value decoder ABIs, and check positive draw
   size and bounds;
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
    authenticated dependency and derivation result.

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
module-support results. It forms:

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
the pre-draw receipt prefix, checks `DerivedPrefix` and `RequiredInfluence`, and
only then runs Section 7.

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
and terminal. It requires exact record exhaustion. A cached state digest or
prefix is only a comparison witness and cannot replace the canonical state
transition.

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
CheckFSConstruction(
  AdmittedFreshProtocol source,
  AdmittedFSProtocol target,
  AdmittedTranscriptConstruction construction)
  -> Qualified<CheckedFSConstruction>
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
`CheckedFSConstruction`. They need a separate checked IOR-to-concrete-Core
construction and Analysis result. Plain same-Core FS may be used after that
step.

An ideal Oracle Core with Verifier-only queries is Fresh-valid but fails
`PublicCoinEligible` and therefore cannot receive this FS interpretation. An
Oracle Core whose binding, public queries, answers, and accepting computation
are publicly reconstructible can pass, subject to its exact module and theorem
obligations.

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

## 13. Source views and downstream questions

An admitted construction exports immutable PIR-owned views carrying exact
`CoreId` and `TranscriptConstructionId`:

```text
TranscriptDeclarationView =
  (state/bytes types, initial state, absorb/squeeze-bytes/advance-state
   algorithms and contracts, application domain, sampling-failure coordinate,
   exact FrameBody law)

RequiredInfluenceView =
  (InfluenceAtom algebra, scope bindings, per-challenge ordered requirements,
   reduction/module additions, derived exact prefix law)

ChallengeTransitionView =
  (namespace derivation, acceptance/decoder ABIs, draw bounds,
   exact-length/state-update/retry/failure law)

FSConstructionView =
  (Fresh/FS Protocol IDs, shared Core ID, identity coordinate maps,
   structural conclusion)
```

Analysis must read these exact views when selecting an FS theorem. It may add
ROM/QROM model, strategy class, query bounds, soundness notion, hash/codec/
sampler assumptions, binding assumptions, and quantitative loss. It may not
substitute a second transcript declaration or infer structural success from a
theorem citation.

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

## 15. Reopening conditions

Reopen the K2 construction if a K4 inhabitant requires:

- challenge derivation from verifier-private state under a justified transform;
- an exact distribution that cannot use a total decoder or bounded semantic
  retry;
- deliberate challenge correlation not expressible by a joint group, or
  reduction-level reuse not expressible by `ReductionUsePolicy`;
- transcript rollback, fork, merge, or tree state as semantic meaning;
- an event whose required influence cannot be derived from an exact supported
  module rule;
- a dynamic Statement introduced after its active scope's first challenge; or
- a same-Core transformation whose verifier-observable interaction actually
  changes.

The response is a new exact model or checked prior construction, not an opaque
callback, manual prefix, skip flag, or theorem name stored in the Core.

## Appendix A. Canonical bodies

Use the K1 notation from the companion page: `R{...}`, `S[...]`, `V(tag,x)`,
`N(n)`, `Q(symbol)`, `Y(bytes)`, `Unit`, `ContentRefV0`,
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
| V(5, R{0:N(occurrence_ref),1:V(boolean_tag,Unit)})
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
  2:OraclePublicationModeBody(mode),
  3:CanonicalValueTypeBody(public_material_type),
  4:public_material.datum
}

OracleQueryFrameBody = R {
  0:N(occurrence_ref),
  1:N(oracle_ref),
  2:CanonicalValueTypeBody(index_type),
  3:index.datum
}

OracleAnswerFrameBody = R {
  0:N(occurrence_ref),
  1:N(oracle_ref),
  2:CanonicalValueTypeBody(element_type),
  3:answer.datum
}
```

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
before comparison.

The message variants 6 and 7 distinguish Prover from Verifier without another
party field. Boolean false and true use K1's exact Boolean cases. Reused bodies
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
admission predicate requires a new supported PIR semantic module/regime. Old
bytes are never reinterpreted.
