# Duplex-Sponge Fiat--Shamir Construction

> **Document kind:** Target semantic specification
> **Document state:** Active redesign target; additive sibling of the
> canonical-framed Fiat--Shamir family
> **Provisional owner:** `pir`
> **Authority:** None during redesign. This is a non-normative target and does
> not alter the current specification under `docs/` before explicit cutover.

## 1. Scope

This page defines one closed duplex-sponge transcript construction and its
Fiat--Shamir Protocol interpretation. It owns:

- the sibling semantic-language profile and exact subject family;
- source-shape eligibility over one unchanged `InteractiveCore`;
- statement-to-binary-instance correspondence;
- construction-public salt material;
- the exact overwrite duplex state machine;
- fixed per-round prover encoding and one-shot challenge decoding;
- verifier-complete and prover-required schedules;
- construction-family receipts, replay, and same-Core checking; and
- family-specific PIR source views and nonclaims.

The companion [canonical-framed construction](fiat-shamir.md) remains a
different sibling family. This page does not weaken its typed frames,
namespaces, influence closure, retry, failure, or replay law.

The operational source is Construction 3.3 and Construction 4.3 of Chiesa and
Orrù,
[*A Fiat--Shamir Transformation From Duplex Sponges*](https://eprint.iacr.org/2025/536),
revision 27 March 2026. The reviewed PDF SHA-256 is
`fca7ba09ebe59141c3c041ac660b4e3e161fdab8a709aee67e236db8d8da3a35`.
Source provenance does not enter transcript identity. Exact construction
meaning is the closed law on this page.

This page does not establish any theorem in that paper. In particular, ideal
oracle distributions, inverse-permutation adversary access, codec
injectivity/bias/inversion, salt distribution, state-restoration properties,
query bounds, and quantitative losses belong to Analysis.

## 2. Shared basis and family profile

Every subject uses the complete prior-meta basis retained by its admitted
Core. The exact semantic regime, identity hash suite, canonical encoding,
value domains, portable algorithms, evaluation contracts, and module closure
are those of [Executable Foundations](../foundation/executable-foundations.md).
No construction introduces a second regime or ambient registry.

The profile topology is:

```text
PIRInteractionProfile
├── PIRCanonicalFramedFSProfile
└── PIRDuplexSpongeFSProfile
```

`PIRDuplexSpongeFSProfile` imports exactly `PIRInteractionProfile`. Its
supported subject kinds are:

```text
{"pir.transcript-construction", "pir.protocol",
 "pir.source-binding-payload", "pir.source-capability-requirement",
 "pir.source-consumer", "pir.source-no-policy",
 "pir.source-policy-closure", "pir.source-purpose"}
```

Its declaration catalog contains the duplex construction body, duplex FS
Protocol body interpretation, three construction-view schemas, checked-result
view schema, runtime material and receipt schemas, their projection and
closure laws, and the common PIR source-authority envelope specializations.

The exact no-extra authenticated closure is owned by the
[PIR profile topology](interactive-core.md#31-exact-pir-language-profile-split):
it contains this profile and `PIRInteractionProfileId`, and no canonical-framed
sibling. An evaluator can support one family without supporting the other.
Adding an unreferenced future sibling does not rotate either existing family.
Changing this page's body grammar, admission, execution, receipt, view, or
replay law rotates the duplex profile and its dependents only.

This page does not yet publish the complete six-field profile preimage or its
independently reconstructible full typed ID. The profile must publish that
preimage before dependent IDs are persistent and before semantic freeze.

## 3. Construction subject

### 3.1 Derived types

Let `T.alphabet_type` be one exact finite admitted Foundation `ValueType` and
let `T.zero_symbol` be one admitted value of that type. This page uses only
Foundation root carriers:

```text
AlphabetSequenceCarrier_T(n) = RootSeq<T.alphabet_type,n>

ExactAlphabetVector_T(n,v) =
  type(v) = AlphabetSequenceCarrier_T(n)
  and SequenceLength(v) = n

BinaryInstanceCarrier_T =
  RootBytes[0,T.maximum_instance_bits / 8]

BinaryString_T(b) = the MSB-first bit string of exact byte sequence b
```

Formation requires `T.maximum_instance_bits` to be divisible by eight. This
profile therefore covers byte-aligned source instances. A non-byte-aligned
source convention requires another checked correspondence rather than an
implicit padding rule.

The duplex state carrier and invariant are derived, not authored:

```text
DuplexStateCarrier_T = RootRecord {
  0: AlphabetSequenceCarrier_T(T.rate + T.capacity),
  1: RootNat[T.rate],
  2: RootNat[T.rate]
}

AdmittedDuplexState_T(st) =
  type(st) = DuplexStateCarrier_T
  and let (s,i_A,i_S) = st in
  ExactAlphabetVector_T(T.rate + T.capacity,s)
  and 0 <= i_A <= T.rate
  and 0 <= i_S <= T.rate
```

Its fields are respectively `(state, absorb_index, squeeze_index)`. The rate
is positive. Rate plus capacity, salt length, every encoded/squeezed length,
and every sequence carrier are at most the Foundation root-sequence capacity.
Instance bound, Core counts, transition counts, and cumulative symbol counts
must also fit Foundation constitutional bounds and this page's finite
execution ceiling of `2^20` semantic transition steps and `2^30` cumulative
canonical bytes.

### 3.2 Algorithm uses

`PIRAlgorithmUse` is the exact portable algorithm and evaluation-contract pair
defined by the imported Interaction profile. This family uses:

```text
HashToCapacityABI(T) =
  [BinaryInstanceCarrier_T]
    -> AlphabetSequenceCarrier_T(T.capacity)
  with exact-length postcondition ExactAlphabetVector_T(T.capacity,result)

PermutationForwardABI(T) =
  [AlphabetSequenceCarrier_T(T.rate + T.capacity)]
    -> AlphabetSequenceCarrier_T(T.rate + T.capacity)
  with exact-length pre/postconditions at T.rate + T.capacity

MessageEncoderABI(T,m) =
  [ProverMessagePayloadType(T.core_id,m)]
    -> AlphabetSequenceCarrier_T(
         DuplexMessageRuleFor(T,m).encoded_length)
  with exact-length postcondition

ChallengeDecoderABI(T,c) =
  [AlphabetSequenceCarrier_T(
     DuplexChallengeRuleFor(T,c).squeeze_length)]
    -> ChallengeValueType(T.core_id,c)
  with exact-length input precondition
```

`ProverMessagePayloadType` and `ChallengeValueType` are the exact owner-derived
types of the named Core occurrence and Challenge. They are projections, not
new value kinds.

Every algorithm is deterministic, total on its exact input type, and has an
empty typed completed-failure row. Admission preflights its complete maximum
request and output shape. A returned value with the wrong exact length is
owner-qualified `Refused`; disagreement with evaluation of the admitted
portable algorithm is `CheckerFailure`.

The words `hash` and `permutation` describe their operational coordinates.
Admission does not prove that the first is a random function, the second is a
uniform random permutation, or a concrete implementation is secure. Analysis
must separately bind an exact model and, when required, a coupled inverse.

### 3.3 Per-occurrence rules

```text
DuplexMessageRule = {
  occurrence: OccurrenceRef,
  encoder: PIRAlgorithmUse,
  encoded_length: Natural
}

DuplexChallengeRule = {
  challenge: ChallengeRef,
  squeeze_length: Natural,
  decoder: PIRAlgorithmUse
}
```

Message rules are ordered by source-round order and cover every and only
eligible `OccurrenceRef` whose active effect is `ProverMessage` exactly once.
Any other effect kind in a message rule is `KindMismatch`. Challenge rules are ordered
by the corresponding source-round order and cover every and only Core
challenge exactly once. Exact lengths may be zero. The two sequences have the
same positive length.

`DuplexMessageRuleFor(T,m)` and `DuplexChallengeRuleFor(T,c)` are the unique
entries selected by those admitted exact-total maps. They are undefined before
map admission and cannot select a default.

When `DuplexChallengeRuleFor(T,c).squeeze_length = 0`, the decoder receives the
unique empty sequence and therefore returns a construction-fixed value that is
independent of transcript state. This degenerate rule is operationally total
and may be admitted; it is not evidence of challenge entropy. Any Analysis
family whose theorem requires a random or history-dependent challenge must
state a positive-length or decoder-distribution premise and refuse applicability
when that premise is false.

### 3.4 Complete subject and identity

```text
DuplexSpongeTranscriptConstruction = {
  core_id: CoreId,
  alphabet_type: ValueType,
  zero_symbol: CanonicalValue<alphabet_type>,
  rate: PositiveNatural,
  capacity: Natural,
  maximum_instance_bits: Natural,
  hash_to_capacity: PIRAlgorithmUse,
  permutation_forward: PIRAlgorithmUse,
  salt_length: Natural,
  message_rules: CanonicalSeq<DuplexMessageRule>,
  challenge_rules: CanonicalSeq<DuplexChallengeRule>
}
```

Its identity is:

```text
TranscriptConstructionId =
  ProfiledSemanticId<"pir.transcript-construction">(
    B,
    PIRDuplexSpongeFSProfileId,
    DuplexSpongeTranscriptConstructionBody(T))

AuthenticatedTranscriptConstructionProfile(
  exact authenticated admitted handle for T) =
  PIRDuplexSpongeFSProfileId
```

The ID commits to every field above, the exact sibling profile, and every
referenced algorithm and evaluation contract. The derived state type,
instance projection, salt schema, source-round schedule, transition law,
resource bound, and source views are recomputed from those authenticated
inputs and the exact Core.

The body contains no self ID. Unlike the canonical-framed family, the duplex
state never absorbs construction, Core, or application-domain identifiers, so
there is no `BindConstructionSelfId` step in this profile.

The explicit `zero_symbol` is a local operational generalization of the
reviewed source construction, which fixes the rate prefix to its alphabet-zero
word. An Analysis import of that source must either require this field to equal
the source alphabet's exact zero value or supply a checked equivalence theorem;
the generic PIR family does not infer that premise.

Runtime public values, salt, messages, transcript state, receipts, proof bytes,
provider paths, source citations, Analysis results, and Evidence do not enter
construction identity.

## 4. Instance and source-shape eligibility

### 4.1 Binary instance correspondence

The source construction starts from a binary instance `x`. The Core instead
has typed binding occurrences. Define the owner-derived vocabulary:

```text
RootInitialStatementBinding(C,b) =
  b is a PublicBindingDecl of admitted C
  and b.scope is C's unique root scope
  and b.class = Statement
  and C.bindings[b].value is PublicInput(_)

DuplexInstanceBindings(C) =
  every and only b satisfying RootInitialStatementBinding(C,b),
  ordered by ascending BindingRef

EncodeDuplexInstance(C,I) =
  M(S[R{
        0: N(b),
        1: CanonicalValueTypeBody(C.public_inputs[ref].value_type),
        2: I.public_inputs[ref].datum
      }
      for b in DuplexInstanceBindings(C) in that order,
      where C.bindings[b].value = PublicInput(ref)])
```

`I` is the exact admitted `CoreInvocation` for `C`; `M` and `S` are the
Foundation canonical encoding and sequence constructors. The function is
undefined before both subjects are admitted or when an invocation value is
missing or has the wrong exact type. It is not an Interface codec.

Equal values at different binding occurrences remain separate. Every selected
binding contributes the exact Foundation record:

```text
R{0: N(BindingRef),
  1: CanonicalValueTypeBody(value_type),
  2: value.datum}
```

Let `instance_bytes` be the Foundation canonical encoding `M(...)` of the
ordered sequence of those triples. It must inhabit `BinaryInstanceCarrier_T`.
The source bit string is exactly `BinaryString_T(instance_bytes)`, so its
length is `8 * len(instance_bytes)` and must not exceed
`T.maximum_instance_bits`. This projection and bit order are profile-fixed;
there is no authored statement map, padding rule, deduplication, external byte
encoder, or Interface serialization input.

The initial operational profile refuses:

- a Statement binding introduced after execution starts or inside a child
  scope;
- a root-initial Statement binding whose value is not a `PublicInput`;
- verifier-private Core inputs;
- runtime `SessionContext` or `PublicParameter` bindings; and
- any public Core input that is not named by exactly one member of
  `DuplexInstanceBindings(C)`.

A richer instance convention requires a separately checked correspondence or
a sibling profile. It cannot be supplied as an opaque prefix.

### 4.2 Duplex source shape

`DuplexSpongeEligible(C,T)` requires all of the following:

1. `T.core_id = C.id` and exact retained evaluator identity;
2. `PublicCoinEligible(C) = true`;
3. at least one source round;
4. one unconditional root-scope prover-message occurrence followed by one
   unconditional root-scope Challenge in each source round;
5. no uncovered or duplicated prover message or Challenge;
6. no prover decision after the final Challenge;
7. no separate verifier-message occurrence;
8. no joint challenge, challenge public condition, Oracle occurrence, or
   extension effect;
9. no guard or scope path that makes source-round coverage conditional; and
10. finite exact maximum state, algorithm-call, symbol, and receipt bounds.

Checks, claims, reductions, and terminals may occur between source events when
they introduce no transcript action, use only already available values, and
preserve the one-message/one-challenge round sequence. Exactly one first-active
terminal must close every admissible path after the final Challenge.

This eligibility predicate is narrower than general public-coin eligibility.
It is deliberately not an author-supplied list of transcript events.

## 5. Fixed state-transition law

Let a state be `(s,i_A,i_S)`, where `s_R` denotes the first `rate` cells of
`s`. The exact operation semantics are profile law, not construction fields.

### 5.1 Start

```text
Start_T(x):
  capacity_state := Evaluate(T.hash_to_capacity,[x])
  s := (repeat(T.zero_symbol,T.rate), capacity_state)
  return (s,0,T.rate)
```

Start makes exactly one hash-to-capacity evaluation and no permutation
evaluation.

### 5.2 Absorb

```text
Absorb_T((s,i_A,i_S), input):
  i_S := T.rate

  if input is empty:
    return (s,i_A,T.rate)

  if i_A < T.rate:
    overwrite s_R[i_A] with first(input)
    return Absorb_T((s,i_A+1,T.rate),rest(input))

  // i_A = rate and input remains
  s := Evaluate(T.permutation_forward,[s])
  return Absorb_T((s,0,T.rate),input)
```

There is no XOR, padding, delimiter, tag, encoded length, eager final
permutation, or decoded-value reabsorption. Filling the last rate cell makes no
permutation call; the next waiting input symbol does.

Empty absorption preserves `s` and `i_A` but sets `i_S = rate`. Consecutive
absorbs without a positive squeeze equal one concatenated absorb.

### 5.3 Squeeze

```text
Squeeze_T(st,0):
  return {post_state:st, symbols:empty}

Squeeze_T((s,i_A,i_S),count > 0):
  i_A := 0

  if i_S < T.rate:
    emit s_R[i_S]
    continue with i_S+1 and count-1

  // i_S = rate
  s := Evaluate(T.permutation_forward,[s])
  continue with i_S=0 and unchanged count
```

The returned state and symbol sequence form one atomic semantic result. A
zero-length request preserves the complete state. Consecutive squeezes
continue one stream. Absorb after a partial squeeze discards unread output,
sets `i_S = rate`, and overwrites again from rate position zero because the
prior positive squeeze set `i_A = 0`.

### 5.4 Exact source schedule

For exact admitted `C` satisfying `C.id = T.core_id`, runtime invocation `I`,
salt `tau`, and source rounds `1..k`:

```text
x       := EncodeDuplexInstance(C,I)
state   := Start_T(x)
state   := Absorb_T(state,tau)

for i = 1 .. k:
  encoded_i := Evaluate(message_rules[i].encoder,[alpha_i])
  state_a   := Absorb_T(state,encoded_i)
  squeezed  := Squeeze_T(state_a,challenge_rules[i].squeeze_length)
  state     := squeezed.post_state
  rho_i     := Evaluate(challenge_rules[i].decoder,[squeezed.symbols])
```

The verifier executes every round. The resolver returns `rho_i` as the exact
Core Challenge value.

The transcript absorbs no Core header, construction header, application
domain, scope marker, binding frame, occurrence coordinate, channel, type tag,
namespace, draw ordinal, retry result, external prefix, or decoded challenge.
Adding any such input is a different construction and fails replay.

## 6. Construction-public material

### 6.1 Exact schema

Every admitted duplex construction derives one family-local material
coordinate:

```text
DuplexConstructionMaterialRef = {
  transcript_construction_id: TranscriptConstructionId,
  ordinal: 0,
  role: Salt
}

DuplexSaltRef(T) = DuplexConstructionMaterialRef {
  transcript_construction_id: T.id,
  ordinal: 0,
  role: Salt
}

DuplexConstructionMaterialSchema(T) = {
  DuplexSaltRef(T): AlphabetSequenceCarrier_T(T.salt_length)
    with ExactAlphabetVector_T(T.salt_length,value)
}

DuplexConstructionMaterialCandidate =
  CanonicalMap<DuplexConstructionMaterialRef,CanonicalValue>

DuplexMaterialRefusalReason =
    InvocationCoreMismatch
  | MaterialKeySetMismatch
  | SaltLengthMismatch
  | LatePreparation

DuplexMaterialRefusalReasonSet =
  CanonicalNonEmptySortedUniqueSeq<
    DuplexMaterialRefusalReason in written tag order>
```

The coordinate exists when `salt_length = 0`; its only value is then the empty
sequence. Salt is public, proof-carried construction material. It is not a
Core input, Statement, SessionContext, PublicParameter, prover message,
challenge, witness, or construction identity field.

### 6.2 Preparation and capability

```text
PrepareDuplexConstructionMaterial(
  exact admitted duplex FS Protocol,
  exact CoreInvocation,
  DuplexConstructionMaterialCandidate,
  exact evaluator and deterministic limits)
    -> Affirmative(ExactDuplexConstructionMaterialCapability)
     | Unsupported | MissingDependency | KindMismatch | Malformed
     | Refused(DuplexMaterialRefusalReasonSet)
     | DeterministicLimitExceeded | CheckerFailure
```

Preparation authenticates the Protocol, construction, Core invocation, exact
material schema, type, length, and total key set before creating one fresh
noncopyable capability. The capability is bound to the exact live handles,
salt value, evaluator, limits, issuance occurrence, and process generation. It
has no canonical body, ID, digest surrogate, serialization, or FFI form.

The qualified partition is exact. An unsupported construction family or
evaluator is `Unsupported`; an absent exact construction, Core, type, or
algorithm preimage is `MissingDependency`; a wrong owner, regime, value kind,
or alphabet type is `KindMismatch`; and a noncanonical map or value carrier is
`Malformed`. A salt sequence declaring a larger carrier type is therefore
`KindMismatch`, while a sequence that exceeds its declared carrier capacity is
`Malformed`; neither reaches owner refusal. A well-formed value in the exact
capacity carrier with fewer than `salt_length` symbols reaches
`SaltLengthMismatch`. A formed candidate returns
`Refused(DuplexMaterialRefusalReasonSet)` containing every and only applicable
reason above: invocation/Core disagreement, a missing or extra schema key, a
well-formed exact-carrier alphabet sequence with the wrong exact salt length,
or preparation after Core execution has started. A map key naming another
construction is an extra/missing-key pair and produces only
`MaterialKeySetMismatch`; there is no separate construction-mismatch tag.
Duplicate keys are structurally noncanonical and therefore `Malformed`, not a
refusal reason. No failure creates a partial capability. It is not a Core
terminal or semantic interpretation failure.

The duplex challenge-resolver capability retains the exact material
capability, so the common `GenerateRun` operation does not gain an untyped
material argument. One observed salt value proves no generation distribution.
Plan/Realization and Analysis separately own honest sampling and its use.

## 7. Lifecycle and admission

```text
CanonicalDuplexConstructionCandidate
  --AuthenticateDuplexConstruction-->
    AuthenticatedDuplexConstructionCandidate
  --AdmitDuplexConstruction-->
    AdmittedDuplexSpongeTranscriptConstruction
```

Authentication recomputes the typed ID, exact duplex profile closure, Core,
types, values, algorithms, contracts, and direct module dependencies in one
request-local binding ledger.

Admission proceeds in this order:

1. authenticate the complete exact prior-meta basis and profile closure;
2. strictly decode Appendix A and reject unknown or duplicated fields;
3. require exact construction/Core ID and retained evaluator equality;
4. form every derived sequence/byte carrier, state invariant, salt, and
   receipt type under exact finite bounds;
5. admit the zero symbol and exact algorithm ABIs with empty failure rows;
6. derive and check `DuplexInstanceBindings` and its maximum encoding size;
7. derive and check `DuplexSpongeEligible`;
8. require ordered total message and challenge maps with exact value types and
   lengths;
9. derive every transition and cumulative execution bound from the fixed
   state machine and Core schedule; and
10. retain every exact dependency, derivation result, material schema, and
    evaluator identity in one immutable admitted handle.

Admission does not execute runtime values or establish encoder injectivity,
decoder bias, a permutation distribution, salt uniformity, soundness,
knowledge soundness, or zero knowledge.

## 8. Protocol formation, execution, and replay

### 8.1 Protocol formation

```text
AdmitDuplexFS(
  AdmittedCore C,
  AdmittedDuplexSpongeTranscriptConstruction T)
    -> AdmittedDuplexFSProtocol
```

requires `T.core_id = C.id`, exact handle/evaluator equality, and all retained
eligibility results. It forms the ordinary physical Protocol body:

```text
Protocol {
  core_id = C.id,
  challenge_interpretation = FiatShamir(T.id)
}
```

and authenticates its `ProtocolId` under
`PIRDuplexSpongeFSProfileId`. A canonical-framed construction is a profile
mismatch, not a coercible implementation of this Protocol.

### 8.2 Receipts

```text
DuplexInitializationReceipt = {
  instance_bindings: CanonicalSeq<BindingRef>,
  binary_instance: CanonicalValue<BinaryInstanceCarrier_T>,
  salt: CanonicalValue<AlphabetSequenceCarrier_T(T.salt_length)>
    satisfying ExactAlphabetVector_T(T.salt_length,salt),
  start_state: CanonicalValue<DuplexStateCarrier_T>
    satisfying AdmittedDuplexState_T(start_state),
  post_salt_state: CanonicalValue<DuplexStateCarrier_T>
    satisfying AdmittedDuplexState_T(post_salt_state)
}

DuplexChallengeReceipt = {
  challenge: ChallengeRef,
  initialization:
    Present(DuplexInitializationReceipt) exactly for the first challenge
    | Absent exactly thereafter,
  message_occurrence: OccurrenceRef whose effect is ProverMessage,
  encoded_message:
    CanonicalValue<AlphabetSequenceCarrier_T(encoded_length)>
      satisfying ExactAlphabetVector_T(encoded_length,encoded_message),
  pre_absorb_state: CanonicalValue<DuplexStateCarrier_T>
    satisfying AdmittedDuplexState_T(pre_absorb_state),
  post_absorb_state: CanonicalValue<DuplexStateCarrier_T>
    satisfying AdmittedDuplexState_T(post_absorb_state),
  squeezed_symbols:
    CanonicalValue<AlphabetSequenceCarrier_T(squeeze_length)>
      satisfying ExactAlphabetVector_T(squeeze_length,squeezed_symbols),
  post_squeeze_state: CanonicalValue<DuplexStateCarrier_T>
    satisfying AdmittedDuplexState_T(post_squeeze_state),
  decoded_value: CanonicalValue<Core challenge type>
}
```

`ChallengeResolverReceipt` dispatches the exact FS receipt schema through the
authenticated Protocol profile. A duplex receipt has no namespace, draw
ordinal, acceptance flag, retry sequence, or sampling failure.

The duplex interpretation has an empty semantic completed-failure row.
Malformed inputs, missing support, deterministic evaluator exhaustion, and
provider disagreement remain qualified operational noncompletion and produce
no Protocol result.

### 8.3 Execution

Before the first strategy call, the duplex resolver requires the exact
material capability, derives the binary instance, evaluates Start and salt
absorption, and retains the initialization receipt. At each eligible Challenge
it requires the paired prior prover message, evaluates its exact encoder,
applies the fixed absorb and squeeze laws, evaluates the decoder, returns the
exact challenge value to the unchanged Core engine, and emits one receipt.

The Core remains the sole owner of strategy causality, visible history, checks,
claims, reductions, Oracles, and terminal selection. Transcript state is never
visible to the prover strategy.

### 8.4 Replay

Replay authenticates the exact duplex Protocol, construction, Core invocation,
completed record, algorithms, contracts, and profile closure. It:

1. reconstructs the instance binding sequence and binary instance;
2. checks the unique first-receipt salt and initialization;
3. re-evaluates every message codec and exact transition;
4. checks symbol counts, decoded challenge values, Core receipts, and
   terminal;
5. requires the final Challenge transition even though proof generation need
   not derive it; and
6. rejects missing, duplicate, reordered, mixed-family, or trailing fields.

Successful replay establishes deterministic record consistency only. It does
not establish a causal strategy, material-generation law, primitive model,
theorem, proof serialization, or concrete implementation correspondence.

## 9. Prover-required prefix

For source rounds `1..k`, define:

```text
DuplexProverRequiredChallengePrefix(T) =
  challenges 1 .. k-1
```

Those and only those challenge values are visible to a later prover decision.
An honest argument-generation Plan may stop transcript derivation after it
produces the final prover message `alpha_k`. Verification and a complete
Protocol execution still derive and record challenge `k` before acceptance.

This static projection changes no Core occurrence and does not authorize a
verifier to omit the final transition.

The family-local correspondence values used below are closed derived records,
not unexplained labels:

```text
ExactDuplexInstanceBindingProjection(source,target,T) = {
  source_bindings: DuplexInstanceBindings(source.core),
  target_bindings: DuplexInstanceBindings(target.core),
  binding_map: IdentityOnEverySelectedBindingRef,
  encoding_law: EncodeDuplexInstance(source.core,I)
                = EncodeDuplexInstance(target.core,I)
                for every exact shared invocation I
}

UniqueTargetOnlySalt(target,T) = {
  source_material_coordinates: empty,
  target_material_coordinates: {DuplexSaltRef(T)},
  target_schema: DuplexConstructionMaterialSchema(T)
}

ExactProverRequiredPrefix(source,target,T) = {
  source_challenges: every ChallengeRef before the final source-round
                     Challenge,
  target_challenges: DuplexProverRequiredChallengePrefix(T),
  challenge_map: identity in source-round order
}

ExactVerifierCompleteSchedule(source,target,T) = {
  source_challenges: every source-round ChallengeRef including the final one,
  target_challenges: every target-round ChallengeRef including the final one,
  challenge_map: identity in source-round order,
  replay_requirement: every mapped target transition is present exactly once
}
```

Each record forms only after both exact admitted Protocols, `T`, and the shared
Core have passed the predicates it names. It has no default or partial form.

## 10. Checked same-Core construction

```text
DuplexFSConstructionDefect =
    SharedCoreMismatch
  | ConstructionCoreMismatch
  | TargetConstructionMismatch
  | PublicCoinEligibilityMissing
  | OccurrenceDomainMismatch
  | NonChallengeValueDomainMismatch
  | ChallengeDomainMismatch
  | TargetCoreFieldMismatch
  | DuplexInstanceBindingMismatch
  | DuplexSourceShapeMismatch
  | DuplexMessageCoverageMismatch
  | DuplexChallengeCoverageMismatch
  | DuplexConstructionMaterialSchemaMismatch

DuplexFSConstructionDefectSet =
  CanonicalNonEmptySortedUniqueSeq<
    DuplexFSConstructionDefect in written tag order>

CheckDuplexFSConstruction(
  AdmittedFreshProtocol source,
  AdmittedDuplexFSProtocol target,
  AdmittedDuplexSpongeTranscriptConstruction construction)
    -> Qualified<
         Affirmative({
           CheckedDuplexFSConstruction,
           ExactCheckedDuplexFSConstructionAuthorityBinding,
           CheckedDuplexFSConstructionCapability
         })
       | Negative(DuplexFSConstructionDefectSet)>
```

The affirmative result is family-local:

```text
CheckedDuplexFSConstruction = {
  source_protocol_id,
  target_protocol_id,
  shared_core_id,
  transcript_construction_id,
  occurrence_map: IdentityOnEveryOccurrenceRef,
  value_map: IdentityOnEveryNonChallengeValueRef,
  challenge_map: IdentityOnEveryChallengeRef,
  instance_projection:
    ExactDuplexInstanceBindingProjection(source,target,construction),
  construction_material_map: UniqueTargetOnlySalt(target,construction),
  prover_schedule_correspondence:
    ExactProverRequiredPrefix(source,target,construction),
  verifier_schedule_correspondence:
    ExactVerifierCompleteSchedule(source,target,construction),
  conclusion: StructurallyConstructed
}
```

Affirmative checking requires identical source and target `CoreId`, exact
Fresh and duplex interpretations, exact construction/Core equality, public-
coin and duplex eligibility, identity maps over every Core occurrence and
nonchallenge value, identity over every Challenge coordinate, and the unique
target-only salt material coordinate.

The negative tags are request-comparison facts over admitted operands. Their
producing predicates are, in written order: unequal source/target Core IDs;
construction/Core disagreement; target/construction disagreement; absent
public-coin eligibility on the source; unequal occurrence domains; unequal
non-Challenge value domains; unequal Challenge domains; any unequal Core body
field; unequal root-initial Statement projections; source failure of the exact
duplex shape; unequal message-rule coverage; unequal Challenge-rule coverage;
and unequal derived salt schemas. The checker emits every applicable tag in
canonical order. Cold authentication failure, missing preimages, wrong kinds,
limit exhaustion, and checker faults remain qualified noncompletion and never
manufacture a negative tag. Final-round omission is covered by the exact
verifier-complete replay requirement, not by a request-comparison tag; no
separate unproducible final-round tag exists.

`OccurrenceDomainMismatch`, `NonChallengeValueDomainMismatch`,
`ChallengeDomainMismatch`, `TargetCoreFieldMismatch`, and
`DuplexInstanceBindingMismatch` are deliberate field-factored diagnostics
beneath `SharedCoreMismatch`: they may co-occur when unequal admitted Core
bodies are compared, but they cannot assert that one equal admitted Core ID
has two bodies. The construction-shape, coverage, and salt-schema tags instead
factor differences attributable to the authenticated construction operands.
No implied diagnostic is an independent identity-collision claim.

The result means only that the unchanged source interaction receives its
public challenges through this exact construction. It proves no property
transport. Analysis must name an exact source property, experiment,
construction assumptions, theorem, loss, and target property.

The result has no semantic ID. An affirmative checking occurrence creates one
collision-free owner-local `CheckedDuplexFSConstructionResultRef`, an exact
owner-local PIR authority binding, and one fresh noncopyable
`CheckedDuplexFSConstructionCapability`. The binding commits to the exact
result ref, source and target Protocols, Core, construction, complete family-
local result schema, affirmative polarity, checker contract, consumer,
purpose, no-policy declaration, and capability requirement. The capability
retains the exact live admitted handles, result and binding objects,
checker/evaluator, and checking occurrence. None has a canonical body, digest
surrogate, serialization, cache form, or FFI representation. Cold use
reauthenticates and readmits all three subjects and reruns this checker.

For every affirmative result formed by this operation:

```text
CheckedFSConstructionProfile(
  CheckedDuplexFSConstructionResultRef) = PIRDuplexSpongeFSProfileId
```

## 11. Exact PIR source views

The coordinate, authority-binding, manifest, closure, capability, and issuance
mechanics are those of
[PIR-owned source views](interactive-core.md#13-pir-owned-source-views). The
duplex profile supplies family-specific payloads under its exact profile ID.

```text
DuplexConstructionViewKind =
    DuplexTranscriptDeclarationView
  | DuplexEncodedInputCoverageView
  | DuplexChallengeTransitionView

DuplexConstructionViewKindRef(kind) =
  (PIRDuplexSpongeFSProfileId, written tag of kind)

DuplexFSResultViewKind = DuplexFSConstructionView
DuplexFSResultViewKindRef =
  (PIRDuplexSpongeFSProfileId, written tag of DuplexFSConstructionView)
```

Each local kind maps to exactly the like-named closed body below. View issuance
uses the common owner-coordinate and capability mechanics with these exact
profile-local references; no canonical-framed kind is accepted here.

### 11.1 Transcript declaration view

```text
DuplexTranscriptDeclarationViewBody = {
  transcript_construction_id,
  core_id,
  construction_family: DuplexSponge,
  alphabet_type,
  zero_symbol,
  rate,
  capacity,
  state_carrier_and_invariant,
  binary_instance_carrier_and_bit_convention,
  exact_instance_binding_projection,
  hash_to_capacity_algorithm_and_contract,
  permutation_forward_algorithm_and_contract,
  fixed_start_absorb_squeeze_laws,
  exact_edge_case_laws,
  exact_construction_material_schema,
  message_encoder_map,
  semantic_argument_shape,
  prover_required_schedule,
  verifier_complete_schedule,
  exact_operational_resource_projection
}
```

### 11.2 Encoded-input coverage view

```text
DuplexEncodedInputCoverageViewBody = {
  transcript_construction_id,
  core_id,
  exact_instance_binding_sequence,
  salt_coordinate,
  per_challenge_ordered_encoded_input_coverage,
  exact_message_coverage,
  exact_challenge_coverage,
  prover_required_prefix_law,
  verifier_complete_schedule_law,
  prohibited_additions
}
```

For challenge `i`, encoded-input coverage is exactly the binary instance,
salt, and encoded prover messages `1..i` in that order. A source view cannot
omit an equal-valued binding occurrence or message. This proves occurrence and
evaluation coverage, not semantic injectivity of an authored encoder. Exact
source correspondence and any security theorem separately require the named
encoder-injectivity judgments.

### 11.3 Challenge transition view

```text
DuplexChallengeTransitionViewBody = {
  transcript_construction_id,
  core_id,
  per_challenge_squeeze_and_decoder_map,
  decoder_totality_contracts,
  decode_after_state_transition_law,
  acceptance_rule: AlwaysAccept,
  retry_rule: NoRetry,
  semantic_sampling_failure: None,
  prover_execution_domain,
  verifier_execution_domain,
  exact_squeeze_event_projection
}
```

### 11.4 Checked result view

```text
DuplexFSConstructionViewBody = {
  result_ref,
  result_schema: exact CheckedDuplexFSConstruction schema,
  fresh_protocol_id,
  fiat_shamir_protocol_id,
  shared_core_id,
  transcript_construction_id,
  construction_family: DuplexSponge,
  occurrence_map: IdentityOnEveryOccurrenceRef,
  value_map: IdentityOnEveryNonChallengeValueRef,
  challenge_map: IdentityOnEveryChallengeRef,
  instance_projection,
  construction_material_map:
    UniqueTargetOnlySalt(exact target,exact construction),
  prover_schedule_correspondence,
  verifier_schedule_correspondence,
  structural_conclusion: StructurallyConstructed
}
```

The profile-specific schema prevents Analysis from requesting canonical
headers, namespaces, retries, or sampling failures from a duplex construction.
It likewise prevents a canonical consumer from treating absent duplex fields
as empty values.

## 12. Analysis and theorem boundary

No active Analysis profile imports a duplex security theorem. Future work must
separate at least:

1. duplex-to-canonical random-function trace reduction;
2. soundness from state-restoration soundness;
3. rewinding state-restoration knowledge soundness together with its
   straight-line specialization; and
4. adaptive single-instance zero knowledge from honest-verifier zero
   knowledge.

Exact applicability would need family views plus:

- independent random `h` and random permutation `p` experiments;
- malicious-role access to the coupled `p^-1`;
- separate `h`, `p`, and `p^-1` query bounds;
- encoder injectivity and inverse-on-image behavior;
- decoder bias, surjectivity, balanced-fiber or corrected-loss conditions,
  and efficient uniform-fiber sampling;
- a well-typed salt-to-binary bridge;
- theorem-specific salt generation and single-instance scope;
- exact state-restoration or HVZK source judgments; and
- authenticated source-theorem validation.

No extractor theorem is imported by this operational profile. The reviewed
source states both a rewinding route and a conditional straight-line
specialization; a future theorem profile must select one exact theorem and
authenticate all of its premises rather than infer either from this state
machine. The future theorem profile must also expose the source's
salt-length/capacity adequacy and
capacity-security terms (including its `min{delta,c}` and
`25 t^2 / |Sigma|^c` dependencies), plus the exact EPROM programming premise;
generic primitive-model labels are insufficient.

The recorded source-validation audit found unresolved proof-level
inconsistencies in the reviewed revision:

- Construction 3.3's operational lazy permutation calls disagree with the
  exact call counts and backtracking offsets in Sections 4--5;
- Definition 4.1 does not supply all decoder-fiber operations used by the
  later reductions;
- Claim 5.22's zero-distance decoder-fiber hybrid fails for unequal fiber
  sizes unless a further bias is charged or fibers are balanced; and
- the reduction's `delta log_2 |Sigma|` is not a natural fixed bit length for
  general non-power-of-two alphabets.

These do not alter the operational state machine. They block activation of the
cited theorem import until a validated repair, restriction, erratum, or
independent proof exists. With no duplex theorem family registered, Analysis
returns `Unsupported`. A future registered family returns `CannotAnswer` when
source validation or required premises are absent, and `Refused` only when an
exact supplied subject is inapplicable. No lane silently repairs the source.

## 13. Downstream support boundary

### 13.1 Interface and Plan

The active Interface/Plan profile supports only Fresh and the canonical-
framed FS sibling. It must return `Unsupported` for this profile.

Duplex support requires a downstream construction-material assignment from
the unique salt coordinate to a public proof slot and a pre-execution
construction-material Plan. Existing prover-decision randomness cannot mint a
fake Core occurrence for the salt.

### 13.2 Canonical PIR

Canonical PIR retains one unchanged Core and Protocol root shape. It carries
the exact construction ID and receives the external profile-specific
construction body during authentication. Salt and transcript state remain
runtime satellites and do not enter the Core group.

### 13.3 Relations

Relations gains no duplex state or salt meaning. A later purpose-specific
correspondence may relate an endpoint proof field to the target-only salt
coordinate. It cannot reinterpret salt as Statement or witness.

### 13.4 OIR, Realization, and Evidence

OIR returns `Unsupported` until a sibling profile owns proof tuple parsing,
salt placement, prover-message serialization, and the distinction between
wire and transcript codecs. Realization later binds exact portable providers
and honest material generation. Evidence may record those bindings and
executions without upgrading them to semantic or cryptographic judgments.

## 14. Outcomes and nonclaims

Representative admission outcomes are:

| Boundary | Outcome |
|---|---|
| malformed body, duplicate map, invalid index or rate zero | `Malformed` |
| wrong Core/profile/type/algorithm ABI or mixed-family receipt | `KindMismatch` |
| absent exact body, algorithm, contract, or Core preimage | `MissingDependency` |
| evaluator lacks this profile or exact algorithm | `Unsupported` |
| non-public-coin or ineligible Core; omitted Statement/message; invented frame, namespace, retry, or schedule event | `Refused` |
| request budget exhausted before a semantic transition | `DeterministicLimitExceeded` |
| provider disagrees with admitted algorithm evaluation | `CheckerFailure` |

This profile establishes none of:

- soundness, knowledge soundness, completeness, zero knowledge, RBR, ROM,
  QROM, UC, global-oracle, multi-instance, or composition security;
- random-function, uniform-permutation, indifferentiability, entropy,
  uniformity, independence, freshness, collision resistance, or capacity-only
  security;
- encoder injectivity, decoder bias, surjectivity, inverse sampling, or
  theorem truth;
- security of any concrete hash, permutation, sponge, field, or library;
- proof-byte serialization, canonical parsing, endpoint safety, or production
  ciphersuite support;
- equality or domain separation of transcript states produced under another
  `CoreId` or `TranscriptConstructionId`; the operational state absorbs no such
  identity header, so any cross-subject byte coincidence is outside this
  family and must be handled by a future proof-byte/OIR profile;
- challenge entropy when a challenge rule has zero squeeze length; and
- causal generation from replay, implementation conformance, constant-time
  behavior, or side-channel resistance; or
- transfer of a canonical-framed Analysis result to this family.

## 15. Reopening conditions

Reopen this profile if a validated source requires joint challenges, public
conditions, verifier messages, Oracles, conditional rounds, runtime labels,
or construction material beyond one public immutable salt.

Reopen the sibling-profile architecture if Foundation gains a closed
construction-class contract that can add top-level families without importing
them, rotating existing subjects, or executing an opaque schedule callback.

Reopen the instance projection if a checked imported protocol cannot relate
its binary instance to the fixed canonical binding encoding.

Reopen the theorem boundary only after an exact source revision, erratum, or
independent repaired proof resolves the recorded call-count, decoder-fiber,
and alphabet-encoding defects.

## Appendix A. Canonical bodies

```text
DuplexMessageRuleBody(x) = R {
  0: N(x.occurrence),
  1: PIRAlgorithmUseBody(x.encoder),
  2: N(x.encoded_length)
}

DuplexChallengeRuleBody(x) = R {
  0: N(x.challenge),
  1: N(x.squeeze_length),
  2: PIRAlgorithmUseBody(x.decoder)
}

DuplexSpongeTranscriptConstructionBody(T) = R {
  0: Y(ContentRefV0(T.core_id)),
  1: CanonicalValueTypeBody(T.alphabet_type),
  2: T.zero_symbol.datum,
  3: N(T.rate),
  4: N(T.capacity),
  5: N(T.maximum_instance_bits),
  6: PIRAlgorithmUseBody(T.hash_to_capacity),
  7: PIRAlgorithmUseBody(T.permutation_forward),
  8: N(T.salt_length),
  9: S[DuplexMessageRuleBody(rule) ...],
 10: S[DuplexChallengeRuleBody(rule) ...]
}
```

`R`, `S`, `N`, and `Y` are the exact Foundation `MetaValueV0` record,
sequence, natural, and bytes constructors used by the companion pages. The
zero datum is admitted at field 1's exact type. Every sequence is canonical,
bounded, ordered by the profile-derived source round, and contains no unknown
field or extension tail.

Changing a tag, field, order, derived type, transition, eligibility condition,
receipt, source view, or admission predicate rotates
`PIRDuplexSpongeFSProfile` and every dependent duplex subject. It does not
reinterpret or rotate an unreferenced canonical-framed subject.
