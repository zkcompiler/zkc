# Design Space and Selection

> **Kind:** Temporary architecture selection record
> **State:** Selected, durably promoted, and closed at the stated boundary
> **Authority:** None. The selected target has authority only after it is
> incorporated into the owning durable specifications.

## 1. Decision

Select a new sibling Fiat--Shamir family profile for the exact duplex-sponge
state machine. Preserve the existing canonical-framed family as a separate
sibling over the same `InteractiveCore`:

```text
                         PIRInteractionProfile
                           /              \
                          v                v
        PIRCanonicalFramedFSProfile   PIRDuplexSpongeFSProfile
              |                              |
      canonical-framed                overwrite-duplex
      construction + FS               construction + FS
      Protocol semantics              Protocol semantics
```

The construction family is selected by the exact construction's semantic
language profile:

```text
ProtocolLanguageProfile(FiatShamir(T)) =
  TranscriptConstructionProfile(T)
```

Both FS Protocols retain the same physical body shape:

```text
Protocol = {
  core_id,
  challenge_interpretation: FiatShamir(transcript_construction_id)
}
```

The profile gives that body its family-specific execution, receipt, failure,
source-view, admission, and replay law. Equal physical shape does not make two
profiles semantically interchangeable.

The selected architecture makes exactly one shared semantic claim:

> Fresh and each Fiat--Shamir Protocol can share the identical admitted
> `InteractiveCore`; each FS family replaces only the resolution of the
> Core's public challenges through its own closed construction.

It does not claim that two transcript constructions are equivalent or that a
theorem for one transfers to another.

## 2. Candidate comparison

| Candidate | Source fidelity | Strong influence | Evolution locality | Independent admission | Decision |
|---|---:|---:|---:|---:|---|
| Keep only canonical-framed construction | No | Strong for existing family | Strong | Strong | Coherent v0 boundary, but does not meet this package's objective |
| Add a mode to canonical-framed construction | No | Easy to confuse | Weak | Weak | Rejected: frames, namespace, retry, and initialization are semantic, not parameters |
| Add a closed sum arm under the current single profile | Yes | Strong | Weak | Strong | Rejected as durable shape: every new arm rotates all existing family IDs |
| Use one common FS profile with separately profiled constructions | Superficially | Depends on callback | Superficially | Weak | Rejected: the common profile must import every family or execute an opaque external meaning |
| Use a generic transcript program or action map | Potentially | Author-controlled | Strong | Weak | Rejected: duplicates scheduling authority and permits omission or invented events |
| Let semantic modules own top-level construction schedules | Potentially | Contract-dependent | Medium | Weak for new families | Rejected for top-level family semantics; retained for exact primitives inside a family |
| Use sibling FS family profiles | Yes | Family-owned and closed | Strong | Strong | Selected |

Adding a future family creates an unreferenced sibling profile. Foundation's
profile locality then leaves existing canonical and duplex construction and
Protocol IDs unchanged. A change to a referenced family law rotates only that
family and its importers.

Modules remain useful below this boundary for exact permutations, codecs,
hash functions, and portable algorithms whose contracts are already covered
by the family. They do not decide which Core events are covered or what makes
the construction succeed.

## 3. Common family contract

The two profiles incorporate one closed contract, without an open callback:

1. the construction names one exact admitted `CoreId`;
2. its profile imports the exact Interaction profile;
3. construction admission requires the same immutable admitted Core handle;
4. the Core must be public-coin eligible;
5. every runtime Statement constituent required by the family is covered
   before its first dependent challenge;
6. every source prover message is covered before its dependent challenge;
7. the family owns a deterministic initialization and challenge-resolution
   schedule with no caller-authored skip map;
8. the family owns exact receipts, replay, and semantic failure rows;
9. `CheckFSConstruction` requires an identical Fresh Core and target FS Core;
   and
10. Analysis reads family-specific views and may not coerce one family to the
    other's schema.

The common contract does not define a universal transcript operation algebra.
It is a condition that each closed family law must discharge.

## 4. Duplex construction subject

The selected family defines:

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

  message_rules:
    OrderedTotalMap<covered OccurrenceRef, {
      encoder: PIRAlgorithmUse,
      encoded_length: Natural
    }>,

  challenge_rules:
    OrderedTotalMap<ChallengeRef, {
      squeeze_length: Natural,
      decoder: PIRAlgorithmUse
    }>
}
```

The exact canonical body is owned by the durable PIR page. The following are
profile-fixed laws, not authored fields:

- overwrite rather than XOR;
- state shape `(Sigma^(r+c), i_A, i_S)`;
- `Start_h`, empty absorb, zero squeeze, partial-squeeze, and lazy-boundary
  behavior;
- the initial salt position;
- construction-material schema;
- source-round schedule derivation;
- absence of labels, headers, namespaces, retry, and decoded-value
  reabsorption;
- verifier-complete and prover-required prefixes; and
- exact transition and resource-bound derivation.

The profile admits the named algorithms only when their exact ABIs, totality,
failure rows, and output shapes agree with the fixed law. A portable provider
supplies the selected hash, permutation, encoders, and decoders. It may
implement the fixed transition law, but it does not author that law.

### 4.1 Algorithm interfaces

The construction-selected state-operation interfaces are:

```text
hash_to_capacity:
  [BinaryInstanceCarrier_T] -> AlphabetSequenceCarrier_T(capacity)

permutation_forward:
  [AlphabetSequenceCarrier_T(rate+capacity)]
    -> AlphabetSequenceCarrier_T(rate+capacity)
```

Message encoders and challenge decoders have the occurrence-specific
interfaces given by their exact rules. `Start`, `Absorb`, and `Squeeze` are
profile-owned semantic operations derived from those algorithm uses; they are
not caller-selected algorithms. `Squeeze` returns state and symbols atomically.
The canonical-framed family's separate squeeze/advance split is not reused
because pairing two independently selected functions could admit an output
from one state transition and a post-state from another.

Construction admission requires exact output length and empty completed-
failure rows for every operationally total function. Missing evaluator support
is operational noncompletion; provider disagreement is checker failure.

The honest construction uses only the forward permutation. A declared inverse
and adversarial inverse access belong to the Analysis experiment selected for
a source theorem.

## 5. Instance correspondence

The paper receives one binary instance `x`; zkc begins with typed public
bindings. The family therefore derives:

```text
DuplexInstanceBindings(core) =
  every and only root-initial Statement binding,
  in ascending exact BindingRef order
```

The initial source-shaped profile requires:

- every Statement binding to exist before execution;
- no child-scope or dynamically introduced Statement;
- no duplicate elimination when two binding occurrences carry equal values;
- no verifier-private inputs; and
- no runtime SessionContext or PublicParameter binding unless a later source
  profile explicitly incorporates it into its binary instance.

The binary instance is the profile-fixed canonical encoding of the ordered
triples `(BindingRef, ValueType, CanonicalValue)`. The complete type-bound
maximum must fit `BinaryInstanceCarrier_T`. Interface wire bytes are not used.

This is a zkc-to-paper correspondence, not a field of the paper's codec. It
prevents an authored instance map from omitting a Statement and gives strong
Fiat--Shamir binding a positive-by-construction route.

If a future imported protocol needs a different binary instance convention,
it requires a separately checked directional correspondence or a sibling
construction profile. It does not mutate this profile at runtime.

## 6. Source-shape eligibility

`PublicCoinEligible(core)` remains necessary but is insufficient. The duplex
family additionally derives:

```text
DuplexSpongeEligible(core, construction)
```

The initial profile requires:

1. at least one source round;
2. one unconditional prover-message occurrence followed by one unconditional
   challenge occurrence in every source round;
3. total, ordered, one-to-one message and challenge rule maps, with every
   covered `OccurrenceRef` resolving to an exact prover-message occurrence;
4. no prover message left uncovered and no invented covered event;
5. no prover decision after the final challenge;
6. no verifier-message occurrence separate from the Challenge;
7. no joint challenge, public challenge condition, Oracle effect, or
   extension effect;
8. root-only scope for all source interaction events;
9. exact public-coin eligibility including guards and terminal dependence; and
10. finite derived transition, state, and output bounds.

Local verifier checks, claims, and reductions may occur when they introduce no
additional transcript event and preserve the fixed source-round order. A
profile extension for richer public-coin interactions requires separate
research; it is not accepted through a generic event list.

### 6.1 Derived execution

For exact runtime instance values and salt `tau`:

```text
x       := CanonicalDuplexInstance(DuplexInstanceBindings(core))
state_0 := Start_h(x)
state   := Absorb_p(state_0, tau)

for each source round i in order:
  encoded       := phi_i(alpha_i)
  state         := Absorb_p(state, encoded)
  (state,raw_i) := Squeeze_p(state, ell_V(i))
  rho_i         := psi_i(raw_i)
```

The resolver returns `rho_i` to the unchanged Core engine. It never absorbs:

- Core, construction, or application headers;
- a type tag, occurrence identifier, label, or encoded length;
- a namespace or draw ordinal;
- the decoded `rho_i`; or
- retry material.

Adding any such value creates a different construction and fails literal
duplex-family replay.

## 7. Construction-public material

The exact material schema is owner-derived:

```text
DuplexConstructionMaterialSchema(T) =
  one DuplexConstructionMaterialRef(T.id, ordinal=0, role=Salt):
    AlphabetSequenceCarrier_T(T.salt_length)
```

The ref exists even when `salt_length = 0`; its value is then the unique empty
vector. It is not a Core input, Statement, prover message, witness, challenge,
or construction-identity value.

Preparation is a PIR runtime operation:

```text
PrepareDuplexConstructionMaterial(
  exact admitted duplex FS Protocol,
  exact CoreInvocation,
  total material map,
  exact evaluator and limits)
    -> ExactDuplexConstructionMaterialCapability
     | qualified noncompletion
```

The capability is fresh, nonserializable, and bound to the exact Protocol,
Core invocation, material values, evaluator, limits, and preparation
occurrence. The admitted duplex resolver requires it. The generic
`GenerateRun` signature need not change because the resolver capability
retains the material capability.

For generation, a provider supplies one exact salt value and records the
declared uniform-law coordinate. One observed value does not prove uniformity,
independence, or freshness. For replay, the first family challenge receipt
supplies the public salt and replay needs no generation provenance.

Missing, extra, late, duplicated, or wrong-length material fails preparation
before Core execution. It is not Core rejection, sampling exhaustion, or a
transcript theorem failure.

## 8. Receipts and replay

Fiat--Shamir challenge receipts dispatch through the admitted Protocol's exact
authenticated family profile and its closed receipt schema:

```text
ProfileFSChallengeReceipt(duplex Protocol) = DuplexChallengeReceipt
```

This is semantic profile dispatch, not an open serialized union. The duplex
receipt is:

```text
DuplexChallengeReceipt = {
  challenge: ChallengeRef,
  initialization:
    Present(DuplexInitializationReceipt) exactly on the first challenge
    | Absent exactly thereafter,
  message_occurrence: exact prover-message OccurrenceRef,
  encoded_message: CanonicalValue<AlphabetSequenceCarrier_T(encoded_length)>,
  pre_absorb_state: CanonicalValue<DuplexStateCarrier_T>,
  post_absorb_state: CanonicalValue<DuplexStateCarrier_T>,
  squeezed_symbols: CanonicalValue<AlphabetSequenceCarrier_T(squeeze_length)>,
  post_squeeze_state: CanonicalValue<DuplexStateCarrier_T>,
  decoded_value: CanonicalValue<challenge type>
}

DuplexInitializationReceipt = {
  instance_bindings: exact ordered BindingRefs,
  binary_instance: CanonicalValue<BinaryInstanceCarrier_T>,
  salt: CanonicalValue<AlphabetSequenceCarrier_T(T.salt_length)>,
  start_state: CanonicalValue<DuplexStateCarrier_T>,
  post_salt_state: CanonicalValue<DuplexStateCarrier_T>
}
```

The duplex family has an empty semantic interpretation-failure row. It has no
namespace, acceptance result, retry sequence, or sampling-exhaustion failure.
Malformed runtime values, unsupported algorithms, deterministic limit
exhaustion, and provider disagreement remain the ordinary qualified
noncompletion classes.

Replay authenticates the exact family profile, construction, Core invocation,
and record, reconstructs initialization and every transition, requires exact
field exhaustion, and compares the Core terminal. Receipt equality proves one
deterministic replay only. It establishes no causal generation, salt law,
ideal primitive, or theorem.

## 9. Prover-generation prefix

The verifier-side FS interpretation executes every source round. The family
also derives:

```text
ProverRequiredChallengePrefix =
  every challenge whose value is visible to a later prover decision
```

For the fixed alternating source shape, this is challenges `1 .. k-1`. An
honest construction-material/prover Plan can stop transcript derivation after
producing the final prover message. Verification and a complete Protocol run
still execute and record round `k`.

This prefix is a Plan-facing static view. It does not delete the final
Challenge from the Core or change the verifier-complete Protocol.

## 10. Codec property boundary

Construction admission can check:

- exact message and challenge map coverage;
- deterministic total algorithm shape;
- exact input/output ABIs;
- exact encoded and squeezed lengths;
- empty operational failure rows; and
- output value-type admission.

It must not accept authored Booleans such as `injective = true` or
`ideal_permutation = true`.

General prover-codec injectivity, efficient inversion, verifier-decoder bias,
surjectivity, balanced fibers, efficient uniform fiber sampling, salt
uniformity, ideal models, and query bounds are Analysis premises. A closed
codec algebra may later make a property structural by construction, but
Analysis cannot become a prerequisite of PIR admission.

## 11. Identity law

Construction identity includes:

- exact sibling profile;
- `CoreId`;
- alphabet type and zero symbol;
- rate, capacity, state, and binary-instance bounds;
- exact algorithm and evaluation-contract references;
- salt length;
- complete ordered message and challenge rules; and
- exact lengths and decoder/encoder identities.

It excludes:

- runtime Statement values;
- the actual salt and prover messages;
- provider source paths and validation fixtures;
- Analysis assumptions or results;
- proof-byte placement; and
- implementation or evidence coordinates.

Thus one Core can have Fresh, canonical-framed FS, and duplex-sponge FS
Protocols with one shared `CoreId` and three pairwise-distinct `ProtocolId`s.
Changing runtime values changes execution data, not semantic construction or
Protocol identity.

## 12. Consumer routing and initial support

| Consumer | Selected disposition |
|---|---|
| Canonical PIR | Keep Core and Protocol root shape; authenticate the external construction body under its exact family profile |
| Interface | Current profile remains canonical-framed only; duplex construction material needs a separate downstream extension |
| Plan | Current decision-scoped randomness cannot mint pre-execution salt; a construction-material Plan satellite is deferred |
| Relations | No duplex state or salt semantics; optional later proof-material correspondence only |
| Analysis | Add family-specific source views and explicit no-active-theorem status |
| OIR | Return `Unsupported` for duplex until a sibling endpoint/OIR profile owns salt placement and proof parsing |
| Realization | Later bind exact portable providers and pre-execution material generation |
| Evidence | Later record provider correspondence and observed execution without upgrading semantic or theorem claims |

Existing canonical AFK results remain bound to the canonical-framed profile.
They do not transfer through equal Core identity.

## 13. Rejected opportunities

The comparison revealed useful but intentionally unselected capabilities:

- caller-defined transcript labels and metadata;
- STROBE transport roles, encryption, MAC, ratchet, and secret state;
- transcript forking, rollback, tree state, or external mutable prefixes;
- one universal transcript DSL;
- private witness-derived RNG mixed with the public transcript;
- a generic public-condition, joint-challenge, or Oracle schedule; and
- an automatic theorem bridge between interface-compatible constructions.

Each would enlarge authority beyond the source case. None has two independent
current consumers with one common law.

## 14. Reversal conditions

Reopen the sibling-profile choice if Foundation gains a closed, non-callback
construction-class contract that can authenticate new top-level schedules
without importing them and without author-controlled influence.

Reopen source-shape eligibility if another primary source proves the same
duplex construction for a materially richer Core shape and identifies exact
coverage, challenge, and failure laws.

Reopen the runtime-material seam if a second construction needs secret,
stateful, or post-start material that cannot use this public immutable
capability without conflating authority.

Reopen the typed instance choice if an exact imported implementation cannot be
related to the fixed canonical encoding by a checked directional
correspondence.

No reversal is triggered merely by a host library exposing a similar
`absorb`/`squeeze` trait.
