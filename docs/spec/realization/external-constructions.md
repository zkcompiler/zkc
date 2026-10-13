# Explicit external construction data transitions

This contract installs atomic external construction operations in authored local
functions. Their source operations, logical MLIR kernels, physical bindings and
native implementations preserve explicit call boundaries. The operations do not
contain a proof algorithm or determine which proof fields are observed.

These are ordered, fallible local operations, even though their state values
are copyable. Equal operands do not permit common-subexpression elimination,
dead-call removal or speculation: calls consume work and can stop. Their kernel
operations make no MLIR purity or speculatability claim.

## Serialized state envelopes

The Monero and OpenVM construction states are ordinary, copyable
`indices` values. Every component has the
existing canonical unsigned 64-bit index encoding. State envelopes are
`[1514881876, 0, suite, payload...]`. Version 0 fixes these suites:

| Suite | Exact interpretation | Payload |
|---|---|---|
| 1 | Monero v0.18.5.1 scalar hash chain, Keccak-256 then little-endian reduction modulo the Edwards scalar order | 32 byte indices |
| 2 | OpenVM stark-backend v2.0.1 duplex with BabyBear Poseidon2 from Plonky3 0.4.3 | 16 canonical field words, absorb cursor, sample cursor |

Monero is pinned to revision `4f92268d7c16741cfb41e5bbe2aa46cc260a9ea5`;
OpenVM v2.0.2 is pinned to `59a69b8b0cbee7011ac978e4cc07707ee3681944`, with
stark-backend v2.0.1 at `362c7ad8c6b042b320471a137e3eadec7ec69a44`.
Source provenance and primitive adapter boundaries are maintained in
[`external/provenance.json`](../../../crates/zkc-backends/src/external/provenance.json).

Every transition validates the full state envelope. Byte indices must be below
256. Field words must be below 2013265921; absorb cursor is below 8 and sample
cursor is at most 8. Field words are converted only after the range check.
Ordinary indices represent the finite integer encodings injectively. No modular
index arithmetic, BabyBear field law, extension-field law, raw-point subgroup
law or Ristretto interpretation follows from this representation. Monero hash
inputs are opaque encoded 32-byte words, with no point decoding or cofactor
clearing; the initial word need not be a canonical scalar. Hash outputs are
canonical reduced scalars encoded as bytes, without automatically acquiring an
arithmetic domain type.

An envelope is a checked data representation, not an unforgeable capability.
Importing any canonical snapshot is meaningful, including snapshots not reached
from the standard constructor. Reachability and the intended construction
schedule are separate authored-program obligations. Reusing a data state is an
explicit branch or trial. It does not duplicate an internal affine resource or
refund consumed native work. Existing affine transcript/RNG/nonce rules are
unchanged. A state can be disclosed as ordinary data; this does not assert that
such disclosure is safe for an arbitrary enclosing protocol.

## Atomic contracts

Every operation has no static arguments and no operation attributes. The sole
installed physical implementation is `native/<operation>`. The `external.monero`
and `external.openvm` names select the version-0 suites above, independently of
any internally installed transcript suite. Unknown providers fail admission.

| Operation | Inputs | Outputs |
|---|---|---|
| `external.monero.init` | `indices` initial bytes | `indices` state |
| `external.monero.hash` | `indices` concatenated words | `indices` scalar bytes |
| `external.monero.update` | `indices` state, `indices` concatenated words | `indices` successor, `indices` scalar bytes |
| `external.openvm.init` | none | `indices` state |
| `external.openvm.observe` | `indices` state, `indices` field words | `indices` successor |
| `external.openvm.sample` | `indices` state | `indices` successor, `index` sample |
| `external.openvm.sample_ext` | `indices` state | `indices` successor, `indices` four coefficients |
| `external.openvm.sample_bits` | `indices` state, `index` bits | `indices` successor, `index` masked sample |
| `external.openvm.check_witness` | `indices` state, `index` bits, `index` witness | `indices` successor, `bool` accepted |

Monero init accepts exactly 32 bytes and performs no hashing. Hash inputs must
have length divisible by 32, including length zero. Stateless hash computes
`Hs(items)`; update computes and installs `Hs(state || items)`. An empty update
still hashes the state. One update with two words differs from two updates with
one word each. Zero scalar outputs are returned without retry or rejection.

OpenVM init gives zero words and cursors, with no permutation. Observe overwrites
successive rate positions; filling position 7 permutes and sets cursors to 0 and
8. A partial observation retains the current sample cursor. Empty observation
is identity. Sample first permutes when the absorb cursor is nonzero or the
sample cursor is zero, then decrements the sample cursor and returns that word.
`sample_ext` repeats sample four times in coefficient order and grants no
extension arithmetic. Bits are in 0..30 and mask a canonical sample by
`2^bits - 1`; `sample_bits(0)` still consumes one sample. This is not a claim
of unbiased bounded sampling.

Witness checks require a canonical BabyBear witness even at zero difficulty.
For bits zero the result is the identical state and true, with no observation
or sample. Otherwise the transition observes the witness, samples the requested
bits, and tests zero. A false result **returns the reached successor state**;
it is not an implicit rollback, halt, or retry. The authored caller decides
whether to reject, continue, or perform a trial on a copied prior state.

## SHAKE128 state

`zkc::shake128::State` is an immutable, copyable, discardable local value with
logical type `shake128_state`, MLIR type `!crypto.shake128_state`, and physical
representation `native.shake128/0`. It has no participant-family or external
construction admission, ingress codec, equality operation, or managed capability.
Snapshot size is bounded independently of the absorb history; cloning and
updating a snapshot never replay earlier absorbed bytes.

| Operation | Inputs | Outputs |
|---|---|---|
| `shake128.init` | none | state |
| `shake128.absorb` | state, `bytes` | successor state |
| `shake128.squeeze` | state, `index` length | successor state, `bytes` |

The abstract state is `(M, k)`, initially `(empty, 0)`. Absorbing `x` returns
`(M || x, 0)`. Squeezing `n` returns `SHAKE128(M)[k..k+n]` and `(M, k+n)`.
Even an empty absorb resets the read position. Absorb boundaries and previous
reads do not become part of `M`; library code supplies framing, session binding
and sampling rules. These semantics match the SHAKE128 XOF used by Spongefish
0.7.4, without introducing its protocol or proof schedule into the primitive.

The installed operations use `native/<operation>` with no static arguments or
attributes. Absorb and squeeze retain ordered History effects. Allocation and
wire limits are checked before work. Each call charges the existing cumulative
external-work budget by `n + ceil(n/168) + 1`, using absorbed or requested bytes;
init uses `n = 0`. Live-state accounting includes the fixed backing per distinct
snapshot, including snapshots inside aggregates. A fork does not refund work.

## Mathematical byte encodings

`zkc::encoding` provides explicit encodings independently of transport and
transcript observation. The installed implementations use arkworks for
BLS12-381 Fr and G1. Other domains require their own installed implementations;
the generic source signature does not promise support for every field or group.

| Operation | Inputs | Outputs | Interpretation |
|---|---|---|---|
| `field_be<F>` | `F` | `Bytes` | Canonical 32-byte big-endian integer |
| `field_from_be<F>` | `Bytes` | `(bool, F)` | Exact width and integer below the scalar modulus |
| `field_reduce_be<F>` | `Bytes` | `F` | Big-endian integer reduced modulo the scalar modulus |
| `group_compressed<G>` | `G` | `Bytes` | Canonical 48-byte compressed G1 point |
| `group_from_compressed<G>` | `Bytes` | `(bool, G)` | Exact width, canonical encoding and prime-order subgroup check |

The decoder Boolean reports validity. On invalid encoding the accompanying value
is zero or the group identity. Decoding has no transcript effect; a caller uses
`require valid` before observing a decoded value when the protocol requires that
order. Resource exhaustion still stops execution. Reduction accepts an arbitrary
bounded byte string, including empty, and is distinct from canonical decoding.
Reduction uses constant auxiliary storage and debits two logical work units per
input byte before computation.
The wire format may retain the original bytes for later observation; these
operations impose no universal re-encoding policy on a protocol.

## Construction, resources and trust boundaries

The installed `SourceHistory` facet permits ordinary source calls to the
copyable data-state transitions above. Declaration validation requires a
matching `History` successor, a concrete Copy/Drop state constructor and no
managed observation or sampling facet. Source calls retain their installed
ordered operation in IR, including when a successor is unused. This permission
does not admit managed RNG or transcript kernels through ordinary functions.
Copyable external state carries no trusted challenge provenance. In particular,
a wire-capable snapshot received from a peer is peer-controlled; choosing it as
a challenge source is the author's responsibility. Only managed services carry
compiler-tracked sampling authority.

No operation prepends an artifact identity, session, source origin, domain tag or
zkc prefix to the cryptographic input. The state envelope tags are checked
metadata and are never hashed or observed. Serialization does not observe a
field. Proof-container mapping, application-statement checks, authenticated
response guards, randomness and attempt selection are separate obligations.
These operations do not install a `Transcript` domain or a generic automatic
Fiat-Shamir construction rule. Internal Merlin/Spongefish artifact-bound
constructions remain distinct; selecting an external name in their suite slot
is unsupported. No automatic construction correspondence is asserted.

Native kernel diagnostic identities use `external-…`. The current Lean import
profile does not admit these external constructions. With sufficient host capacity, validation checks the state envelope
and its canonical payload before other operands. Monero update checks state
bytes before item length/bytes. Witness checking checks state, u32 bit width,
allowed bit range, u32 witness and field canonicality in that order. A malformed
operand causes no hash/permutation or work debit. These ordered refusals do not
assert native/reference host-capacity correspondence.

Execution validates operands and capacity before invoking cryptographic work.
Consumed work remains consumed; copying a state never copies its work allowance.
Attempt, candidate-search and primitive-work policies are distinct. A reference
interpretation may obtain the hash and permutation through an explicit primitive
interface, whose replies are bound to exact inputs and call origins. Such a
provider assumption alone establishes neither primitive correctness nor a
complete native correspondence. Current APIs and evidence are recorded in the
[authored native guide](../../compiler/construction.md)
and [backend adapter](../../../crates/zkc-backends/src/external/README.md).

## Authored native deployment

The [native proof profile](../formats/proof.md) admits
these transitions through ordinary local functions and its `indices` input and
message codec. An empty selected suite declares no derived transcript. It does
not forbid an authored data-state computation. Existing affine transcript inputs
remain outside this host's input-constructor contract.

The application independently supplies the expected deployment digest and
validator public inputs. Canonical snapshot bytes are public configuration when
declared as such. The host checks framing, declared input consistency and the
proof header; the first reached external operation checks state representation.
No host constructor attests that an imported state is reachable. State received
from the producer has only the meaning given by the authored verification code.

Authored code selects the exact inputs to each update, observation and sample.
The native container header and ambient invocation context are not automatically
absorbed by these primitives. `binding_scope = "header"` describes the host's
binding guarantee, including when authored external calls are present. An ignored
input, or a duplex word overwritten before sampling, need not affect a response.
A declaration of public inputs alone is no cryptographic binding theorem.

Source/candidate checking preserves the chosen calls and operands. It does not
prove transcript completeness: an authored program can omit a received word
from its chain, import an inappropriate root or return an inadequate acceptance
predicate. There is no automatic external construction correspondence claim.
The `History` facet identifies the declared state input/successor relation; it
neither makes copyable data affine nor proves a unique live chain. Affine-origin
analysis tracks affine outputs only. These operations are admitted in ordinary
`local.if` and `local.for`; the existing lexical prohibition on history calls in
private `local.match` arms still applies. History metadata does not permit
deleting or reordering a call.

## Work, attempts and control

External primitive work is cumulative within one native proof invocation,
including all producer attempts. Each independent producer or validator
invocation starts its own allowance. Trial copies, failed witness predicates,
discarded proofs and cleanup never refund completed work. A call refused before
its debit consumes no primitive work; earlier calls remain charged. The default
allowance is 16,777,216 units under the metric above.

The native proof host permits an application to lower this allowance through
`NativeDeployment::with_external_work_limit`. Values above the default refuse
with `native-proof-external-work-limit`; zero admits only zero-work transitions.
This is local execution configuration, outside deployment and attempt-policy
identities and transcript bytes. Reports record the actual allowance, cumulative
consumption and each attempt's consumption. The CLI retains the default.
An exhausted primitive budget is a fatal execution stop, never a retry decision.

A returned completion Boolean uses the existing attempt contract. A conditional
can skip a local suffix while returning actual RNG successors. It cannot skip a
later participant send. A bounded loop with a carried found bit can skip later
trial calls, but still enters its remaining iterations and charges control
instructions and frame bindings. Such an encoding is not early return or break
and can exhaust interpreter budgets after its last trial. True participant
abandonment requires a separate control/custody contract.

Canonical wire decoding and primitive validation remain different boundaries.
Malformed frame bytes fail decoding. An admitted `indices` value with an invalid
state envelope, byte, field word or bit width stops at the reached primitive
with its `refused:external-*` diagnostic. A canonical false witness check returns
its successor and Boolean; an authored guard can stop there with
`artifact-stopped:Explicit("reject")`. The reached primitive validates its
complete input before charging any work, including all words in one observation.
A normal false terminal Boolean produces `artifact-rejected`. Full proof
consumption and atomic publication retain the native proof contract in every case.

Invalid primitive data received in a canonical frame is also non-acceptance.
The first reached failure retains its diagnostic and consumed work; unread
later frames do not replace it with `proof-trailing`. Full-consumption checking
occurs on normal participant return, before testing the terminal Boolean.
