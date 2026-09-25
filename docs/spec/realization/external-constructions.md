# Explicit external construction data transitions

This contract installs atomic external construction operations in authored local
functions. Their source operations, logical MLIR kernels, physical bindings and
native implementations preserve explicit call boundaries. The operations do not
contain a proof algorithm or determine which proof fields are observed.

## Interpretation and admission

An external construction state in this contract is an ordinary, copyable
`indices` value, not an affine `transcript` capability. Every component has the
existing canonical unsigned 64-bit index encoding. State envelopes are
`[1514881876, 1, suite, payload...]`. Version 1 fixes these suites:

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
and `external.openvm` names select the version-1 suites above, independently of
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

## Construction, resources and trust boundaries

No operation prepends an artifact identity, session, source origin, domain tag or
zkc prefix to the cryptographic input. The state envelope tags are checked
metadata and are never hashed or observed. Serialization does not observe a
field. Proof-container mapping, application-statement checks, authenticated
response guards, randomness and attempt selection are separate obligations.
These operations do not install a `Transcript` domain or a generic automatic
Fiat-Shamir construction rule. Internal Merlin/Spongefish artifact-bound
constructions remain distinct; selecting an external name in their suite slot
is unsupported. No automatic construction correspondence is asserted.

Kernel diagnostic identities use `external-…` consistently in native and Lean
execution. With sufficient host capacity, validation checks the state envelope
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
[implementation guide](../../compiler/interactive-execution.md#external-construction-execution)
and [backend adapter](../../../crates/zkc-backends/src/external/README.md).
