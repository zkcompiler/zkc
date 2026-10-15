# Bulletproofs+

This family provides a blinded weighted inner-product argument and Monero's
64-bit aggregated range proof. All equations, rounds, transcript transitions
and proof layout are ordinary `.zkc` code. The runtime supplies field/group
operations, byte encodings, Keccak-256 and managed randomness.

## Public modules

| Module | Exports and use |
|---|---|
| `bulletproofs::inner_product` | `Bases<G>`, `Claim<G>`, `Witness<F>`, `PointEncoding<G>` and `Argument<G,Encoding,MaxRounds>`; `count` reports basis length; `cross`, `fold_bases` and `fold_witness` expose the dense reduction equations; `fold_coefficients` and `evaluate_bases` expose their coefficient form |
| `bulletproofs::monero` | `Range`, `Monero`, `commit`, `dimensions`, `generators`, `value_base`, `mask_base`, `Wire`, `G`, `F`; `initial_transcript` and `hash_scalar` supply the concrete hash-chain helpers |
| `bulletproofs::monero::transcript` | `Provider`: the concrete Keccak/scalar hash chain |
| `bulletproofs::monero::codec` | `Codec`: complete `BulletproofPlus` serialization and exact scalar admission |

`Argument` proves knowledge of equal-length vectors `a,b` and a mask `alpha`
opening `C = sum(a_i G_i) + sum(b_i H_i) + sum(y^(i+1) a_i b_i) H + alpha B`.
Its basis length must be `2^rounds`, with `rounds <= MaxRounds` and nonzero `y`.
The caller establishes the statement and supplies suitable independent generators.
The terminal blinding step is part of the argument. Both participants retain
their own received challenges and messages. `PointEncoding` separates raw
transcript observations from admitted group points.

The verifier carries a `Claim<G>` as coordinates over its two bases plus a
`zkc::linear::Combination<G>` of other terms. `point_claim(bases, point)` wraps
an already evaluated commitment. Folding updates scalar coordinates and adds
admitted round points; the final equation combines coefficients per basis
position before one MSM. The prover still computes dense folded bases and
emits the same messages. Raw wire bytes remain the transcript input, and point
admission occurs before adding a received point to the expression.

`Range` specializes this argument to 1..16 unsigned 64-bit amounts. Counts pad
to the next power of two. The public input is the concatenation of the original
32-byte commitments `V`; the private input is `Indices` amounts and scalar masks.
`commit` creates these inverse-eight commitments. `dimensions` returns
`(count, padded_bit_count, rounds)`. The shared `rounds` argument controls the
protocol loop; both participants check it against the commitment count.

```text
use bulletproofs::monero::{Range, Monero};

proof Proof = Range {
  prover P;
  verifier V;
  public { commitments, rounds };
  accept accepted;
  construction Monero;
}
```

The [runnable example](../../examples/projects/bulletproofs-plus/README.md)
provides public inputs and witness files. A project can also call `Range` as a
child protocol; native transcript framing and the Monero construction are
separate choices.

## Concrete compatibility boundary

`Monero` implements the `BulletproofPlus` object at Monero v0.18.5.1,
revision `4f92268d7c16741cfb41e5bbe2aa46cc260a9ea5`. Its [source](https://github.com/monero-project/monero/blob/4f92268d7c16741cfb41e5bbe2aa46cc260a9ea5/src/ringct/bulletproofs_plus.cc)
and [Bulletproofs+ paper](https://eprint.iacr.org/2020/735) specify the algorithm.
The proof does not include `V`; the application supplies those statement bytes.
This family does not encode a complete Monero transaction or verify signatures,
fees, balance, consensus rules or a batch of proofs.

The nominal `edwards25519.prime` group uses the scalar-order field
`ristretto255.scalar`; sharing a field does not identify Edwards and Ristretto
points. Mathematical points stay in the prime subgroup. Monero's emitted points
are divided by eight; admitted full-curve wire points are multiplied by eight.
Original canonical wire bytes are hashed before this projection, including
legal torsion components. Generator derivation uses Monero's legacy point map,
not RFC 9380 hash-to-curve. Proof scalar words are canonical little-endian values;
challenge hashes are reduced modulo the scalar order.

The verifier uses the single-proof equation. It does not need the randomized
batch coefficients used by upstream's multi-proof verifier. Serialization uses
`A,A1,B,r1,s1,d1,len(L),L,len(R),R`, even though interaction sends folding rounds
before the terminal proof. The codec requires exact lengths, minimal count
encodings and complete consumption.

Private blinding draws use `zkc::sampling::Nonzero<F,32>` to match upstream's
nonzero scalar requirement. It retains the managed service across rejected
zero draws and stops if 32 consecutive candidates are zero. This bounds work;
there is no fallback value. Random-byte streams and PRNG algorithms are not
part of the byte-compatibility claim: exact comparisons couple scalar coins.

One invocation is one attempt. Zero challenges stop both roles; callers can
invoke again with fresh managed randomness. Automatic recovery from this stop
is not exposed by this Entry. Upstream restarts its prover on that negligible
case; accepted proof bytes and the nonzero-challenge verification predicate are
unchanged. No challenge is silently replaced. Masks and private coins must be
fresh and secret in an application; checked-in witnesses and replay coins are
public examples. The interpreter is not a constant-time proving implementation.

## Checks

The [source integration tests](../../common/tests/protocol/test_bulletproofs_plus.py)
compare exact bytes for all 16 counts and four amount patterns against the
[pinned independent producer](../../common/tests/reference/monero/README.md).
They also check independent random-coin proofs, torsion before/after hashing,
malformed encodings, wrong statements, invalid witnesses and compiler modes.
The native point map has separate upstream vectors. These controls demonstrate
finite interoperability and execution; they are not a security proof or a
claim of parser equivalence on all inputs.
