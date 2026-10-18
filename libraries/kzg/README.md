# KZG commitments

This family provides univariate KZG commitments to polynomials in evaluation
form and Ethereum's EIP-4844 blob commitments. Evaluation, quotients, the
reproduced challenge hash inputs, proof layout and setup admission are ordinary
`.zkc` code. The runtime supplies BLS12-381 field and group operations, the
pairing check, byte encodings and SHA-256.

## Public modules

| Module | Exports and use |
|---|---|
| `kzg` | `evaluate`, `quotient`, `in_domain`, `position`, `unit`: evaluation-form algebra over the `n`-th roots of unity of any field |
| `kzg::eip4844` | The EIP-4844 functions, the `Commit`, `Prove`, `Challenge` and `PointEvaluation` protocols, the proof protocols `PointOpening`, `BlobOpening` and `BlobBatch<MaxBlobs>` with their constructions `Point`, `Blob` and `Batch<MaxBlobs>`, plus `F`, `G1`, `G2`, `roots`, `bit_reverse`, `verifier_key` and `admit_setup` |
| `kzg::eip4844::transcript` | `Statement` and `Combination`: c-kzg-4844's two challenge hash inputs as copyable transcript data |

`kzg::evaluate(values, points, z)` returns `p(z)` for `values[i] = p(points[i])`,
where `points` lists every `n`-th root of unity in some fixed order. At a domain
point it returns the stored value; elsewhere it uses the barycentric formula
`p(z) = (z^n - 1)/n * sum_i values[i] points[i] / (z - points[i])`.
`kzg::quotient` returns `(p(X) - y)/(X - z)` in the same form, including the
derivative form of the entry at a domain point. Both are exact field
computations; their order of operations does not affect the result.

## EIP-4844 functions

| EIP-4844 function | `kzg::eip4844` |
|---|---|
| `blob_to_kzg_commitment` | `blob_to_kzg_commitment(blob, setup)`; protocol `Commit` |
| `compute_kzg_proof` | `compute_kzg_proof(blob, z, setup)`; protocol `Prove` |
| `compute_blob_kzg_proof` | prover of `BlobOpening` under construction `Blob` |
| `verify_kzg_proof` | `verify_kzg_proof(commitment, z, y, proof)`; verifier of `PointOpening` under construction `Point` |
| `verify_blob_kzg_proof` | verifier of `BlobOpening` under construction `Blob` |
| `verify_blob_kzg_proof_batch` | verifier of `BlobBatch` under construction `Batch` |
| `compute_challenge` | `compute_challenge(blob, commitment)`; protocol `Challenge`, which first requires a 131072-byte blob and a commitment that decodes as a point, as c-kzg-4844's Go binding does before calling it |
| Point evaluation precompile (address `0x0A`) | `point_evaluation(input)`; protocol `PointEvaluation` |

```text
use kzg::eip4844::{BlobOpening, Blob};

proof BlobProof = BlobOpening {
  prover P;
  verifier V;
  public { blob, commitment };
  accept accepted;
  construction Blob;
}
```

The [example project](../../examples/projects/eip4844/README.md) selects every
function as an Entry. Under the default execution capacity a batch verifier
handles 63 blobs, the limit of the proof Host's public-input binding, and a
batch prover 19 blobs; the prover's bit reversal in `.zkc` dominates its
allocation. A larger batch needs an explicit capacity configuration.

A blob is 131072 bytes: 4096 canonical 32-byte big-endian scalars of the
BLS12-381 scalar field. Blob element `i` is the polynomial's value at
`roots()[i]`, the roots of unity in bit-reversed order.
Commitments and proofs are 48-byte compressed G1 points; points `z` and values
`y` are 32-byte big-endian scalars.

### Protocols and transcripts

`BlobOpening` is the interactive protocol behind the blob functions: after the
statement (blob and commitment) is fixed, the verifier draws the evaluation
point `z`, the prover sends the opening proof, and the verifier evaluates the
blob at `z` itself and checks the pairing equation. The construction `Blob`
replaces the draw with `compute_challenge`: SHA-256 of `FSBLOBVERIFY_V1_`, the
16-byte big-endian degree bound 4096, the blob and the commitment, reduced
modulo the scalar field order as a big-endian integer. The proof is the 48-byte
compressed opening proof.

`BlobBatch` checks several blob openings with one random linear combination
(`verify_kzg_proof_batch`). Each opening point is that blob's own evaluation
challenge, computed locally by both participants from its blob and commitment
alone (`compute_challenge`). The evaluation challenge has no per-position
domain separation, as upstream: equal statements at different positions share
a point. After every proof is fixed, the verifier draws one weight `r` and
checks the combination with weights `r^i`. The two bindings stay separate: the
construction `Batch` derives only `r`, as SHA-256 of `RCKZGBATCH___V1_`, the
8-byte big-endian degree bound and count, then commitment, `z`, `y` and proof
of every opening in order. Positions enter only through this order, and blobs
are not hashed again. The transcript provider recomputes each `z` and
`y = p(z)` from the statement, as the verifier does: they are verifier-side
values, not messages.
The proof is the concatenation of the 48-byte proofs. The public `count` sizes
the loop up to the static bound `MaxBlobs`; both participants check it against
the commitments and blobs.

Both constructions reproduce c-kzg-4844's explicit hash inputs, tagged
`FSBLOBVERIFY_V1_` and `RCKZGBATCH___V1_`, byte for byte; the upstream vectors
and derived cases check that agreement. They follow c-kzg-4844 rather than a
Fiat–Shamir transformation of the interactive protocols: `Statement::draw`
returns `compute_challenge(blob, commitment)` without advancing its state, and
`BlobBatch` computes each `z_i` with SHA-256 in the protocol body. No
Fiat–Shamir security theorem covers these constructions.

`PointOpening` has no verifier randomness: the prover, holding the blob behind
the commitment, sends the proof for the stated `z` and `y`. Its construction
`Point` transports the proof bytes unchanged.

Deliveries of the drawn values to the prover are erased by the constructions.
The verifier of a construction accepts exactly when the corresponding
EIP-4844 function returns true; it rejects when the function returns false and
stops when the function raises an error. Malformed inputs therefore stop: a
wrong length, a noncanonical scalar, a point encoding that is not canonical,
not on the curve or not in the prime-order subgroup, and trailing or missing
proof bytes. The upstream single-blob path for one blob and the immediate
acceptance of no blobs coincide with the batch equation, which this library
always evaluates.

### Trusted setup

[`eip4844/trusted_setup.txt`](eip4844/trusted_setup.txt) is the Ethereum KZG
ceremony output as distributed by c-kzg-4844 v2.1.8 under the Apache License
2.0 (`src/trusted_setup.txt`,
SHA-256 `d39b9f2d047cc9dca2de58f264b6a09448ccd34db967881a6713eacacf0f26b7`). It
lists 4096 G1 Lagrange points, 65 G2 monomial points and 4096 G1 monomial
points, as hexadecimal compressed encodings. The library uses two parts:

- The verifier key `[tau]` in G2 is the second G2 monomial point.
  `verifier_key()` embeds it as a constant, so verification has no setup input.
- The prover receives the G1 Lagrange points, in file order, as a
  `Groups<G1>` input. `admit_setup` accepts only points whose concatenated
  compressed encodings have SHA-256
  `52c7615a9bd3eb20df67eb5a81ee701c96787c82a5ff638740b54fbadfde960b`.
  Commitments use the bit-reversed basis by bit-reversing the values instead.

The constants are checked against the file by the integration tests. The
library does not re-run the ceremony's consistency checks; the digest pins the
published points.

## Compatibility boundary

The functions follow Ethereum's normative KZG specification,
[`ethereum/cryptography-specs`](https://github.com/ethereum/cryptography-specs)
(`EthCryptographySpecs/Kzg/Core.lean`), and are byte-compatible with
[c-kzg-4844 v2.1.8](https://github.com/ethereum/c-kzg-4844/tree/v2.1.8), revision
`e125905e5e01186e6ccb7a0ced4845bf7eddbcfe`. EIP-7594 cell functions are not
included. Inputs are `Bytes` of any length; the length checks of the upstream
typed interfaces are ordinary `require` checks here.

## Checks

The [integration tests](../../common/tests/protocol/test_kzg_eip4844.py) run all
262 EIP-4844 vectors of c-kzg-4844 v2.1.8 through the example Entries and compare
exact bytes and accept, reject or stop outcomes. A second corpus derives 57
cases from those inputs (malformed point encodings and lengths, changed and
negated proofs, duplicated, repeated and reordered batch openings) with
outcomes computed by the pinned c-kzg-4844 reference. The tests also build the
precompile input from the point vectors, check the challenge entry point's
typed inputs, the setup constants and digest against the asset, the prover's
statement checks and the batch bounds. The
[corpora](../../common/tests/fixtures/kzg-eip4844/) and their
[reproduction](../../common/tests/reference/c-kzg/README.md) are pinned to the
upstream revision. These controls demonstrate finite interoperability; they
are not a security proof. The interpreter is not a constant-time
implementation.
