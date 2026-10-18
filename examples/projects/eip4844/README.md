# EIP-4844 blob commitments

Ethereum's EIP-4844 polynomial-commitment functions as Entries of the
[KZG library](../../../libraries/kzg/README.md). Proofs and commitments are
byte-compatible with c-kzg-4844 v2.1.8.

| Entry | Kind | EIP-4844 function |
|---|---|---|
| `BlobToCommitment` | run | `blob_to_kzg_commitment` |
| `ComputeKzgProof` | run | `compute_kzg_proof` |
| `ComputeChallenge` | run | `compute_challenge` |
| `PointEvaluationPrecompile` | run | point evaluation precompile `0x0A` |
| `KzgProof` | proof | `verify_kzg_proof` (prover: the opening for a stated point and value) |
| `BlobProof` | proof | `compute_blob_kzg_proof` and `verify_blob_kzg_proof` |
| `BlobBatchProof` | proof | `verify_blob_kzg_proof_batch` (prover: every blob proof), at most 64 blobs |

Blobs and the prover's setup are large, so the sample inputs reference native
frame files beside each document. `prepare.py` writes them from the
[upstream vectors](../../../common/tests/fixtures/kzg-eip4844/vectors.json) and
the library's trusted setup into `build/inputs`. With built tools on `PATH`,
run here:

```sh
python3 prepare.py
zkc run BlobToCommitment --input=P=build/inputs/example.BlobToCommitment/P.json
zkc prove BlobProof --public=build/inputs/example.BlobProof/public.json \
  --witness=build/inputs/example.BlobProof/witness.json --output=build/blob.proof --allow-authored
zkc verify BlobProof --public=build/inputs/example.BlobProof/public.json \
  --proof=build/blob.proof --allow-authored
```

The other Entries follow the same pattern with their `P.json`, `public.json`
and `witness.json` documents. `--allow-authored` authorizes the library's
byte construction; it does not certify cryptographic security.

The public inputs of `BlobProof` are the blob and commitment; the prover's only
private input is the setup's G1 Lagrange points, which the library admits only
with the pinned digest. The proof is the 48-byte opening proof. `BlobBatchProof`
takes the concatenated blobs and commitments and their count; its proof is the
concatenation of the blob proofs. A verifier needs no setup input: the G2 point
`[tau]` is a library constant.

The vector tests run every Entry; see the library's checks for their scope.
Under the default execution capacity, `BlobBatchProof` verifies up to 63 blobs,
the limit of the proof Host's public-input binding, and proves up to 19.
