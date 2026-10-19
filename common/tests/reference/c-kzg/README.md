# c-kzg-4844 reference

The [EIP-4844 corpora](../../fixtures/kzg-eip4844/) come from
[c-kzg-4844 v2.1.8](https://github.com/ethereum/c-kzg-4844/tree/v2.1.8), revision
`e125905e5e01186e6ccb7a0ced4845bf7eddbcfe`:

- `vectors.json` holds the 262 upstream EIP-4844 vectors (`tests/*/kzg-mainnet`)
  for `blob_to_kzg_commitment`, `compute_kzg_proof`, `compute_blob_kzg_proof`,
  `compute_challenge`, `verify_kzg_proof`, `verify_blob_kzg_proof` and
  `verify_blob_kzg_proof_batch`. Blobs are stored once, keyed by SHA-256.
  These vectors are identical to those of `ethereum/cryptography-specs` at
  `d1331f02e308fe6d0aedda8601e4d5b0fc360318`.
- `extra.json` holds cases derived from those inputs: point encodings with
  cleared or misplaced flags, a coordinate equal to the base-field modulus, a
  coordinate with no curve point, a point outside the prime-order subgroup,
  wrong lengths, negated and changed proofs, and batches with duplicated,
  repeated, reordered, swapped or missing openings. Their outcomes are computed
  by this directory's executable, which links the published `c-kzg` 2.1.8 crate.
  The crate's C sources are identical to the tagged revision.

c-kzg-4844 is distributed under the Apache License 2.0, the license of this
repository; the retained vectors and the library's copy of its trusted setup
are redistributed under it.

The executable is a separate Cargo workspace with its own lockfile; nothing
here enters the native workspace or its builds. It loads the trusted setup
from the given file. To regenerate and compare the corpora:

```sh
git clone --branch v2.1.8 https://github.com/ethereum/c-kzg-4844 build/experiments/c-kzg-4844
cargo build --release --locked --manifest-path common/tests/reference/c-kzg/Cargo.toml \
  --target-dir build/experiments/c-kzg-reference
python3 common/tests/reference/c-kzg/reproduce.py \
  --source build/experiments/c-kzg-4844 \
  --reference build/experiments/c-kzg-reference/release/zkc-c-kzg-reference \
  --output build/experiments/kzg-eip4844-fixtures
cmp build/experiments/kzg-eip4844-fixtures/vectors.json common/tests/fixtures/kzg-eip4844/vectors.json
cmp build/experiments/kzg-eip4844-fixtures/extra.json common/tests/fixtures/kzg-eip4844/extra.json
```

The reproduction script rejects a different or modified checkout and a
different trusted setup. The build compiles c-kzg-4844 and blst from the crate
sources. The [integration tests](../../protocol/test_kzg_eip4844.py) consume the
retained corpora; they never run this executable. These are finite
compatibility checks, not a proof of parser equivalence or security.
