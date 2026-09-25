# zkc-arkworks

Rust kernels for BLS12-381 field tables, groups and multilinear PCS, plus
BN254 arithmetic used by the Groth16 path, over arkworks **0.6.0**. This crate implements no participant runner, Sumcheck protocol,
compiler trait, Fiat–Shamir transform, or provider registry. The caller performs
ordinary Fr add/mul/equality and composes the kernels in its authored algorithm.

## API

```rust
use zkc_arkworks::{Bounds, Keys, Scalar, Table, VerifierKey};
# fn main() -> Result<(), zkc_arkworks::Error> {
let bounds = Bounds::new(8, 256, 1 << 20, 8 * 256);
let keys = Keys::setup_for_development(2, &bounds)?;
let table = Table::from_logical(&[2u64, 3, 5, 7].map(Scalar::from), &bounds)?;
let original = keys.prover_key().commit(&table)?;
let scratch = table.restrict_first(Scalar::from(11u64))?;
assert_eq!(scratch.arity(), 1);
let point = [11u64, 13].map(Scalar::from); // logical order, unchanged
let (value, proof) = original.open(&point)?;

// Obtain this pin from authenticated local configuration, separately from
// any untrusted incoming key file. This example has both roles in one process.
let pin = keys.verifier_key().metadata().key_id();
let verifier = VerifierKey::from_bytes(
    &keys.verifier_key().to_bytes(&bounds)?, pin, &bounds)?;
let commitment = verifier.decode_commitment(
    &original.commitment().to_bytes(&bounds)?, &bounds)?;
let proof = verifier.decode_proof(&proof.to_bytes(&bounds)?, &bounds)?;
assert!(verifier.check(&commitment, &point, value, &proof)?);
# Ok(())
# }
```

`Keys::setup_with_rng` accepts a caller-owned `RngCore + CryptoRng` for test
fixtures or an explicitly managed local generator. Keys serve exactly one arity
and can be shared across any number of tables/openings at that arity. The setup
arrays are moved into the prover key; the implementation avoids `trim`'s full
array clone. There is no automatic per-commit setup. `ProverKey` is public proving/SRS
material; its persistence API includes no private witness or opening state.

`Table` supplies `from_logical`, `from_logical_vec`, `from_logical_bytes`,
`logical_values`, `to_logical_bytes`, `arity`, `restrict_first`, `evaluate`,
`product_boolean_sum`, `round_product`, and `scalar_at_zero_arity`.
`round_product` returns `[constant, linear, quadratic]`; it is the product of
the two MLE factors, not the interpolation of their pointwise product.
`evaluate` uses the independent tensor definition in O(n 2^n) time with no
whole-table scratch. Opening includes this evaluation and the actual upstream
PCS proof. Restriction and round generation each take O(2^n) field operations.

Zero-variable tables have one scalar and can be evaluated, serialized, and
multiplied in a Boolean sum. Extract their value with `scalar_at_zero_arity`.
PCS setup/commit requires n >= 1; `round_product`/`restrict_first` also requires
at least one remaining coordinate. No artificial dummy PCS variable is added.

## Coordinates and custody

Logical input index coordinate 0 selects the high half. The one-time conversion
is `backend[j] = logical[bitReverse_n(j)]`. This permutation is its own inverse;
logical serialization applies it in reverse. Points are never reversed.
`from_logical` copies into one new scalar vector, then swaps in place.
`from_logical_vec` consumes and permutes the existing vector without an extra
whole-table allocation. Decoding logical bytes allocates one scalar vector.

`Table` clones share `Arc<DenseMultilinearExtension<Fr>>`; no mutable/raw public
access exists. `restrict_first` builds a new scratch vector and never changes
an older table, including through aliases. The object returned by `commit`,
`CommittedTable`, retains that exact table, key and commitment. Its `open`
method takes only a point: callers cannot substitute scratch or a different
same-arity table/key during a delayed opening. Ordinary table references are
not session capabilities; invocation/subject admission remains the runtime's job.

Key and proof clones share their immutable allocations. A `Commitment` clone
copies a group point and metadata and retains no private table. Table Debug
output omits scalar contents. Original tables are private data but are not
zeroized on drop. There is no mutable randomness state in commit/open/check.

## Ingress and wire format v1

`Bounds::new(max_arity, max_table_elements, max_artifact_bytes,
max_setup_cells)` is explicit and finite. The last limit is the setup work
measure `n * 2^n`. There is no default hidden maximum. Host shifts, integer
overflow and allocation representability are checked independently of policy.
PCS verifier transport uses the same table-arity profile as the prover; this
check does not allocate or require access to the private table.

Scalars use the upstream compressed canonical **32-byte little-endian** Fr
encoding. Integers >= the modulus, truncated/trailing bytes, and noncanonical
encodings are errors. `parse_decimal` accepts only unsigned canonical decimal
integers in `[0,p)`, including zero. Signs, whitespace and leading zeroes are
rejected; the parser uses upstream exact big-integer parsing, not modular input
reduction. Field `Display` output is suitable for this fixture parser.

Logical table bytes concatenate those scalars without a length prefix. The
enclosing caller supplies the declared arity and profile. Admission checks
power-of-two shape or `32 * 2^arity` exact byte length before vector allocation.

Public PCS objects have an **81-byte envelope**:

| Offset | Width | Meaning |
|---|---:|---|
| 0 | 8 | ASCII `ZKCAR006`, the fixed v1 marker |
| 8 | 1 | Kind: verifier key = 1, commitment = 2, opening proof = 3, prover key = 4 |
| 9 | 8 | Arity, unsigned little-endian u64 |
| 17 | 32 | Setup fingerprint |
| 49 | 32 | Key fingerprint |

The marker selects the crate's exact `PROFILE` (field, scheme/version,
nonhiding, high-half logical coordinates, bit reversal, unchanged point order,
identity base/challenge embedding, compressed exact codec). A future profile
needs a new marker/version. After the envelope:

| Object | Payload | Total size |
|---|---|---:|
| Verifier key | G1 generator, G2 generator, n G1 masks | 225 + 48n |
| Commitment | One G1 point | 129 |
| Proof | n G2 quotient commitments | 81 + 96n |
| Prover key | G1 generator, G2 generator, all G1 basis rows, all G2 basis rows | 81 + 144(2^(n+1) - 1) |

G1/G2 encodings are upstream compressed BLS12-381 (48/96 bytes), including its
big-endian base-field convention. No vector length or nested allocation count
is taken from an upstream serialized object. Header limits, expected identity,
and exact total byte length precede allocation from arity. Each point uses
validated upstream deserialization (curve/subgroup checks), exact consumption,
and byte-for-byte canonical reserialization. Infinity is permitted for zero
commitments/quotients; zero setup generators are refused. Incoming commitment
arity becomes the raw upstream `nv` only after matching the verifier key.

`VerifierKey::check` validates both metadata bindings, commitment.nv, exact
point length and proof length before upstream indexing/pairing. Upstream ignores
commitment.nv and accepts excess point coordinates; regression tests demonstrate
both behaviors and the wrapper's refusals. The verifier requires no private table.
`Err(Error)` denotes admission/host failure, `Ok(false)` a well-formed failed
opening, and only `Ok(true)` is acceptance. Error codes are available via `code()`.

## Identity and setup trust

Fingerprints use the actual SHA-256 implementation in `sha2 = 0.10.9`.
The preimage is `LE64(len(domain)) || domain || LE64(len(PROFILE)) || PROFILE ||
LE64(len(context)) || context || canonical_compressed(object)`.

- Setup domain: `zkc-arkworks/setup/v1`, empty context, object = all upstream
  `UniversalParams` in upstream field order (`num_vars`, G1 basis vectors, G2
  basis vectors, g, h, masks). This binds all public setup material, not a label.
- Key domain: `zkc-arkworks/key/v1`, context = the 32-byte setup ID, object =
  upstream `VerifierKey` (`nv`, g, h, masks). Thus the key pin also binds the
  claimed full-setup fingerprint and the selected layout/codec profile.
- Prover domain: `zkc-arkworks/prover/v1`, context = `setup_id || key_id`
  (64 bytes), object = upstream `CommitterKey` in field order (`nv`, G1 basis
  vectors, G2 basis vectors, g, h). This pins every prover basis, including rows
  unused by commit, and the complete profile/metadata association. It is distinct
  from the VK key ID and is not carried as self-authority in the wire envelope.

Canonical upstream usize/vector lengths in these hash preimages are encoded
as u64 little-endian. Setup hashing streams its full canonical material without
an extra serialized setup buffer. The fingerprint is not a MAC or provenance
certificate. A transported verifier recomputes the key fingerprint, but cannot
recompute the full setup hash from the verifier projection alone. Authentication
of the expected key pin and trust in its associated setup must come from outside
the incoming artifact. No malicious chosen-setup security or ceremony validation
is claimed. Exact-arity prover/SRS import is described below; setup trimming
and ceremony integration remain omitted.

This PCS is deterministic and **nonhiding**. Local setup sees trapdoor randomness;
the library does not guarantee erasure, malicious-setup soundness, zero knowledge,
knowledge extraction, constant-time execution, or an audited secure deployment.
`RandomSource::from_os` fallibly seeds upstream StdRng once from OS entropy, then
samples uniform Fr values with upstream rejection sampling. It is not cloneable.
The optional `test-utils` feature exposes `for_testing(seed)`; tests otherwise use
an explicitly seeded StdRng with `setup_with_rng`. Neither fixture mode is a
ceremony or a freshness claim. The caller determines challenge order, use of
independent resources, subject binding, and resource effects across suspension.

## Persistent public prover material

`ProverKey::material_fingerprint()` returns a cached 32-byte full-material pin.
`ProverKey::to_bytes(&bounds)` exports the canonical kind-4 object.
`ProverKey::from_bytes(&bytes, expected_material_fingerprint, &verifier, &bounds)`
requires both an independently expected prover pin and an actual admitted
`VerifierKey`. Use local setup/export or authenticated configuration for the pins.
Do not derive expected pins from incoming candidate files or their headers.

The importer checks, in order:

1. Actual byte limit, marker/kind, positive admitted arity, checked total size
   and exact length. It then matches the entire metadata against the VK,
   including exact arity, setup ID and key ID.
2. Host representability for the aggregate G1/G2 basis counts and both outer
   vectors before any point parsing or vector allocation.
3. Canonical subgroup-checked g/h and equality with the actual VK generators.
4. Exactly n G1 rows, then n G2 rows; row i contains `2^(n-i)` points for
   `0 <= i < n`. Each point is curve/subgroup checked and canonically re-encoded.
   There are no wire row/vector lengths, and no nested upstream deserialization.
5. Exact EOF, fixed upstream key shape, the independently expected full prover
   fingerprint, and the existing setup fingerprint reconstructed from the prover
   key plus the VK masks. The reconstruction streams a borrowed view in upstream
   `UniversalParams` field order, without cloning the bases.

The layout follows actual arkworks 0.6.0
[setup, trim, commit and open](https://docs.rs/crate/ark-poly-commit/0.6.0/source/src/multilinear_pc/mod.rs)
and [key structures](https://docs.rs/crate/ark-poly-commit/0.6.0/source/src/multilinear_pc/data_structures.rs).
Each group has `2^(n+1)-2` total basis points. Upstream commit uses G1 row 0;
open uses every G2 row, with duplicated quotient coefficients. Persistence keeps
all rows in upstream order, including the other G1 rows, rather than projecting
only currently used fields. Existing kinds/profile and setup/key IDs are unchanged.
There is no generic serializer, raw constructor, or opening-state transport API.

Import/export use the existing arity, table-element and byte limits. They run no
setup and do not consume the `max_setup_cells` work allowance. The importer
checks aggregate native point storage for representability, and each wrapper
vector uses `try_reserve_exact`. Native storage is larger than compressed wire
storage; bounds are not a global live-memory budget. The caller must bound file
or network reads before creating the input slice. The material pin is checked
after point decoding, so a wrong pin can still cost a full bounded load. Setup
computes the cached pin once by streaming its material; clones share it.

The reconstructed setup hash establishes a byte association, **not algebraic
SRS consistency**. Even an authenticated pin may identify malicious/inconsistent
bases or masks, adversarial trapdoors, or material whose trapdoor is known.
Such material can break correctness and/or the security premises of the PCS.
A valid subgroup point need not be the correct basis element. Infinity is allowed
in bases and masks (honest sampled parameters can have zero coefficients), while
setup generators must be nonzero and must match the VK. The application must
trust the generation/provenance and relevant algebraic consistency of the selected
material separately. This codec provides no universal setup-verification theorem,
ceremony validation, or chosen-SRS soundness guarantee. A regression fixture
recomputes every pin after replacing all G2 bases with infinity: import succeeds,
then a real opening fails check. The failure is intentional evidence of this limit.

For separate development processes, build and run the example:

```sh
cargo build --locked --release --example persistent_keys
# DIR must not exist. Setup generates OS-seeded development material once.
target/release/examples/persistent_keys setup /tmp/pcs-demo 8
target/release/examples/persistent_keys produce /tmp/pcs-demo
target/release/examples/persistent_keys validate /tmp/pcs-demo
```

The setup process writes public `prover.key` and trusted local `config/` containing
verifier material and both pins. The producer loads those, constructs its private
table locally and writes only public commitment/value/proof files in `candidate/`.
The validator reads only `config/verifier.key`, `config/verifier.pin` and
`candidate/`; it needs neither prover material nor the original table. The fixed
public query and producer-returned value merely demonstrate a PCS opening, not a
proof of an independently authenticated application statement. Local configuration
is trusted by this example; file adjacency is not authentication for a deployment.
Example file reads have explicit finite bounds. Multi-file output is not an atomic
publication protocol; missing/malformed files cause failure. Timings separate setup,
export, import (without file I/O), commit, open and check. Single runs are diagnostic
receipts, not performance or security claims.

## Allocation contract and tests

Bounds are per object/operation, not a total memory reservation. Wrapper vectors
use `try_reserve_exact`; failure preserves published originals. Arc allocation,
upstream PCS/MSM/setup internals, and some upstream scalar-parser internals remain
ordinary infallible Rust allocations. Upstream setup has O(n 2^n) temporary field
storage and O(2^n) basis storage in both groups. Open/commit allocate their own
scratch. Out-of-memory abort and unexpected upstream panic recovery are outside
this crate's Result contract. Runtime BufferStore reservation does not cover
these allocations; do not advertise an allocation-free publication adapter.

Tests cover exact scalar ingress, independent logical-half evaluation and
restriction, all 60 rounds from 20 Lean cases, omitted-permutation negative
controls, real openings, key identity, malformed headers and lengths, subgroup
and exceptional point codecs, every truncation and bounded byte mutations,
zero arity, unchanged originals after failure/folding, shared aliases, thread
transfer, and OS randomness.
Prover-key tests additionally compare independent upstream setup and manual wire/hash
reconstruction, post-reload commitments/openings, all point slots, re-pinned hostile
material, setup/VK mask associations and wrapper allocation requests on rejected
dimensions. The fixture records actual `CoordinateLayout.lean` output, freshly reproduced in
the delivery lane. Tests establish bounded implementation evidence, not a PCS
security theorem or complete compiler correspondence. `examples/kernels.rs`
reports conversion/setup/commit/open/check separately as cost diagnostics.

## Public G1 primitive adapter

`GroupPoint` wraps an opaque validated BLS12-381 G1 affine point from arkworks
0.6.0, the same curve/Fr library used by PCS. It provides `generator`, `identity`,
`add`, `scale`, `to_bytes`, and `from_bytes`. Its 48-byte canonical compressed
codec validates subgroup membership, requires exact consumption, and rejects
noncanonical exceptional encodings. Identity and zero scalar arithmetic are
allowed. Raw upstream coordinates cannot construct this wrapper.

`scalar_from_wide_be(&[u8; 64])` is the named transcript sampler adapter: an
existing arkworks big-endian integer reduction modulo Fr, including zero. It is
separate from strict ordinary `decode_scalar`, which admits only canonical
32-byte little-endian values below the modulus. Neither API implements a new
cryptographic primitive or claims exact sampling uniformity/side-channel hardening.
