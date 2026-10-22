# Resident BLS12-381 kernels

`Scalar`, `G1` and `G2` keep validated upstream coordinates private. Scalar
arithmetic implements `Coefficient`, so the existing vector, matrix and
polynomial kernels work directly on scalar wrapper slices. Inverse returns
`None` exactly at zero. Unsigned decimal parsing and exact 32-byte little-endian
decoding reject noncanonical integers; they never reduce malformed inputs.
Point decoding checks canonical compressed bytes, curve membership and prime
subgroup membership, including the unique identity encoding.

`ScalarVector`, `G1Vector` and `G2Vector` own typed upstream buffers. They avoid
constructing temporary wrapper vectors when borrowed by `G1Vector::msm` or
`G2Vector::msm`. `try_from_fn` constructs directly into final storage;
`from_slice` copies once at an explicit storage boundary. Iterators and `get`
copy individual validated elements. `set` accepts validated wrappers and uses
ordinary Rust bounds checking. There are no slice casts or type erasure.
Carriers do not clone buffers implicitly; a backend
can put a finished carrier in its existing shared owner for cheap inert clones.

Trusted backend families can use the public upstream `ScalarElement`,
`G1Element` and `G2Element` aliases. `Scalar/G1/G2::into_element` and
`from_element` transfer an element in O(1). Bulk `from_elements`, `as_elements`
and `into_elements` adopt, borrow or move the original Vec without copying,
allocation or validation. `ScalarElement` implements the same `Coefficient`
interface. These adapters require valid mathematical field/prime-subgroup values;
they are not validation tokens. Upstream exposes raw coordinate manipulation in
safe Rust, and fabricated or mutated raw coordinates violate these mathematical
premises. External data must use checked canonical decoders. This trusted typed
interface lets existing family adapters publish upstream output buffers directly
and borrow them on later calls, without an unsafe wrapper-slice reinterpretation.

Scalar bulk destination operations reuse the existing `vector::Plan` and batch
inversion algorithms on their private upstream storage. They report
`field::Error`; construction, group operations and codecs report the provider's
`Error`. Destinations have exact extents, checked before writes. Batch inversion
also checks every input for zero before writing. Empty MSM is identity; empty
dot/sum is zero; empty product is one. Pairing-product checks share one
implementation across slice and bulk APIs, remove unit factors, and return true
for empty or all-unit products.

The scalar-slice `G1/G2::msm` functions are storage adapters to the same bulk
implementation. They copy the two input slices into upstream buffers on each
call. Use the owned carriers for repeated resident MSM. Scalar slices remain
useful for the generic `Coefficient` algorithms. The `arkworks` module's scalar
and point import/export functions perform explicit canonical conversions;
resident kernels never invoke those bridges implicitly. G1/G2 residency grants
no target-group or PCS-object representation compatibility.

`from_bytes` on a bulk carrier reads concatenated fixed-width canonical elements
directly into final upstream storage. `write_bytes` requires an exact caller
destination and allocates nothing. These functions add no container framing,
wire authorization, sampling/reduction semantics or codec identity.

## Allocation and admission

The calling backend owns admission, numerical reservations and publication.
Constructors check element payload overflow and use `allocation::reserve` for
fallible managed allocation. A failed callback discards its private buffer.
Empty carriers allocate nothing. `storage_bytes` reports reserved element
capacity times the upstream element size, excluding the Vec header, any shared
owner, allocator overhead and process memory. Keep those costs in the backend's
existing retained-storage accounting. Destination arithmetic allocates no
managed workspace and never returns a borrow of call scratch.

Use existing numerical output and workspace reservations before allocation.
When freezing a wrapper-vector output into a resident carrier, keep both staging
and final payload reserved until conversion succeeds. Alternatively construct
directly into a reserved final result. Output storage must remain unpublished
until the complete operation succeeds. The kernel does not update a backend's
ledger automatically, or infer permission from available memory.

`msm_workspace_bytes` retains its conservative bound for both slice and resident
MSM. It includes wrapper copies for the slice adapter, affine normalization,
scalar serialization, Pippenger buckets and pinned small-input C stack tables.
Residency omits wrapper reconstruction but **does not eliminate upstream
allocations**: blstrs 0.7.1 still constructs affine point and scalar-byte vectors,
and blst 0.3.17 allocates algorithm workspace. Pairing uses an infallibly
allocated context, covered for admission by `PAIRING_WORKSPACE_BYTES`, and
normalizes points as they are aggregated. The all-unit product avoids that
context. Hidden provider allocations can abort the process on exhaustion;
fallible wrapper allocation does not make those failures recoverable. These
payload bounds do not bound allocator overhead or RSS. Re-audit them when pins
change. The pinned blst build disables its internal worker pool.

## Timing premises

MSM uses variable-time Pippenger. The caller needs explicit trusted timing
authorization appropriate to the application's leakage assumptions. Residency,
participant role, determinism and provider identity grant no such permission.

`Scalar::pow(u64)` uses variable-time powering and requires a public exponent.
Pinned blstrs inversion calls blst's Euclidean inverse. Zero validation, decimal
parsing, canonical decoding, equality, reductions and pairing unit filtering
make no whole-operation constant-time guarantee. Scalar arithmetic and vector
plans preserve provider timing behavior; this module establishes no whole-call
or whole-runtime side-channel property. No benchmark or performance claim
follows from eliminating a storage reconstruction.
