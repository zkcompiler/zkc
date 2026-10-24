# zkc-kernels

Typed mathematics without VM values, participant control or Host authority.
Kernels take typed operands and explicit limits or caller-owned destinations.
They check mathematical shapes and canonical encodings. The calling backend
owns installed bindings, VM adaptation, authority, resource admission and output
publication. The VM and kernels do not depend on each other.

## Modules

| Owner | Responsibility |
|---|---|
| `field` | Minimal coefficient arithmetic shared by mathematical algorithms |
| `vector`, `matrix`, `polynomial` | Provider-independent algorithms and checked views |
| `numerical`, `allocation` | Scoped work, managed payload reservations and fallible destinations |
| `arkworks::bls12_381` | BLS12-381 scalars, G1/G2, pairings and nonhiding multilinear PCS |
| `blst::bls12_381` | Canonical scalar algebra, typed resident bulk storage, G1/G2, variable-time MSM and pairing products |
| `arkworks::bn254` | BN254 scalars, G1/G2, pairings and polynomial transforms |
| `arkworks::scaling` | Bounded affine-base multiplication and batch normalization |
| `halo2curves::bn254` | Independent BN254 scalar/G1/G2 arithmetic, validated bulk storage, MSM and pairing-product checks |
| `plonky3` | Registered prime/extension and binary fields, transforms, selected hashes and Merkle commitments |
| `dalek` | Ristretto255 scalar/group arithmetic and checked Edwards25519 points |
| `interop` | Exact pinned external constructions and their source provenance |
| `cpu` | Shared application-owned workers for typed numerical phases |

Concrete types are imported from their provider and mathematical family. There
is no default scalar field or group at the crate root. Distinct construction
profiles retain their canonical bytes, layouts and domain separation.

The [BLS12-381 PCS guide](src/arkworks/bls12_381/README.md) defines its API,
coordinate convention, fixed wire format, setup trust and allocation limits.
The [interop guide](src/interop/README.md) records external source pins and
conformance boundaries. Other typed APIs are documented beside their modules.

## Storage and work

`numerical::Call` bounds managed work and payload, including staging/final
overlap. Limits do not bound total process memory or provider-private allocation.
Scratch remains unpublished; finished outputs retain their charge until the
call ends. Caller-owned destinations must have exact extents and stay private
until successful completion. Providers do not install operations or infer Host
permissions by implementing a mathematical trait.

## Choosing an existing implementation

`vector::Plan<S>` binds an exact length and chooses scalar or native packed
lanes over the same element representation. `select` uses the provider's
compile-time packing width and public length. A fixed unavailable packed choice
refuses; it never introduces a coordinate conversion. Slice convenience methods
use the same implementation. Plans report exact managed output and workspace
payloads; native work charges remain with the operation adapter.

`arkworks::scaling::Plan<P>` owns bounded curve scratch. Fixed direct and batched
choices are explicit; automatic preparation may fall back to direct scaling if
optional scratch allocation fails. The prepared choice stays fixed during
execution. Vector and curve plans preserve provider timing behavior and grant
no new timing or authority permission. Existing compiler physical plans and
installed backend bindings remain responsible for representation and contract
selection.

## CPU execution

`cpu::CpuExecution::new(workers)` creates a fallible, clonable worker owner.
Use `cpu.enter(|| kernel_call())` to supply it while keeping validation and
partial effects on the caller. Parallel-capable numerical leaves install their
work on those workers. `cpu.execute` is for an already isolated, `Send` numerical
phase. Explicit clones share one pool across concurrent callers. Lexical context
does not propagate across asynchronous suspension or application-created Rayon
tasks. Capture a clone and enter it inside each such task that calls zkc kernels.

The pinned Arkworks curve and PCS `parallel` features stay disabled because
their MSM implementation creates private pools. Field and FFT parallelism stays
enabled and uses the supplied pool. Cargo feature unification is additive:
applications adding other Arkworks dependencies must preserve that restriction.
Tests check the resolved workspace and normal SDK consumer graphs. The worker
ceiling covers this pool, not other contexts, caller threads or foreign code.
Standalone typed calls without a supplied context retain upstream execution
policy. Small element-wise phases avoid a worker hop.

## Alternative BLS12-381 provider

`blst::bls12_381` owns private, validated subgroup points and scalars. Its exact
compressed G1/G2 encodings agree with the Arkworks provider. The `arkworks`
submodule bridges through canonical encodings, including subgroup checks; these
are conversions with measurable costs. The pinned blst build disables its worker
pool. Unsafe foreign calls remain inside the upstream libraries; zkc forbids
unsafe Rust.

The [resident kernel guide](src/blst/bls12_381/README.md) documents scalar
`Coefficient` support, owned upstream bulk buffers, destination arithmetic,
explicit conversions and the remaining hidden foreign allocations. Bulk MSM
borrows resident buffers; the scalar-slice MSM adapter constructs those buffers
once per call and delegates to the same implementation.

The calling backend installs exact physical bindings and owns provider
selection, value adaptation and publication. Kernel scalar and bulk support
does not install a VM type or grant wire or Host permissions. Mixed provider
paths use explicit canonical conversions with their associated costs.

Pippenger MSM is variable-time. Selecting it requires an application-appropriate
leakage premise; participant role alone does not establish that scalars are
public. No whole-runtime timing guarantee follows from the provider choice.
The caller admits arithmetic work, any explicit conversion staging, result payload and
conservative foreign MSM/pairing workspace before publication. The pinned MSM
bound includes small-input C stack tables; re-audit it on dependency upgrades.
Work weights are admission units, not cycle estimates. Bounds do not cover total
process memory; upstream infallible allocations can still abort on exhaustion.

This module exposes pairing-product checking. A target-group output would require
a complete safe bridge to the shared GT representation; blstrs' torus encoding
is a different format and does not cover identity through its compression API.
It is not used as a substitute for the existing GT codec.

## Registered Plonky3 residue fields

`plonky3::residue::{PrimeWord, Residue}` supplies exact canonical coordinate
words and the prime-base DFT cache for KoalaBear (base/quartic/octic), BabyBear
(base/quartic `X^4 - 11`), and Goldilocks (base/quadratic `X^2 - 7`). The pinned
Plonky3 family is 0.8.0; independent OpenVM adapter dependencies retain 0.4.3.

`plonky3::polynomial::{Domain, Kernels}` shares the same numerical algorithms
across these fields. A domain always uses the base field's two-adic generator,
with maximum log size 24 for KoalaBear, 27 for BabyBear and 32 for Goldilocks.
An extension-valued shift can have nonzero higher coordinates. Structural
admission at the maximum size performs no allocation. Execution also requires
caller-owned resource limits. Typed CPU leaf installation remains in place.

Canonical coordinates are ascending basis coefficients, with exactly four
little-endian bytes for KoalaBear/BabyBear or eight for Goldilocks. Decoding
rejects each coordinate at or above the exact modulus. Decimal naturals embed
in coordinate zero, preserving every u64 bit; they are not packed extension
representations. Montgomery words are available only for explicitly supported
31-bit bases. Field support alone installs no hash or commitment profile.
