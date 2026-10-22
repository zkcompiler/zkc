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
| `blst::bls12_381` | Checked G1/G2 scaling, variable-time MSM and pairing products through blstrs/blst |
| `arkworks::bn254` | BN254 scalars, G1/G2, pairings and polynomial transforms |
| `arkworks::scaling` | Bounded affine-base multiplication and batch normalization |
| `plonky3` | KoalaBear and binary fields, transforms, hashes and Merkle commitments |
| `dalek` | Ristretto255 scalar/group arithmetic and checked Edwards25519 points |
| `interop` | Exact pinned external constructions and their source provenance |

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

## Alternative BLS12-381 provider

`blst::bls12_381` owns private, validated subgroup points and scalars. Its exact
compressed G1/G2 encodings agree with the Arkworks provider. The `arkworks`
submodule bridges through canonical encodings, including subgroup checks; these
are conversions with measurable costs. The pinned blst build disables its worker
pool. Unsafe foreign calls remain inside the upstream libraries; zkc forbids
unsafe Rust.

Native installs `blst/curve.scale`, `blst/curve.scale_each`,
`blst/curve.vector_scale`, `blst/curve.msm` for BLS12-381 G1/G2, and
`blst/pairing.check` for BLS12-381 Fr. These alternatives use the existing
Arkworks physical ports and wire encodings. Explicit physical binding selection
opts in; normal frontend compilation retains the Arkworks defaults. Installation
alone grants no new algebraic law or Host permission.

Pippenger MSM is variable-time. Selecting it requires an application-appropriate
leakage premise; participant role alone does not establish that scalars are
public. No whole-runtime timing guarantee follows from the provider choice.
The adapter admits conversion and arithmetic work, staging, result payload and
conservative foreign MSM/pairing workspace before publication. The pinned MSM
bound includes small-input C stack tables; re-audit it on dependency upgrades.
Work weights are admission units, not cycle estimates. Bounds do not cover total
process memory; upstream infallible allocations can still abort on exhaustion.

Only pairing-product checking is installed. A target-group output would require
a complete safe bridge to the shared GT representation; blstrs' torus encoding
is a different format and does not cover identity through its compression API.
It is not used as a substitute for the existing GT codec.
