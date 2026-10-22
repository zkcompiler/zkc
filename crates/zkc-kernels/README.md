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
