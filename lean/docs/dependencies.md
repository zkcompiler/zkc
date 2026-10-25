# Dependency baseline

The owning `lean-toolchain`, `lakefile.toml` and `lake-manifest.json` files are
normative for exact sources. The core depends on Mathlib. Reusable security owns VCVio, PolyFun and CompPoly
without ArkLib in its closure; optional packages own
their external requirements and override shared transitive pins consistently.

| Component | Selected version or exact revision |
|---|---|
| Lean | 4.35.0 |
| Mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679` (4.35.0) |
| ArkLib | `1e0241333c18d8b22cb68f9522da5f9fb88f9a06` |
| VCVio | `96754a37e739270ac5bb8fe7deaeafef6964b688` |
| Clean | `1a6c28426372bb99af79e533aa7b9a0788eff0d7` |
| CompPoly | `1cb8f5cd0e22a8c9ec165000915c21d0f8e12525` |
| PolyFun | `a5edfe2dd24d9d76f9a13cc1f131b220617ad534` |

The selected closure uses Lean and Mathlib 4.35.0. The four protocol libraries
are upstream main snapshots selected on 2026-10-26; their shared dependencies
are overridden to one exact revision in every owned package. Mathlib uses the
4.35.0 release rather than master, which has advanced to Lean 4.36. Clean still
targets an older toolchain and uses the declared patch below. The owning locks
also record the cslib dependency introduced by PolyFun and VCVio.

Admission decisions expose their Boolean computation to the kernel, including
equality of `Except` results. Recursive instruction equality uses
`decidable_of_iff`; primality certificates use Lean's `Nat.powMod` and its
correctness theorem without an artificial exponent-fuel bound. Constructed
view normalization opts into `Construction.reduceTransport`, which asks Lean
to reduce equality recursors at default transparency. It does not identify
nominal domains or discard unresolved transports.

The selected ArkLib contains the end-to-end FRI soundness results previously
carried by the local compatibility patch (upstream pull request #992). The
ArkLib integration therefore uses unmodified upstream sources and no longer
ships that patch. Its actual FRI consumers and axiom closure remain required
upgrade checks.

Security uses `EvalDistEq` (`=ᵈ`) for equality of laws and `Pr{...}[...]` for
native event probabilities. These compare every output event, independently of
an arbitrarily chosen measurable structure. Distribution transport uses the
upstream bind/map/coupling laws directly, without SPMF compatibility aliases. A scoped
`ZkcSecurity.VCVio.UniformChallenge` instance selects the uniform law only when
explicitly opened; sum oracles inherit their component laws. Merely importing
the module does not choose a challenge distribution.

The Schnorr family imports `VCVio.Schemes.Schnorr.SigmaProtocol`. Uniform-product
sampling, persistent bad states and event bounds from couplings use upstream
VCVio results directly. Polynomial agreement uses CompPoly's root-counting
theorem. These substitutions preserve the existing game, resource and domain
assumptions. Upstream weakest-precondition and state-restoration results need
separate adapters for those boundaries; upgrading a dependency does not
establish such an adapter or extend a security claim.

Clean's selected adapter and native example cone uses a declared compatibility
patch at [the integration boundary](../integrations/clean/compatibility.json).
Upstream still imports the renamed `Mathlib.Logic.Basic`, and a `ring_nf` call
in `Clean.Air.Balance` now fails under the changed normalization order. The patch updates the
import and proves the required reassociation directly with ring arithmetic; theorem
statements and executable definitions are unchanged.

Preparation checks a patch's exact upstream revision and the before/after hashes
of every file it changes; a file absent on one side has a null hash, so a patch
may add files. Cache preparation, fresh source reproduction and the Nix packages apply the
same declared patches where present. Clean is a patched-source claim; ArkLib
is unmodified upstream. Neither describes a whole-library build unless its
complete default target set was checked.

Upgrades must build actual protocol consumers, check their axiom closures,
regenerate the native Clean fixture, and run source/target negative controls.
An import-only smoke test is not a security compatibility test.
