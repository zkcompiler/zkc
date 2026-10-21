# Dependency baseline

The owning `lean-toolchain`, `lakefile.toml` and `lake-manifest.json` files are
normative for exact sources. The core depends on Mathlib. Reusable security owns VCVio, PolyFun and CompPoly
without ArkLib in its closure; optional packages own
their external requirements and override shared transitive pins consistently.

| Component | Selected version or exact revision |
|---|---|
| Lean | 4.34.1 |
| Mathlib | `d13f23b723b8a846827a245b89c10fc7d3f11612` (4.34.1) |
| ArkLib | `db7005f84a9dbad7ff2abbbb4e8feeeac6f4dfd8` |
| VCVio | `d606eab018ab87bf4a0a6ac7b6d2da4fedfa53b0` |
| Clean | `b449bf590f93e13827c3c7e747e392d6969aa380` |
| CompPoly | `df591bb8c6745126d1d72f5243faae3022b0432a` |
| PolyFun | `3710d71b28404a151b8d1f0ce080ea448778dec0` |

At selection, Lean 4.35.0 was stable but Mathlib's latest stable was 4.34.1.
The tested coherent stable baseline is therefore 4.34.1. VCVio main at
`afa6593f15e1e79ecb3cf22fc56191cecb452bb0` removes `SampleableType.NativeMeasure`
and `QueryTracking.LoggingOracle`, which the selected ArkLib still imports.
Use ArkLib's tested VCVio pin until an upstream migration or maintained adapter
makes a newer joint closure work. These are revisable compatibility decisions,
not a requirement to remain on older Lean indefinitely.

ArkLib's selected revision carries a declared patch at
[the integration boundary](../integrations/arklib/compatibility.json): the Lean
sources of ArkLib pull request #992, "prove end-to-end soundness of the
computable IOP" (head `768b1dba0e4e028156d052488ba8e3f6d01b1a0a`, based on
`0b5b67c63d74b26e38715bb90fa5d7d5a07def25`). The pull request's changes from its
base to its head apply to `db7005f84` by a three-way apply without conflicts and
build there without modification; its kernel checks
(`ArkLibTest/ProofSystem/Fri/Soundness.lean`) pass at this revision. The patch
covers `ArkLib.lean`, `ArkLib/` and `ArkLibTest/` (29 files, 20 of them new); the
pull request's blueprint, knowledge-base, wiki and axiom-baseline files are
omitted because no Lean module reads them. The FRI security modules use its
per-round lemmas. This patch is temporary: when the pull request merges, the
ArkLib pin moves to a revision that contains it and the patch is removed.

Clean's selected adapter and native example cone uses a declared compatibility
patch at [the integration boundary](../integrations/clean/compatibility.json).
Upstream still imports the renamed `Mathlib.Logic.Basic`, and a `ring_nf` call
in `Clean.Air.Balance` now fails under the changed normalization order. The patch updates the
import and proves the required reassociation directly with ring arithmetic; theorem
statements and executable definitions are unchanged.

Preparation checks a patch's exact upstream revision and the before/after hashes
of every file it changes; a file absent on one side has a null hash, so a patch
may add files. Cache preparation, fresh source reproduction and the Nix ArkLib
package apply the same patches. These are patched-source claims, not unmodified
upstream or whole-library build claims.

Upgrades must build actual protocol consumers, check their axiom closures,
regenerate the native Clean fixture, and run source/target negative controls.
An import-only smoke test is not a security compatibility test.
