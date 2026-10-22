# Dependency baseline

The owning `lean-toolchain`, `lakefile.toml` and `lake-manifest.json` files are
normative for exact sources. The core depends on Mathlib. Reusable security owns VCVio, PolyFun and CompPoly
without ArkLib in its closure; optional packages own
their external requirements and override shared transitive pins consistently.

| Component | Selected version or exact revision |
|---|---|
| Lean | 4.34.1 |
| Mathlib | `d13f23b723b8a846827a245b89c10fc7d3f11612` (4.34.1) |
| ArkLib | `a93ee1ebbbf7b6b939ba3dd1c6115d33c92a4253` |
| VCVio | `afa6593f15e1e79ecb3cf22fc56191cecb452bb0` |
| Clean | `b449bf590f93e13827c3c7e747e392d6969aa380` |
| CompPoly | `df591bb8c6745126d1d72f5243faae3022b0432a` |
| PolyFun | `3710d71b28404a151b8d1f0ce080ea448778dec0` |

The maintained, tested dependency closure is 4.34.1. Lean and Mathlib 4.35.0
are both released; retaining this baseline does not mean that a newer Mathlib
release is unavailable. An upgrade must validate the joint closure and actual
consumers described below. ArkLib's selected revision already uses VCVio's
native measure API and pins the selected VCVio revision. That joint upstream
closure targets Lean 4.34.0 and is checked here with Lean/Mathlib 4.34.1.
VCVio main at `aa7efec268907a03566087ec2ebd6f4cdbf99949` requires Lean 4.35.0;
selecting it belongs to a joint toolchain upgrade. These are revisable
compatibility decisions, not a requirement to remain on older Lean indefinitely.

The selected ArkLib contains the end-to-end FRI soundness results previously
carried by the local compatibility patch (upstream pull request #992). The
ArkLib integration therefore uses unmodified upstream sources and no longer
ships that patch. Its actual FRI consumers and axiom closure remain required
upgrade checks.

Security uses `EvalDistEq` (`=ᵈ`) for equality of laws and `Pr{...}[...]` for
native event probabilities. These compare every output event, independently of
an arbitrarily chosen measurable structure. Distribution transport uses the
upstream bind/map/coupling laws. Existing compatibility declaration names that
contain `evalSPMF` do not retain the removed SPMF implementation. A scoped
`ZkcSecurity.VCVio.UniformChallenge` instance selects the uniform law only when
explicitly opened; sum oracles inherit their component laws. Merely importing
the module does not choose a challenge distribution.

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
