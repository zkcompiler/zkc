# Toolchain and CI maintenance

Native manifests own selected dependency versions; Nix locks the tools and package
inputs used to build them. Prefer current stable releases when upgrading unless
an actual compatibility constraint requires otherwise. Keep unrelated upgrades
separate and record selected versions in the owning manifest.

## Format versions

Persisted or exchanged formats and cryptographic byte constructions carry
versions at their contract boundaries. These include program and Entry carriers,
Host requests and results, relation formats, proof bindings and transcript
framing. Opaque compiler fingerprints, generated symbol seeds and in-process
structures do not need independent format versions.

Before stabilization, use version `0` for all zkc-owned formats and constructions,
including binary headers, suite identifiers and independent research tools. Use
`0.0.0` where package manifests require SemVer. Keep these versions fixed during
internal development. Update producers, readers, examples and fixtures together,
including independently derived byte and hash vectors when their inputs change.
Maintain one current schema with strict admission; do not add
older readers, compatibility layers or migration histories. Equal version numbers
do not guarantee that artifacts from different development builds are compatible.

Use version `1` for the first stabilized external contract. After that, review
version changes when its encoding, interpretation or cryptographic construction
changes. Ordinary implementation refactoring does not require a format version
change. Upstream standards, algorithm names and dependency releases retain their
own version rules.

## Pins and source ownership

| Boundary | Owner |
|---|---|
| Main LLVM/MLIR and C++ packages | Compiler CMake requirements and Nix inputs |
| Rust workspace | Cargo manifests, lockfile, toolchain selection and `nix/rust.nix` vendor hash |
| Python tooling | `pyproject.toml` and `uv.lock` |
| Independent Lean package | `lean/lean-toolchain`, Lake manifests and lockfiles |
| Optional integrations | Their own manifests, source pins and compatible toolchains |

`rust-toolchain.toml` selects the exact Rust release for rustup, Nix and CI.
`nix/default.nix` selects the Python and LLVM package families; `flake.lock`
resolves their releases. Python packages resolve through `uv.lock`. Update the
CMake tested LLVM version with the Nix selection; other compatible LLVM patches
remain supported and are reported by doctor. No parallel version inventory is
maintained in CI or just.

LLZK remains a generic optional relation adapter with a separate LLVM process.
Do not link incompatible LLVM versions into the main compiler. OpenVM retains
its upstream Plonky3 family and RNG types in its separate adapter workspace;
these are compatibility constraints, not accidental duplicate pins.

## Lean dependency sets

The main package owns the Lean and Mathlib selection. ArkLib and Clean remain
separate Lake packages so their dependencies do not enter ordinary native or
main Lean builds. All maintained packages use one Lean toolchain and identical
revisions for every shared dependency, including dependencies shared only by
integrations such as CompPoly. Separate packages do not make incompatible
Lean libraries composable.

Select an exact stable Mathlib commit and compatible integration commits:

```sh
python3 scripts/update-lean-pins.py --mathlib MATHLIB_COMMIT --arklib ARKLIB_COMMIT --clean CLEAN_COMMIT
```

Omitted integration arguments retain their current revisions. Mathlib selects
the Lean release. The helper updates the three toolchain files, the direct
requirements and Lake manifests, verifies the resolved dependency set, and
refreshes Nix source hashes. It does not build proofs or download Mathlib's
compiled cache. A failed resolution leaves its changes for inspection.

The integration lakefiles explicitly select the main Mathlib revision after
other requirements. Clean also selects the CompPoly revision shared with
ArkLib. When upstream requirements change, reconcile these ordinary Lake
requirements before accepting the upgrade. The helper refuses conflicting
resolved revisions; it does not silently choose a winner. Lake lockfiles and
Nix hashes are committed, while `.lake` output is not.

Run the main build, both integration builds, independent consumers and
reached-axiom audits after changing this set. A successful resolution alone is
not compatibility evidence. If a current stable release cannot build a
maintained integration without changing its meaning, retain the newest
compatible set and record the concrete constraint here. Do not suppress proof
checks or add a second dependency manager to force an upgrade.

The maintained set currently retains Lean/Mathlib 4.33.1 and the ArkLib,
VCVio and Clean revisions recorded in the Lake manifests. The 4.34.1 upgrade
built the main package, but ArkLib 4.34.0 selects a VCVio revision that deprecates the discrete
probability API (`probOutput`, `probEvent` and `Pr[...]`) still used by the
maintained bridges. Retaining the earlier VCVio/PolyFun revisions with Lean 4.34.1
also fails upstream reducibility and proof checks. Upgrade this set together
with an explicit probability-interface migration; do not mix toolchains or
relax the owned warning/axiom checks to accept it.

## Upgrade and validate

Update the owning pin and its resolved lock/hash together. Crane derives Rust vendoring from `Cargo.lock` and caches compiled dependencies using the selected manifests, profile, features and toolchain. There is no separate `cargoHash` to recalculate. Verify this boundary with `nix build .#tools .#test-drivers .#checks.x86_64-linux.rust --no-link`; a direct Cargo build does not check Nix's dependency artifacts. Update the Crane release through its flake input when needed, independently of language dependency upgrades.

Inspect API, schema,
codec and behavior changes at actual consumers. Reconfigure fresh build trees
when compiler ABI or toolchain identity changes. Run affected native tests,
installed static/shared consumers and package checks according to the change.
Use [configuration](configuration.md) to select explicit existing outputs.

Caches accelerate builds; they do not establish that a source reproduction ran.
Distinguish an incremental test, a clean native build and a sandboxed Nix package
in the result. Keep previous failure reports, exact commands and selected outputs
when diagnosing a disagreement.

## Workflow scopes and reports

The [test guide](../../common/tests/README.md) and CI manifests own current scopes.
Automatic CI checks source hygiene, docs and the Python harness. Changes to
native code, libraries or build configuration also run cached Nix checks for
Rust tests/Clippy, the installed CLI, SDK discovery fixtures, an installed C++ SDK consumer, representative source-to-execution semantics, source boundaries and C++ formatting. Rust and compiler/package work run in independent jobs; the existing `Native build and execution` gate requires both selected jobs to succeed and accepts skipped jobs only when change selection explicitly excludes native work.

Native pushes to `main` additionally run all Nix checks, including full CTest, protocol/kernel integration and input-invalidation controls. The weekly schedule repeats the full native suite plus sanitizer and static/shared domain-installation checks. Manual `main`, `optional`, `fresh` and `cache` scopes remain available; optional formal/external checks stay explicit. A narrow PR check is not evidence that the full suite passed.

CI saves a Nix store snapshot per job. Rust uses the check's derivation identity so unrelated C++ commits do not upload duplicate snapshots; other jobs use the commit. Jobs restore the latest snapshot for the same job and flake lock when the exact key is absent. Successful build graphs retain temporary GC roots, including compiled build-time dependencies; garbage collection removes obsolete results before saving. This avoids one GitHub cache entry and upload request per store path. Weekly sanitizer/domain jobs restore the native snapshot without saving their large variant stores. Formal and external optional packages have separate scopes. GitHub's normal cache quota and eviction policy still apply. Cache misses rebuild normally. The explicit `cache` scope checks that project outputs were absent before restoration and then requires all main outputs with local and remote builders disabled.

The Rust check runs Clippy and workspace tests directly, without building the release CLI or depending on C++ tools and release test drivers. Source style checks own Cargo formatting. The application and project checks own those execution boundaries. Keep these derivations independent so Rust checks can run alongside the compiler build and reuse their result after unrelated C++ changes.

The installed compiler package builds the CLI and SDK with `BUILD_TESTING=OFF`. `checks.compiler` builds and runs the full CTest suite and exports its test helpers for the project integration check. Sanitizers use that testing configuration; domain installation checks use the installed compiler configuration.

When investigating CI time, compare job and step timings first, then the Nix build log's derivation phases. Separate dependency downloads, project compilation and test execution; a binary cache hit for dependencies does not reuse compilation of changed project sources. Retain the automatic checks when optimizing their dependency graph. The build wrapper retains selected targets, the exact flake lock, output paths, elapsed time and successful check reports in CI artifacts; build logs retain failures. Compare changes on the same runner and distinguish cold dependencies, reused dependency artifacts and complete output-cache hits.

A direct test driver requires built tools. Report directories are allocated
independently of shared build trees; concurrent reports do not isolate concurrent
CMake, Cargo or Lake mutations. Serialize writes to one build/profile. Use
bounded relevant checks before broad integration, and retain resource-boundary
cases in the scope that owns them.

## Public documentation

A published guide should describe current commands and support. Move durable
semantic decisions into their owning specification or design page; remove
superseded implementation guides instead of preserving a compatibility archive.
Private review/process records stay outside the public reference. Follow the
[documentation guide](documentation.md) and run its link/whitespace checks.
