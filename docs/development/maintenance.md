# Toolchain, cache and CI maintenance

Use the [development guide](README.md) for daily commands and
[configuration](configuration.md) for environment variables. This page owns
the pinned inputs, upgrade procedure and the workflow's execution requirements.

## Pins and source ownership

Use current stable toolchains and dependencies unless a concrete compatibility
constraint requires an older release. A recorded version or lockfile is a
reproduction input, not a reason to reject an upgrade. Update the owning inputs
and run the affected checks together; document any exception with its actual
failure or upstream requirement. Rust follows the stable channel. Lean and its
dependencies must be upgraded together because compiled Lean objects are
toolchain-specific. Nix locks retain reproducible snapshots and should advance
with the selected toolchains.

Version checks enforce demonstrated compatibility requirements: the main
compiler uses LLVM/MLIR 23; the separate LLZK adapter uses LLVM/MLIR 20 and
upstream's minimum 20.1.8. Compatible patch releases are accepted. Lean's
compiler, dependency objects and optional integration must use the same release.
Fixture reproductions still check their named external sources and tool versions
because those versions identify the evidence being reproduced.

The remaining Lean 4.33.1 selection is a compatibility exception, not the
default upgrade policy. A Lean/mathlib 4.34.1 trial builds the main formal
package after updating deprecated theorem names, quoting the `requires`
identifier and replacing two failing `cbv` proofs with `rfl`. The coordinated
ArkLib/VCVio trial still rejects the adapters' deprecated scalar probability
API (`probOutput` and `probEvent`). Move those proofs to the upstream measure
API and rerun the integration's dependency/axiom audits before adopting the
new formal dependency graph. Disabling the existing strict checks is not an
upgrade fix.

| Input | Authority |
|---|---|
| System packages, LLVM/MLIR, Clang and build tools | [flake.lock](../../flake.lock), selected in [nix/default.nix](../../nix/default.nix) |
| Rust and standard components | [rust-toolchain.toml](../../rust-toolchain.toml) |
| Rust dependencies | [Cargo.lock](../../Cargo.lock); separate benchmark locks remain owned by those workspaces |
| Lean/Lake release | [lean-toolchain](../../formal/lean-toolchain) and its archive hash in [lean-toolchain.nix](../../nix/lean-toolchain.nix) |
| Lean dependencies | Main and optional integration `lake-manifest.json` files; Nix transport hashes in [lake-sources.json](../../nix/lake-sources.json) |
| Python tools | [pyproject.toml](../../pyproject.toml) and [uv.lock](../../uv.lock) |
| Optional adapters and fixture generators | Their source manifests and Cargo/npm locks; the [package map](README.md#packages-and-checks) lists the entry points |

Read selected versions from these files and `just doctor`. A distribution's LLVM
patch release may differ from the upstream release packaged by Nix; CMake checks
the supported major and warns about an untested patch baseline. Historical
measurements retain the tool versions under which they were obtained.

Lake and fixture provenance checks need Git commit objects. Downloads of the
same commit can have different pack encodings. The Nix fetcher normalizes the
selected commit and tree with a sorted, single-threaded pack, and the hash
updater uses that same format. Changing transport encoding requires refreshed
hashes; it does not select a new source revision.

Lean's executable driver uses Nix's compiler wrapper through `LEAN_CC` and the
release's bundled libraries. This supplies a usable runtime loader while
retaining the selected Lean release. The development shell selects Clang for
the project; Lean's bundled compiler is not the C++ toolchain selector.

## Upgrade and rollback

Update one owning layer at a time:

1. Change a named flake input, for example `nix flake update nixpkgs`. Review
   both the lock diff and the resulting tool versions.
2. For Rust or Lean upgrades, edit the owning toolchain file. A changed Lean
   release also needs its verified archive hash in the Nix package. For a
   coordinated Lean/Mathlib/ArkLib candidate, run
   `python3 scripts/update-lean-pins.py --arklib COMMIT` with a full ArkLib commit.
   It selects that commit's Lean release and Mathlib revision, records the
   archive hash, resolves both Lake manifests in the new shell and refreshes
   the Nix transport hashes. It checks shared revisions and the selected
   ArkLib commit; it does not prove that the upgraded adapters build. Review
   the diff and run the affected formal and integration checks. A failure
   leaves the edited files available for inspection or rollback.
3. Update language dependencies through their native manifests and locks.
   Refresh the selected Lean Git-source transport hashes with
   `nix develop .#maintenance --command python3 scripts/update-nix-sources.py`.
   This script reads already selected revisions; it does not choose upgrades.
4. When a Cargo/npm lock closure changes, recompute and review its fixed-output
   hash in the owning Nix recipe. A hash mismatch must not be bypassed by an
   impure fetch.
5. Record `just doctor`, run the affected local checks and Nix checks, and
   validate the affected optional packages. Changes to source fetching or
   packaging also require the relevant source rebuild on an adequate machine.
   Report version drift separately from changed program behavior.

Rollback the manifests, associated content hashes and `flake.lock` together.
Re-enter the shell and recreate CMake build directories when changing compiler
or ABI. A retained Nix output is reusable only for its matching derivation.

## Workflow scopes and runner requirements

The [workflow](../../.github/workflows/ci.yml) runs quick source and harness
checks on pushes to main and pull requests. They check the public file set,
Python dependencies/lint, Rust and Nix formatting, workflow syntax, documentation
and the test harness. The `quick` Nix shell supplies these tools without building
the project compiler, runtime or Lean packages. Run the same checks locally with
`nix develop .#quick --command bash .github/scripts/check-quick.sh`.

Full compilation, semantic tests, formal audits and cross-language/resource
controls remain separate manual scopes. Quick success does not imply they
passed. Record affected local or manual full checks in each PR. Scheduled full
builds are disabled until suitable runners are configured; hosted duration has
not been measured.

The full main job requires at least **24 GiB RAM** for a retained checker
workload; an undersized runner fails before building. The standard
public-repository `ubuntu-24.04` runner has
[16 GB RAM](https://docs.github.com/en/actions/reference/runners/github-hosted-runners#standard-github-hosted-runners-for-public-repositories).
Before dispatching `main`, `all` or `cache`, configure `ZKC_MAIN_RUNNER` at
repository or organization level to select an accessible runner with sufficient
capacity. A passing local run does not establish that the hosted runner is
configured.

| Dispatch scope | Work |
|---|---|
| `quick` (default) | Source, formatting, documentation and harness checks; no project builds |
| `main` | Main packages/checks and retained test/library outputs |
| `optional` | Optional integrations and sanitizer checks |
| `fresh` | Main and ArkLib source reconstruction without a restored project cache |
| `cache` | Restore main outputs in a fresh project store with builders disabled; a cache miss fails |
| `all` | Quick checks and all build scopes except the separate cache-acceptance mode |

Quick jobs allow twenty minutes, ordinary full jobs three hours, and the
cache-acceptance mode six hours. These are upper job limits, not expected
durations or completed-run evidence. Run the main
scope for matching inputs before testing restoration. Full cache restoration
has not been accepted as a publication guarantee.

`ZKC_MAIN_RUNNER` selects the full main runner. Optional jobs first use
`ZKC_OPTIONAL_RUNNER`, and fresh jobs first use `ZKC_FRESH_RUNNER`, then the
optional/main fallbacks. The workflow's final fallback is `ubuntu-24.04`;
it does not provision sufficient memory by selecting that label. Use an
ephemeral runner or fresh store for the fresh scope: it rejects already-realized
formal outputs. Allow substantial disk space for source builds, writable
copies and toolchains; 64 GiB free is a starting budget, not a measured bound.

The local [Nix action](../../.github/actions/nix/action.yml) selects an installer
release, reports the active version and checks sandbox and concurrency
settings. Existing installations need not match the installer version; they
must support the commands used here and provide the required isolation.
Runners also need curl, xz and SHA-256 tools. Every job rebuilds an isolation
probe; a configuration flag alone is
not evidence that sandboxing worked. Container runners need working PID/mount
namespaces and `/proc` remounting. Runner configuration belongs to the host,
not to shell entry or Just.

Actions are pinned to commits; Dependabot proposes action updates. Read success,
duration and scope from the actual run and its reports. Workflow configuration
alone is not validation of a particular revision.

## Cache behavior and failure records

The workflow prefers NixOS's signed public cache for upstream packages. Full
jobs except `fresh` also use the pinned Magic Nix Cache action with GitHub Actions
storage for project outputs. Quick jobs use only the upstream cache and do not
restore the project's compiled outputs. FlakeHub uploads and diagnostic export
are disabled. The current
configuration needs no separate cache write secret. Branch access, quota and
retention follow the backing GitHub storage; caching is an optimization, not a
source dependency.

Runtime closures of newly built outputs can be uploaded, including dependencies
available upstream. Whole-store diffing is disabled, so merely restoring an
output does not enqueue it again. Large closure transfers can still dominate
elapsed time. Ordinary cache misses must build successfully; the explicit
`cache` scope fails on a miss to distinguish restoration from a new build.

A reused successful check output is cached evidence, not a new execution.
The fresh scope restricts substitution to the upstream NixOS cache and rebuilds
the selected Lean dependencies from source. A future shared project cache needs
an operator, signing policy and explicit write permissions.

For local diagnosis, `nix build -L --keep-failed .#checks.x86_64-linux.project`
retains the failed directory and its test reports. Preserve the command,
source/lock identities and relevant diagnostics with a failure report.

Generated reports, `.lake`, virtual environments and native build directories
remain local. Keep a Nix result symlink or development profile for outputs that
should survive garbage collection. Removing such a reference does not remove
source files. Routine development needs no machine-wide configuration changes.

## Preparing a public branch

Review both the final file set and the outgoing history before publication.
Messy commit messages or retired implementations alone do not require a new
branch. If every outgoing revision is suitable for public access, an ordinary
PR and squash merge are sufficient.

When development history contains material that should remain private,
create the publication branch from the current public `main` in a separate
worktree. Copy the reviewed tracked tree into that worktree and commit it there.
Before pushing, verify that its tree exactly matches the reviewed tree and that
its new history contains only the intended publication commits. Keep the
development branch and its history locally.

A clean final tree does not remove files from earlier commits. GitHub's squash
merge happens after the PR branch has been pushed, so it does not prevent that
branch's development history from becoming public. Check the intended Git
history as well as running `.github/scripts/public-tree-guard.sh` on the final
tree. Confirm the runner configuration above before relying on PR checks.
