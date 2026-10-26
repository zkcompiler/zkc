# Pinned replay tools

[manifest.json](manifest.json) owns the exact Lean 4.35.0, lean4lean,
Batteries and lean4export revisions, the 33 source hashes, the three patches,
their resulting source hashes, and the finite compilation/link recipe.
Only two native modules and lean4lean's 29-module executable closure are built.
No zkc proof, installed tool, dependency checkout or shared cache is changed.

The patches repair implicit string-literal prerequisite scheduling in both
readers and validate lean4lean's four reconstructed quotient records. They
retain ordinary declaration checking, reconstruction, axiom policy and the
separate paranoid allocator. They do not modify the model or comparator.

The native adapter follows upstream
[Lean replay](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Replay.lean),
[release CMake](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/CMakeLists.txt)
and the [minimal-initialization link adaptation](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/script/lean4lean-minimal-init.sh).
The other adapter patches
[lean4lean replay](https://github.com/Kha/lean4lean/blob/456abe5015fc8f54ea595561fc39523d7733c93f/Lean4Lean/Replay.lean)
and its [entry point](https://github.com/Kha/lean4lean/blob/456abe5015fc8f54ea595561fc39523d7733c93f/Main.lean).
These upstream sources and patch contexts are Apache-2.0 licensed.

## Prepare sources and build

Use the installed release Lean 4.35.0 toolchain and local source roots from the
manifest's exact revisions. The Lean sources come from that installation's
`src/lean`. The other three roots can be existing pinned checkouts or minimal
source copies; every consumed file is checked by SHA-256 before compilation.
No dependency oleans from those checkouts are used. The older toolchain named
by lean4lean's upstream package is deliberately replaced by the release 4.35.0
compiler and its installed core ABI for this finite build.

If sources are absent, fetch them explicitly into new local directories:

```sh
git init /path/to/replay-sources/lean4lean
git -C /path/to/replay-sources/lean4lean fetch --depth 1 https://github.com/Kha/lean4lean 456abe5015fc8f54ea595561fc39523d7733c93f
git -C /path/to/replay-sources/lean4lean checkout --detach FETCH_HEAD
git init /path/to/replay-sources/batteries
git -C /path/to/replay-sources/batteries fetch --depth 1 https://github.com/leanprover-community/batteries f8e1f4b2e1478e39113d32d0af75234aa86423fb
git -C /path/to/replay-sources/batteries checkout --detach FETCH_HEAD
git init /path/to/replay-sources/lean4export
git -C /path/to/replay-sources/lean4export fetch --depth 1 https://github.com/leanprover/lean4export 411dce7db58a3afc60ecab2d211acd1042b593dc
git -C /path/to/replay-sources/lean4export checkout --detach FETCH_HEAD
```

From the repository root, build without network access:

```sh
python3 lean/checks/build_replay_tools.py \
  --lake /path/to/lean-4.35.0/bin/lake \
  --lean4lean-source /path/to/replay-sources/lean4lean \
  --batteries-source /path/to/replay-sources/batteries \
  --export-source /path/to/replay-sources/lean4export \
  --output /path/to/new-replay-tools
```

Python 3.12+, `patch` and Linux are required. Output must be new. The builder
uses one compiler at a time, `lean -j2 -M8192`, a 120-second per-command timeout,
64 GiB address-space ceiling, and the shared runner's 8 MiB combined diagnostic
limit and process-group cancellation. `--memory-mb` and `--timeout` can be set
explicitly. No core/library rebuild occurs. Read-only symlinks mirror installed
library inputs during native compilation; all native output names and sidecars
are excluded from that mirror. The final runtime contains only regular copies.

`manifest.json` in the output records every installed `bin`, `lib` and `include`
input by size/SHA-256, patched sources, patch identities, exact commands, and all
runtime files. The runtime copies the stock Lake, Lean launcher, exporter,
nanoda, con-leche, con-ron and required shared libraries; only leanchecker,
leanchecker-paranoid and lean4lean are patched. This is a check-only runtime:
capture continues to use the stock installation and existing oleans.

To reuse an earlier build, repeat the same command with a new output and
`--reuse /path/to/previous-replay-tools/manifest.json`. Reuse requires identical
recipe, builder, patched sources, options and complete installed input inventory.
The original commands and binary identities remain in the reuse receipt. A
missing or changed input fails; reuse never silently becomes a new build.

## Use the runtime

Pass its manifest explicitly to `check_independent.py compare` or `replay` with
`--replay-toolset`. See the [independent-checking guide](../../docs/development/independent-checking.md)
for complete commands and verdict scope. The driver checks stock runtime
identity, validates this checkout's recipe/patch/source hashes and the complete
toolset runtime, then makes a separate local runtime snapshot for Lake. Lake's
normal sandbox binds that runtime read-only. No symlink or hardlink points into
the installed toolchain, and hidden home/tmp paths need no extra sandbox grants.

Manifest, source and runtime identities are checked before and after every
checker command, including inode, size, mode, mtime and ctime. Restoring bytes
after a write does not restore file identity. Keep inputs free of concurrent
writers. These checks detect mutation; hashes and build receipts do not prove
authenticity or replace review of the build and selected final artifacts.
Inherited installation and loader overrides, including an empty
`LAKE_CHECK_EXPORT`, are refused. Checking uses a restricted environment while
retaining explicit sandbox/toolchain discovery settings. Linux namespace or
resource failures remain failures, with no unsandboxed fallback.

Run the Python controls from the independent-checking guide. To include small
patched real-tool controls, additionally set
`ZKC_INDEPENDENT_REPLAY_TOOLSET=/path/to/new-replay-tools/manifest.json` alongside
`ZKC_INDEPENDENT_TOOLCHAIN`. They exercise literal replay, corrupt proofs and
quotient records directly, and all six kernels when sandbox namespaces work.
Direct reader controls are diagnostic evidence, never a sandboxed verdict.
