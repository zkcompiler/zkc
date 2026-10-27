# Independent checking of locked declarations

From the repository root, use `python3 lean/checks/check_independent.py` to
capture existing compiled declarations, compare two explicit export captures,
or replay a candidate under the current model.
The default covers every declaration in `checks/claims.lock.json` across the
main, security, ArkLib, and Clean packages. Each package's `comparator.json` must
match its lock entries exactly and permit only `propext`, `Classical.choice`,
and `Quot.sound`. Definition holes are forbidden.

Prepare dependencies and build each package separately using the normal formal
development commands. Capture **before** changing the proofs, preserve that
directory, then capture the independently rebuilt candidate:

```sh
python3 lean/checks/check_independent.py capture --output /path/to/base-exports
# Change proofs and build the affected packages separately.
python3 lean/checks/check_independent.py capture --output /path/to/candidate-exports
python3 lean/checks/check_independent.py compare \
  --base-manifest /path/to/base-exports/manifest.json \
  --candidate-manifest /path/to/candidate-exports/manifest.json \
  --output /path/to/comparison
```

Output directories must be new. `--lean-root` selects another checkout's `lean`
directory, and `--lake` selects its Lake launcher (with a sibling `lean`
launcher). Toolchain discovery invokes `lean --print-prefix` directly and never
evaluates the workspace Lake configuration. Repeat `--package main`,
`--package security`, `--package arklib`, or `--package clean` for a partial run;
its verdict covers only those packages. Every comparator configuration is still
validated. Capture never invokes `lake build` and never certifies that existing
oleans correspond to current sources. It records the Git revision and dirty
status, diff hash, lock/configuration hashes, tool versions and binary hashes,
selected olean file hashes, commands, and export SHA-256/size. Dependency
declarations are included transitively by `leanexport`.

For each package, capture explicitly runs:

```text
lake env <toolchain>/bin/leanexport <locked modules> -- <locked names> <standard axioms> <primitive targets>
```

The primitive targets match Lean 4.35.0's `Lake/CLI/Check.lean`
`primitiveTargets`/`builtinTargets`, including `Nat.xor`, `semiOutParam`, and
the quotient declarations. Compare runs these commands sequentially:

```text
lake comparator --config <package comparator.json> --challenge-from-export <base export> --solution-from-export <candidate export>
lake check --paranoid --from-export <candidate export>
```

Both exports bypass Lake's build/export path, including for packages with
dependencies outside their directory (`path = ".."`). The comparator's module
labels `LockedStatements` are inert with these flags; they are not aggregate
Lean modules. Always supply both exports. The comparator checks identical
statements and their referenced declarations, permitted axiom closure, and the
default kernel. The second command additionally requires all five bundled
checkers: Lean paranoid, lean4lean, nanoda, con-leche, and con-ron. Linux and a
working `bwrap` sandbox are required. Missing tools, rejected declarations,
resource exhaustion, and sandbox failures fail the run; no checker is skipped
and sandboxing is never disabled. The driver currently requires Lean 4.35.0
because the explicit primitive list is version-specific.

The comparator is deliberately stricter than semantic equivalence. Lean 4.35
compares the complete constant records of non-target dependencies, including
theorem proof bodies reached through definitions in a locked statement. A
proof-only simplification of such a helper can therefore fail comparison even
when its type is unchanged. The real-tool controls reproduce this case. Keep
that refusal; do not add definition holes or silently replace the baseline.
To diagnose proof validity separately, run the documented `lake check --paranoid
--from-export` command on each candidate export. That replay proves neither
baseline correspondence nor source freshness and must be reported separately.

Lean 4.35's replay implementations also have a string-literal dependency
limitation. The full main export contains `Char.ofNat` and `String.ofList`, yet
Lean default/paranoid replay rejects `SumcheckVerifierBodies.roundBody` with
unknown `String.ofList`, and lean4lean rejects `ProtocolOp.arguments` with
unknown `Char.ofNat`. Replay walks explicit constant references; string literals
can require primitives that this walk has not installed yet. A small two-string
definition control reproduces lean4lean's ordering failure. Three other bundled
kernels accept the full main export, but this is not an all-kernel verdict.
Keep the failed result and diagnose without `--silent` using `leanchecker
--from-export` or `leanchecker-paranoid --from-export` inside a read-only sandbox.
Do not alter protocol meanings, skip a checker, or classify the failure as a pass.

For the pinned upstream repair, prepare the exact sources and run
[build_replay_tools.py](../../checks/build_replay_tools.py) as described in the
[replay tool recipe](../../checks/replay_tools/README.md). It builds only the
affected checker closure into a new local directory, with exact source, patch,
installed-input, command and binary provenance. No installed tool is changed.
The explicit option selects a checked local runtime overlay containing the
three patched readers and the remaining stock tools/libraries:

```sh
python3 lean/checks/check_independent.py compare \
  --lake /path/to/stock-lean-4.35.0/bin/lake \
  --replay-toolset /path/to/replay-tools/manifest.json \
  --base-manifest /path/to/base-exports/manifest.json \
  --candidate-manifest /path/to/candidate-exports/manifest.json \
  --output /path/to/new-patched-comparison
```

The comparator and axiom policy are unchanged. Lake selects all six checkers
from the local runtime and retains its read-only, network-isolated sandbox.
Reports explicitly label patched readers and retain stock runtime identities.
Keep earlier stock failure reports; a patched verdict does not rewrite them.
Without `--replay-toolset`, the stock workflow remains selected. Capture rejects
this option and continues to read existing oleans through the stock exporter.

An intentional model transition may need independent proof replay before its
separate model review and baseline decision. Run the selected final captures:

```sh
python3 lean/checks/check_independent.py replay \
  --lake /path/to/stock-lean-4.35.0/bin/lake \
  --replay-toolset /path/to/replay-tools/manifest.json \
  --candidate-manifest /path/to/final-exports/manifest.json \
  --output /path/to/new-final-replay
```

This runs `lake check --paranoid --from-export` on each selected package and
validates exact locked coverage and every comparator configuration first. A
bounded streaming inventory also requires every locked root to occur in the
actual export; a manifest's coverage list alone is insufficient. Inventory
records are limited to 8 MiB, and loaded exports obey `--export-mb` as well.
The `zkc.independent-replay/0` report establishes only current proof/standard-axiom
validation. It does not compare models, exempt fingerprints, permit definition
holes, certify source freshness or accept a baseline. Preserve the fixed-model
comparison failure and complete the separate transition review. Default replay
covers all four packages; repeated `--package` selects a narrower verdict.

Comparison checks artifact hashes before and after checking, requires identical
declaration coverage, and rejects shared manifest/export paths, symlinks, and
hard links between base and candidate. Distinct captures can have identical
bytes when nothing changed; their capture provenance remains reviewable.
`report.json` records the verdict, selected declarations, input provenance and
commands. `failure.json` and command logs explain unsuccessful runs. A capture
alone is not a checking verdict. Preserve trusted baseline artifacts and review
their provenance; hashes establish file identity, not authenticity or source
freshness. Do not modify artifacts while checking them.
Replay also checks artifact identity before and after commands. Patched toolset
validation rejects symlinks and extra/missing runtime files, snapshots the local
runtime, and checks hashes and file metadata around every command. Installation
overrides such as `LEAN_SYSROOT`/`LAKE_OVERRIDE_LEAN`, dynamic-loader overrides,
and any inherited `LAKE_CHECK_EXPORT` are refused before checking.

The defaults bound each child to 8192 MiB of address space, 1800 seconds,
8 MiB of combined diagnostic output, and 2048 MiB per export. Configure these
with `--memory-mb`, `--timeout`, `--log-mb`, and `--export-mb`. Limits apply to
each process, not aggregate descendant memory. Commands run sequentially and
oversized output or timeout kills their process group. Large captures may need
an explicitly larger memory limit. Logs and exports stream to disk.

Lean 4.35 does not forward a worker limit to bundled `con-leche`. Its default
reserves approximately 1 GiB of virtual stack per hardware thread, so the
8 GiB default can fail even on a tiny proof on a many-core host. For a full
run, choose `--memory-mb` explicitly from the export size and hardware thread
count; `(hardware threads + 32) * 1024` MiB allowed the local controls to run.
This is an address-space ceiling, not measured resident memory. No checker
is omitted to satisfy the limit.

Run the Python configuration, artifact, and process controls without Lean:

```sh
uv run --no-sync --locked pytest common/tests/harness/test_lean_independent.py
```

The small real-tool controls compile temporary fixtures with `lean` and check
distinct proof terms, changed statements/dependencies, forbidden axioms, and a
corrupted proof. They do not build the project:

```sh
ZKC_INDEPENDENT_TOOLCHAIN="$(cd lean && lake env lean --print-prefix)" \
  uv run --no-sync --locked pytest common/tests/harness/test_lean_independent_tools.py
```

Set `ZKC_INDEPENDENT_REPLAY_TOOLSET=/path/to/replay-tools/manifest.json` as well
to exercise the explicit runtime, string literals, corrupt proof/quotient
records, and sandboxed all-checker selection. Existing stock controls remain.

If a namespace probe fails, the tests explicitly skip the sandbox-dependent
controls; statement, dependency, and axiom mismatch controls and direct default
kernel replay controls still run. Direct replay is a separate control, not a
verdict from `lake check --paranoid`. The production driver never skips kernels
or treats a sandbox failure as acceptance.

These checks apply to the exported locked declarations and their dependencies.
They do not establish correspondence with native zkc execution or security
properties beyond the statements and assumptions being checked. CI is unchanged.
