# Compiler tooling

The CLI and Rust `project` SDK share project loading, setting resolution and
compilation requests. Build settings select existing checked implementation
alternatives. They do not select a protocol, field, hash, security parameter,
provider authority or weaker verification.

## Configure a build

Add partial settings to the consuming `zkc.toml`:

```toml
[build]
simplify = true

[profile.vector]
finite-bulk = false

[profile.storage]
release-storage = true
```

Resolution is shipped defaults → root `[build]` → selected `[profile.NAME]` →
explicit command options. Dependencies cannot impose settings on consumers.
There is one inheritance step; `default` is reserved for the root build without a
named profile. Unknown profiles and fields refuse. The six current settings and
defaults are:

| Setting | Default | Command override |
|---|---|---|
| `simplify` | `true` | `--no-simplify` |
| `finite-bulk` | `true` | `--no-finite-bulk` |
| `release-storage` | `false` | `--release-storage` |
| `fuse-vector-reductions` | `false` | `--fuse-vector-reductions` |
| `fuse-collect-fold` | `false` | `--fuse-collect-fold` |
| `calculation-batching` | `true` | `--no-calculation-batching` |

```sh
zkc inspect --view=project --profile=vector
zkc compile Proof --profile=vector
zkc inspect --view=toolchain
```

JSON command reports retain effective values and each value's origin. Packages
retain the published policy. Pinned-package execution rejects source settings;
it uses the policy of the authenticated package.

## Inspect and explain

`inspect` defaults to the checked Entry interface. `--view=project` shows the
resolved dependency graph and settings; `api` shows checked public contracts and
exports; `placement` shows completed callable contracts. Expression placement is
available in Protocol IR dumps. `notations` shows syntax metadata, with optional
`--notation-private` and `--notation-installation` visibility. Source inventories
appear under `checked` in JSON reports. `toolchain` works outside a project and reports
the selected compiler's installation, actual executable SHA-256 and capabilities,
alongside the calling Rust runtime's count-instrument capability.

```sh
zkc compile Proof --report=build/explain --dump=entry,protocol,participant,exec,physical
zkc run Main --report=build/run-observation
```

The report directory must be fresh. `command.json` retains the operation result;
`compilation.json` contains phase operation counts, operation histograms, bounded
location/binding/type metadata, inclusive pass times, and mathematical decisions.
Requested phase dumps are separate `.mlir` files with ordinal prefixes. The
`entry` phase describes application control; nested calculations and child
deployments retain their own phases. Each observation has a `unit` path from
the root Entry to the calculation or deployment, so repeated phases remain
distinct. Bounded journals report omitted records. `time-trace.json` is an LLVM
scoped trace suitable for Chrome tracing or Perfetto. Compilation observations
are explicit instrumentation and are unsuitable as uninstrumented compile-time
baselines. Report publication errors are separate from the operation's status.

Mappings bind to the package SHA-256 and original capture. A location can identify
only a containing expression; unknown or omitted mappings are marked. Static
binding arguments and result types describe domains and representations, not
runtime values or dynamic shapes. Selection remarks are analysis observations:
a proposal's success alone does not establish publication. The detailed journal
retains proposals, checks, discarded candidates, retry policy and publication.
When a checking cause identifies a numerical invocation, it records the actual
source subject (declaration, site and occurrence path), not a traversal ordinal.
SDK observations retain the actual compiler executable hash and capabilities;
the executable identity is checked again after compilation.
Counters and dumps identify truncation; no sidecar authorizes execution.

Compiler failures retain structured codes and available primary/related byte
spans, plus bounded plain diagnostics for upstream messages. Source indices use
the checked catalog, including installation sources and their origin. Direct
`zkc-compile` observation, diagnostic and time-trace paths must be fresh files;
they cannot replace source files or prior evidence. Reports may contain
source names and IR; review them before sharing. They do not capture witness data
or randomness. For compiler development, use `zkc-opt`'s standard MLIR pipeline,
IR-printing, pass timing/statistics and crash-reproducer options. A failure report
identifies its source capture; it is not a self-contained source archive.

## Observe execution

Build the CLI with `cargo build -p zkc-cli --features execution-counts`, then use
`run`, `prove` or `verify` with `--instrument=counts`. Unsupported builds refuse the
instrument instead of returning empty measurements. Ordinary builds retain no
counter storage or collection work.

Reports expose VM/value/storage counters, operation totals and installed binding
contexts without operand values. Equal bindings aggregate across call sites;
these counts are not per-expression timing. Match the package identity to a
compilation report for static context. Host stages distinguish admission, readable
root and invocation input decoding and validation, preparation, SDK execution, and diagnostic
materialization, and output encoding/publication when requested. Proof SDK
execution includes preparation and is labelled that way. Times are inclusive wall
times and must not be summed across nested scopes.
The CLI command timer starts after argument validation, includes CPU initialization
and report-directory preparation, and stops before report publication. External
subprocess wall time additionally includes process startup and publication.
Count-enabled builds and diagnostic runs are separate from release timing
baselines. Counts can reveal reached control flow.

## Test consumers

A root project can declare ordinary consumer Entries:

```toml
[test.interface]
entry = "example::Main"

[test.execute]
entry = "example::Main"
operation = "run"
args = ["--input=inputs/example.Main/arguments.json", "--no-results"]

[test.missing]
entry = "example::Absent"
expect = "source-compilation"
```

`zkc test` runs all recipes; `zkc test execute --profile=vector` selects one.
Operations are `check` (default), `run`, `prove` and `verify`. Each recipe uses the
ordinary compiler and Host; `expect` is `success` or an exact diagnostic code.
File arguments are resolved beside the root manifest. Recipes cannot replace the
root, compiler or profile. Dependencies' recipes are never run implicitly. There
is no dependency scheduler: tests should own their input/proof fixtures and output
paths. Library-only projects can test consumer Entries without a new source DSL.

## Reuse local compilation

`zkc compile Proof --cache=build/compiler-cache` opts into a trusted local output
store. The CLI quota is 256 MiB; the SDK `CompilationCache` accepts an explicit
bounded quota and provides `clear()`. Oldest publications are evicted first.
The key includes captured module/asset names, formats and exact bodies, selected
Entry/kind, effective options, compiler executable and installation identity.
Compilation reads a private captured snapshot. Records are authenticated and
normal Host admission still runs. Cache-local locks protect complete publication
and accounting; unrelated builds and benchmarks acquire no global lock.

Requested observations recompute so that cache reuse cannot supply an incomplete
report. Successful compilations carrying plain diagnostics are not retained.
Witnesses, inputs, setup keys, providers and sessions are never cached. The store
is a development convenience, not a deployment trust root or an incremental query
engine. Removing its directory while no clients use it also clears its contents.

## Editors and experiments

Configure `-DZKC_ENABLE_MLIR_LSP=ON` to build `zkc-lsp`, the standard MLIR language
server with zkc dialects. This supports MLIR documents; a `.zkc` language server
requires a separate frontend snapshot and recovery contract.

The existing [benchmark runner](../../common/benchmarks/README.md) accepts named
profile candidates, validates them before timing, and retains settings and
compiler observations. It does not automatically select an optimization policy.

## Command responsibilities

`check` validates source; `inspect` queries checked metadata.
`prepare` creates missing input templates, preserving existing regular files.
`run --dry-run`, `prove --dry-run` and `verify --dry-run` validate the selected
invocation without protocol execution, resource issuance or proof/result publication. Lower-level
authenticated artifacts use `bundle run`, `bundle prove` and `bundle verify`.
