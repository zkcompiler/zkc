# Development

## Prerequisites

- [elan](https://github.com/leanprover/elan), which installs the Lean toolchain that
  `lean/compiler/lean-toolchain` names; the formal package names the same toolchain.
- [just](https://github.com/casey/just), which runs the commands below.
- `python3`, for the scripts, which use only the standard library: the document checker, the
  generator of the lexer's Unicode tables, and the independent replay of a derived proof that
  the frontend's tests run.

## Layout

| Path | Content |
|---|---|
| `lean/compiler/` | the Lake package of the compiler: the core (`Zkc/Core`), the frontend (`Zkc/Frontend`), their tests (`Zkc/Tests`) and tools (`Zkc/Tools`) |
| `lean/formal/` | the Lake package of statements and proofs over the meaning of the core; it requires `../compiler` |
| `language/` | the reference of the source language and its conformance tests |
| `libraries/zkc/` | the library of the source language, in source |
| `examples/` | worked programs |
| `docs/` | the status, this guide and the specification of the core language |
| `scripts/check_docs.py` | the document checker |
| `.github/` | the contribution guide, the pull request template and CI |

Lake writes the outputs of each package to its `.lake/` directory, which git ignores.
Both packages pin Lean 4.36.0. See the [toolchain guide](lean-toolchain.md) for its trust boundary,
feature choices and upgrade checks. Rebuild artifacts for the exact toolchain; do not reuse
4.35 `.olean` files.

The default targets build the core, vocabulary, their tests and the audit. The separate
interactive suite checks selected source protocols through admission and replays their formal
proofs. The full frontend CLI and historical formal receipt suite still await migration.

## Commands

Run every command from the root of the repository.

| Command | What it does |
|---|---|
| `just` | lists the recipes |
| `just build` | `lake build` in `lean/compiler`: all active targets |
| `just test` | `lake build` and `lake test` in `lean/compiler`, then `just audit` |
| `just test-interactive` | build the interactive formal modules, check emitted source entries and mutations, and audit the interactive library and its mathematical controls |
| `just test-written-knowledge` | compile both Schnorr and Chaum–Pedersen written clauses, check admission and extraction, consume the public theorems, replay their project imports, and test permitted forks, source mutations and diagnostics |
| `just audit` | `lake exe zkc-audit` in `lean/compiler`: core, vocabulary and their tests |
| `just check` | the checks that need no build: `bash .github/scripts/public-tree-guard.sh`, `python3 scripts/check_docs.py --all`, and `python3 lean/compiler/scripts/generate_unicode_tables.py --check` |

Lake builds incrementally, so `just build` after a change rebuilds only the modules that the
change affects. Run `just test` and `just test-interactive` for changes that cross the compiler and interactive proof boundary. Include `just test-written-knowledge` when a change affects generated claims, their source types, role projection or shared proof rules.

### The tests

`lake test` in `lean/compiler` builds `ZkcCoreTests` and the vocabulary tests it requires.
The checks run during compilation. For a focused change, build the affected module first.
After the change stabilizes, `just test` also performs the audit.

The retained frontend's separate driver and its optional `--trees` comparison belong to the
pending frontend port; they are not the active test driver. Its
[guide](../lean/compiler/Zkc/Frontend/README.md) describes those tests.

### Lean proof tools

Use [Lean Beam](https://github.com/leanprover/lean-beam) by default for Lean search, navigation,
diagnostics, proof experiments and profiling. Keep `lean-lsp-mcp` enabled for now as a fallback
when Beam is unavailable, incompatible, fails, or lacks a needed feature. Routine navigation and
proof work should stay in the same Beam workspace.

Lean 4.36 bundles Beam on Linux and macOS. It is an optional development tool, with no dependency
or import in the compiler package. Register the selected toolchain's `bin/lean-beam-mcp` with the
agent client and install the matching official Beam skill and its references; the
[setup guide](https://github.com/leanprover/lean-beam/blob/10c7238efd7915bba2a7cca951c32b8485b8fa2e/docs/SETUP.md)
covers both. One bundled server serves projects using its containing Lean installation. Match
the tool to the package's pin; do not change a project's toolchain merely to use Beam. If MCP
is not loaded, the matching Beam CLI is another entry point.

Use the `lean-beam` skill for tool operation and the `lean4` skill for proof methodology and
review. The Beam default here takes precedence over generic LSP-first advice in proof skills.

Beam provides name search (`lean_workspace_symbols`), file structure (`lean_document_symbols`),
type information (`lean_hover`), definition and reference lookup, as well as proof-state inspection
and speculative execution. LSP's external mathematical search integrations remain optional
fallbacks; they are not needed for ordinary zkc symbol navigation.

Every Beam request identifies the Lake package root, such as the absolute path to `lean/compiler`,
through `workspace.root`. After a source edit, use the version returned by `lean_update` or
`lean_sync`; positions are zero-based UTF-16 coordinates. LSP MCP positions are one-based.
Prefer independent `lean_run_at` attempts for small candidates. Retain a handle when candidates
share substantial preparation, release unused handles, and reacquire them after edits.
For a changed dependency, sync and save that module before refreshing its importer.
`lean_save` writes a development checkpoint from the server state; it does not edit source.

Use one artifact-producing workflow at a time per package. Before an external build or an LSP
fallback that may rebuild dependencies, drop the affected Beam workspace (or stop its CLI session)
and confirm cleanup. LSP dependency handling can build imports even when its explicit build tool
is disabled. Recreate Beam after external artifact changes; the servers do not share document
versions or proof handles. Do not stop another session's processes.

A successful tactic attempt can still leave goals, and a checkpoint-ready file can contain
`sorry` warnings. After proof edits stabilize, run the affected compilation and the audit below.
Beam does not replace either acceptance check.

### The audit

`just audit` checks the core, vocabulary and their tests.

- Every logical declaration is replayed through Lean's kernel, including its project import
  closure. Only Lean's own libraries are taken as built; unsafe declarations and compiled
  partial-definition code are outside kernel replay.
- The dependency closure uses only `propext` and `Quot.sound`, with no `sorryAx` or
  `Classical.choice`. Explicit hypotheses of a theorem remain hypotheses.
- No audited declaration carries `@[extern]` or an unrecognized `@[implemented_by]`.
  Lean's recursive implementations retain their exception. The new constructor-index native
  replacements must match both generated bodies exactly. Their execution remains a compiler
  and runtime trust assumption, and their counts are reported separately.
- The core imports only itself, `Init` and `Std`; the vocabulary may also import the core.
  Neither imports tests or tools. Root imports cover every library source file, and every
  test source is built and loaded.

The audit accepts a positive fixture of generated helpers, refuses all 16 negative controls
and fails if any expected result changes. Private declarations are loaded from
`.olean.private`; the controls also check private native attributes. The
[compiler guide](../lean/compiler/README.md#build-test-and-audit) describes the entry points.

### The documents

`python3 scripts/check_docs.py --all` checks the Markdown of the repository: every local link
names a file or directory that exists, every fragment names a heading of the page it points to,
and every page other than `README.md` and `AGENTS.md` is reachable from `README.md` or
`docs/README.md`. Without `--all` it checks only `README.md`, `AGENTS.md` and `docs/`. It does
not fetch external links.

## CI

CI runs on every pull request to `main` and every push to `main`. It runs only the checks that
need no build: the public tree guard, the document checker and the check of the generated
Unicode tables, the commands of `just check`.
It does not build or test the Lean packages. The author of a change verifies the Lean packages
locally with `just test`, or with the part of it that the change affects, and states the result
in the pull request, as the [contribution guide](../.github/CONTRIBUTING.md) describes.
