# Development

## Prerequisites

- [elan](https://github.com/leanprover/elan), which installs the Lean toolchain that
  `lean/compiler/lean-toolchain` names; the formal package names the same toolchain.
- [just](https://github.com/casey/just), which runs the commands below.
- Python 3 for the document checker and Unicode table generator. These scripts use the standard library.

## Layout

| Path | Content |
|---|---|
| `lean/compiler/` | the Lake package of the compiler: the core (`Zkc/Core`), the frontend (`Zkc/Frontend`), their tests (`Zkc/Tests`) and tools (`Zkc/Tools`) |
| `lean/formal/` | the Lake package of statements and proofs over the meaning of the core; it requires `../compiler`. Its modules have roots of their own: the library (`ZkcFormal`), its tests (`ZkcFormalTests`) and its tools (`ZkcFormalTools`) |
| `language/` | the reference of the source language and its conformance tests |
| `libraries/zkc/` | the library of the source language, in source |
| `examples/` | worked programs |
| `docs/` | the status, this guide and the specification of the core language |
| `scripts/check_docs.py` | the document checker |
| `.github/` | the contribution guide, the pull request template and CI |

A module root belongs to one package: the compiler package has `Zkc`, the formal package the three above. Lean finds a module by name through the folder of its first name component, so a tool that takes module names (`leanchecker`, `leanexport`, `lake check`, `lake comparator`) finds the modules of both packages.

Lake writes the outputs of each package to its `.lake/` directory, which git ignores.
Both packages pin Lean 4.36.0. See the [toolchain guide](lean-toolchain.md) for its trust boundary,
feature choices and upgrade checks. Rebuild artifacts for the exact toolchain; do not reuse
4.35 `.olean` files.

The default targets build the core, vocabulary, their tests and the audit. The separate
interactive suite checks selected source protocols through admission and replays their formal
proofs. The formal package builds its public root and test modules with the pinned Mathlib and VCVio dependencies. The historical receipt suite is preserved with its original Core revision.

## Commands

Run every command from the root of the repository.

| Command | What it does |
|---|---|
| `just` | lists the recipes |
| `just build` | `lake build --iofail` in `lean/compiler`: the package default targets |
| `just test` | `lake build --iofail` and `lake test` in `lean/compiler`, then `just audit` |
| `just test-interactive` | build the interactive formal modules, check emitted source entries and mutations, and audit the interactive library and its mathematical controls |
| `just test-frontend` | build the three frontend libraries, check source contracts and generated views, then run the driver with its table of known failures |
| `just test-packages` | print every admitted root of eight examples as a Lean module in which the kernel elaborates the program by names, compare that program with what the frontend gave to admission, read a fixture with every constructor back, and refuse four controls |
| `just test-written-knowledge` | compile both Schnorr and Chaum–Pedersen written clauses, check admission and extraction, consume the public theorems, replay their project imports, and test permitted forks, source mutations and diagnostics |
| `just test-written-charge` | issue and audit the two source-bound probability endpoints, check depth-specific member laws, close the proof arguments of each use, read the clause of a goal and what its goals claim, judge the five subjects of a written soundness goal (`Count<8>`, Freivalds' check, `Guess<3>`, `Either`, `Twice`) within the tables of caps of their goals in generated modules, each with its controls, judge the accepted proof modules against their challenges in one run of `lake comparator`, check that use of the comparator on pairs that it must refuse, exercise independent fixed-table sampling and replay the charge issuer. The checks build their generated modules, and export what is judged, under `bwrap` (bubblewrap), which the host needs |
| `just test-formal` | build and audit the formal library, its tests and the charge issuer together, then run the charge checks |
| `just audit` | `lake exe zkc-audit` in `lean/compiler`: compiler module coverage and the audit of the core, vocabulary and their tests |
| `just check` | the checks that need no build: `bash .github/scripts/public-tree-guard.sh`, `python3 scripts/check_docs.py --all`, and `python3 lean/compiler/scripts/generate_unicode_tables.py --check` |

Every recipe builds with Lake's `--iofail`, under which a module that logs anything fails
the build. Lake keeps what a module logs and replays it whenever a module that imports it is
built or opened, so a module that prints (a `#print axioms` left after a theorem, a line that
a test writes when it passes) puts those lines into every later build and every editor
session. The rule reaches the pinned dependencies too: a change of a pin that brings in a
module which logs fails the recipe on a module outside this repository.

Lake builds incrementally, so `just build` after a change rebuilds only the modules that the
change affects. Run `just test` and `just test-interactive` for changes that cross the compiler and interactive proof boundary. Include `just test-packages` when a change affects the Core program, admission, emission, the printed package, the keys of the standard vocabulary or the parameters of a project primitive: no other recipe and no CI job checks that the fixture of the printer holds every constructor. Include `just test-written-knowledge` when a change affects generated claims, their source types, role projection or shared proof rules.

### The tests

`lake test` in `lean/compiler` builds `ZkcCoreTests` and the vocabulary tests it requires.
The checks run during compilation. For a focused change, build the affected module first.
After the change stabilizes, `just test` also performs the audit.

The frontend driver runs under `just test-frontend`. It checks source rules and locations,
admission of emitted packages, formatting and independent conformance cases. It counts passes,
known failures and failures separately. A new failure or an entry whose diagnostic has
disappeared fails the recipe. See the
[frontend guide](../lean/compiler/Zkc/Frontend/README.md).

### Lean proof tools

Use [Lean Beam](https://github.com/leanprover/lean-beam) for Lean search, navigation,
diagnostics, proof experiments and profiling. Routine navigation and proof work should stay in
the same Beam workspace.

Lean 4.36 bundles Beam on Linux and macOS. It is an optional development tool, with no dependency
or import in the compiler package. Register the selected toolchain's `bin/lean-beam-mcp` with the
agent client and install the matching official Beam skill and its references; the
[setup guide](https://github.com/leanprover/lean-beam/blob/10c7238efd7915bba2a7cca951c32b8485b8fa2e/docs/SETUP.md)
covers both. One bundled server serves projects using its containing Lean installation. Match
the tool to the package's pin; do not change a project's toolchain merely to use Beam. If MCP
is not loaded, the matching Beam CLI is another entry point.

Use the `lean-beam` skill for tool operation.

Beam provides name search (`lean_workspace_symbols`), file structure (`lean_document_symbols`),
type information (`lean_hover`), definition and reference lookup, as well as proof-state inspection
and speculative execution.

Every Beam request identifies the Lake package root, such as the absolute path to `lean/compiler`,
through `workspace.root`. After a source edit, use the version returned by `lean_update` or
`lean_sync`; positions are zero-based UTF-16 coordinates.
Prefer independent `lean_run_at` attempts for small candidates. Retain a handle when candidates
share substantial preparation, release unused handles, and reacquire them after edits.
For a changed dependency, sync and save that module before refreshing its importer.
`lean_save` writes a development checkpoint from the server state; it does not edit source.

Use one artifact-producing workflow at a time per package. Before an external build, drop the
affected Beam workspace (or stop its CLI session) and confirm cleanup. Recreate Beam after
external artifact changes. Do not stop another session's processes.

A successful tactic attempt can still leave goals, and a checkpoint-ready file can contain
`sorry` warnings. After proof edits stabilize, run the affected compilation and the audit below.
Beam does not replace either acceptance check.

### The audit

`just audit`, also run by `just test`, checks that every Lean source file under
`lean/compiler/Zkc` is selected by exactly one whole library target. It reads the module
list from Lake for each library declared by the compiler package. The audit also checks
the core, vocabulary and their tests.

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

The formal audit adds `ZkcFormalTools.DrawCharge` as a replay root. Both
`lake test` in the formal package and `just test-written-charge` check the issuer and its
project import closure through the kernel. The formal policy takes Lean and the pinned
Mathlib and VCVio import closures as built, checks for project modules in the upstream
closure before replay, and follows proof dependencies through those libraries for axioms.
It permits `propext`, `Quot.sound` and `Classical.choice`. The focused audit loads controls
separately and requires the private extra axiom and the imported unchecked proof to be refused
by their respective rules. A control also attempts to preload the unchecked module through
the prebuilt set and requires the replay boundary to reject it. See the [formal package guide](../lean/formal/README.md).

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
