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

## Commands

Run every command from the root of the repository.

| Command | What it does |
|---|---|
| `just` | lists the recipes |
| `just build` | `lake build` in `lean/compiler`, then in `lean/formal` |
| `just test` | `lake build` and `lake test` in `lean/compiler`, then the same in `lean/formal`, then `just audit` |
| `just test <arguments>` | `lake test -- <arguments>` in `lean/compiler`: only the frontend's test driver, with its own options |
| `just audit` | `lake exe zkc-audit` in `lean/compiler`, then `lake exe zkc-formal-audit` in `lean/formal` |
| `just check` | the checks that need no build: `bash .github/scripts/public-tree-guard.sh`, `python3 scripts/check_docs.py --all`, and `python3 lean/compiler/scripts/generate_unicode_tables.py --check` |

Lake builds incrementally, so `just build` after a change rebuilds only the modules that the
change affects. `just test` with no argument is the whole validation of the Lean packages.

### The frontend's tests

`just test` with arguments passes them to the test driver of the frontend and runs nothing
else. The driver has one option, `--trees`, which runs only the second reading of typed trees:
for every protocol of its corpus (the library, the worked programs, the generators and the
programs of the run tests), a run of the emitted program is compared with a run read from the
typed tree. It is not part of the default run because it takes about 25 minutes:

```sh
just test --trees
```

The section Tests of the [frontend guide](../lean/compiler/Zkc/Frontend/README.md) says what
each part of the tests checks, and what the second reading does not compare.

### The audit

`just audit` checks the libraries that hold theorems and their tests: the core (`Zkc.Core`) and
its tests in `lean/compiler`, the formal library (`Zkc.Formal`) and its tests in `lean/formal`.

- Every declaration is replayed through Lean's kernel, so a declaration that was compiled
  without the kernel's check is refused.
- No declaration uses `sorry` or an axiom beyond Lean's three (`propext`, `Classical.choice`
  and `Quot.sound`), and none has `@[extern]` or `@[implemented_by]`.
- The core imports only the core, `Init` and `Std`; the formal library only the core and
  itself; no library imports a module of the tests or of the tools; every file of a library
  is imported by its root module, and every file of a library of tests is loaded.

The frontend (`Zkc.Frontend`) is checked for the same axioms, attributes and imports but is not
replayed: no theorem rests on it, and admission checks what it emits. The audit runs on
controls that break each rule and passes only when it refuses all of them. It takes about two
minutes.

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
