# Development

## Prerequisites

- [elan](https://github.com/leanprover/elan), which installs the Lean toolchain that
  `lean/compiler/lean-toolchain` names; the formal package names the same toolchain.
- [just](https://github.com/casey/just), which runs the commands below.
- `python3`, for the document checker, which uses only the standard library.

There is no other environment to prepare: no Nix environment and no Python project.

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
| `just check` | the checks that need no build: `bash .github/scripts/public-tree-guard.sh`, then `python3 scripts/check_docs.py --all` |

Lake builds incrementally, so `just build` after a change rebuilds only the modules that the
change affects. `just test` with no argument is the whole validation of the Lean packages.

### The frontend's tests

`just test` with arguments passes them to the test driver of the frontend and runs nothing
else. The driver has one option: `--trees` runs only the second reading of typed trees, which
compares, for every protocol of the worked programs, a run of the emitted program with a run
read from its typed tree. It takes several minutes and is not part of the default run:

```sh
just test --trees
```

The section Tests of the [frontend guide](../lean/compiler/Zkc/Frontend/README.md) says what
each part of the tests checks.

### The audit

`just audit` checks both packages: no declaration uses `sorry`, no proof uses an axiom beyond
Lean's three (`propext`, `Classical.choice` and `Quot.sound`), and the imports between the
libraries follow their rules.

### The documents

`python3 scripts/check_docs.py --all` checks the Markdown of the repository: every local link
names a file or directory that exists, every fragment names a heading of the page it points to,
and every page other than `README.md` and `AGENTS.md` is reachable from `README.md` or
`docs/README.md`. Without `--all` it checks only `README.md`, `AGENTS.md` and `docs/`. It does
not fetch external links.

## CI

CI runs on every pull request to `main` and every push to `main`. It runs only the checks that
need no build: the public tree guard and the document checker, the two commands of `just check`.
It does not build or test the Lean packages. The author of a change verifies the Lean packages
locally with `just test`, or with the part of it that the change affects, and states the result
in the pull request, as the [contribution guide](../.github/CONTRIBUTING.md) describes.
