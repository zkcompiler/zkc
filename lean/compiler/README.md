# Compiler

The Lake package `zkc_compiler`: the compiler of the zkc source language, in Lean. The frontend
reads the source and emits packages of the core; the core admits a package as a program,
constructs its schemes, projects it to role programs and runs them. It has no Lake dependency;
the formal package (`../formal`) requires it.

Libraries:

- `ZkcCore` (`Zkc.Core`): the core language, its admission and its theorems
  ([guide](Zkc/Core/README.md)).
- `ZkcFrontend` (`Zkc.Frontend`): the lexer, the parser, the checker and the emitter of the
  source language ([guide](Zkc/Frontend/README.md)).
- `ZkcCoreTools`, `ZkcFrontendTools` (`Zkc.Tools.Core`, `Zkc.Tools.Frontend`): the code of the
  executables.
- `ZkcCoreTests`, `ZkcFrontendTests` (`Zkc.Tests.Core`, `Zkc.Tests.Frontend`): the checks of the
  core, which the kernel runs when they are built, and the test driver of the frontend.
- `ZkcAudit` (`Zkc.Tools.Audit`): the audit of the declarations and the imports of a library,
  with the replay of its declarations through the kernel.

Executables:

- `core-tool`: the core's commands on a package (`admit`, `compile`, `step …`, `literal`), and
  `selftest`.
- `zkc-syntax`: the lexer, the parser and the canonical printer on source files.
- `zkc-check`: the checks of names, instances and types, the emitted packages, runs, proofs.
- `zkc-frontend-tests`: the test driver of the frontend, which `lake test` runs.
- `zkc-audit`: the audit of `ZkcCore`, `ZkcFrontend` and `ZkcCoreTests`.

## Build, test and audit

The entry points of the repository are `just build`, `just test` and `just audit`. In this
directory:

```sh
lake build              # every library and executable; the checks of the core run in the kernel
lake test               # the test driver of the frontend
lake test -- --trees    # the typed trees of the protocols and their second reading only
lake exe zkc-audit      # the audit of the core, the frontend and the tests of the core
```

The test driver reads the repository from this directory: `../../language` (the reference of
the language and its conformance tests), `../../libraries` (the library in source) and
`../../examples` (the worked programs). A directory that is missing is an error. The derived
Schnorr proof is replayed by `scripts/replay_derived_schnorr.py`, so the tests need `python3`.

`zkc-audit` imports the core, the frontend and the tests of the core from their built files
and checks, for every declaration, that its axioms are among `propext`, `Classical.choice` and
`Quot.sound` and that it carries no `@[extern]` or `@[implemented_by]`. It replays the
declarations of the core and of its tests through the kernel, together with every module that
they import outside Lean's libraries (the tool that the tests import), on an environment that
takes only Lean's libraries as built, so that a declaration stored without the kernel's check is
refused; the frontend is not replayed, since it is the unproved part of the compiler and no
theorem of the project rests on it, and a replayed module that imports it is a finding. It
checks that a module of the core imports only the core, `Init` and `Std`, that no module of the
core or of the frontend imports a module of the tests or of the tools, that every file of the two
is imported by its root module (`Zkc/Core.lean`, `Zkc/Frontend.lean`), and that every file of the
tests is built and audited. It prints the number of `partial` definitions of each library, what
it replayed and what it took as built, and exits with 0 only when the libraries pass and it
refuses each of its controls (`Zkc/Tools/Audit/Controls/`) by the rule that the control is for.

## Files

- `fixtures/`: the packages, declarations and outputs of the tool that the checks of the core
  read; `fixtures/construction/` are those of the constructions.
- `scripts/generate_unicode_tables.py`: writes `Zkc/Frontend/Syntax/UnicodeData.lean` from the
  Unicode data pinned in `unicode/`; with `--check` it refuses a table that differs.
- `scripts/replay_derived_schnorr.py`: the independent replay of the derived Schnorr proof.
