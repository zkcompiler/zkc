# Compiler

The Lake package `zkc_compiler`: the compiler of the zkc source language, in Lean. The frontend
reads the source and emits packages of the core; the core admits a package as a program,
constructs its schemes, projects it to role programs and runs them. It has no Lake dependency;
the formal package (`../formal`) requires it.

On this branch the package builds the core, the vocabulary, their tests and the audit. The
frontend (its libraries and executables below) and the formal package are not built on this
branch until they are attached again to the core.

Libraries:

- `ZkcCore` (`Zkc.Core`): the core language, its admission and its theorems
  ([guide](Zkc/Core/README.md)).
- `ZkcVocabulary` (`Zkc.Vocabulary`): the standard vocabulary of the core, its keys and its
  table ([guide](Zkc/Vocabulary/README.md)).
- `ZkcCoreTests` (`Zkc.Tests.Core`): the checks of the core, which the kernel runs when they are
  built; the test driver of the package.
- `ZkcVocabularyTests` (`Zkc.Tests.Vocabulary`): the checks of the vocabulary's table against
  the reference and the conformance cases that a function over the vocabulary expresses, which
  the kernel runs when they are built.
- `ZkcAudit` (`Zkc.Tools.Audit`): the audit of the declarations and the imports of a library,
  with the replay of its declarations through the kernel.
- `ZkcFrontend`, `ZkcFrontendTools`, `ZkcFrontendTests` (`Zkc.Frontend`, `Zkc.Tools.Frontend`,
  `Zkc.Tests.Frontend`): the lexer, the parser, the checker and the emitter of the source
  language ([guide](Zkc/Frontend/README.md)), the code of its executables and its tests; not
  built on this branch.

Executables:

- `zkc-audit`: the audit of `ZkcCore`, `ZkcVocabulary`, `ZkcCoreTests` and
  `ZkcVocabularyTests`.
- `zkc-syntax`, `zkc-check`, `zkc-frontend-tests`: the frontend's lexer, parser and canonical
  printer on source files, its checks, and its test driver; not built on this branch.

## Build, test and audit

The entry points of the repository are `just build`, `just test` (the build, the tests and the
audit), `just audit` and `just check`. In this directory:

```sh
lake build              # the core, the vocabulary, their tests and the audit
lake test               # the tests of the core, and those of the vocabulary that they need
lake exe zkc-audit      # the audit of the core, the vocabulary and their tests
```

`zkc-audit` imports the core, the vocabulary and the tests of each from their built files and
checks, for every declaration, that its axioms are among `propext` and `Quot.sound` and that it
carries no `@[extern]` or `@[implemented_by]`. It replays the declarations of the four libraries
through the kernel, together with every module that they import outside Lean's libraries, on an
environment that takes only Lean's libraries as built, so that a declaration stored without the
kernel's check is refused. It checks that a module of the core imports only the core, `Init` and
`Std`, and a module of the vocabulary only the vocabulary, the core, `Init` and `Std`; that no
module of the two imports a module of the tests or of the tools; that every file of the two is
imported by its root module (`Zkc/Core.lean`, `Zkc/Vocabulary.lean`); and that every file of the
tests is built and audited. It prints the number of `partial` definitions of each library, what
it replayed and what it took as built, and exits with 0 only when the libraries pass and it
refuses each of its controls (`Zkc/Tools/Audit/Controls/`) by the rule that the control is for.

## Files

- `scripts/generate_unicode_tables.py`: writes `Zkc/Frontend/Syntax/UnicodeData.lean` from the
  Unicode data pinned in `unicode/`; with `--check`, which `just check` runs, it refuses a
  table that differs.
- `scripts/replay_derived_schnorr.py`: the independent replay of the derived Schnorr proof, which
  the tests of the frontend run.
