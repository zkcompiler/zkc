# The source language

This directory is the definition of the source language of zkc and what is checked against
it.

| Path | Content |
|---|---|
| [`LANGUAGE.md`](LANGUAGE.md) | the reference: lexical structure, grammar, static rules, elaboration to the core |
| [`CORE-LIBRARY.md`](CORE-LIBRARY.md) | the nine modules that the rules of the reference name |
| [`STANDARD-LIBRARY.md`](STANDARD-LIBRARY.md) | the libraries above them |
| [`conformance/`](conformance/README.md) | the tests that an implementation passes: each a program with its expected outcome |
| `conformance/independent/` | a second suite for the frozen layer, written from the reference alone by a reader who had seen no implementation: `cases/<id>/` and `expectations.json` |

The library in source is [`libraries/zkc/`](../libraries/zkc/) and the worked programs in source
are [`examples/`](../examples/), both at the root of the repository.

The language is designed in layers (`LANGUAGE.md` §0.1). The inner layer, layer A, is frozen
as the baseline of the implementation: its rules, the library and the programs that use only
it, and its tests change only by a clarification. The later layers are carried from the
earlier design of the language and are not frozen; each of their sections says so.

Run `just test-frontend` from the repository root to check parsing and canonical printing
of the libraries, examples and reference cases. The same command checks the diagnostics from
assembly and name resolution against the reference and exercises the typed protocol views.
Many negative cases need later phases to reach their expected refusal. The frontend driver checks names, instances, typing, packages and formatting, including the
independent conformance suite. Its commands are in the
[frontend guide](../lean/compiler/Zkc/Frontend/README.md).

`lake test` in `lean/compiler` selects the Core and vocabulary tests.
`just test-written-knowledge` also exercises the two supported source-to-theorem paths.
See the [development guide](../docs/development.md) for their scope.

The independent suite keeps the expectations with which it was written. Where a later
clarification of the reference changed an outcome, the frontend's harness lists the case and
the reason (`Zkc.Tests.Frontend.SyntaxHarness`).
