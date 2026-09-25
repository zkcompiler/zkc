# Contributing to zkc

Thank you for your interest in contributing. zkc is an early research
compiler for zero-knowledge protocols, and contributions of all kinds are
welcome — bug reports, tests, documentation, and code.

One thing to know before you start. Changes to protocol semantics, artifact
identity, and security claims carry more review than ordinary implementation
changes, because a mistake there is not a bug in a feature: it changes what
a sealed artifact means, or what a judgment is taken to have established.
The [change requirements](#change-requirements) below say what those changes
are expected to carry.

## Table of contents

- [Code of conduct](#code-of-conduct)
- [Where to look first](#where-to-look-first)
- [Submitting a pull request](#submitting-a-pull-request)
- [Commit and pull request messages](#commit-and-pull-request-messages)
- [Change requirements](#change-requirements)

## Code of conduct

Be respectful and assume good faith. Technical disagreement is welcome and
is settled against the specification and the evidence, not against seniority
or volume.

## Where to look first

| To find out | Read |
|---|---|
| What the project is and where it is going | [Project Overview](../docs/overview.md) |
| What the current checkout actually claims | [Current Status](../docs/status.md) |
| Which document decides what | [documentation authority map](../docs/README.md) |
| How to build and run the checks | [Development guide](../docs/development/README.md) and [test scopes](../tests/README.md) |
| Where documentation belongs | [Documentation guide](../docs/development/documentation.md) |
| The exact semantics of a surface | [Specification](../docs/spec/README.md) |

## Submitting a pull request

Work happens on a branch and lands through a pull request; nothing is pushed
to `main` directly. Branch names are short and topical — `feat/…`, `fix/…`,
`docs/…`, `test/…`.

1. Run the tests and lint checks affected by the change, using the
   [test guide](../tests/README.md#selecting-checks). Use `just test` for broad
   integration validation, not for every edit. Run optional suites when their
   integration boundary changes, and describe the checks actually performed.
   Automatic CI checks sources, formatting, documentation and the test harness.
   Full builds, Nix packaging and cross-language suites are separate manual
   workflow scopes. Run affected checks locally and record their results; see the
   [maintenance guide](../docs/development/maintenance.md).
2. Open the pull request and write its title and body as described below.
3. Respond to review on the branch. What review confirms is fixed in the
   same pull request rather than deferred to a later one.

Pull requests merge by squash.

## Commit and pull request messages

Because pull requests merge by squash, **the pull request title becomes the
commit subject on `main`, and the pull request body becomes the commit
message.** Write both for someone reading `git log` later.

### Format

Titles follow [Conventional Commits](https://www.conventionalcommits.org/):

```
<type>: <description>
```

The type is one of `feat`, `fix`, `docs`, `test`, `refactor`, `perf`,
`chore`, or `ci`. Scopes are not used at present; the component boundaries
are still moving, and an unstable taxonomy is worse than none.

Write the description in the imperative mood, so that it completes the
sentence *"applying this commit will …"* — `add the query phase`, not
`added the query phase` or `the query phase`. Keep it under about seventy
characters, lower case after the type, and with no trailing period. Name
what the change *is*; what it contains is the body's job.

### The body

Write prose first, then two bulleted sections:

- **Verification** — what was run and what it covered. Test counts and suite
  names are more useful than "tests pass".
- **Decisions** — the choices the change rests on, and why.

Do not hard-wrap lines in the pull request body.

Commit messages on a branch need only their subject line. The reasoning
belongs in the pull request body, which is what survives the squash.

## Change requirements

- **Tests.** Test at the level the change acts: tests through the tools for
  behavior, unit tests for the pure cores, and a negative test for
  every refusal a change introduces. A file in `compiler/test` is one test to
  CTest, so a bare `assert` ends it and hides every check after it. Where such
  a file walks a list of independent inputs, `with case(...)` from
  `support/cases.py` lets each one fail on its own and names it in the report.
  It is optional, and blocks that share state belong in one case. A Lean
  module whose entry point is `def run : IO Unit` has the same choice:
  `Tests.Checks` records a condition that does not hold and carries on, while
  a shape error stays fatal because there is no value to go on with.
- **Semantics.** Update the owning specification. `docs/spec/` describes the
  intended model and is not weakened to match what is built; what is built
  belongs on the [status page](../docs/status.md), not in the
  specification.
- **Carrier formats.** These may change freely at v0; a break
  is the norm rather than an event. What a change carries is that the
  compiler, the native workspace and the Lean reference move in the same
  change set, and that loading stays fail closed.
- **Independent implementations.** The compiler, the native runtime and the
  Lean reference admit the same carriers independently. A change to a surface
  they share moves all of them. Where they disagree, the specification decides.
- **Diagnostics.** Identifiers are the stable surface and message prose is
  not, so a new diagnostic is asserted by a test that names
  the identifier.
- **Security rules and judgments.** Keep what a judgment rests on explicit.
  A citation is not a proof of what it cites, and a passing test is not a
  judgment.
- **External integrations.** Pin exact sources in the manifest that owns them
  and state the adapter boundary. Code adapted from elsewhere names its source
  in the file that holds it. One reproduced run is not a conformance claim.
- **Documentation.** Update whatever the change makes wrong or incomplete,
  in the [document that owns it](../docs/development/documentation.md). A design choice that a reader could reasonably
  have made differently gets a [rationale record](../docs/rationale/README.md)
  only when its reason does not fit beside the definition; that page states
  what a record contains and what it never contains.

Generated files and private development records are not committed.
