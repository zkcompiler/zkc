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
| What the project is | [README](../README.md) |
| What the current checkout supports | [Status](../docs/status.md) |
| Which document decides what | [Documentation index](../docs/README.md) |
| How to build and run the checks | [Development guide](../docs/development.md) |
| The exact rules of the source language | [Language reference](../language/README.md) |
| The exact semantics of the core language | [Core language specification](../docs/spec/core/README.md) |

## Submitting a pull request

Work happens on a branch and lands through a pull request; nothing is pushed
to `main` directly. Branch names are short and topical — `feat/…`, `fix/…`,
`docs/…`, `test/…`.

1. Run the checks that the change needs, as the
   [development guide](../docs/development.md) describes. Every change runs
   `just check`. A change to the Lean packages, the language reference, the
   libraries or the examples also runs `just test`, or the part of it that
   the change affects, locally. CI runs only `just check`; it does not build
   or test the Lean packages. State what you ran and its result in the pull
   request.
2. Open the pull request and write its title and body as described below.
   The [pull request template](PULL_REQUEST_TEMPLATE.md) gives the sections.
3. Respond to review on the branch. What review confirms is fixed in the
   same pull request rather than deferred to a later one.

Pull requests merge by squash. For a reviewed batch, constituent pull requests
may first merge into an explicit integration branch. One final pull request from
that branch to `main` carries the complete batch and its integration fixes. The
required CI check applies to that final candidate; merging into the integration
branch does not mean a package has landed on `main`.

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

- **Tests.** Test at the level the change acts: programs through the
  frontend's test driver for the source language, tests of the core for its
  definitions, and a negative test for every refusal a change introduces.
- **Semantics.** Update the owning document: the
  [language reference](../language/LANGUAGE.md) for the source language and
  the [core language specification](../docs/spec/core/README.md) for the core
  language. Keep the definition of a language and the coverage of its
  implementation distinct; do not weaken a definition to match a missing
  implementation. Record what is implemented in the
  [status](../docs/status.md).
- **Proofs.** A theorem does not use `sorry` or an axiom beyond Lean's three,
  and the imports between the libraries follow their rules; `just audit`
  checks both. State what a theorem covers in the guide of its package.
- **Formats and identities.** Version persisted or exchanged formats and
  cryptographic byte constructions. Before stabilization, all zkc-owned formats
  stay at version `0`, such as `zkc.core/0`. Publish a schema change in the
  owning specification with the change to its readers and writers. Maintain one
  current schema with exact shape and unknown-field validation; do not add
  compatibility readers. Exact subjects and digests identify the actual
  artifacts.
- **Diagnostics.** Rule identifiers are the stable surface and message prose
  is not, so a new refusal is asserted by a test that names the identifier.
- **Security rules and judgments.** Keep what a judgment rests on explicit.
  A citation is not a proof of what it cites, and a passing test is not a
  judgment.
- **External dependencies.** Pin exact versions in the file that owns them:
  `lean-toolchain` and the Lake manifest of a package, or the workflow for an
  action. Code adapted from elsewhere names its source in the file that holds
  it.
- **Libraries.** Reusable `.zkc` algorithms belong in `libraries/`; worked
  programs belong in `examples/`. Document a public module in
  [`CORE-LIBRARY.md`](../language/CORE-LIBRARY.md) or
  [`STANDARD-LIBRARY.md`](../language/STANDARD-LIBRARY.md), whichever owns it.
- **Documentation.** Update whatever the change makes wrong or incomplete, in
  the document that owns it, and keep `just check` passing.

Generated files and private development records are not committed.
