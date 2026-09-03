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
| How to build and run the checks | [Getting Started](../docs/getting-started.md) |
| The exact semantics of a surface | [Specification](../docs/spec/overview.md) |

## Submitting a pull request

Work happens on a branch and lands through a pull request; nothing is pushed
to `main` directly. Branch names are short and topical — `feat/…`, `fix/…`,
`docs/…`, `test/…`.

1. Run the checks in
   [Getting Started](../docs/getting-started.md#5-run-the-checks). They are
   what continuous integration runs, and the lints and format checks are
   part of that set — most red builds here are one of those rather than a
   failing test.
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

- **Tests.** Test at the level the change acts: lit tests for behavior
  through the tools, unit tests for the pure cores, and a negative test for
  every refusal a change introduces.
- **Semantics.** Update the owning specification. `docs/spec/` describes the
  intended model and is not weakened to match what is built; a gap between
  the two belongs in the [gap ledger](../docs/gap-ledger.md), not in the
  specification.
- **Artifact and registry formats.** These may change freely at v0; a break
  is the norm rather than an event. What a change carries is that the
  implementations and their goldens move in the same change set, and that
  loading stays fail closed. See
  [Versioning](../docs/spec/versioning.md).
- **The reference twin.** `reference/` is an independently written
  implementation, not a mirror to update mechanically. A change to a surface
  the two share moves both. Where they disagree, the specification decides,
  and the twin is as likely to be the one that is wrong.
- **Diagnostics.** Identifiers are the stable surface and message prose is
  not, so a new diagnostic is allocated and asserted by a test that names
  the identifier. [Versioning](../docs/spec/versioning.md) owns the
  allocation rules, and a lint enforces them.
- **Security rules and judgments.** Keep what a judgment rests on explicit.
  A citation is not a proof of what it cites, and a passing test is not a
  judgment.
- **External integrations.** Pin exact sources, state the adapter boundary,
  and update [THIRD_PARTY.md](../THIRD_PARTY.md). One reproduced run is not
  a conformance claim.
- **Documentation.** Update whatever the change makes wrong or incomplete,
  in the document that owns it.

Generated files and private development records are not committed.
