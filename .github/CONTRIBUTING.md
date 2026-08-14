# Contributing

zkc is an early research compiler. Focused issues and pull requests are
welcome, but protocol semantics, artifact identity, and security claims
require more review than ordinary implementation changes.

## Workflow

- Every change lands through a pull request; nothing is pushed to
  `main` directly. Branch names are short and topical: `feat/…`,
  `fix/…`, `docs/…`, `test/…`.
- Pull requests merge by squash: one commit per pull request, and the
  PR title is that commit. Titles follow Conventional Commits —
  `type(scope): summary` — with types `feat`, `fix`, `docs`, `test`,
  `refactor`, `perf`, `chore`, `ci`, and the scope drawn from the fixed
  set below (or omitted when a change crosses several):

  | Scope | Owns |
  |---|---|
  | `carrier` | PIR/OIR dialects, encoding, identity, artifacts |
  | `kernel` | sealing and the protocol-kernel judgments |
  | `soundness` | the soundness kernel and signature |
  | `compiler` | the checked-search core and transform passes |
  | `exec` | the interpreter and execution profiles |
  | `emit` | the endpoint emitters and their runtime |
  | `oracle` | the Python reference twin |
  | `registry` | the registry JSON surfaces |
  | `spec` | the normative corpus under `docs/spec/` |
  | `docs` | non-normative documentation |
  | `ci` | workflows and repository process |

- One pull request is one implementation unit; when it grows past that,
  split it. Size is not the measure: a one-line process change is a unit,
  and several unrelated small changes are not.
- Review happens on the branch, and what it confirms is fixed in that same
  pull request. A defect found after the merge has already split the unit.
- CI must be green before a merge.
  [Getting Started](../docs/getting-started.md) describes the local
  build and checks.

## Before starting

- Read the [Project Overview](../docs/overview.md),
  [Current Status](../docs/status.md), and the
  [documentation authority map](../docs/README.md).
- For a substantial feature, format change, or protocol-family addition,
  open an issue first so its boundary and evidence burden can be agreed.

## Change requirements

- **Semantics:** update the owning specification and add positive and
  fail-closed negative tests.
- **Artifact or registry formats:** preserve canonical encoding and
  identity rules, update both implementations where applicable, and
  follow the versioning policy.
- **Diagnostics:** use the allocated diagnostic namespace and test the
  stable identifier rather than incidental prose.
- **Security rules or judgments:** keep assumptions, notion, track,
  source annotations, bindings, and derivation evidence explicit.
- **External integrations:** pin exact sources, state the adapter
  boundary, update [THIRD_PARTY.md](../THIRD_PARTY.md), and avoid turning
  one reproduced run into a conformance claim.
- **Documentation:** put current claims in `docs/status.md`, future work
  in `docs/roadmap.md`, and exact semantics in `docs/spec/`.

Keep unrelated cleanup out of a semantic change. Generated files and
private development records should not be committed.

## Licensing

Unless explicitly agreed otherwise, contributions are submitted under
the project's Apache-2.0 license. By submitting a contribution, you
represent that you have the right to do so and that any third-party
material is clearly identified with compatible provenance and notices.
