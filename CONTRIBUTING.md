# Contributing

zkc is an early research compiler. Focused issues and pull requests are
welcome, but protocol semantics, artifact identity, and security claims require
more review than ordinary implementation changes.

## Before starting

- Read the [Project Overview](docs/overview.md),
  [Current Status](docs/status.md), and
  [documentation authority map](docs/README.md).
- For a substantial feature, format change, or protocol-family addition, open
  an issue first so its boundary and evidence burden can be agreed.

## Build and checks

Use the public workflow in [Getting Started](docs/getting-started.md). Before a
pull request, run:

```sh
cmake --build --preset ci --target check-zkc
uv run --locked --project reference python -m oracle.model
```

Document any unsupported test or environment difference. A passing bounded
fixture must not be described as general protocol or backend support.

## Change requirements

- **Semantics:** update the owning specification and add positive and
  fail-closed negative tests.
- **Artifact or registry formats:** preserve canonical encoding and identity
  rules, update both implementations where applicable, and follow the
  versioning policy.
- **Diagnostics:** use the allocated diagnostic namespace and test the stable
  identifier rather than incidental prose.
- **Security rules or judgments:** keep assumptions, notion, track, source
  annotations, bindings, and derivation evidence explicit.
- **External integrations:** pin exact sources, state the adapter boundary,
  update [THIRD_PARTY.md](THIRD_PARTY.md), and avoid turning one reproduced run
  into a conformance claim.
- **Documentation:** put current claims in `docs/status.md`, future work in
  `docs/roadmap.md`, and exact semantics in `docs/spec/`.

Keep unrelated cleanup out of a semantic change. Generated files and private
development records should not be committed.

## Licensing

Unless explicitly agreed otherwise, contributions are submitted under the
project's Apache-2.0 license. By submitting a contribution, you represent that
you have the right to do so and that any third-party material is clearly
identified with compatible provenance and notices.
