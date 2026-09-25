# Working on zkc

If `AGENTS.local.md` exists, read it for additional local instructions.

## Project context

- Follow [the contribution guide](.github/CONTRIBUTING.md) for repository changes.
- Use [the documentation index](docs/README.md) to find relevant documents.
  `docs/spec/` defines semantics; `docs/status.md` records implementation support.
  Research notes provide context, not specification. Read what the task needs.

## Development

- Write code, comments, and technical documentation in English.
- Use descriptive names in shipped code and documentation, without internal
  task numbers or research shorthand.
- When upgrading dependencies, prefer current stable releases unless a concrete
  compatibility constraint prevents it. Existing pins are revisable; record
  selected versions in the owning manifests. Avoid unrelated upgrades.

## Validation

- Use [the development guide](docs/development/README.md) for builds and
  [the test guide](tests/README.md#selecting-checks) to select affected checks.
- `just test` includes expensive resource-boundary cases. Use it for broad
  integration validation, not every edit. Expand or repeat checks when changes,
  failures, or unresolved concerns justify it.
