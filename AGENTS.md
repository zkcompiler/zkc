# Working on zkc

Read `AGENTS.local.md` if present.

## Project context

- Follow [the contribution guide](.github/CONTRIBUTING.md) for repository changes.
- Use [the documentation index](docs/README.md) to find relevant documents. `language/` defines the source language; `docs/spec/core/` defines the core language. `docs/status.md` records implementation support. The guides of the Lean packages describe the implementation. Research notes provide context, not specification. Read what the task needs.

## Code navigation

- For structural searches, use ast-grep.
- For symbol navigation in Python, use LSP; fall back to Serena.
- For Lean navigation and proofs, use lean-lsp-mcp (`lean-lsp`); use the installed `lean4` skill for proof development, review, and build diagnosis.

## Development

- Write code, comments, and technical documentation in English.
- Use descriptive names in shipped code and documentation, without internal task numbers or research shorthand.

## Validation

- Use [the development guide](docs/development.md) for the layout and the commands: `just build`, `just test`, `just audit` and `just check`.
- `just check` needs no build and is what CI runs. `just test` is expensive; choose the validation scope to suit the change.
- For Lean development, start with focused checks and incremental builds. Reuse valid results and avoid redundant checks; run expensive integration checks after changes stabilize, and repeat validation when relevant changes, failures, or unresolved concerns justify it.
