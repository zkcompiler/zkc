# Examples

| Directory | Contents |
|---|---|
| [Projects](projects/README.md) | Runnable applications of the maintained source libraries, with concrete Entries and invocation inputs |
| [Relations](relations/README.md) | Small external R1CS and AIR assets for relation ingress |

Reusable algorithms live in [`libraries/`](../libraries/README.md). Projects
show how to choose and run them; there is no separate protocol example catalog.
Data used by only one project belongs with that project.

Compiled MLIR, Entry packages, proofs and execution reports are generated into
build or temporary output directories. The current project JSON files contain
application inputs, not compiler output. The [walkthrough](../docs/getting-started.md)
explains their use. Compiler and runtime edge cases belong in tests.
