# Repository layout

| Directory | Responsibility |
|---|---|
| `compiler/` | C++ Language, mathematical MLIR, relation adapters, native compilation and installed SDK |
| `crates/` | Rust Runner, backend bindings, Entry/proof/joint Hosts and CLI |
| `examples/libraries/` | Maintained `.zkc` Schnorr and Sumcheck libraries |
| `examples/projects/` | Separately authored Entries and invocation inputs |
| `examples/relations/` | Relation data JSON |
| `formal/` | Independent Lean research library, model-specific tools and optional integrations |
| `tests/` | Native execution integration, installed consumers and documentation/build checks |
| `docs/` | Public reference, specification, support and development guides |
| `scripts/`, `nix/` | Workspace commands, environment and package ownership |

## Naming and dependencies

Use descriptive English names for source, comments and technical documents.
Do not put internal work identifiers in shipped APIs. A directory should have
one responsibility; common utilities belong below their consumers.

The [architecture owner map](../architecture.md#implementation-owners) identifies
Language, Relation, Program, IR, Translation, Transforms, Target and Compiler.
The exact exported graph lives in the compiler's CMake manifest and
[component reference](../../compiler/README.md#components-and-ownership). Runtime ownership is
separate from compiler implementation selection. Source Assets and installed
kernels remain general inputs to that graph.

## Build ownership

Native manifests own language dependencies, toolchain pins and component graphs.
Nix selects their environment and package composition; just forwards ordinary
commands. Keep generated output under configured build/report directories and
private research records outside the public reference. An independent formal
model need not be ported when a native component changes, and a native change
must not claim a formal result about a different representation.
