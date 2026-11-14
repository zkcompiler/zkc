# Repository layout

| Directory | Responsibility |
|---|---|
| `compiler/` | C++ Language, Protocol IR, relation adapters, native compilation and installed SDK |
| `crates/` | Rust kernels, VM, interpreter, native bindings, Entry/proof/joint Hosts and CLI |
| `libraries/` | Reusable `.zkc` libraries, their public interfaces and protocol contracts |
| `examples/projects/` | Separately authored Entries and invocation inputs |
| `examples/relations/` | Relation data JSON |
| `lean/` | Shared formal documentation and tooling; no root Lake package |
| `lean/program/`, `lean/ir/`, `lean/protocol/`, `lean/verification/` | Independent semantic packages with a Program → IR/Protocol → Verification dependency diamond |
| `lean/adapters/arklib/`, `lean/adapters/clean/` | Pure upstream adapters |
| `lean/applications/` | Concrete clients downstream of Verification and the adapters |
| `lean/core/` | The re-founded core language and its tool; no Lake dependency |
| `lean/formal/` | Statements about admitted programs over the core's meaning, and their proofs; requires the core |
| [`common/`](../../common/README.md) | Shared build inputs and project-level validation |
| `common/unicode/` | Pinned source-name data and generation shared by C++ and Rust |
| `common/tests/` | Native execution integration, installed consumers and documentation/build checks |
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

Native integration clients live in `crates/zkc-test-drivers`;
[their manifest](../../crates/zkc-test-drivers/README.md) selects test providers.
The user CLI is built separately with default features.
The [Rust SDK guide](../../crates/zkc/README.md) owns embedding and generated bindings;
Python tools in the development environment own testing, compiler and research workflows.

## Build ownership

Native manifests own language dependencies, toolchain pins and component graphs.
Nix selects their environment and package composition; just forwards ordinary
commands. Keep generated output under configured build/report directories and
private research records outside the public reference. An independent formal
model need not be ported when a native component changes, and a native change
must not claim a formal result about a different representation.
