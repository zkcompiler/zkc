# zkc

zkc is a research compiler for zero-knowledge **protocols**: the layer above
relations, circuits, AIRs, and other arithmetized statements.

> **Current status:** active research snapshot. This repository is
> not a production release or a claim of general backend conformance.
> [Current Status](docs/status.md) is the coverage and evidence dashboard.

An authored protocol is elaborated into a common source. The
[compiler](compiler/README.md) imports it into registered MLIR dialects,
projects one program for each participant and selects a physical plan for each.
An executable [Lean reference](formal/README.md) checks the exported candidate
against the source, and the [native workspace](crates) executes the participants
over arkworks and Plonky3 backends. The model that these components share is
defined in the [documentation](docs/README.md) and the Lean library.

## Build and check

The [development environment](docs/development/README.md) pins LLVM/MLIR, Clang,
Rust, Lean, Python and their build tools with Nix on x86_64 Linux. CMake/Ninja,
Cargo, Lake and uv retain ownership of their builds and dependencies:

```sh
nix develop
just doctor
just setup    # explicit dependency downloads for development
just build
just demo     # generate development inputs, produce a proof, verify it separately
just test-harness  # quick configuration and test-runner checks
just test         # full main suite; requires at least 24 GiB RAM
```

`nix flake check -L` runs the main sandboxed packages and checks. The
[test guide](tests/README.md) identifies focused and optional scopes;
[maintenance](docs/development/maintenance.md) covers caches, CI, upgrades and rollback.
[The first protocol walkthrough](docs/getting-started.md) explains each demo
step and its limits. [Build and run](compiler/README.md) gives native commands.

## Read next

- [Documentation map](docs/README.md)
- [Compile and verify a protocol](docs/getting-started.md)
- [Project overview](docs/overview.md)
- [Architecture](docs/architecture.md)
- [Current Status](docs/status.md)
- [Roadmap](docs/roadmap.md)
- [Specification](docs/spec/README.md)
- [Example protocols](examples/protocols/README.md)
- [Example libraries and their clients](examples/libraries/README.md)
- [Contributing](.github/CONTRIBUTING.md)

## License

Licensed under the [Apache License, Version 2.0](LICENSE.md). Dependencies are
named in the manifests and pinned in the lockfiles; their terms stay with them.
