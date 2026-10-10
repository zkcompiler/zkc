# Common resources and tests

This directory contains shared build inputs and project-level validation.

- [Unicode](unicode/README.md) owns the source-name data, manifest and C++ generator consumed by the compiler and Rust tools.
- [Tests](tests/README.md) owns integration, cross-implementation, installation and development-tool checks, including their fixtures and harness.

Component-specific tests remain with the [compiler](../compiler/README.md), [Rust packages](../crates) and [Lean library](../lean/README.md). Native and shared contracts live in [the specification](../docs/spec/README.md); independent Lean model definitions live in [the Lean reference](../lean/docs/README.md).
