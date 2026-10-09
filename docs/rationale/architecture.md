# System boundaries

The [architecture](../architecture.md) places source checking and MLIR
transformation in C++, execution and backend integration in Rust, and independent
semantic models and proofs in Lean. The exported program is the compiler/runtime
boundary. Hosts own application authority, inputs and publication; the shared
Runner owns execution.

## Why this split

C++ gives the compiler direct access to MLIR's types, regions, analyses and pass
infrastructure. Moving compiler orchestration into another language would add a
boundary to ordinary compiler work. Requests and artifacts cross the component
boundary; individual optimization steps stay inside the compiler.

Rust gives the runtime typed integration with its selected cryptographic backends
and ownership tools for resource custody. A shared interpreter lets Entry, proof
and joint Hosts use the same admitted instructions and limits. A runtime callback
for each complete protocol would hide the operations that the compiler and
runtime need to inspect.

Lean models can state meanings independently of mutable compiler structures and
study proofs without becoming a runtime dependency. Their theorems apply to
their stated models. Connecting them to native code requires the explicit
[correspondence work](../assurance.md#6-native-correspondence-policy).

## Alternatives and cost

An all-C++ implementation would remove a language boundary but give up direct
Rust backend integration. A Rust compiler with a subordinate MLIR wrapper would
introduce bindings across the compiler's central transformations. Implementing
the whole compiler in Lean would also require an MLIR integration strategy and
an execution deployment model. None of these choices follows from a proof model.

The selected split costs separate builds and matching producers and consumers
of concrete formats. Shared contracts and independent admission checks manage
that cost. It makes no claim that Rust is faster, constant-time or correct by
language choice alone. A measured integration cost or a required backend can
justify revisiting the split.
