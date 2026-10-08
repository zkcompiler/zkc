# Project overview

zkc compiles proof protocols into participant programs. Its source makes local
mathematics, messages, randomness, resources and terminal checks visible in one
program. This gives analyses and transformations explicit operands and effects
instead of hiding a complete prover behind a library call.

## What is compiled

A relation specifies the statement and witness condition. A protocol specifies
the computation and interaction that establish a result about that relation.
The compiler handles the protocol. It can consume R1CS or AIR as relation data,
while protocols such as Schnorr can state their equations directly.

Authors write `.zkc` modules, reusable local functions and protocols, then select
an Entry with its participants, inputs, construction and result. The
[Schnorr and Sumcheck projects](../examples/projects/README.md) are maintained
examples. [Language](language/README.md) explains authoring, including explicit
relation Assets and installed mathematical kernels.

## One execution model

Language emits mathematical MLIR. The `protocol` profile carries joint structure
and participant availability. Projection forms independent `participant`
programs; `exec` makes demanded computation explicit; `physical` selects admitted
representations and kernels. The result is `zkc.program/1`.

Entry packages, native proof deployments and joint bundles give that executable
different application interfaces. All use the Rust Runner and installed backend
contracts. A proof validator executes independently with its public context and
proof bytes. A joint Host dispatches actual messages among participant runners.
[Architecture](architecture.md) and the [runtime guide](runtime/README.md) describe
the ownership and authority boundaries.

## Research and evidence

The Lean library independently formalizes execution, observations, refinement,
probability and selected protocol models. Formal laws help state what a compiler
transformation should preserve, including failed prefixes and residual state.
They do not automatically apply to a C++ transformation or Rust kernel with a
similar name. Native correspondence requires an explicit interpretation and a
proof or checker connection to the actual program.

Current compiler checks and runtime tests cover bounded native profiles.
Cryptographic security, source encoding adequacy, setup correctness and backend
implementation correctness remain separate claims. Consult [status](status.md)
for capabilities and [assurance](assurance.md) for evidence boundaries.

The [roadmap](roadmap.md) develops this model through general mechanisms and
independent validation. Retired applications and execution paths are available
in Git history; they impose no requirement to port their libraries, carriers or
compatibility behavior into the supported implementation.
