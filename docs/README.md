# Documentation

zkc has one supported implementation model: `.zkc` Language → mathematical MLIR
(`protocol`, `participant`, `exec`, `physical`) → `zkc.program/0` → the shared Rust
Runner, installed kernels and Entry/proof/joint Hosts. Direct MLIR authoring uses
that same pipeline. The independent Lean research library has its own semantic
subjects and proof boundaries.

## Reading routes

| Task | Route |
|---|---|
| Compile and run a protocol | [Walkthrough](getting-started.md) → [language](language/README.md) → [Entry execution](language/entries.md) |
| Understand the system | [Overview](overview.md) → [architecture](architecture.md) → [status](status.md) |
| Develop a component | [Development](development/README.md) → [compiler](compiler/README.md) or [runtime](runtime/README.md) |
| Study semantics and proofs | [Model guides](guides/README.md) → [specification](spec/README.md) → [formal support](../formal/SUPPORT.md) |
| Evaluate evidence or future work | [Assurance](assurance.md) → [roadmap](roadmap.md) |

The [maintained projects](../examples/projects/README.md) contain Schnorr and
Sumcheck clients. [Relation data](language/relations.md) enters through explicit
Assets or relation adapters. [Theory](theory.md) explains the mathematical tools
behind the model; [rationale](rationale/README.md) records consequential choices.

## Which document decides

`spec/` owns definitions, judgments and profile contracts. Its
[scope map](spec/README.md#adopted-scope) distinguishes current native contracts
from independently formalized models. [Status](status.md) owns implementation
support, [architecture](architecture.md) assigns responsibilities, and
[roadmap](roadmap.md) sequences remaining work. A theorem establishes its exact
proposition under its hypotheses; a correspondence claim must identify the
actual implementation to which it applies.

Build commands and maintenance belong in [development](development/README.md).
The [test guide](../tests/README.md) selects checks. Documentation changes follow
[the writing and placement guide](development/documentation.md) and the
[organization decision](rationale/documentation-structure.md). Review logs,
private research records and superseded guides do not belong in this reference.
