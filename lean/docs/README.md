# Formal models

The Lean library defines independent models of execution, typed source,
transformations, probability and protocol properties. Their proofs concern the
exact subjects and hypotheses stated here. They do not establish correspondence
with native `.zkc`, MLIR or Rust execution.

## Reading routes

| Task | Reference |
|---|---|
| Understand the semantic model | [Model guides](guides/README.md), [theory](theory.md) |
| Read exact definitions | [Model specification](spec/README.md) |
| Find established propositions and limits | [Support](support.md) |
| Understand library structure | [Architecture](architecture.md) |
| Build or use Lean APIs and tools | [Formal package](../README.md) |
| Assess a native connection | [Connection boundary](native-connection.md), [assurance policy](../../docs/assurance.md#native-correspondence) |

## Definitions and proofs

`lean/docs/spec/` owns model-specific prose definitions. Shared mathematical
and representation laws remain in the [native/common specification](../../docs/spec/README.md#mathematical-and-checking-contracts).
[Support](support.md) owns theorem scope. Correspondence maps identify the exact
clause-to-declaration connections and remaining obligations:

- [Execution and observations](correspondence/core.md)
- [Programs, inputs and interaction](correspondence/programs.md)
- [Domains and source](correspondence/domains.md)
- [Transformations and judgments](correspondence/transformations.md)
- [Properties and release](correspondence/properties.md)
- [Realization and binding](correspondence/realization.md)

## Design and tools

Adopted choices are grouped into [semantics](design/semantics.md),
[analysis](design/analysis.md) and [observations](design/observations.md).
Maintained tool and application designs cover [artifact checking](design/artifact-reference.md),
[interactive references](design/interactive-reference.md),
[local control](design/local-control.md), [role execution](design/role-execution.md)
and [committed Sumcheck](design/committed-sumcheck.md).
The [theory chapter](theory.md#references) cites the methods used by these models.
Unadopted implementation proposals and review history are private research.
