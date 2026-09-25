# Documentation

zkc compiles proof protocols and connects their implementations to explicit
semantic contracts. These documents explain the project, how to work on it,
what the implementation supports, and the model used to judge it.

## Start with your task

| You want to… | Read |
|---|---|
| Understand the problem and approach | [Overview](overview.md), then [architecture](architecture.md) |
| Compile and run a first protocol | [Walkthrough](getting-started.md), then [source notation](language/reference.md) |
| Author a reusable protocol library | [Source projects](language/projects.md), [checked interfaces](language/components.md#checked-interfaces-and-static-components) and [example clients](../examples/projects/README.md) |
| Build or develop the repository | [Development guide](development/README.md), [configuration](development/configuration.md) and [repository layout](development/layout.md) |
| Select and interpret checks | [Test guide](../tests/README.md) and [assurance](assurance.md) |
| Assess current capabilities and limits | [Implementation status](status.md), then [remaining work](roadmap.md) |
| Read the mathematical model | [Specification](spec/README.md), [PIR guide](guides/protocol-model.md) and [theory](theory.md) |
| Use the Lean library independently | [Formal package](../formal/README.md) and its [support map](../formal/SUPPORT.md) |
| Interpret a performance result | [Benchmarks](../bench/README.md) and the linked campaign's comparison conditions |
| Extend dialects, passes or backends | [Implementation maintenance](development/extensions.md) |
| Maintain dependencies or CI | [Maintenance guide](development/maintenance.md) |
| Contribute code or documentation | [Contribution guide](../.github/CONTRIBUTING.md) and [documentation guide](development/documentation.md) |

## Reading routes

- **Protocol authors:** [walkthrough](getting-started.md) →
  [language](language/README.md) → [library projects](language/projects.md) →
  [runtime inputs](runtime/inputs.md).
- **Compiler and backend contributors:** [architecture](architecture.md) →
  [compiler pipeline](compiler/protocol-pipeline.md) →
  [compiler reference](compiler/README.md) or [runtime reference](runtime/README.md) →
  [extension guide](development/extensions.md).
- **Formal and research readers:** [model guides](guides/README.md) →
  [specification](spec/README.md) → [correspondence maps](spec/correspondence/core.md)
  and the [Lean support map](../formal/SUPPORT.md).

## Reference by subject

| Area | Responsibility |
|---|---|
| [Language](language/README.md) | Protocol authoring, types, static components, projects and compiled relations |
| [Semantic guides](guides/README.md) | Execution, observations, contracts, composition, properties and contrasting protocol interpretations |
| [Compiler](compiler/README.md) | Retained source, IR, analyses, construction, transformation and lowering |
| [Runtime](runtime/README.md) | Execution, backend integration, artifact consumption and concrete formats |
| [Specification](spec/README.md) | Normative definitions, judgments, failure behavior and implementation discretion |
| [Theory](theory.md) | Mathematical methods, primary references and where their laws apply |
| [Formal package](../formal/README.md) | Lean definitions, proofs, executable tools and independently resolved integrations |
| [Rationale](rationale/README.md) | Consequential design choices, alternatives and reopening conditions |

A theorem establishes its exact proposition under its hypotheses; an adapter
identifies the actual source or implementation to which it applies. The
[assurance map](assurance.md) separates proofs, checker results, implementation
trust and bounded measurements. [Status](status.md) states what is implemented.

## Which document decides

`docs/` and root `formal/` define the model. Normative definitions live in
`spec/`; the [specification index](spec/README.md#adopted-scope) lists their exact
scope, and the domain chapters explain their use. The [status page](status.md)
distinguishes model coverage from native support. The
[organization decision](rationale/documentation-structure.md) explains the layout.

Review, research and planning records are development notes and stay outside
this reference. A finished study reaches it as the design it produced, with a
[rationale record](rationale/README.md) where a choice needs one.
