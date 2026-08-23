# Stage 1 comparative case dossiers

> **Document kind:** Temporary research index and dossier template
> **Document state:** First Stage 1 portfolio complete
> **Provisional owner:** `project`
> **Authority:** None. Case studies provide design evidence and analogy limits;
> they do not select PIR architecture.
> **Disposition:** Preserve only reviewed cross-case rationale in durable
> decisions, then delete this directory with the Stage 1 package.

> **Completion note — 2026-08-22:** The portfolio fed the completed
> [candidate instantiation](../candidate-instantiations.md),
> [scenario evaluation](../scenario-results.md), and
> [convergence record](../convergence.md). It remains comparative evidence,
> not architecture authority.

## Purpose

This directory holds representative case studies selected by architectural
pressure. It is not an ecosystem catalog, compatibility matrix, or ranking.

## Required dossier structure

Each dossier should use this structure when applicable:

```text
scope and exact questions
source set and evidence limits
semantic subject and explicit non-subjects
original goals and consumers
authoring, internal, canonical, and interchange forms
validation and admission
identity and canonicalization
text, binary, schema, and semantic versioning
extension and unknown-content policy
dialect or abstraction-level decomposition
legal mixed-form states and conversion boundaries
effect, state, order, and target-environment representation
transformation and preservation model
composition and dependency model
independent implementation or formalization boundary
strengths supported by evidence
pain points supported by evidence
installed-base constraints
counterfactual inference
PIR-transfer hypotheses
analogy limits
primary references
```

Use explicit prefixes where prose could blur authority:

```text
Source fact
Implementation observation
Historical report
Design inference
PIR transfer
Analogy limit
```

## Active portfolio

| Dossier | Cases and architectural pressure | State |
|---|---|---|
| [Portable semantic and interchange IR contracts](portable-ir-contracts.md) | StableHLO/VHLO, SPIR-V, ONNX: stable subset, portable artifact, compatibility, validation environment, extension authority | First pass complete |
| [Multi-level MLIR compiler architectures](multilevel-mlir.md) | CIRCT, IREE, upstream MLIR: dialect granularity, mixed forms, progressive and irreversible lowering, mechanism limits | First pass complete |
| [Long-lived IR contracts](long-lived-ir-contracts.md) | LLVM, WebAssembly, SPIR-V: semantic evolution, text/binary promises, environment, difficult legacy decisions | First pass complete |
| [ZK and proof-adjacent IR boundaries](zk-proof-adjacent-irs.md) | LLZK, CirC, ACIR/Brillig, Sierra/CASM, AIR, zkInterface/R1CS, I-R1CS: relation, witness, protocol, and backend binding time | First pass complete |
| [Protocol semantics and transformation theory](protocol-semantics-theory.md) | Interaction, Fiat--Shamir, transcript framing, ordered effects, trace relations, projection, translation validation | First pass complete |
| [Current zkc Protocol IR correspondence](current-zkc-correspondence.md) | Specifications, source, tests, authority seams, and feasibility constraints | First static pass complete |
| [First-wave cross-case synthesis](../cross-case-synthesis.md) | Shared pressure matrix, conflicts, non-transfers, open hypotheses, refined candidate axes, and candidate consequences | First pass complete |

A weakly documented or redundant case should be removed. A new case is added
only when it contributes a distinct pressure or mechanism.
