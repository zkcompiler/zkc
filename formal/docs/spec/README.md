# Formal model specification

This reference defines independent semantic models used by the Lean library.
It does not specify the native `.zkc` frontend or `zkc.program/0` interpreter.
Start with [conventions](conventions.md) for notation, finite execution scope and
conformance claims. Definitions and rules are normative within their premises;
examples are informative.

| Subject | Chapters |
|---|---|
| Complete execution | [Execution](core/execution.md), [iteration](core/iteration.md), [observations](core/observations.md) |
| Interpretation and contracts | [Interpretations](core/interpretations.md), [contracts](core/contracts.md) |
| Typed source and interaction | [Programs](language/programs.md), [inputs](language/inputs.md), [interaction](language/interaction.md) |
| Experiments and release | [Probability](properties/probability.md), [experiments](properties/experiments.md), [disclosure](properties/disclosure.md) |
| Concrete model choices | [Profiles](profiles/README.md): source, plans, realization, providers, Sumcheck and services |

Shared [domain objects](../../../docs/spec/README.md#mathematical-and-checking-contracts),
[relation terminals](../../../docs/spec/relations.md), [representation laws](../../../docs/spec/realization/representations.md)
and [validation judgments](../../../docs/spec/verification/judgments.md) retain one owner.
A profile fixes its actual parameters, vocabulary, interpretation and experiment;
its restrictions do not constrain every other profile.

[Support](../support.md) records established propositions and limits.
[Correspondence](../README.md#definitions-and-proofs) maps selected clauses to
Lean declarations. A generic obligation is not automatically a mechanized
theorem or an implementation guarantee. The [assurance policy](../../../docs/assurance.md)
governs those distinctions.
