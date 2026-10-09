# Compiler reference

The compiler takes checked `.zkc` source or direct mathematical MLIR through
`protocol → participant → exec → physical`, then exports `zkc.program/2`.
Start with the [pipeline](protocol-pipeline.md); the [implementation design](design.md)
assigns its internal responsibilities.

## Read by boundary

| Boundary | Guides |
|---|---|
| Source to mathematical IR | [Language](../language/mathematical.md), [relation ingress](relation-ingress.md) |
| IR formation and correctness | [Verification](ir-verification.md), [preservation](preservation.md), [validation evidence](foundation-validation.md) |
| Mathematics and realization | [Structured mathematics](structured-mathematics.md), [representation](representation.md), [operation contracts](operation-contracts.md) |
| Control and resources | [Local control](local-control.md), [resource origins](resource-origins.md), [Entry completion](entry-completion.md) |
| Data and composition | [Nested data](nested-data.md), [numeric state](composed-state.md), [mathematical composition](mathematical-composition.md) |
| Relation clients | [Bindings](relation-bindings.md), [native reduction and composition](relation-composition.md) |
| Proof construction | [Native proofs](native-proofs.md), [structured messages](structured-proofs.md), [public-coin analysis](public-coin.md) |
| Stateful proof execution | [Attempts](native-attempts.md), [authored transcripts](authored-transcripts.md) |

The [foundation boundary](ir-foundation.md) explains which general mechanisms
belong in the IR. [Runtime](../runtime/README.md) owns artifact use and Host
execution; [extensions](../development/extensions.md) explains contributor work.

## Meaning and evidence

[Refinement](../spec/verification/refinement.md),
[analysis](../spec/verification/analysis.md) and
[evidence judgments](../spec/verification/judgments.md) define the semantic
obligations. Native checkers recognize bounded relations over actual retained
subjects. Independent Lean proofs concern their specified models and do not
establish native compilation correctness. [Status](../status.md) records current
support and [assurance](../assurance.md) distinguishes these claims.
