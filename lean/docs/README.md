# Formal reference

Start with [supported claims](support.md), [architecture](architecture.md) and the
[theorem ledger](../README.md#what-is-proved). Native contracts live separately in
[docs/spec](../../docs/spec/README.md). Research/design notes explain choices and
do not expand implemented support.

## Meaning and construction

- [Shared semantics](spec/semantics.md), [weakest preconditions](spec/weakest-preconditions.md)
- [Core language](spec/core-language.md): types, sides, dialects, side meaning and the `zkc.core/0` importer
- [Source construction](spec/source-construction.md) and [authoring](development/source-construction.md)
- [Structured source](spec/structured-source.md), [logical decoding](spec/structured-source-foundation.md)
- [Nominal data](spec/nominal-data.md), [numerical source](spec/numerical-source.md)
- [Components](spec/components.md), [fixed verification claims](spec/verification.md)
- [Logical contexts](design/logical-contexts.md), [structured computations](design/structured-computations.md)

## Mathematical libraries

- [Multilinear Sumcheck](spec/multilinear-sumcheck.md), [security](spec/multilinear-sumcheck-security.md), [base embedding](spec/sumcheck-embedding.md)
- [FRI security](spec/fri-security.md), [STARK components](spec/stark-components.md)
- [Fiat–Shamir](spec/fiat-shamir.md), [multi-round security](spec/fiat-shamir-security.md)
- [Table relations](spec/table-relations.md), [index services](spec/index-services.md), [uniform queries](spec/uniform-query-service.md)
- [Selected adapters](spec/selected-property-adapters.md), [ring expressions](spec/ring-expressions.md)

## Development and evidence

- [Declaration records](spec/declaration-records.md), [independent checking](development/independent-checking.md)
- [Module ownership](development/module-ownership.md), [dependencies](dependencies.md)
- [Lean toolchain adoption](development/lean-4.35-adoption.md), [component authoring](development/component-authoring.md)
- [Structured import design](design/structured-native-import.md)
