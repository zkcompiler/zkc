# Relation data and source Assets

Relation import captures domain data separately from the protocol that consumes
it. R1CS retains an exact field, sparse constraints and ordered public layout;
AIR retains trace expressions and row scopes. Neither is a universal protocol IR.
The [ingress guide](../compiler/relations.md) owns compiler adapters, and
[constraint semantics](../spec/domains/constraints.md) defines their meanings.

## Capture and bind

`.zkc` compilation accepts explicit `--asset=NAME=FORMAT=FILE` inputs, with
`r1cs-json`, `r1cs-binary`, `air-json`, `ring-json` and `relation-bundle-json`
formats. Bounded native readers validate the captured data, including unused
assets. File names locate input; canonical contents and layout identify the
relation. See the
[source profile](../spec/language/definitions.md#capture-and-names)
for the exact capture interface. Ring expressions and relation bundles are
named in source through
[asset domains](../spec/language/definitions.md#asset-domains-and-projections),
whose projections give libraries the asset's dimensions as static naturals.

A relation declaration binds a captured asset by name: `r1cs(asset name)`,
`air(asset name)` or `bundle(asset name)`. The asset fixes the signature. A
bundle's formals are derived from its public slots, tables and column groups,
one formal per slot, presence choice, height and group, each with the purpose
its authority implies; the
[protocol contract](../spec/language/protocols.md#bundle-declarations) defines
that derivation and what an assignment of the formals means.

Capture alone does not attach a relation to a protocol, add runtime inputs,
generate a prover or check satisfaction. Source relation declarations and their
actual application bindings select what a clause means. The
[relation binding guide](../compiler/relations.md) explains the retained
identity and argument checks.

## Use data through the native model

An authored protocol can use explicit matrix/trace inputs and installed kernels,
or a selected native relation adapter can produce mathematical MLIR. The bounded
[R1CS/Sumcheck adapter](../compiler/relations.md) makes its reduction
and terminal computation explicit. It has its own size and field restrictions.
It is distinct from merely importing a relation.

Imported coefficients, setup material and public statements require application
authority. Equal dimensions do not authorize replacing one relation or setup
with another. Setup integrity, source encoding adequacy and cryptographic security
remain separate obligations from parsing and execution.

[Maintained relation JSON](../../examples/relations/README.md) provides data
examples. The optional LLZK integration supplies a generic external relation
adapter.
