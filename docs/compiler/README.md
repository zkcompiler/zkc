# Compiler reference

The compiler accepts checked `.zkc` source or mathematical MLIR and exports
`zkc.program/0`. The [pipeline](pipeline.md) explains representations and ownership;
[verification](verification.md) explains the comparisons performed before
publication.

| Responsibility | Guide |
|---|---|
| Profiles, dialects and lowering | [Pipeline](pipeline.md) |
| Formation and source-relative comparisons | [Verification](verification.md) |
| Algebra, polynomials and structured values | [Mathematics and data](mathematics.md) |
| Local control and participant completion | [Control](control.md) |
| Affine identity through branches and calls | [Resource origins](resource-origins.md) |
| Imported assets and relation bindings | [Relations](relations.md) |
| Derived and authored transcripts | [Construction](construction.md) |
| Verifier dependency analysis | [Public-coin views](public-coin.md) |
| Operation metadata and kernel selection | [Operation contracts](operation-contracts.md), [representation](representation.md) |

[Specification](../spec/README.md) owns exact rules; [native tests](../../tests/native.md)
own validation scope. [Runtime](../runtime/README.md) owns application execution.
The [C++ SDK](../../compiler/README.md) describes installed targets and APIs;
[extensions](../development/extensions.md) explains contributor work.
