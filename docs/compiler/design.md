# Compiler implementation design

The [pipeline](protocol-pipeline.md) uses one mathematical MLIR program and the
closed executable model. The [architecture owner map](../architecture.md#implementation-owners)
locates installed components; this page explains their internal boundaries.

## Representation and dialects

`protocol` owns role interfaces, availability, messages, services, repetition and
completion. `local` owns ordered algorithms, calls and structured control.
`algebra`, `poly`, `data`, `oracle`, `pcs` and `crypto` retain their domain meanings
and installed operation contracts. `relation` stores structured declarations and
R1CS/AIR assets. Physical types and bindings use `plan` without introducing a
second execution engine.

Mandatory verifiers belong to IR and remain usable without compiler workflows.
Translation owns Language emission/comparison, relation import and executable
export. Program owns the MLIR-free executable structure, codec and admission.
Transforms owns preparation, projection, demand lowering and representation
selection. Compiler composes these into complete Entry, bundle and proof
compilations; drivers only parse requests and publish results.

## Checking and invalidation

A mutable MLIR object has no permanent verification fact. Reverify changed IR,
recompute affected analyses and compare actual candidates against retained input.
A source location or copied origin locates an occurrence; it does not establish
that the occurrence has the correct operand or effect.

[IR verification](ir-verification.md) checks formation.
[Preservation](preservation.md) checks selected adjacent relations through the
emitted program, schedule and deployment maps. Unknown rewrites can refuse even
when mathematically equal. Checkers need an independent comparison procedure;
reusing the producer's emission routine alone cannot detect its mistakes.

## Operations and implementations

[Operation contracts](operation-contracts.md) own type, effect, resource and
representation facts. Mathematical recipes and installed kernels have distinct
roles: a total expression may need a guarded ordered realization, while a kernel
can be meaningful only for a bounded capacity or representation.

Target selection validates every chosen implementation, conversion and actual
result use. It does not authorize changing the field, transcript suite, relation
or application setup. [Representation](representation.md) owns these decisions.
General algebra and bulk kernels remain reusable across protocols; application
algorithms belong in source libraries or transparent local bodies.
