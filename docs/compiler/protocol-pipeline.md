# Mathematical protocol pipeline

One mathematical program passes through four verified profiles. Direct MLIR and
checked `.zkc` source share this pipeline, executable format and Rust Runner.
The [mathematical profile](../spec/profiles/compiler/mathematical-protocols.md)
owns exact formation and projection rules.

## Representations and their consumers

| Profile | Meaning and consumers |
|---|---|
| `protocol` | Joint mathematical values, declared roles, explicit communication, services and relations; source analysis and preparation |
| `participant` | Each role's values and ordered actions, with actual receive results; participant simplification and proof construction |
| `exec` | Calculations at their demand sites and explicit local recipes; execution verification and physical planning |
| `physical` | Installed kernels, representations, conversions and storage handling; checked executable export |

The `plan` dialect's physical data wrappers do not provide a separate table/plan
executor. The [program profile](../spec/profiles/compiler/program.md) admits the
closed physical artifact as `zkc.program/0`.

## Preparation and projection

Language checks explicit modules, static applications, permissions and Entry
closure. Translation emits mathematical IR and independently compares it with
the checked source. The immutable original and interface retain logical schemas,
role availability, services and relation clause bindings.

Preparation expands supported static helpers and applications under bounded work.
It admits definitions before erasure and validates the actual expanded candidate.
Projection computes each role's values without adding communication. A receive
is a fresh role-local input even if the receiver already has a same-typed value.
[Participant generation](../rationale/participant-generation.md) explains this
restriction. Structured repetition preserves counts, captures, carried values,
ordered actions and dynamic occurrence coordinates.

## Mathematics and ordered work

Total mathematics stays in ordinary SSA so simplification can see dependencies.
[Flat mathematical SSA](../rationale/mathematical-ir.md) explains that choice.
Ordered local calls, service queries, guards and resource transitions retain their
execution order and failure behavior. Demand lowering realizes mathematics at
its consuming action; a kernel recipe must preserve its complete contract.

Physical selection chooses an installed implementation and inserts validated
conversions. Storage release respects copy/drop permissions and affine custody.
[Representation](representation.md) describes this boundary, and
[preservation](preservation.md) states the checks on actual materialized code.

## Construction and deployment

Native proof construction analyzes the retained common program and rewrites
unsimplified participant mathematics. It threads ordinary role-local transcript
state through the same profiles. The native
[proof contract](../spec/profiles/compiler/native-proofs.md) covers flat programs,
loops, PCS and structured messages within the participant profile.

A joint bundle adds a checked dispatch schedule and role layouts to the program.
A proof deployment binds producer/validator roles, public context, construction
and acceptance. An Entry package adds the source interface and named application
boundary. The Rust Hosts authenticate each publication and prepare inputs before
execution. See [runtime](../runtime/README.md).

## Semantic boundary

Each lowering has its own selected relation and premises. Generic MLIR legality
or retained origin metadata cannot establish source correspondence. The
[formal design](../../formal/design/semantics.md#interpretation-and-representations)
explains why mathematical interpretation is broader than a fixed compiler
pipeline.
Independent Lean models can specify obligations for these transitions; their
existing source/direct-plan theorems are not native implementation proofs.
