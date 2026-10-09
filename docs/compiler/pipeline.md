# Compilation pipeline

Checked `.zkc` source and direct mathematical MLIR use the same compiler,
executable format and Rust Runner. The [protocol contract](../spec/ir/protocols.md)
owns exact formation and projection rules.

## Profiles and dialects

| Profile | Retained meaning and consumer |
|---|---|
| `protocol` | Joint mathematics, declared roles, messages, services and relations; source analysis and preparation |
| `participant` | Each role's mathematics, actual receives and ordered actions; simplification and transcript construction |
| `exec` | Computations at demand sites and explicit local recipes; execution verification and physical planning |
| `physical` | Installed kernels, representations, conversions and storage; executable export |

Profiles constrain mixed-dialect programs. `protocol` owns interaction and role
interfaces; `local` owns ordered algorithms and control. `algebra`, `poly`,
`data`, `oracle`, `pcs` and `crypto` retain domain meaning. `relation` stores
declarations and R1CS/AIR assets. `plan` provides physical types and bindings.
It does not introduce a second executor.

Total mathematics stays in ordinary SSA so transformations can inspect
dependencies and sharing. Ordered queries, guards and resource transitions
retain their execution order. [Flat mathematical SSA](../rationale/mathematical-ir.md)
records the design choice. Availability, degrees, resource origins and schedules
are derived views of the same program.

## Preparation and projection

Language checks modules, static applications, permissions and Entry closure.
[Translation](../spec/language/translation.md) independently compares emitted
MLIR against checked source before simplification. The immutable original and
interface retain logical schemas, availability, services and relation clauses.

Preparation admits every original definition before erasure, expands supported
helpers and applications under [bounded work](../spec/ir/limits.md), and checks
the actual expanded candidate. Projection computes each role's values without
adding communication. A receive is a fresh role-local input even if the receiver
already has a same-typed value. [Participant generation](../rationale/participant-generation.md)
explains this restriction. Repetition retains counts, captures, carried values,
ordered actions and dynamic occurrence coordinates.

## Realization and publication

Demand lowering realizes mathematics at its consuming action. An ordered recipe
preserves its complete operation contract, including failure. Physical selection
chooses an installed implementation and validated conversions; storage handling
respects copy/drop permissions and affine custody. [Representation](representation.md)
describes selection and [verification](verification.md) describes the independent
comparisons of the actual candidate and emitted bytes.

Proof [construction](construction.md) rewrites unsimplified participant
mathematics and threads explicit transcript state through the remaining profiles.
A joint bundle adds a dispatch schedule. A proof deployment selects roles,
public context, construction and acceptance. An Entry package adds the named
source interface. Each [Host](../runtime/README.md) authenticates its artifact
and prepares actual inputs before execution.

## Implementation owners

| Owner | Responsibility |
|---|---|
| IR | Dialects, interfaces and mandatory verifiers usable without compiler workflows |
| Language | Source capture, resolution, typing and Entry closure |
| Translation | Source emission/comparison, relation import and checked executable export |
| Program | MLIR-free executable structure, codec and admission |
| Transforms | Preparation, projection, demand lowering and physical selection |
| Compiler | Complete Entry, bundle and proof compilations |
| Driver | Request parsing and publication |

The [architecture map](../architecture.md#implementation-owners) locates these
components. Mutable IR must be reverified after changes; affected analyses and
source-relative comparisons must be recomputed. A copied origin identifies an
occurrence without proving its operands or effects.

## Analysis boundary

Retain actual source operands, role-local receives, draw occurrences, resource
roots, ordered guards/stops, outputs and later disclosure. A loop occurrence
includes its iteration coordinates. [Public-coin views](public-coin.md) consume a
bounded part of this information. Honest delivery, independent randomness and
cryptographic assumptions are separate premises.

The [formal models](../../formal/docs/README.md) specify independent subjects and
laws. Applying them to this pipeline requires the explicit connection described
by [assurance](../assurance.md#native-correspondence).
