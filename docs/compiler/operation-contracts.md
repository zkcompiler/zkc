# Shared operation contracts

The installed catalog connects exact mathematical contract keys, typed MLIR
operations and physical implementations. Mathematical meanings belong in the
[domain specifications](../spec/README.md); selecting a kernel does not change
the field, operation or resource contract.

[Neutral declarations](../../compiler/include/zkc/Contracts/Declarations) own
logical signatures, requirements, static parameter schemas, type permissions and
installed facets. Language and IR adapters consume those records. Semantic
validators and backend implementations retain their separate obligations.

## Signatures, effects and observations

The `zkc.contract-declarations/0` inventory distinguishes constructor-application
ports from an explicit complete-Type port (`{"term": index}`). The latter is
restricted to construction-only observation payloads, with exact static-type and
representation checks. Source admission does not gain arbitrary operations from
catalog presence; the [structured observer](../spec/formats/messages.md#transcript-observation)
owns that boundary.

Declaration presence and authoring stage govern source availability. Semantic
facets govern sampling, history, guards and resources; source `stop` and `opaque`
allowances remain explicit. Catalog presence alone grants no purity, totality or
permission to reorder work. Language catalog identity uses
`zkc.language-catalog`; the [public interface overview](../status.md#current-public-interfaces)
identifies its consumers.

Operation facets identify actual sampling ports, provider successors, observation
payloads, history transitions, accepted guards and supported algebraic maps.
Analyses use only the installed facts they understand. An unknown operation has
no positive dependency or purity facts. A known state successor does not prove
sampling independence, and a transcript counterpart does not prove construction
security.

Replaying an operation adds an occurrence; common-subexpression elimination
removes one. Neither is licensed by the other's mathematical determinism. No
facet grants permission to discard failure, resource consumption, logical work
or a transcript occurrence. Partial operations remain ordered local work.

Polynomial interpretation conversions belong to `poly`: `point_to_vector`,
`point_from_vector`, `table_to_vector` and `table_from_vector`. Catalog keys such
as `vector.from_point` retain their declared meanings independently of IR spelling.
Coordinate order and Boolean-table shape remain domain obligations even when
representations share storage.

## Custody is independent of transport

Type properties distinguish copy/drop permissions, public codec values, private
immutable custody and affine resources. Public representability is not permission
to disclose a value. Unknown abstract kinds acquire no positive copy, drop or
transport permission merely because they are not recognized as affine.

Provider and capability tokens retain generation/use rules. Generic storage
release cannot discharge them. A copyable external transcript snapshot may still
participate in history-sensitive operations; copyability grants no motion across
those dependencies. Immutable prepared key material can be reused while each
invocation keeps its own setup authorization and runtime state.

Physical release uses discardability and the Runner's retained-value accounting.
A resource successor or alias must remain the actual value selected by control;
see [resource origins](resource-origins.md).

## Representation and assurance

Logical contraction interfaces identify operand/result roles after exact type
and contract checks. They select neither a backend nor storage layout.
[Physical planning](representation.md#checked-physical-decisions) separately
validates installed alternatives, conversions and all actual uses.

Compiler and runtime independently check their consumed contracts. Shared
schema data and matching signatures do not prove kernel correctness. Independent
Lean operation interpretations and sampling/locality laws apply to their named
models; extraction, native realization and security reductions need their own
connections. Use the [extension guide](../development/extensions.md#logical-contracts-and-source-exports)
when changing this boundary.
