# Shared operation contracts

The installed catalog connects exact mathematical contract keys, typed MLIR
operations and physical implementations. Mathematical meanings belong in the
[domain specifications](../spec/README.md); selecting an implementation does not
change the field, operation or resource contract.

[Neutral declarations](../../compiler/include/zkc/Contracts/Declarations) own
logical signatures, requirements, static parameter schemas, type permissions and
installed facets. Language and IR adapters consume those records. Semantic
validators and backend implementations retain their separate obligations.
Ordinary library declarations own public function names and argument names.
The generated inventory exports types and capabilities; it does not duplicate
source function APIs or turn installed operations into implicit imports.

## Execution ownership

The same operation has three distinct sets of obligations. Existing binding and
invocation records carry them; no separate contract registry is needed.

| Boundary | Owner and checked facts |
|---|---|
| Logical operation | Declarations and IR admission: exact domains, ports, parameters, effects and mathematical laws |
| Selected implementation | Checked physical plan and independent runtime installation: implementation identity, physical ports and fixed application choices |
| Reached invocation | VM and provider: actual operands, frame, role, site, remaining allowances, retained backing and current resource/setup authority |

| Fact or obligation | Existing carrier and lifetime |
|---|---|
| Nominal domain, ports and mathematical laws | `OperationContracts`, logical types and admitted `BindingApplication`; stable declaration facts |
| Representation and fixed implementation | `PhysicalPlan`, selected binding and `BoundSignature`; checked against the actual materialized call |
| Immutable dependencies | Source SSA/helper closure and exact static application attributes; compiler analyses expire when either changes |
| Installed code | `InstalledOperation`; linked against the instance's owned backend, with no captured frame or resource authority |
| Role, site, origin and ordered operands | `CallContext` and the active VM frame; derived at the reached invocation |
| Output allowance and retained backing | `Invocation`, VM storage accounting and provider value contracts; aliases retain their backing, fresh output consumes capacity |
| Setup authorization, capability generation and resource successors | Provider custody checks at use; a handle or cached validation result cannot replace them |

`plan.apply` represents an installed operation, which may have effects or fail.
The runtime's `InstalledOperation` establishes its signature and installation
facts. Neither grants purity or permits inspecting an operation's implementation
as if it were source mathematics. PCS, transcript and resource operations retain
their ordered invocation and provider-owned authorization checks.

The VM owns loading, frames, value retention, accounting and reached-call
preparation. The interpreter owns instruction walking, environments and control
provenance. Providers own representations, arithmetic and cryptographic resource
state; Hosts own application authorization, participant scheduling and acceptance.
See the [VM contract](../spec/runtime/vm.md).

Static structure is checked on admission, installed signatures on linking and
mutable authority at use. Shared immutable validation evidence can avoid repeated
structural walks; it cannot replace current custody checks. Compiler mathematical
rewrites use separate source/candidate comparisons and invalidate analyses when
the inspected IR changes.

## Mathematical meaning and realization

The mathematical declarations own stable identities, source intrinsic spellings
and the closed scalar/access laws consumed by the compiler. Generated typed
queries are shared by Language, IR and analysis. Exact nominal signatures
establish applicability: a group action uses that group's associated scalar
field, and checked index arithmetic acquires no field reassociation law.

`mathematicalMeaning` describes an identity without choosing an executable
operation. `admitMathematicalMeaning` checks a complete logical application,
including static arguments, ports and parameters. It can describe an explicitly
pinned operation without resolving its physical provider. Ordinary binding
admission still validates that provider, and `admitComputationContract` separately
requires eligibility for mathematical replacement.

Private [realization recipes](../../compiler/lib/Transforms/MathematicalRecipes.td)
associate these meanings with lane and reduction algorithms. Generation checks
endpoint signatures, domain mappings and operand order. For example, scalar
group action takes `(point, scalar)`, while MSM takes `(scalars, points)`.
Analysis keeps semantic operand roles; selection applies this permutation.
Removing a recipe leaves the meaning available and optional selection falls
back to ordered evaluation. Physical implementation choice remains a later step.

The independent correspondence reader consumes the original and proposed IR
and their admitted meanings. It does not use a recipe selection as evidence.
Generated declarations and signature checks do not establish kernel correctness.

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
Lean scalar interpretations and reached-query sampling laws apply to their named
models; extraction, native realization and additional security reductions need their own
connections. Use the [extension guide](../development/extensions.md#logical-contracts-and-source-exports)
when changing this boundary.
