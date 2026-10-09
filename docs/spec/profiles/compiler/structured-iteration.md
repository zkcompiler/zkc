# Structured values and iteration

This extension of [mathematical protocols](mathematical-protocols.md) retains one
SSA program with profiles `protocol → participant → exec → physical`.
It adds canonical data observations, copyable aggregates and bounded common
iteration. It does not infer equality between role components.

## Canonical data

The mathematical homogeneous containers have no encoding attribute:

| MLIR type | Logical executable identity |
|---|---|
| `ui64` | `index` |
| `tensor<?xui64>` | `indices` |
| `tensor<?x!algebra.field<F>>` | `vector:F` |
| `tensor<?x?x!algebra.field<F>>` | `matrix:F` |
| `tensor<?x!algebra.group<G>>` | `groups:G` |
| `tensor<Nx!algebra.field<F>>` | `field_array<F,N>`, including `N = 0` |

Storage layouts are physical choices. Matrix shape includes both dimensions
even when either is zero. Static arrays and
dynamic vectors have distinct complete identities; no implicit shape cast or
codec substitution equates them. Empty arrays are data, but cannot construct an
MLE or a coefficient polynomial. Those constructors still require positive sizes.

Products and sums reuse `!local.variant` and its canonical nominal descriptor.
One alternative is a product; multiple alternatives form a sum. Payload identity
includes nested field/group/container identities. Copy/drop/shared permission is
checked recursively over every alternative. A sum containing an affine payload
is not copyable, even when its currently selected alternative is empty.
Copyable variants are admitted at common/participant and program ports;
affine variants remain local. Availability is conservative for the whole value.
These permissions grant neither secrecy nor a wire codec.

The Data dialect owns total data operations. Its operands/results retain the
native total-payload policy; copyability alone does not grant mathematical
rewrites for tables or PCS objects. Existing checked local variant operations
can construct and eliminate copyable non-total payloads. The separate
[structured proof boundary](structured-proof-messages.md) supplies selected
aggregate codecs without widening total-operation admission.

The operations are:

- `data.index`: a canonical decimal string in `[0, 2^64-1]` to `ui64`.
- `data.index_equal`, `data.index_less`: comparisons of unsigned indices.
- `data.make`: inject exactly the selected alternative's typed payload.
- `data.get`: extract an in-range field from a **single-alternative** product.
- `data.is`: test one declared alternative without extracting its payload.
- `data.dim`: observe an in-range tensor axis, including a zero extent.

Sum elimination uses ordered `local.match`. Dynamic indexing, equal-length zip,
shape conversion and inverse remain checked local work unless a separate total
contract establishes their preconditions. No generic tensor operation gains
admission just because MLIR accepts its types. Preparation omits upstream tensor
canonicalization patterns that could change container identity.

Finite products cover heterogeneous and optional data, including matrices with
independent runtime dimensions. Runtime-length collections of such values use
[`data.sequence`](nested-data.md), with its element, permission and framing rules.

## Common iteration

`protocol.repeat` has one isolated, single-block body. Its operands are a count,
`N` initial carried values, and immutable captures; its results are the `N`
final carried values. The `carried` attribute is `N`; `roles` is a nonempty
subset of the enclosing protocol roles; `carried_roles` has one nonempty role
set for each carried value. `maximum` is in `[0, 1048576]`. `site` is unique
across the entire protocol, including nested regions.

The block receives induction `ui64`, carried values and captures, in that order.
`protocol.yield` returns exactly the carried types. The count is available at
every loop role; each action's roles are contained in the loop roster. Nested
repeats and static protocol applications are allowed. Application expansion
happens once and prefixes nested sites. No runtime iteration is unrolled.

For each role `a`, let `c_a` be its actual count component and `s_a` its initial
carried components. After validating `c_a ≤ maximum`, zero iterations return
`s_a`. Otherwise iteration `i` executes the body with induction `i` and the
previous yield, for `0 ≤ i < c_a`. The joint driver additionally requires all
participating counts to agree **before any body entry**. Availability or a shared
SSA spelling does not establish this agreement. A count may be received or
computed from an enclosing iteration; the normal action schedule establishes
when that component exists.

Each carried role set is an invariant checked on both initial and yielded
values. Yielding fewer available roles is refused. An affine carried output
must retain exactly its corresponding input root. Swapping two same-typed roots
is refused even though it would preserve their unordered set. Identity means the
root of the resource, not equality of its current state or generation. Local branches establish identity from every continuing arm; a local
loop establishes it separately for each carried slot, including zero trips.
A stop only removes continuation within that local execution. One role stopping
cannot make another role's common actions unreachable. Calls preserve these
rules under actual argument substitution. Unknown origins are refused where this
invariant is required; unrelated local programs need not preserve their input
roots. The bounded implemented transfer vocabulary belongs to the
[resource-origin analysis](../../../compiler/resource-origins.md).

Captures are immutable copyable values or an immutable alias of a one-owner
entry service port. A service reference cannot be carried, returned, selected or
sent. Child frames borrow the original endpoint lease; they neither acquire nor
clone authority. An affine token, in contrast, must be explicitly carried.

## Demand, projection and realization

Projection emits one executable `protocol.loop` per participating role, carrying
only its components. Pure expressions needed only inside the body remain inside
it, including computations derived from outer captures. They do not execute on
the zero path. Only their required outer leaves are captured. Ordered work
already executed before the loop retains its effects. Immutable captures that
are directly returned still need their values.

Formal polynomial degree requirements are validated in every nested block
before simplification, including unused observations. Loop metadata and lowering
postconditions retain count operands, captures, per-role carried ports, scoped
actions and yields. Depth is bounded to 64; common formation and projected
operation/port work have independent bounds. Runtime work and retained storage
remain separately bounded.

The native carrier count is `['value', ssa_name, maximum_decimal, induction_name]`.
It is admitted by `zkc.program/0`. This contract requires
value counts and refuses participant calls, parameters, family selectors,
participant `stop` and `incomplete` at **every nesting level**. Local stops
inside local computations retain their existing behavior.

The complete compact schedule and its independent admission rules belong to
[native joint execution](run.md#compact-iteration).
[Polynomial recipes](polynomial-recipes.md) provide the uniform residual state
used by dynamic-arity Sumcheck. No source-correspondence or cryptographic
security certificate follows from ordinary native admission.
