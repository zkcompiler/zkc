# Structured values and iteration

This extension of [mathematical protocols](protocols.md) retains one
SSA program with profiles `protocol → participant → exec → physical`.
It adds canonical data observations, copyable aggregates and bounded common
iteration. It does not infer equality between role components.

## Canonical data

Logical collections have dedicated nominal MLIR types:

| MLIR type | Logical executable identity |
|---|---|
| `ui64` | `index` |
| `!algebra.indices` | `indices` |
| `!data.bytes` | `bytes` |
| `!algebra.field_vector<"F">` | `vector:F` |
| `!algebra.field_matrix<"F">` | `matrix:F` |
| `!algebra.group_vector<"G">` | `groups:G` |
| `!algebra.field_array<"F", N>` | `field_array<F,N>`, including `N = 0` |
| `!algebra.fixed_vector<T, N>` | `fixed_vector<T,N>`, with `T` encoded recursively |
| `!data.sequence<T>` | `sequence<T>`, with `T` encoded recursively |

Storage layouts are physical choices. Matrices have row then column axes,
including when either extent is zero; sparse storage does not change rank.
Vectors, matrices, indices and bytes have runtime extents. Field arrays and fixed
vectors retain their length in type identity. Learning a vector's length or a
matrix's dimensions cannot change its nominal family, logical encoding or codec
permission. There is no builtin tensor compatibility alias for these types.
Empty field arrays are data, but cannot construct an MLE or a coefficient
polynomial. Those constructors still require positive sizes.

`CollectionTypeInterface` describes only collection kind, element type, rank
and type-guaranteed extents. Field vectors/arrays derive their field element
from the domain; group vectors derive their group element; indices use `ui64`.
Matrices have rank two and the other collection families have rank one. Nested
elements do not flatten rank: a sequence of matrices is a rank-one sequence.
An unknown extent is distinct from zero. An out-of-range extent query returns no
extent; callers must check rank before interpreting an axis. Only field arrays
and fixed vectors provide intrinsic exact extents.

Interface membership does not authorize finite iteration, mathematical
operations, Copy/Drop, wire encoding or physical implementation. Each operation
retains its admitted family set, and Contracts/profile checks retain permission
authority. Source `[T; N]` remains a structural array with its existing flattened
ABI; it is distinct from both nominal field arrays and fixed vectors.

Products and sums reuse `!data.variant` and its canonical nominal descriptor.
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
[structured proof boundary](../formats/messages.md) supplies selected
aggregate codecs without widening total-operation admission.

The operations are:

- `data.index`: a canonical decimal string in `[0, 2^64-1]` to `ui64`.
- `data.index_equal`, `data.index_less`: comparisons of unsigned indices.
- `data.make`: inject exactly the selected alternative's typed payload.
- `data.get`: extract an in-range field from a **single-alternative** product.
- `data.is`: test one declared alternative without extracting its payload.
- `data.dim`: observe an in-range axis of a field vector, group vector, indices,
  field matrix, field array or bytes, including a zero extent. Sequences and fixed
  vectors do not gain admission through the collection interface.

Sum elimination uses ordered `exec.match`. Dynamic indexing, equal-length zip,
shape conversion and inverse remain checked local work unless a separate total
contract establishes their preconditions. Structural similarity and generic
tensor operations confer no mathematical admission. Shape evidence supplies
bounds under the admitted rules without changing logical collection identity.

Finite products cover heterogeneous and optional data, including matrices with
independent runtime dimensions. Runtime-length collections of such values use
[`data.sequence`](data.md), with its element, permission and framing rules.

Ordered collection folds and materialization use the [finite computation contract](finite.md).

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
[resource-origin analysis](../../compiler/resource-origins.md).

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
[native joint execution](../runtime/joint.md#compact-iteration).
[Polynomial recipes](polynomials.md) provide the uniform residual state
used by dynamic-arity Sumcheck. No source-correspondence or cryptographic
security certificate follows from ordinary native admission.
