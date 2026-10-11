# Finite computations

Finite computation retains an ordered domain and statically referenced helpers
in the existing [mathematical profiles](protocols.md). Its executable counterpart
uses [Local control](control.md). A preparation descriptor is not a native value
or an executable callback.

## Domain declarations

Domain formation is bounded to 1024 arguments/items, 4096 constructor-body
operations and constructor depth 64. Static reference closure is bounded to depth
64 and 100000 visits; dependency analysis uses a separate bounded work budget.
Exhausting analysis work refuses the input rather than asserting a result.

A private `data.domain` symbol has a `function_type` from native arguments
`A...` to one `!data.domain<I...>`. Its isolated single block has arguments
`A...` and returns a descriptor with `data.domain_yield`. Its complete body,
including unused intermediates, admits only these typed constructors:

| Constructor | Enumeration |
|---|---|
| `data.domain_elements(C)` | Stored positions of a vector, group vector, fixed field array, indices or sequence; duplicates are retained |
| `data.domain_indices(C) {axis}` | Indices of the selected explicit axis, with provenance to that exact container |
| `data.domain_range(lower, upper)` | Half-open unit-step index range; reversed bounds give an empty enumeration |
| `data.domain_zip(d...)` | Strict equal-cardinality zip, concatenating item parameters |
| `data.domain_product(d...)` | Independent Cartesian product, last factor varying fastest |
| `data.domain_matrix_row(M, r)` | Logical row in increasing column order |
| `data.domain_matrix_column(M, c)` | Logical column in increasing row order |
| `data.domain_matrix_coordinates(M) {order}` | The full logical rectangle, with explicit `row_major` or `column_major` order |

Zip and product require at least one factor. Matrix coordinates include sparse
zeros. Row and column selectors are checked even when the other dimension is
zero. Fixed arrays remain native field arrays; other immutable element types
use their explicitly selected sequence representation.

Bounds, containers and capture snapshots are computed by ordinary eager
operations at the call site. A descriptor cannot evaluate arbitrary expressions.
Every domain constructor is admitted in descriptor order before traversal,
including ignored zip factors and unused intermediate constructors. Independent
product admits all its factors even when another factor is empty. A nested finite
operation inside a helper is entered only when execution reaches that helper
operation; its checks and captures cannot be hoisted to an outer empty domain.

Cardinalities are natural numbers. Executable arithmetic must check representable
sizes and resource limits before multiplication can overflow. No wrapping count
or truncated zip is a valid realization. The current flattened Local recipe
applies the existing executable loop-bound admission to each product factor and
intermediate cardinality before multiplication. Range bounds receive that same
admission even for reversed or empty ranges. These resource checks can refuse
before traversal; bulk recognition preserves the original domain checks.

## Helper and operand ABI

Let `S...` be a nonempty state list, `C...` invariant captures, `B` a collected
item type, and `R` an explicitly selected native collection of `B`.

| Computation | Inputs and outputs | Helper attribute |
|---|---|---|
| `algebra.finite_fold` | `(A..., S..., C...) -> S...` | `step` |
| `algebra.finite_collect` | `(A..., C...) -> R` | `body` |
| `local.finite_fold` declaration | Same fold signature | `step` |
| `local.finite_collect` declaration | Same collect signature | `body` |

Every computation has a static `domain` reference and an optional `predicate`.
Helpers use exactly these signatures:

```text
predicate(I..., A..., C...) -> i1
step(S..., I..., A..., C...) -> S...
body(I..., A..., C...) -> B
```

Algebra references defined private Math helpers. Local references defined
private Local helpers; a Math helper can be explicitly realized and called from
a Local wrapper. Local finite declarations implement the preparation callable
interface and are invoked through `local.apply`. An owned protocol occurrence
calls an ordinary Local wrapper through `protocol.local_call`.

The canonical operand partition does not reorder the operations that produced
those operands. Domain arguments and invariant captures permit Copy/Drop. Local
fold state follows ordinary carried-state ownership: every continuing transition
preserves the exact affine root in its corresponding state slot, and zero trips
return the original state. Total Algebra inputs, items, captures and results obey
the total-data policy. Declaration-specific Local admission does not weaken the
existing total `local.realize` or `algebra.map_realize` signatures.

Collection results are field vectors, group vectors, indices, immutable sequences,
or fixed field arrays with a proven exact cardinality. Filtering cannot justify
an exact fixed result size without additional evidence.

## Ordered evaluation

At a call, eager operands execute in authored order, followed by complete domain
admission. Each item then evaluates its predicate before the body or step. False
preserves state or appends nothing. Predicate and body stops propagate immediately;
no subsequent item is evaluated. An empty fold returns its initial state after
entry checks. All syntactic branches and helper intermediates still require
formation, even for empty domains and always-false predicates.

A materialized reducer is a collect followed by an ordinary call. The reducer
executes once, after every collected body has succeeded. It is not implicitly
streamed: a later map failure must precede a reducer failure that would have
occurred on the first item.

## Total bounds and formation

`data.bounded_at(container, index)` and
`data.bounded_matrix_at(matrix, row, column)` require checked provenance; neither
accepts an `in_bounds` assertion. Private helpers may declare parameter relations:

```mlir
data.preconditions = [#data.index_bound<indexArg, containerArg, axis>,
                      #data.equal_extent<leftArg, leftAxis, rightArg, rightAxis>]
```

Parameter positions are zero-based in the complete helper signature. Every call
must independently discharge them under argument substitution. Supported facts
include exact domain indices/coordinates, valid constants for fixed arrays,
forwarding, and verified equal extents. Equal extents transfer a bound, not element
identity. Bounds from `indices(xs)` do not authorize a distinct `ys`, an appended
successor, or a shifted index without further evidence. Dynamic total zip likewise
requires an equal-extent derivation; a Local runtime guard is not a Math proof.

Static-reference cycle checks include ordinary calls, finite helper/predicate
references, nested finite computations and Math realizations. Whole-unit formation
precedes liveness and includes dead operations and polynomial observations reached
through the helper closure.

Finite result dependencies close monotonically over repeated state transitions,
including initial state, cardinality, predicate and captures. A single-step summary
is insufficient for `(a,b) -> (b,item)`. Formation requirements remain separate
from result dependencies. Consumers that clone a complete operation retain all
operand dependencies until a checked decomposition supports narrower cloning.

## Realization and checking

Finite structure remains available through ordinary helper expansion. Recognizers
inspect helper bodies and native contract identities. A recognition miss uses
Local loops, branches and checked collection access; it cannot make a well-formed
Local expression illegal. Sum/product, dot, MSM and selected matrix contractions
retain every original domain admission check, including ignored zip factors.
Sparse-zero elision requires a mathematical contraction, not an arbitrary Local
callback with per-cell failures.

The producer and independent reader share structural recognition of the retained
helper syntax; the reader does not invoke the producer or trust a recognition
attribute. It checks the actual candidate operations, operand mappings,
entry checks, helper closure and state results. Equal symbol spellings alone do
not establish correspondence when a referenced body changed. Projection retains
domain/helper declarations until total realization has consumed their references.
Multi-result folds are checked and lowered as a complete state list.

Bulk and loop realizations can consume different resources. Their value and
non-resource failure contract assumes sufficient resources; it does not require
identical exhaustion. Capacity checks must measure representative inputs, including
`2^17` items where bulk support is required. Raising the ordinary loop limit does
not establish a bulk realization. Independent formal models do not, by themselves,
establish a bridge to the native implementation.

The [handwritten controls](../../../compiler/test/fixtures/finite/README.md)
record the compiler and native test entry points.
