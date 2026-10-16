# Finite computations

Finite computation retains an ordered domain and statically referenced helpers
in the existing [mathematical profiles](protocols.md). Its executable counterpart
uses [Local control](control.md). A preparation descriptor is not a native value
or an executable callback.

Shape and bound premises use the [shared mathematical fact
contracts](../domains/mathematical-facts.md). Exact origins, selected axes and
scope remain part of every fact; equal shape does not identify two containers.
Ordered domain admission remains authoritative even when result cardinality is
known independently.

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

Collection element, rank and intrinsic extent queries use the structural
[`CollectionTypeInterface`](iteration.md). The interface does not widen domain,
fold, collect or bounded-access admission: in particular, fixed vectors do not
gain finite-operation permission. Type-guaranteed extents for field arrays and
fixed vectors remain distinct from value-level evidence derived from admitted
constructors or helper premises. Such evidence can establish a bound or exact
collection cardinality without changing a vector into a field array, changing
a matrix's nominal family, or equating container contents. Field-array collection
still requires the exact output length and rejects filtering that cannot provide
that cardinality.

Bounds, containers and capture snapshots are computed by ordinary eager
operations at the call site. A descriptor cannot evaluate arbitrary expressions.
Every domain constructor is admitted in descriptor order before traversal,
including ignored zip factors and unused intermediate constructors. Independent
product admits all its factors even when another factor is empty. A nested finite
operation inside a helper is entered only when execution reaches that helper
operation; its checks and captures cannot be hoisted to an outer empty domain.

Domain constructors therefore expose conservatively unknown effects to MLIR
and no speculation interface. They are not `Pure` or `NoMemoryEffect`: generic
canonicalization and CSE must retain the complete constructor sequence, including
unused and equal-looking constructors, with its operands and returned descriptor.
Disabling speculation alone would still permit dead-code elimination. Unknown
effects preserve admission obligations without asserting heap allocation or
mutable mathematical data. A domain-aware rewrite needs separate justification
that it preserves complete ordered admission and the conditional entry of nested
computations; equality of the enumerated items alone is insufficient.

Cardinalities are natural numbers. Executable arithmetic must check representable
sizes and resource limits before multiplication can overflow. No wrapping count
or truncated zip is a valid realization. The current flattened Local recipe
applies the existing executable loop-bound admission to each product factor and
intermediate cardinality before multiplication. Range bounds receive that same
admission even for reversed or empty ranges. These resource checks can refuse
before traversal; bulk recognition preserves the original domain checks.

## Helper and operand ABI

Let `S...` be a state list, `C...` invariant captures, `B` a collected
item type, and `R` an explicitly selected native collection of `B`.
The state list may be empty, as when a source Unit state has no native leaves.
An ordered fold with no results still performs admission, predicates and steps;
its stops remain observable. Total folds retain all formation obligations even
when they have no result dependencies.

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

A Local fixed result is checked on its declaration's formal inputs. It cannot
use a range literal or dynamic-container count known only at one application.
Native static field-array extents survive this boundary; a source array lowered
to a dynamic Sequence does not carry its source length as a declaration fact.

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
accepts an `in_bounds` assertion. Their operation verifiers check local attributes
and types. The enclosing symbol closure establishes semantic bounds after helper
structure has been verified, including units without a finite computation.
Verifying an isolated access is therefore not whole-program admission. Private
helpers may declare parameter relations:

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

A finite callback's bound may refer to a captured container when a total
consumer proves its selected extent equals that of the domain container.
Local consumers retain exact domain-argument bounds; captures or carried state
do not acquire assumptions from type equality alone.

Extent analysis also recognizes an exact immutable `data.sequence_empty` /
`data.sequence_append` chain returned by an ordinary Math helper. This permits
fixed source-array adapters to retain their length evidence across calls without
changing the dynamic Sequence carrier. Exact unfiltered collection counts can
also supply extent evidence; filtered results normally supply only upper bounds.
Each finite admission or call-condition check shares a 65,536-step allowance
across forwarding, bounds, extents and cardinality queries. Helper observations
are cached within the immutable symbol closure. Fact extraction allows 256
interpretation frames, including actual/formal substitution; the independent
helper-closure admission limit remains 64 call levels.
An unknown producer or exhausted search gives no fixed extent;
no size annotation is trusted. Equal lengths still do not equate container values.

Static-reference cycle checks include ordinary calls, finite helper/predicate
references, nested finite computations and Math realizations. Whole-unit formation
precedes liveness and includes dead operations and polynomial observations reached
through the helper closure.

Finite operation verification separates local attributes/result shape from
referenced domain/helper ABI and premise checks. The latter use MLIR's
`SymbolUserOpInterface` and its supplied symbol-table collection; local operation
verification does not independently repeat that symbol traversal. Whole-unit
closure checking continues to own reference cycles and call preconditions.

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

The selector consumes a read-only computation view of actual typed domain,
helper, access, seed and capture SSA. Declaration-owned scalar/access laws state
exact nominal field/group premises; source annotations or matching function
names do not grant these laws. Recognition is independent of a physical provider
or a lane/reduction recipe. Private transformation recipes choose native
operations and operand permutations only after replacement eligibility is
established. Explicit implementation bindings retain their selected execution
path even when their mathematical meaning is known.

Before equation selection, total callbacks without a predicate may expand
ordinary helper calls under the shared optional structural allowance. A bounded
scan borrows call-free callbacks unchanged. Expanded callbacks live in a private
analysis scope that retains their own preconditions and gives the occurrence
fresh entry arguments with no caller-only premises. Matching and lane emission
borrow that body for its entire lifetime; original helpers and the independent
reader's source remain unchanged. Indexed reads inside ordinary helpers can
use the original callback's extent premises. The independent reader retains the callback's exact argument meanings throughout its call
closure and separately queries the existing Analysis fact service. Positional
substitution, including reordered, repeated and returned arguments, preserves
container and index identity. Equal extents never equate container elements.
The leaf helper need not receive the domain's anchor container. These facts
remain local to one source comparison; outer caller-only assumptions are not
imported. The reader also retains each admitted callee's own premises.

Each callback has a private ceiling of 8,192 optional structural work units,
within the cumulative stage allowance. The same envelope covers call discovery,
preparation and structural analysis, including call-free bodies. A memoized
preflight sizes the immutable helper DAG before copying. It charges inspection,
counts each call occurrence and intermediate call operation, and saturates above
the ceiling. A predicted expansion-size decline spends inspection work only;
actual copying remains charged when attempted. The cache is local to that
preflight. The ceiling limits one callback's structural interference, while
equation, evidence, lane and comparison limits remain separate. It does not
promise selection independent of callback order.

This preparation does not spend required helper-operation, helper-slot or
polynomial reserves. A capacity decline emits no diagnostic and retains ordered
execution; spent optional work is not restored on retry. Disabled bulk selection
skips preparation. Nested finite computations exposed by expansion, including
unused ones, also retain the ordered path and their conditional domain admission.
This selection step performs no dead-code or polynomial elimination. Field
reduction selection requires every payload instruction, including unused work,
to belong to its supported field/access formula. An unrelated total group
operation keeps the body ordered; a valid source must not become a failed
correspondence proposal because its selected comparison omits that algebra. Group
reduction selection likewise requires the scalar-ring/group-action fragment,
field-vector or group-vector element domains (possibly zipped), and
single-result helper calls. Extra indexed
work or multi-result group helpers remain valid ordered computations until the
independent group reader covers them. These are selection limits, not new source
admission rules.

Field-additive folds also compose supported pointwise bodies with native sum.
The pointwise expression must be independent of recurrent state and use the
same admitted field-vector domains and total field-ring operations as a
collection. Uniform terms are broadcast to the admitted cardinality; mixed
operations use scalar/vector recipes where available. Bounded indexed reads
retain their exact container provenance. Every domain,
including unused zip members, is admitted before payload work. The result adds
the original seed to the sum, including for an empty domain. Existing direct
reductions and contractions take precedence. This realization reuses vector
operations and the independent finite reader; it introduces no new operation or
runtime fallback. Intermediate vectors have the ordinary resource charges, so
ordered and bulk execution need not exhaust the same capacity.

The analysis retains all constructors in admission order separately from the
items of the returned descriptor, and retains every helper instruction even
when no bulk equation applies. Reduction, elementwise and bilinear selection
consume this common view through separate transient equation matches; the
structural record contains no selected strategy or operation name. Axis identity
includes the domain occurrence and coordinate. Exact input environments retain
domain inputs, seeds, items and invariant captures without substituting an
initial seed for recurrent state. Extent premises for optional selection come from
the source domain and admitted helper preconditions; occurrence-only evidence
that the independent reader cannot reconstruct retains the ordered realization.

Optional lane realization distinguishes a supported candidate, an unsupported
formula, and exhausted strategy capacity. The latter two outcomes emit no payload
or bindings and retain the checked ordered loop, including all domain admission.
In particular, exceeding Ring depth 1,024 does not make an otherwise admitted
Local collection invalid. Construction or correspondence errors are mandatory
failures; they cannot authorize publishing an unchecked candidate. Explicit map
realization, which requires its bulk implementation, reports a diagnostic when
that implementation is unavailable.

One Local preparation invocation shares realization work across helper, finite
and map realization: 1,000,000 optional lane work units, 100,000 expanded helper
operations, 1,000,000 helper operand/result slots, 100,000 polynomial expansion
units and 100,000 total finite expressions.
Lane work reserves eight units per operation, block argument and operand/result
slot before building or emitting its formula. These are compiler implementation limits,
separate from runtime resources and Ring's own admission bounds. Standalone
transform invocations start a fresh stage scope; an enclosing caller can supply
the shared context. Required helper expansion reports a capacity refusal.
Bound/extent queries made by the independent payload reader consume its enclosing
comparison budget rather than obtaining a fresh allowance for every query.
Required maps consume the shared helper-copy allowance, independently of optional
lane work. The staged ordinary-call expander retains its own cumulative
occurrence and work accounting. Diagnostic stage observations never reset either
context. A private candidate publishes only after its source/candidate reader
accepts; failure leaves the source and externally published occurrence state
unchanged.

Each finite declaration or total-expression check has a separate required-reader
allowance of 100,000 work units. Optional exact payload comparison receives at
most 100,000 units, capped by the required reader's remaining allowance without
spending it. A successful comparison may consume its final unit. Work or
representation exhaustion is distinguished from a correspondence mismatch.
On optional comparison exhaustion, the enclosing candidate is discarded and
retried once from the immutable source with finite bulk selection disabled.
The retry preserves spent optional recognition/lane work and reserves required
construction work for ordered execution. Declaration realization retries its
whole module; total-expression realization retries its selected calculations.
Already checked earlier stages remain unchanged. An observed mismatch fails
immediately. Required-reader exhaustion, or exhaustion of the ordered retry,
refuses with `finite-verification-capacity`; it never publishes unchecked IR.

Optional decision observations distinguish unsupported structure or equations,
missing extent/bound evidence, actual capacity failure, policy disablement,
replacement restrictions and unavailable recipes. A zero remaining allowance
does not by itself indicate failure. Recording an outcome must not spend
semantic work, change a reader's input, or supply a mathematical premise.
The record distinguishes selection, private proposal, discard, retry and
publication. Publication into a parent candidate does not imply installation
for the caller: a later refusal of that parent discards its incorporated work.
These observations have no authority in the independent correspondence check.

The independent reader reconstructs the source domain and payload and reads
actual candidate operands separately. It does not use the selector's classified
access map or emitter caches. The supported field-ring fragment admits
structural sharing, neutral elements, and associative/commutative addition and
multiplication; group/module contractions have a separate interpretation.
Ordered domain checks, helper closure, seed and result mappings remain separate
obligations. Unsupported ordered callbacks use the checked loop path.
Projection retains domain/helper declarations until total realization has
consumed their references. Multi-result folds preserve the complete state list.

A selected row or column contraction produces one scalar via `matrix.row_dot`
or `matrix.column_dot`. It does not materialize unrelated matrix outputs.
Supported collection of all row/column contractions uses one whole matvec,
inside a nonempty-outer branch. The empty branch returns an empty vector without
performing the inner fold's shape checks. A uniform nonzero seed is added to
each result. Both forms retain the corresponding source admission and field
interpretation.
This nested strategy covers the explicit outer matrix-index collection and
inner dot fold described in the [nested matrix collection contract](nested-matrix-collections.md).
Its conditional emitter and independent structural reader implement that
bounded equation, not an equivalence rule for arbitrary nested Local loops.
Bulk and loop realizations can consume different resources. Their value and
non-resource failure contract assumes sufficient resources; it does not require
identical exhaustion. Capacity checks must measure representative inputs, including
`2^17` items where bulk support is required. Raising the ordinary loop limit does
not establish a bulk realization. Independent formal models do not, by themselves,
establish a bridge to the native implementation.

The [handwritten controls](../../../compiler/test/fixtures/finite/README.md)
record the compiler and native test entry points.


## Preparation options

Default source preparation enables finite contraction and collection recognition.
`--no-finite-bulk` disables those selections and uses the checked loop path;
it does not disable domain admission or source/native correspondence checks.
`--no-simplify` independently controls generic total-expression simplification.
The separate `--fuse-vector-reductions` option controls explicit ring map plus
native sum fusion. These choices do not promise equal resource exhaustion: a large
computation can fit the default optimized path and exceed the unchanged execution
budget when run as a scalar loop.

The [nested matrix collection contract](nested-matrix-collections.md) specifies
the admitted whole-matrix rule and its conditional inner admission.
