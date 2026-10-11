# Mathematical facts

The shared fact vocabulary describes exact value origins, selected container
extents, strict index bounds and collection cardinality. It supplies premises
for [finite formation](../ir/finite.md) and mathematical analysis. It does not
define another program representation or change a collection's nominal type.

## Subjects and premises

A fact belongs to one immutable source or SSA subject, including every helper
body inspected to derive it. An origin identifies an exact value and its full
projection path. Equal types, contents, lengths or source names do not establish
origin identity. A helper may preserve identity by exact argument forwarding;
constructing another container of equal shape does not.

An extent identifies one axis of one exact container. Extent equality is
symmetric and transitive, and exact equal counts establish extent equality.
It never establishes container, element or iteration-axis identity. An index
bound states `0 <= i < extent(v, axis)` under the adapter's unsigned-index
interpretation. The bound transfers to another extent only through established
extent equality. A known integer and an exact extent may establish the bound
by strict numerical comparison.

Adapters distinguish established premises from operations still to execute:

| Information | Meaning |
|---|---|
| Formation premise | An assumption whose caller must discharge before using a total helper |
| Result premise | A property derived from the actual construction of a result |
| Reached fact | A property established by successful admission at a particular program point |
| Ordered admission obligation | A program action that remains subject to control flow and failure order |

The current kernel accepts formation and result premises. Reached facts need a
control-flow adapter and a query policy that distinguishes them from formation
assumptions; they are not admitted by the current API. Ordered obligations do
not become facts merely by appearing in IR. A successful shape result does not
authorize erasing, moving or deduplicating a Local guard. A callee's formation
premises cannot discharge its caller's obligations by assuming them there.
Adapters establish type, axis, premise consistency and reachability before
asking the shared kernel for consequences.

## Scope and lifetime

Fact handles belong to a unique snapshot and cannot be used in another one.
Forking a scope copies its established facts; later additions to either scope
do not alter the other. A join retains only facts established on all incoming
paths that reach it. Intersecting identical explicit premises is a permitted
conservative implementation: it may omit a common consequence whose derivations
differ between branches. No fact from one branch alone may escape the join.

Loop entry, recurrence and zero-trip results are separate subjects. A property
of a callback result does not establish that property of the initial state or
of a loop that never executes. A consumer requiring a loop invariant must
establish it for entry and every applicable transition.

Changing a value, helper body, binding or relevant declaration invalidates its
analysis. Pass-managed SSA analysis is owned by the enclosing symbol closure;
function-local analysis cannot inspect concurrently mutable sibling bodies.
Analysis-manager invalidation does not make a borrowed view safe after mutation
inside a pass. Manual users must discard or rebuild it before querying again.
Clones and candidate programs have their own subjects and independently
extracted facts. Summary attributes and producer-selected access descriptions
are not authority for a checker.

## Counts and arithmetic

Cardinality has two precisions: an exact count or a nonnegative upper bound.
An unfiltered collection preserves the domain count. Filtering generally gives
only an upper bound; an upper bound of zero is also exact zero. An upper bound
alone cannot prove extent equality or that an arbitrary index is in range.

Product and sum combine counts with checked nonnegative arithmetic. Exactness
is retained only when justified by the operands. An exact zero factor makes a
product zero even when another factor's count is unknown. An empty product is
one. A half-open range has count `max(upper - lower, 0)`; subtraction occurs only
after ordering the endpoints. These count rules do not eliminate domain
admission, including unused constructors and empty products.

The shared constructor view borrows the existing finite-domain graph. Source
and SSA adapters independently identify extent leaves, ranges, zips, products
and matrix coordinates. A zip takes its first child's count; this does not
discharge the separate equal-size obligation. Matrix coordinates multiply row
and column counts. Structural equality can also follow from matching range
endpoints, corresponding product factors or both matrix extents. The view owns
neither program nodes nor an independent work allowance.

Source symbolic natural dimensions retain their source interpretation. An
adapter may establish equality between two such dimensions without reducing
them to runtime integers. Runtime `ui64` arithmetic is not mathematical integer
arithmetic: overflow-sensitive conclusions require a separate non-overflow
premise. An unrepresentable count is unknown, never a wrapped count.

## Work and independent extraction

Queries return one of three outcomes:

- **Proven:** the requested property follows from the admitted premises.
- **Unknown:** the supported rules or available premises do not establish it.
- **Capacity:** the shared allowance could not pay for extraction or derivation.

Unknown is not a proof of falsity. Capacity is not permission to infer an unmet
precondition, assert an equation, or publish an unchecked transformation. Every
nested query and extraction charges the same enclosing allowance. Exhaustion
remains visible even if an algebraic shortcut would otherwise yield zero.
Optional callers may retain the ordered path. Mandatory formation checks report
`finite-analysis-limit` on capacity and use the corresponding missing-evidence
diagnostic on unknown; source checks report `source.limit` on capacity.

Language and SSA adapters independently read their actual subjects. Optimizers
and validators may share the bounded fact kernel, whose implementation and
adapter extraction rules are part of the native checking trust boundary.
Tests of this implementation do not establish a correspondence with the
independent Lean models.
